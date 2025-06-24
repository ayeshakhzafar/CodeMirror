// Don't import z3-solver directly
// Instead, load it dynamically

// Initialize Z3 in the worker
let z3Instance = null;

async function initializeZ3() {
  try {
    console.log("Worker: Starting Z3 initialization");
    
    // Use fetch instead of importScripts for module workers
    const response = await fetch('/public/z3/z3-built.js'); 
    if (!response.ok) {
      console.error("Worker: Failed to fetch Z3 script:", response.statusText);
      return { success: false, error: `Failed to fetch Z3 script: ${response.statusText}` };
    }
    
    const scriptText = await response.text();
    
    // Execute the script safely using a Function constructor
    try {
      // Create a function that sets up a global variable to capture Z3
      const globalObj = {};
      const executeScript = new Function('global', `
        // Create a self object that the script can reference
        const self = global;
        ${scriptText};
        // If Z3 is defined globally, capture it
        if (typeof Z3 !== 'undefined') {
          global.Z3 = Z3;
        }
        // Some builds might assign to self or this instead
        else if (typeof self.Z3 !== 'undefined') {
          global.Z3 = self.Z3;
        }
        return global.Z3;
      `);
      
      // Execute the script with our global object
      const z3 = executeScript(globalObj);
      
      // Check if Z3 is available
      if (z3) {
        z3Instance = z3;
        console.log("Worker: Z3 initialized successfully");
        return { success: true };
      } else {
        console.error("Worker: Z3 object not found after loading script");
        return { success: false, error: "Z3 object not found" };
      }
    } catch (execError) {
      console.error("Worker: Error executing Z3 script:", execError);
      return { success: false, error: `Error executing Z3 script: ${execError.message}` };
    }
  } catch (error) {
    console.error("Worker: Z3 initialization failed:", error);
    return { success: false, error: error.message };
  }
}

// Rest of the code remains the same...
// Parse SMT assertions from SMT-LIB2 code
function parseSmtAssertions(smtCode) {
  console.log("Worker: Parsing SMT assertions");
  const assertions = [];
  const lines = smtCode.split("\n");
  let currentAssertion = "";
  let parenCount = 0;

  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed.startsWith("(assert") || parenCount > 0) {
      currentAssertion += trimmed + " ";
      
      // Count parentheses to handle multi-line assertions
      for (const char of trimmed) {
        if (char === '(') parenCount++;
        if (char === ')') parenCount--;
      }
      
      if (parenCount === 0 && currentAssertion.trim().length > 0) {
        assertions.push(currentAssertion.trim());
        currentAssertion = "";
      }
    }
  }

  console.log(`Worker: Found ${assertions.length} assertions`);
  return assertions;
}

// Extract variable declarations from SMT code
function extractVariableDeclarations(smtCode) {
  console.log("Worker: Extracting variable declarations");
  const declarations = [];
  const lines = smtCode.split("\n");
  
  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed.startsWith("(declare-const") || trimmed.startsWith("(declare-fun")) {
      declarations.push(trimmed);
    }
  }
  
  console.log(`Worker: Found ${declarations.length} variable declarations`);
  return declarations;
}

// Extract model values from Z3 model
function extractModelValues(model) {
  console.log("Worker: Extracting model values");
  const values = {};
  
  if (!model || typeof model.decls !== 'function') {
    console.warn("Worker: Invalid model or model.decls is not a function");
    return values;
  }
  
  try {
    const decls = model.decls();
    for (const decl of decls) {
      const name = decl.name().toString();
      const value = model.eval(decl.apply()).toString();
      values[name] = value;
    }
    console.log(`Worker: Extracted ${Object.keys(values).length} model values`);
  } catch (error) {
    console.error("Worker: Error extracting model values:", error);
  }
  
  return values;
}

// Solve SMT constraints using Z3
async function solveSMTWithZ3(smtCode) {
  console.log("Worker: Starting SMT solving");
  if (!z3Instance) {
    console.error("Worker: Z3 not initialized");
    throw new Error("Z3 not initialized");
  }
  
  try {
    console.log("Worker: Creating Z3 context and solver");
    const ctx = new z3Instance.Context();
    const solver = new ctx.Solver();
    
    // Extract declarations and add them to the solver
    const declarations = extractVariableDeclarations(smtCode);
    const declVars = {};
    
    console.log("Worker: Processing variable declarations");
    for (const decl of declarations) {
      if (decl.startsWith("(declare-const")) {
        // Parse (declare-const varName Int)
        const match = decl.match(/\(declare-const\s+([a-zA-Z0-9_]+)\s+([a-zA-Z]+)\)/);
        if (match) {
          const [_, varName, typeName] = match;
          let sort;
          
          if (typeName === "Int") {
            sort = ctx.IntSort();
          } else if (typeName === "Bool") {
            sort = ctx.BoolSort();
          } else {
            console.warn(`Worker: Skipping unsupported type: ${typeName}`);
            continue; // Skip unsupported types
          }
          
          declVars[varName] = ctx.constant(varName, sort);
        }
      } else if (decl.startsWith("(declare-fun")) {
        console.log("Worker: Array declaration found, using simplified handling");
      }
    }
    
    // Parse assertions and add them to the solver
    const assertions = parseSmtAssertions(smtCode);
    
    console.log("Worker: Adding assertions to solver");
    for (const assertion of assertions) {
      try {
        console.log(`Worker: Parsing assertion: ${assertion.substring(0, 50)}...`);
        const expr = ctx.parseSMTLIB2String(assertion, [], [], declVars);
        solver.add(expr[0]);
      } catch (error) {
        console.warn(`Worker: Failed to parse assertion: ${assertion.substring(0, 50)}...`, error);
      }
    }
    
    console.log("Worker: Checking satisfiability");
    const result = await solver.check();
    console.log(`Worker: Satisfiability result: ${result}`);
    
    if (result === "sat") {
      console.log("Worker: Getting model for satisfiable result");
      const model = solver.model();
      const modelValues = extractModelValues(model);
      
      return {
        satisfiable: true,
        model: modelValues
      };
    } else {
      console.log("Worker: Result is unsatisfiable, no model available");
      return {
        satisfiable: false,
        model: null
      };
    }
  } catch (error) {
    console.error("Worker: Error in Z3 solving:", error);
    throw error;
  }
}

// Handle messages from the main thread
self.onmessage = async function(e) {
  const { type, smtCode, id } = e.data;
  
  console.log(`Worker: Received message of type: ${type}`);
  
  if (type === 'init') {
    console.log("Worker: Initializing Z3");
    const result = await initializeZ3();
    console.log(`Worker: Z3 initialization result: ${result.success}`);
    self.postMessage({ type: 'init', result, id });
    return;
  }
  
  if (type === 'solve') {
    console.log("Worker: Solving SMT constraints");
    try {
      if (!z3Instance) {
        console.log("Worker: Z3 not initialized, initializing now");
        const initResult = await initializeZ3();
        if (!initResult.success) {
          console.error(`Worker: Failed to initialize Z3: ${initResult.error}`);
          throw new Error(`Failed to initialize Z3: ${initResult.error}`);
        }
      }
      
      console.log("Worker: Calling solveSMTWithZ3");
      const result = await solveSMTWithZ3(smtCode);
      console.log("Worker: Sending result back to main thread");
      self.postMessage({ type: 'result', result, id });
    } catch (error) {
      console.error("Worker: Error in solve handler:", error);
      self.postMessage({ 
        type: 'error', 
        error: error.message, 
        id 
      });
    }
  }
};