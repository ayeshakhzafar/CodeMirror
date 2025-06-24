/**
 * Convert an SSA expression to SMT-LIB2 format
 * @param {Object} expression - The SSA expression
 * @returns {string} SMT-LIB2 format expression
 */
function expressionToSMT(expression) {
  if (!expression) return ""

  switch (expression.type) {
    case "SSABinaryExpression":
      const left = expressionToSMT(expression.left)
      const right = expressionToSMT(expression.right)

      switch (expression.operator) {
        case "+":
          return `(+ ${left} ${right})`
        case "-":
          return `(- ${left} ${right})`
        case "*":
          return `(* ${left} ${right})`
        case "/":
          return `(div ${left} ${right})`
        case "%":
          return `(mod ${left} ${right})`
        case "==":
          return `(= ${left} ${right})`
        case "!=":
          return `(not (= ${left} ${right}))`
        case "<":
          return `(< ${left} ${right})`
        case "<=":
          return `(<= ${left} ${right})`
        case ">":
          return `(> ${left} ${right})`
        case ">=":
          return `(>= ${left} ${right})`
        case "&&":
          return `(and ${left} ${right})`
        case "||":
          return `(or ${left} ${right})`
        default:
          return `(unknown_op ${left} ${right})`
      }

    case "SSAIdentifier":
      return expression.name

    case "SSALiteral":
      return expression.value.toString()

    case "SSAArrayAccess":
      const arrayName = expressionToSMT(expression.array)
      const indexExpr = expressionToSMT(expression.index)

      // Use SMT array select operation
      return `(select ${arrayName} ${indexExpr})`

    case "SSAQuantifiedExpression":
      const varName = expression.variable.name
      const endExpr = expressionToSMT(expression.end)
      const bodyExpr = expressionToSMT(expression.body)

      // Create a quantified expression in SMT-LIB2 format
      if (expression.quantifier === "forall") {
        return `(forall ((${varName} Int)) (=> (and (>= ${varName} 0) (< ${varName} ${endExpr})) ${bodyExpr}))`
      } else if (expression.quantifier === "exists") {
        return `(exists ((${varName} Int)) (and (>= ${varName} 0) (< ${varName} ${endExpr}) ${bodyExpr}))`
      }
      return `(unknown_quantifier ${bodyExpr})`

    default:
      return `unknown_${expression.type}`
  }
}

/**
 * Generate SMT constraints for an assert statement
 * @param {Object} statement - The SSA assert statement
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForAssert(statement) {
  return expressionToSMT(statement.condition)
}

/**
 * Generate SMT constraints from SSA form
 * @param {Object} ssaForm - The program in SSA form
 * @returns {string} SMT-LIB2 format constraints
 */
export function generateSMT(ssaForm) {
  let smt = ""

  // Add header
  smt += "; SMT-LIB2 constraints generated from program\n"
  smt += "(set-logic QF_ALIA)\n\n" // Changed to QF_ALIA to support arrays

  // Collect all variables and their types
  const variables = collectVariables(ssaForm)
  const arrayVariables = variables.filter((v) => v.isArray)
  const scalarVariables = variables.filter((v) => !v.isArray)

  // Declare variables
  smt += "; Variable declarations\n"

  // Declare scalar variables
  scalarVariables.forEach((variable) => {
    smt += `(declare-const ${variable.name} Int)\n`
  })

  // Declare array variables using SMT arrays
  if (arrayVariables.length > 0) {
    smt += "\n; Array declarations\n"
    arrayVariables.forEach((variable) => {
      // Fix: Safely extract base name
      const baseName = getBaseVariableName(variable.name)
      smt += `(declare-const ${variable.name} (Array Int Int))\n`
    })
  }

  // Add range assumptions for input variables
  smt += "\n; Input variable constraints\n"
  scalarVariables.forEach((variable) => {
    smt += `(assert (and (>= ${variable.name} -100) (<= ${variable.name} 100)))\n`
  })

  // Add array size constraints
  if (arrayVariables.length > 0) {
    smt += "\n; Array size constraints\n"
    smt += "(declare-const array_size Int)\n"
    smt += "(assert (and (>= array_size 1) (<= array_size 10)))\n"
  }

  smt += "\n; Program constraints\n"

  // Generate constraints for each statement
  const constraints = []
  const assertions = []

  ssaForm.ssaStatements.forEach((statement) => {
    const result = generateConstraintsForStatement(statement)
    if (result) {
      if (statement.type === "SSAAssert") {
        assertions.push(result)
      } else {
        constraints.push(result)
      }
    }
  })

  // Add assertions for phi nodes
  ssaForm.phiNodes.forEach((node) => {
    const constraint = generateConstraintsForPhiNode(node)
    if (constraint) {
      constraints.push(constraint)
    }
  })

  // Add all program constraints
  if (constraints.length > 0) {
    smt += "(assert (and\n"
    constraints.forEach((constraint) => {
      smt += `  ${constraint}\n`
    })
    smt += "))\n"
  }

  // Add assertions to check
  if (assertions.length > 0) {
    smt += "\n; Assertions to check\n"
    smt += "(assert (not (and\n"
    assertions.forEach((assertion) => {
      smt += `  ${assertion}\n`
    })
    smt += ")))\n"
  }

  // Add closing commands
  smt += "\n(check-sat)\n(get-model)\n"

  return smt
}

/**
 * Helper function to safely get the base name of a variable
 * @param {string} name - The variable name
 * @returns {string} The base name of the variable
 */
function getBaseVariableName(name) {
  if (!name) return "unknown";
  
  // Check if the name contains an underscore
  const parts = name.split("_");
  if (parts.length > 1) {
    return parts[0];
  }
  
  return name;
}

/**
 * Collect all variables used in the SSA form
 * @param {Object} ssaForm - The program in SSA form
 * @returns {Array} List of variables with their types
 */
function collectVariables(ssaForm) {
  const variableSet = new Set()
  const variables = []
  const arrayVariables = new Set()

  // Process all statements to find variables
  ssaForm.ssaStatements.forEach((statement) => {
    collectVariablesFromStatement(statement, variableSet, arrayVariables)
  })

  // Process phi nodes
  ssaForm.phiNodes.forEach((node) => {
    variableSet.add(node.target)
    node.sources.forEach((source) => variableSet.add(source))
    if (node.condition) {
      collectVariablesFromExpression(node.condition, variableSet, arrayVariables)
    }
  })

  // Convert sets to arrays
  variableSet.forEach((varName) => {
    variables.push({
      name: varName,
      isArray: arrayVariables.has(getBaseVariableName(varName)),
    })
  })

  return variables
}

/**
 * Collect variables from a statement
 * @param {Object} statement - The SSA statement
 * @param {Set} variableSet - Set to collect variable names
 * @param {Set} arrayVariables - Set to collect array variable names
 */
function collectVariablesFromStatement(statement, variableSet, arrayVariables) {
  if (!statement) return;
  
  switch (statement.type) {
    case "SSAAssignment":
      variableSet.add(statement.target)
      collectVariablesFromExpression(statement.expression, variableSet, arrayVariables)
      break

    case "SSAArrayAssignment":
      variableSet.add(statement.target)
      arrayVariables.add(getBaseVariableName(statement.target))
      collectVariablesFromExpression(statement.index, variableSet, arrayVariables)
      collectVariablesFromExpression(statement.expression, variableSet, arrayVariables)
      break

    case "SSAIfStatement":
      collectVariablesFromExpression(statement.condition, variableSet, arrayVariables)
      if (statement.thenBlock && Array.isArray(statement.thenBlock)) {
        statement.thenBlock.forEach((s) => collectVariablesFromStatement(s, variableSet, arrayVariables))
      }
      if (statement.elseBlock && Array.isArray(statement.elseBlock)) {
        statement.elseBlock.forEach((s) => collectVariablesFromStatement(s, variableSet, arrayVariables))
      }
      break

    case "SSAAssert":
      collectVariablesFromExpression(statement.condition, variableSet, arrayVariables)
      break
  }
}

/**
 * Collect variables from an expression
 * @param {Object} expression - The SSA expression
 * @param {Set} variableSet - Set to collect variable names
 * @param {Set} arrayVariables - Set to collect array variable names
 */
function collectVariablesFromExpression(expression, variableSet, arrayVariables) {
  if (!expression) return

  switch (expression.type) {
    case "SSAIdentifier":
      if (expression.name) {
        variableSet.add(expression.name)
      }
      break

    case "SSABinaryExpression":
      collectVariablesFromExpression(expression.left, variableSet, arrayVariables)
      collectVariablesFromExpression(expression.right, variableSet, arrayVariables)
      break

    case "SSAArrayAccess":
      // Fix: Check if expression.array exists and has a name property
      if (expression.array) {
        if (expression.array.name) {
          const arrayName = getBaseVariableName(expression.array.name)
          arrayVariables.add(arrayName)
          variableSet.add(expression.array.name)
        } else if (expression.array.type === "SSAArrayAccess") {
          // Handle nested array access
          collectVariablesFromExpression(expression.array, variableSet, arrayVariables)
        }
      }
      collectVariablesFromExpression(expression.index, variableSet, arrayVariables)
      break

    case "SSAQuantifiedExpression":
      if (expression.variable && expression.variable.name) {
        variableSet.add(expression.variable.name)
      }
      collectVariablesFromExpression(expression.end, variableSet, arrayVariables)
      collectVariablesFromExpression(expression.body, variableSet, arrayVariables)
      break
  }
}

/**
 * Generate SMT constraints for a statement
 * @param {Object} statement - The SSA statement
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForStatement(statement) {
  if (!statement) return null;
  
  switch (statement.type) {
    case "SSAAssignment":
      return generateConstraintsForAssignment(statement)

    case "SSAArrayAssignment":
      return generateConstraintsForArrayAssignment(statement)

    case "SSAIfStatement":
      return generateConstraintsForIfStatement(statement)

    case "SSAAssert":
      return generateConstraintsForAssert(statement)

    case "SSAComment":
      return null // Comments don't generate constraints

    default:
      return null
  }
}

/**
 * Generate SMT constraints for an assignment
 * @param {Object} statement - The SSA assignment statement
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForAssignment(statement) {
  const target = statement.target
  const expression = expressionToSMT(statement.expression)

  return `(= ${target} ${expression})`
}

/**
 * Generate SMT constraints for an array assignment
 * @param {Object} statement - The SSA array assignment statement
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForArrayAssignment(statement) {
  const target = statement.target
  const index = expressionToSMT(statement.index)
  const value = expressionToSMT(statement.expression)

  // Use SMT array store operation
  return `(= ${target} (store ${target} ${index} ${value}))`
}

/**
 * Generate SMT constraints for an if statement
 * @param {Object} statement - The SSA if statement
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForIfStatement(statement) {
  const condition = expressionToSMT(statement.condition)

  // Generate constraints for then branch
  const thenConstraints = []
  if (statement.thenBlock && Array.isArray(statement.thenBlock)) {
    statement.thenBlock.forEach((stmt) => {
      const constraint = generateConstraintsForStatement(stmt)
      if (constraint) {
        thenConstraints.push(constraint)
      }
    })
  }

  // Generate constraints for else branch
  const elseConstraints = []
  if (statement.elseBlock && Array.isArray(statement.elseBlock)) {
    statement.elseBlock.forEach((stmt) => {
      const constraint = generateConstraintsForStatement(stmt)
      if (constraint) {
        elseConstraints.push(constraint)
      }
    })
  }

  // Combine constraints using implications
  let result = ""

  if (thenConstraints.length > 0) {
    const thenExpr = thenConstraints.length === 1 ? thenConstraints[0] : `(and ${thenConstraints.join(" ")})`
    result += `(=> ${condition} ${thenExpr})`
  }

  if (elseConstraints.length > 0) {
    const elseExpr = elseConstraints.length === 1 ? elseConstraints[0] : `(and ${elseConstraints.join(" ")})`

    if (result) {
      result = `(and ${result} (=> (not ${condition}) ${elseExpr}))`
    } else {
      result = `(=> (not ${condition}) ${elseExpr})`
    }
  }

  return result
}

/**
 * Generate SMT constraints for a phi node
 * @param {Object} node - The phi node
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForPhiNode(node) {
  if (!node || !node.condition || !node.sources || node.sources.length < 2) {
    return null;
  }
  
  const condition = expressionToSMT(node.condition)
  const thenSource = node.sources[0]
  const elseSource = node.sources[1]

  return `(= ${node.target} (ite ${condition} ${thenSource} ${elseSource}))`
}

/**
 * Generate SMT for checking program equivalence
 * @param {Object} ssaForm1 - The first program in SSA form
 * @param {Object} ssaForm2 - The second program in SSA form
 * @returns {string} SMT-LIB2 format constraints for equivalence checking
 */
export function generateEquivalenceSMT(ssaForm1, ssaForm2) {
  let smt = ""

  // Add header
  smt += "; SMT-LIB2 constraints for program equivalence checking\n"
  smt += "(set-logic QF_ALIA)\n\n" // Changed to QF_ALIA to support arrays

  // Collect all variables from both programs
  const variables1 = collectVariables(ssaForm1)
  const variables2 = collectVariables(ssaForm2)

  const arrayVars1 = variables1.filter((v) => v.isArray)
  const arrayVars2 = variables2.filter((v) => v.isArray)
  const scalarVars1 = variables1.filter((v) => !v.isArray)
  const scalarVars2 = variables2.filter((v) => !v.isArray)

  // Declare variables from both programs with prefixes
  smt += "; Variable declarations for both programs\n"

  // Declare scalar variables
  scalarVars1.forEach((variable) => {
    smt += `(declare-const p1_${variable.name} Int)\n`
  })

  scalarVars2.forEach((variable) => {
    smt += `(declare-const p2_${variable.name} Int)\n`
  })

  // Declare array variables
  if (arrayVars1.length > 0 || arrayVars2.length > 0) {
    smt += "\n; Array declarations\n"

    arrayVars1.forEach((variable) => {
      smt += `(declare-const p1_${variable.name} (Array Int Int))\n`
    })

    arrayVars2.forEach((variable) => {
      smt += `(declare-const p2_${variable.name} (Array Int Int))\n`
    })

    // Add array size constraint
    smt += "\n; Array size constraint\n"
    smt += "(declare-const array_size Int)\n"
    smt += "(assert (and (>= array_size 1) (<= array_size 10)))\n"
  }

  // Identify input and output variables
  const inputVars1 = variables1.filter((v) => !v.name.startsWith("output"))
  const inputVars2 = variables2.filter((v) => !v.name.startsWith("output"))
  const outputVars1 = variables1.filter((v) => v.name.startsWith("output"))
  const outputVars2 = variables2.filter((v) => v.name.startsWith("output"))

  // Generate program 1 constraints with p1_ prefix
  smt += "\n; Program 1 constraints\n"
  const constraints1 = []

  ssaForm1.ssaStatements.forEach((statement) => {
    const constraint = generateConstraintsForStatementWithPrefix(statement, "p1_")
    if (constraint) {
      constraints1.push(constraint)
    }
  })

  ssaForm1.phiNodes.forEach((node) => {
    const constraint = generateConstraintsForPhiNodeWithPrefix(node, "p1_")
    if (constraint) {
      constraints1.push(constraint)
    }
  })

  if (constraints1.length > 0) {
    smt += "(assert (and\n"
    constraints1.forEach((constraint) => {
      smt += `  ${constraint}\n`
    })
    smt += "))\n"
  }

  // Generate program 2 constraints with p2_ prefix
  smt += "\n; Program 2 constraints\n"
  const constraints2 = []

  ssaForm2.ssaStatements.forEach((statement) => {
    const constraint = generateConstraintsForStatementWithPrefix(statement, "p2_")
    if (constraint) {
      constraints2.push(constraint)
    }
  })

  ssaForm2.phiNodes.forEach((node) => {
    const constraint = generateConstraintsForPhiNodeWithPrefix(node, "p2_")
    if (constraint) {
      constraints2.push(constraint)
    }
  })

  if (constraints2.length > 0) {
    smt += "(assert (and\n"
    constraints2.forEach((constraint) => {
      smt += `  ${constraint}\n`
    })
    smt += "))\n"
  }

  // Add input equality constraints
  smt += "\n; Input equality constraints\n"
  smt += "(assert (and\n"

  // Make scalar input variables equal between programs
  const scalarInputPairs = []
  scalarVars1
    .filter((v) => !v.name.startsWith("output"))
    .forEach((var1) => {
      scalarVars2
        .filter((v) => !v.name.startsWith("output"))
        .forEach((var2) => {
          // Match variables by base name (without SSA suffix)
          const baseName1 = getBaseVariableName(var1.name)
          const baseName2 = getBaseVariableName(var2.name)

          if (baseName1 === baseName2) {
            scalarInputPairs.push(`  (= p1_${var1.name} p2_${var2.name})`)
          }
        })
    })

  // Make array input variables equal between programs
  const arrayInputPairs = []
  arrayVars1
    .filter((v) => !v.name.startsWith("output"))
    .forEach((var1) => {
      arrayVars2
        .filter((v) => !v.name.startsWith("output"))
        .forEach((var2) => {
          // Match variables by base name (without SSA suffix)
          const baseName1 = getBaseVariableName(var1.name)
          const baseName2 = getBaseVariableName(var2.name)

          if (baseName1 === baseName2) {
            // For arrays, we need to assert equality for all elements in range
            arrayInputPairs.push(
              `  (forall ((i Int)) (=> (and (>= i 0) (< i array_size)) (= (select p1_${var1.name} i) (select p2_${var2.name} i))))`,
            )
          }
        })
    })

  // Add all input equality constraints
  ;[...scalarInputPairs, ...arrayInputPairs].forEach((pair) => {
    smt += `${pair}\n`
  })

  smt += "))\n"

  // Add assertion for output inequality (to check for equivalence)
  smt += "\n; Output inequality assertion (for equivalence checking)\n"
  smt += "(assert (or\n"

  // Check for inequality in scalar output variables
  const scalarOutputPairs = []
  scalarVars1
    .filter((v) => v.name.startsWith("output"))
    .forEach((var1) => {
      scalarVars2
        .filter((v) => v.name.startsWith("output"))
        .forEach((var2) => {
          // Match output variables by base name
          const baseName1 = getBaseVariableName(var1.name)
          const baseName2 = getBaseVariableName(var2.name)

          if (baseName1 === baseName2) {
            scalarOutputPairs.push(`  (not (= p1_${var1.name} p2_${var2.name}))`)
          }
        })
    })

  // Check for inequality in array output variables
  const arrayOutputPairs = []
  arrayVars1
    .filter((v) => v.name.startsWith("output"))
    .forEach((var1) => {
      arrayVars2
        .filter((v) => v.name.startsWith("output"))
        .forEach((var2) => {
          // Match output variables by base name
          const baseName1 = getBaseVariableName(var1.name)
          const baseName2 = getBaseVariableName(var2.name)

          if (baseName1 === baseName2) {
            // For arrays, we need to check if any element differs
            arrayOutputPairs.push(
              `  (exists ((i Int)) (and (>= i 0) (< i array_size) (not (= (select p1_${var1.name} i) (select p2_${var2.name} i)))))`,
            )
          }
        })
    })

  // Add all output inequality constraints
  ;[...scalarOutputPairs, ...arrayOutputPairs].forEach((pair) => {
    smt += `${pair}\n`
  })

  // If no matching output variables found, use the last assigned variables
  if (scalarOutputPairs.length === 0 && arrayOutputPairs.length === 0) {
    const outputs1 = findOutputVariables(ssaForm1)
    const outputs2 = findOutputVariables(ssaForm2)

    outputs1.forEach((output, index) => {
      if (index < outputs2.length) {
        const isArray1 = arrayVars1.some((v) => v.name === output)
        const isArray2 = arrayVars2.some((v) => v.name === outputs2[index])

        if (isArray1 && isArray2) {
          smt += `  (exists ((i Int)) (and (>= i 0) (< i array_size) (not (= (select p1_${output} i) (select p2_${outputs2[index]} i)))))\n`
        } else {
          smt += `  (not (= p1_${output} p2_${outputs2[index]}))\n`
        }
      }
    })
  }

  smt += "))\n"

  // Add closing commands
  smt += "\n(check-sat)\n(get-model)\n"

  return smt
}

/**
 * Find output variables in an SSA form
 * @param {Object} ssaForm - The program in SSA form
 * @returns {Array} List of output variable names
 */
function findOutputVariables(ssaForm) {
  // For simplicity, we'll consider the last assigned variables as outputs
  const outputs = new Set()
  const assignments = new Map()

  // Collect all assignments
  ssaForm.ssaStatements.forEach((statement) => {
    if (statement.type === "SSAAssignment" || statement.type === "SSAArrayAssignment") {
      const baseName = getBaseVariableName(statement.target)

      if (!assignments.has(baseName)) {
        assignments.set(baseName, [])
      }

      assignments.get(baseName).push(statement.target)
    }
  })

  // For each variable, add the last assigned version to outputs
  assignments.forEach((versions, baseName) => {
    // Sort versions by their numeric suffix
    versions.sort((a, b) => {
      const numA = Number.parseInt(a.split("_")[1] || "0", 10)
      const numB = Number.parseInt(b.split("_")[1] || "0", 10)
      return numB - numA
    })

    // Add the highest version to outputs
    if (versions.length > 0) {
      outputs.add(versions[0])
    }
  })

  return Array.from(outputs)
}

/**
 * Generate constraints for a statement with a variable prefix
 * @param {Object} statement - The SSA statement
 * @param {string} prefix - Prefix to add to variable names
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForStatementWithPrefix(statement, prefix) {
  if (!statement) return null;
  
  switch (statement.type) {
    case "SSAAssignment":
      return generateConstraintsForAssignmentWithPrefix(statement, prefix)

    case "SSAArrayAssignment":
      return generateConstraintsForArrayAssignmentWithPrefix(statement, prefix)

    case "SSAIfStatement":
      return generateConstraintsForIfStatementWithPrefix(statement, prefix)

    case "SSAAssert":
      return generateConstraintsForAssertWithPrefix(statement, prefix)

    default:
      return null
  }
}

/**
 * Generate constraints for an assignment with a variable prefix
 * @param {Object} statement - The SSA assignment statement
 * @param {string} prefix - Prefix to add to variable names
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForAssignmentWithPrefix(statement, prefix) {
  const target = prefix + statement.target
  const expression = expressionToSMTWithPrefix(statement.expression, prefix)

  return `(= ${target} ${expression})`
}

/**
 * Generate constraints for an array assignment with a variable prefix
 * @param {Object} statement - The SSA array assignment statement
 * @param {string} prefix - Prefix to add to variable names
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForArrayAssignmentWithPrefix(statement, prefix) {
  const target = prefix + statement.target
  const index = expressionToSMTWithPrefix(statement.index, prefix)
  const value = expressionToSMTWithPrefix(statement.expression, prefix)

  // Use SMT array store operation
  return `(= ${target} (store ${target} ${index} ${value}))`
}

/**
 * Generate constraints for an if statement with a variable prefix
 * @param {Object} statement - The SSA if statement
 * @param {string} prefix - Prefix to add to variable names
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForIfStatementWithPrefix(statement, prefix) {
  const condition = expressionToSMTWithPrefix(statement.condition, prefix)

  // Generate constraints for then branch
  const thenConstraints = []
  if (statement.thenBlock && Array.isArray(statement.thenBlock)) {
    statement.thenBlock.forEach((stmt) => {
      const constraint = generateConstraintsForStatementWithPrefix(stmt, prefix)
      if (constraint) {
        thenConstraints.push(constraint)
      }
    })
  }

  // Generate constraints for else branch
  const elseConstraints = []
  if (statement.elseBlock && Array.isArray(statement.elseBlock)) {
    statement.elseBlock.forEach((stmt) => {
      const constraint = generateConstraintsForStatementWithPrefix(stmt, prefix)
      if (constraint) {
        elseConstraints.push(constraint)
      }
    })
  }

  // Combine constraints using implications
  let result = ""

  if (thenConstraints.length > 0) {
    const thenExpr = thenConstraints.length === 1 ? thenConstraints[0] : `(and ${thenConstraints.join(" ")})`
    result += `(=> ${condition} ${thenExpr})`
  }

  if (elseConstraints.length > 0) {
    const elseExpr = elseConstraints.length === 1 ? elseConstraints[0] : `(and ${elseConstraints.join(" ")})`

    if (result) {
      result = `(and ${result} (=> (not ${condition}) ${elseExpr}))`
    } else {
      result = `(=> (not ${condition}) ${elseExpr})`
    }
  }

  return result
}

/**
 * Generate constraints for an assert statement with a variable prefix
 * @param {Object} statement - The SSA assert statement
 * @param {string} prefix - Prefix to add to variable names
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForAssertWithPrefix(statement, prefix) {
  return expressionToSMTWithPrefix(statement.condition, prefix)
}

/**
 * Generate constraints for a phi node with a variable prefix
 * @param {Object} node - The phi node
 * @param {string} prefix - Prefix to add to variable names
 * @returns {string} SMT-LIB2 format constraints
 */
function generateConstraintsForPhiNodeWithPrefix(node, prefix) {
  if (!node || !node.condition || !node.sources || node.sources.length < 2) {
    return null;
  }
  
  const condition = expressionToSMTWithPrefix(node.condition, prefix)
  const thenSource = prefix + node.sources[0]
  const elseSource = prefix + node.sources[1]

  return `(= ${prefix}${node.target} (ite ${condition} ${thenSource} ${elseSource}))`
}

/**
 * Convert an SSA expression to SMT-LIB2 format with a variable prefix
 * @param {Object} expression - The SSA expression
 * @param {string} prefix - Prefix to add to variable names
 * @returns {string} SMT-LIB2 format expression
 */
function expressionToSMTWithPrefix(expression, prefix) {
  if (!expression) return ""

  switch (expression.type) {
    case "SSABinaryExpression":
      const left = expressionToSMTWithPrefix(expression.left, prefix)
      const right = expressionToSMTWithPrefix(expression.right, prefix)

      switch (expression.operator) {
        case "+":
          return `(+ ${left} ${right})`
        case "-":
          return `(- ${left} ${right})`
        case "*":
          return `(* ${left} ${right})`
        case "/":
          return `(div ${left} ${right})`
        case "%":
          return `(mod ${left} ${right})`
        case "==":
          return `(= ${left} ${right})`
        case "!=":
          return `(not (= ${left} ${right}))`
        case "<":
          return `(< ${left} ${right})`
        case "<=":
          return `(<= ${left} ${right})`
        case ">":
          return `(> ${left} ${right})`
        case ">=":
          return `(>= ${left} ${right})`
        case "&&":
          return `(and ${left} ${right})`
        case "||":
          return `(or ${left} ${right})`
        default:
          return `(unknown_op ${left} ${right})`
      }

    case "SSAIdentifier":
      return prefix + expression.name

    case "SSALiteral":
      return expression.value.toString()

    case "SSAArrayAccess":
      const arrayName = expressionToSMTWithPrefix(expression.array, prefix)
      const indexExpr = expressionToSMTWithPrefix(expression.index, prefix)

      // Use SMT array select operation
      return `(select ${arrayName} ${indexExpr})`

    case "SSAQuantifiedExpression":
      const varName = prefix + expression.variable.name
      const endExpr = expressionToSMTWithPrefix(expression.end, prefix)
      const bodyExpr = expressionToSMTWithPrefix(expression.body, prefix)

      // Create a quantified expression in SMT-LIB2 format
      if (expression.quantifier === "forall") {
        return `(forall ((${varName} Int)) (=> (and (>= ${varName} 0) (< ${varName} ${endExpr})) ${bodyExpr}))`
      } else if (expression.quantifier === "exists") {
        return `(exists ((${varName} Int)) (and (>= ${varName} 0) (< ${varName} ${endExpr}) ${bodyExpr}))`
      }
      return `(unknown_quantifier ${bodyExpr})`

    default:
      return `unknown_${expression.type}`
  }
}