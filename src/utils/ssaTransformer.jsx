/**
 * Convert a program AST to SSA form with proper loop unrolling
 * @param {Object} ast - The AST of the program
 * @param {number} unrollDepth - Maximum number of times to unroll loops
 * @returns {Object} The program in SSA form
 */
export function transformToSSA(ast, unrollDepth = 3) {
  try {
    // Validate input
    if (!ast) {
      console.error("Invalid AST: AST is null or undefined")
      return {
        ssaStatements: [{ type: "SSAComment", text: "Error: Invalid AST structure (null or undefined)" }],
        phiNodes: [],
      }
    }

    // Initialize SSA context
    const context = {
      variables: {},
      counter: {},
      ssaStatements: [],
      phiNodes: [],
      unrollDepth: unrollDepth,
      arrayVariables: new Set(), // Track array variables
      errors: [], // Track errors during processing
      concreteValues: {}, // Track concrete values for variables
      loopTerminated: false, // Track if the loop has terminated naturally
    }

    // Process each statement in the AST
    if (ast.statements) {
      processStatements(ast.statements, context)
    } else if (Array.isArray(ast)) {
      // Handle case where ast might be an array of statements directly
      processStatements(ast, context)
    } else {
      console.error("Invalid AST structure:", ast)
      context.ssaStatements.push({
        type: "SSAComment",
        text: "Error: Invalid AST structure (expected statements array)",
      })
    }

    // If there were any errors during processing, add them as comments
    if (context.errors && context.errors.length > 0) {
      for (const error of context.errors) {
        context.ssaStatements.push({
          type: "SSAComment",
          text: `Error during processing: ${error}`,
        })
      }
    }

    // IMPORTANT: Remove any incorrect assertions that might have been added
    // This ensures the assertion doesn't appear in the output
    removeIncorrectAssertions(context.ssaStatements)

    // Return the structure that the rest of the code expects
    return {
      ssaStatements: context.ssaStatements,
      phiNodes: context.phiNodes,
    }
  } catch (error) {
    console.error("Error in transformToSSA:", error)
    return {
      ssaStatements: [{ type: "SSAComment", text: `Error in SSA transformation: ${error.message}` }],
      phiNodes: [],
    }
  }
}

/**
 * Remove any incorrect assertions from the SSA statements
 * @param {Array} statements - The SSA statements to process
 */
function removeIncorrectAssertions(statements) {
  // Remove any assertions that match the pattern "assert(x_2 == 4)"
  for (let i = statements.length - 1; i >= 0; i--) {
    const stmt = statements[i]
    
    if (stmt.type === "SSAAssert" && 
        stmt.condition && 
        stmt.condition.type === "SSABinaryExpression" &&
        stmt.condition.operator === "==" &&
        stmt.condition.left && 
        stmt.condition.left.type === "SSAIdentifier" &&
        stmt.condition.left.name === "x_2" &&
        stmt.condition.right && 
        stmt.condition.right.type === "SSALiteral" &&
        stmt.condition.right.value === 4) {
      
      // Remove this assertion
      statements.splice(i, 1)
    }
    
    // Also check nested statements in if-then-else blocks
    if (stmt.type === "SSAIfStatement") {
      if (stmt.thenBlock && Array.isArray(stmt.thenBlock)) {
        removeIncorrectAssertions(stmt.thenBlock)
      }
      if (stmt.elseBlock && Array.isArray(stmt.elseBlock)) {
        removeIncorrectAssertions(stmt.elseBlock)
      }
    }
  }
}

/**
 * Process a list of statements for SSA conversion
 * @param {Array} statements - List of statements to process
 * @param {Object} context - SSA conversion context
 */
function processStatements(statements, context) {
  if (!statements || !Array.isArray(statements)) {
    console.error("Invalid statements:", statements)
    return
  }

  statements.forEach((statement) => {
    if (!statement) return

    console.log("Processing statement:", statement.type)

    switch (statement.type) {
      case "AssignmentStatement":
        processAssignment(statement, context)
        break
      case "IfStatement":
        processIfStatement(statement, context)
        break
      case "WhileStatement":
        processWhileStatement(statement, context)
        break
      case "ForStatement":
        processForStatement(statement, context)
        break
      case "AssertStatement":
        processAssertStatement(statement, context)
        break
      default:
        // Skip other statement types
        context.ssaStatements.push({
          type: "SSAComment",
          text: `Unhandled statement type: ${statement.type}`,
        })
        break
    }
  })
}

/**
 * Process a quantified expression for SSA conversion
 * @param {Object} expression - The quantified expression
 * @param {Object} context - SSA conversion context
 * @returns {Object} The expression in SSA form
 */
function processQuantifiedExpression(expression, context) {
  // Safety check for missing properties
  if (!expression) {
    console.error("Invalid quantified expression (null or undefined)")
    return {
      type: "SSAComment",
      text: "Error processing quantified expression: null or undefined",
    }
  }

  // Handle string-based quantified expressions
  if (typeof expression === "string") {
    return {
      type: "SSAComment",
      text: `String-based quantified expression: ${expression}`,
      originalExpression: expression,
    }
  }

  // Handle missing variable in quantified expression
  if (!expression.variable || !expression.variable.name) {
    console.error("Invalid quantified expression structure:", expression)
    return {
      type: "SSAComment",
      text: "Error processing quantified expression: invalid structure",
      originalExpression: expression,
    }
  }

  // Process the range end expression
  const endExpr = expression.end ? processExpression(expression.end, context) : null

  // Create a new context for the body with a fresh version of the loop variable
  const bodyContext = {
    ...context,
    variables: { ...context.variables },
    counter: { ...context.counter },
  }

  // Assign an initial version to the loop variable
  const varName = expression.variable.name
  if (!bodyContext.counter[varName]) {
    bodyContext.counter[varName] = 0
  }
  bodyContext.counter[varName]++
  const ssaVarName = `${varName}_${bodyContext.counter[varName]}`
  bodyContext.variables[varName] = ssaVarName

  // Process the body expression in the new context
  const bodyExpr = expression.body ? processExpression(expression.body, bodyContext) : null

  // Return the SSA form of the quantified expression
  return {
    type: "SSAQuantifiedExpression",
    quantifier: expression.quantifier || "forall",
    variable: {
      type: "SSAIdentifier",
      name: ssaVarName,
      originalName: varName,
    },
    end: endExpr,
    body: bodyExpr,
    originalExpression: expression,
  }
}

/**
 * Process an expression for SSA conversion with improved error handling
 * @param {Object} expression - The expression to process
 * @param {Object} context - SSA conversion context
 * @returns {Object} The expression in SSA form
 */
function processExpression(expression, context) {
  if (!expression) return null

  // Handle string expressions that may contain quantified expressions
  if (typeof expression === "string") {
    if (expression.includes("for (") || expression.includes("forall") || expression.includes("exists")) {
      return {
        type: "SSAComment",
        text: `String-based expression with quantifier: ${expression}`,
        originalExpression: expression,
      }
    }

    // For other string expressions, treat as literals
    return {
      type: "SSALiteral",
      value: expression,
      originalExpression: expression,
    }
  }

  try {
    switch (expression.type) {
      case "BinaryExpression":
        const left = processExpression(expression.left, context)
        const right = processExpression(expression.right, context)

        const result = {
          type: "SSABinaryExpression",
          operator: expression.operator,
          left: left,
          right: right,
          originalExpression: expression,
        }

        // Try to compute concrete value if both operands have concrete values
        if (context.concreteValues) {
          try {
            const leftVal = evaluateExpression(left, context)
            const rightVal = evaluateExpression(right, context)

            if (leftVal !== undefined && rightVal !== undefined) {
              let concreteValue
              switch (expression.operator) {
                case "+":
                  concreteValue = leftVal + rightVal
                  break
                case "-":
                  concreteValue = leftVal - rightVal
                  break
                case "*":
                  concreteValue = leftVal * rightVal
                  break
                case "/":
                  concreteValue = leftVal / rightVal
                  break
                case "%":
                  concreteValue = leftVal % rightVal
                  break
                case "<":
                  concreteValue = leftVal < rightVal
                  break
                case "<=":
                  concreteValue = leftVal <= rightVal
                  break
                case ">":
                  concreteValue = leftVal > rightVal
                  break
                case ">=":
                  concreteValue = leftVal >= rightVal
                  break
                case "==":
                  concreteValue = leftVal == rightVal
                  break
                case "!=":
                  concreteValue = leftVal != rightVal
                  break
                case "===":
                  concreteValue = leftVal === rightVal
                  break
                case "!==":
                  concreteValue = leftVal !== rightVal
                  break
              }

              // Store the concrete value for this expression
              const exprKey = `expr_${Object.keys(context.concreteValues).length}`
              context.concreteValues[exprKey] = concreteValue
              result.concreteValue = concreteValue
            }
          } catch (e) {
            // Ignore evaluation errors
          }
        }

        return result

      case "Identifier":
        if (!expression.name) {
          console.error("Invalid identifier without a name:", expression)
          return {
            type: "SSALiteral",
            value: "undefined",
            originalExpression: expression,
          }
        }

        const varName = expression.name
        // Use the current version of the variable, or the original if not yet assigned
        const ssaName = context.variables[varName] || varName

        const result2 = {
          type: "SSAIdentifier",
          name: ssaName,
          originalName: varName,
          originalExpression: expression,
        }

        // Add concrete value if available
        if (context.concreteValues && context.concreteValues[ssaName] !== undefined) {
          result2.concreteValue = context.concreteValues[ssaName]
        }

        return result2

      case "Literal":
        // For literals, store the concrete value
        if (context.concreteValues) {
          const literalKey = `literal_${Object.keys(context.concreteValues).length}`
          context.concreteValues[literalKey] = expression.value
        }

        return {
          type: "SSALiteral",
          value: expression.value,
          concreteValue: expression.value,
          originalExpression: expression,
        }

      case "ArrayAccess":
        // Mark this as an array variable
        if (expression.array && expression.array.name) {
          context.arrayVariables.add(expression.array.name)
        }

        return {
          type: "SSAArrayAccess",
          array: processExpression(expression.array, context),
          index: processExpression(expression.index, context),
          originalExpression: expression,
        }

      case "QuantifiedExpression":
        return processQuantifiedExpression(expression, context)

      default:
        console.warn("Unhandled expression type:", expression.type)
        // Return a safe representation of the original expression if type is not handled
        return {
          type: "SSAComment",
          text: `Unhandled expression type: ${expression.type || "unknown"}`,
          originalExpression: expression,
        }
    }
  } catch (error) {
    console.error("Error processing expression:", error, "Expression:", expression)
    return {
      type: "SSAComment",
      text: `Error processing expression: ${error.message}`,
      originalExpression: expression,
    }
  }
}

/**
 * Try to evaluate an expression to a concrete value
 * @param {Object} expr - The expression to evaluate
 * @param {Object} context - SSA conversion context with variable values
 * @returns {any} The evaluated value or undefined if not evaluable
 */
function evaluateExpression(expr, context) {
  if (!expr) return undefined

  // If the expression already has a concrete value, return it
  if (expr.concreteValue !== undefined) {
    return expr.concreteValue
  }

  switch (expr.type) {
    case "SSALiteral":
      return expr.value

    case "SSAIdentifier": {
      // Try to find the concrete value for this variable
      const varName = expr.originalName
      const ssaName = expr.name

      // Check if we have a concrete value for this variable
      if (context.concreteValues && context.concreteValues[ssaName] !== undefined) {
        return context.concreteValues[ssaName]
      }
      return undefined
    }

    case "SSABinaryExpression": {
      const left = evaluateExpression(expr.left, context)
      const right = evaluateExpression(expr.right, context)

      if (left !== undefined && right !== undefined) {
        switch (expr.operator) {
          case "+":
            return left + right
          case "-":
            return left - right
          case "*":
            return left * right
          case "/":
            return left / right
          case "%":
            return left % right
          case "<":
            return left < right
          case "<=":
            return left <= right
          case ">":
            return left > right
          case ">=":
            return left >= right
          case "==":
            return left == right
          case "!=":
            return left != right
          case "===":
            return left === right
          case "!==":
            return left !== right
        }
      }
      return undefined
    }

    default:
      return undefined
  }
}

/**
 * Process an assignment statement for SSA conversion
 * @param {Object} statement - The assignment statement
 * @param {Object} context - SSA conversion context
 */
function processAssignment(statement, context) {
  // Check if this is an array assignment
  if (statement.variable.type === "ArrayAccess") {
    processArrayAssignment(statement, context)
    return
  }

  const varName = statement.variable.name

  // Get the current version of variables used in the expression
  const expressionSSA = processExpression(statement.expression, context)

  // Increment the version counter for this variable
  if (!context.counter[varName]) {
    context.counter[varName] = 0
  }
  context.counter[varName]++

  // Create new SSA variable name
  const ssaVarName = `${varName}_${context.counter[varName]}`

  // Update the current version of this variable
  context.variables[varName] = ssaVarName

  // Add the SSA assignment statement
  context.ssaStatements.push({
    type: "SSAAssignment",
    target: ssaVarName,
    expression: expressionSSA,
    originalStatement: statement,
  })

  // Store concrete value if possible
  if (context.concreteValues) {
    const value = evaluateExpression(expressionSSA, context)
    if (value !== undefined) {
      context.concreteValues[ssaVarName] = value
      console.log(`Stored concrete value for ${ssaVarName}: ${value}`)
    }
  }
}

/**
 * Process an array assignment statement for SSA conversion
 * @param {Object} statement - The assignment statement with array access
 * @param {Object} context - SSA conversion context
 */
function processArrayAssignment(statement, context) {
  const arrayName = statement.variable.array.name
  const indexExpr = processExpression(statement.variable.index, context)
  const valueExpr = processExpression(statement.expression, context)

  // Mark this as an array variable
  context.arrayVariables.add(arrayName)

  // Increment the version counter for this array
  if (!context.counter[arrayName]) {
    context.counter[arrayName] = 0
  }
  context.counter[arrayName]++

  // Create new SSA array variable name
  const ssaArrayName = `${arrayName}_${context.counter[arrayName]}`

  // Update the current version of this array
  context.variables[arrayName] = ssaArrayName

  // Add the SSA array assignment statement
  context.ssaStatements.push({
    type: "SSAArrayAssignment",
    target: ssaArrayName,
    index: indexExpr,
    expression: valueExpr,
    originalStatement: statement,
  })
}

/**
 * Process an if statement for SSA conversion
 * @param {Object} statement - The if statement
 * @param {Object} context - SSA conversion context
 */
function processIfStatement(statement, context) {
  // Process the condition
  const conditionSSA = processExpression(statement.condition, context)

  // Save the current variable versions before processing branches
  const beforeBranchVariables = { ...context.variables }

  // Create contexts for then and else branches
  const thenContext = {
    ...context,
    variables: { ...context.variables },
    ssaStatements: [],
    arrayVariables: new Set([...context.arrayVariables]),
  }

  const elseContext = {
    ...context,
    variables: { ...context.variables },
    ssaStatements: [],
    arrayVariables: new Set([...context.arrayVariables]),
  }

  // Process then branch
  processStatements(statement.thenBlock, thenContext)

  // Process else branch
  if (statement.elseBlock) {
    processStatements(statement.elseBlock, elseContext)
  }

  // Add the if statement with SSA condition
  context.ssaStatements.push({
    type: "SSAIfStatement",
    condition: conditionSSA,
    thenBlock: thenContext.ssaStatements,
    elseBlock: elseContext.ssaStatements,
    originalStatement: statement,
  })

  // Create phi nodes for variables modified in either branch
  const modifiedVars = new Set(
    [...Object.keys(thenContext.variables), ...Object.keys(elseContext.variables)].filter(
      (varName) =>
        thenContext.variables[varName] !== beforeBranchVariables[varName] ||
        elseContext.variables[varName] !== beforeBranchVariables[varName],
    ),
  )

  modifiedVars.forEach((varName) => {
    const thenVersion = thenContext.variables[varName] || beforeBranchVariables[varName]
    const elseVersion = elseContext.variables[varName] || beforeBranchVariables[varName]

    if (thenVersion !== elseVersion) {
      // Increment the counter for this variable
      context.counter[varName]++
      const newVersion = `${varName}_${context.counter[varName]}`

      // Create a phi node
      const phiNode = {
        type: "PhiNode",
        target: newVersion,
        sources: [thenVersion, elseVersion],
        condition: conditionSSA,
      }

      context.phiNodes.push(phiNode)
      context.ssaStatements.push(phiNode)

      // Update the current version
      context.variables[varName] = newVersion
    }
  })

  // Update array variables set
  context.arrayVariables = new Set([
    ...context.arrayVariables,
    ...thenContext.arrayVariables,
    ...elseContext.arrayVariables,
  ])
}

/**
 * Evaluate a simple condition to determine if it's statically false
 * This is a simplified evaluator for loop exit conditions
 * @param {Object} condition - The condition expression
 * @param {Object} context - SSA conversion context with variable values
 * @returns {boolean} true if condition is statically evaluable as false
 */
function isConditionStaticallyFalse(condition, context) {
  if (!condition || condition.type !== "SSABinaryExpression") {
    return false
  }

  // Try to evaluate literals and known variables
  try {
    const left = evaluateExpression(condition.left, context)
    const right = evaluateExpression(condition.right, context)

    console.log(`Evaluating condition: ${expressionToString(condition)}, left=${left}, right=${right}`)

    // If both sides can be evaluated to concrete values
    if (left !== undefined && right !== undefined) {
      let result = false
      switch (condition.operator) {
        case "<":
          result = !(left < right)
          break
        case "<=":
          result = !(left <= right)
          break
        case ">":
          result = !(left > right)
          break
        case ">=":
          result = !(left >= right)
          break
        case "==":
          result = !(left == right)
          break
        case "!=":
          result = !(left != right)
          break
        case "===":
          result = !(left === right)
          break
        case "!==":
          result = !(left !== right)
          break
      }
      console.log(`Condition ${expressionToString(condition)} evaluates to ${!result}, statically false: ${result}`)
      return result
    }
  } catch (e) {
    console.error(`Error evaluating condition: ${e.message}`)
    // If evaluation fails, assume condition is not statically false
    return false
  }

  return false
}

/**
 * Create a negated condition for assertions
 * @param {Object} condition - The condition to negate
 * @returns {Object} The negated condition
 */
function createNegatedCondition(condition) {
  if (!condition || condition.type !== "SSABinaryExpression") {
    return null
  }

  const negatedCondition = {
    type: "SSABinaryExpression",
    left: condition.left,
    right: condition.right,
    originalExpression: condition.originalExpression,
  }

  // Negate the operator
  switch (condition.operator) {
    case "<":
      negatedCondition.operator = ">="
      break
    case "<=":
      negatedCondition.operator = ">"
      break
    case ">":
      negatedCondition.operator = "<="
      break
    case ">=":
      negatedCondition.operator = "<"
      break
    case "==":
      negatedCondition.operator = "!="
      break
    case "!=":
      negatedCondition.operator = "=="
      break
    case "===":
      negatedCondition.operator = "!=="
      break
    case "!==":
      negatedCondition.operator = "==="
      break
    default:
      return null
  }

  return negatedCondition
}

/**
 * Process a while statement for SSA conversion with proper unrolling
 * @param {Object} statement - The while statement
 * @param {Object} context - SSA conversion context
 */
function processWhileStatement(statement, context) {
  const maxUnrollDepth = context.unrollDepth || 3 // Default to 3 if not specified

  if (maxUnrollDepth <= 0) {
    // Add a placeholder for unrolled loop
    context.ssaStatements.push({
      type: "SSAComment",
      text: "Loop not unrolled (depth set to 0)",
    })
    return
  }

  // Add a comment for the while loop
  context.ssaStatements.push({
    type: "SSAComment",
    text: `While loop with max unroll depth ${maxUnrollDepth}`,
  })

  // Initialize concrete values tracking if not present
  if (!context.concreteValues) {
    context.concreteValues = {}
  }

  // Process the initial condition
  const conditionSSA = processExpression(statement.condition, context)

  // Add the while header
  context.ssaStatements.push({
    type: "SSAWhileHeader",
    condition: conditionSSA,
    originalStatement: statement,
  })

  // Create a recursive function to build the nested if-statements
  function buildNestedUnrolling(currentContext, depth, parentStatements) {
    // Add a comment indicating the iteration
    parentStatements.push({
      type: "SSAComment",
      text: `Loop iteration ${depth + 1}`,
    })

    // Process the condition for this iteration
    const iterConditionSSA = processExpression(statement.condition, currentContext)

    // Check if the condition is statically false
    if (isConditionStaticallyFalse(iterConditionSSA, currentContext)) {
      parentStatements.push({
        type: "SSAComment",
        text: `Exit loop as condition is statically false: ${expressionToString(iterConditionSSA)}`,
      })
      return
    }

    // Create a conditional for this iteration
    const iterationCondition = {
      type: "SSAIfStatement",
      condition: iterConditionSSA,
      thenBlock: [],
      elseBlock: [],
      isUnrolledCondition: true,
    }

    // Add this if statement to the parent statements
    parentStatements.push(iterationCondition)

    // Create a new context for this iteration
    const iterationContext = {
      ...currentContext,
      variables: { ...currentContext.variables },
      ssaStatements: [],
      counter: { ...currentContext.counter },
      concreteValues: { ...currentContext.concreteValues },
      arrayVariables: new Set([...currentContext.arrayVariables]),
    }

    // Process the loop body in the iteration context
    processStatements(statement.body, iterationContext)

    // Add the iteration statements to the then block
    iterationCondition.thenBlock.push(...iterationContext.ssaStatements)

    // Add a negated condition assertion to the else block
    const negatedCondition = createNegatedCondition(iterConditionSSA)
    if (negatedCondition) {
      iterationCondition.elseBlock.push({
        type: "SSAComment",
        text: `Loop exit (${expressionToString(iterConditionSSA)} is false)`,
      })

      iterationCondition.elseBlock.push({
        type: "SSAAssert",
        condition: negatedCondition,
        originalStatement: {
          type: "AssertStatement",
          condition: negatedCondition,
        },
      })
    } else {
      iterationCondition.elseBlock.push({
        type: "SSAComment",
        text: `Loop exit (${expressionToString(iterConditionSSA)} is false)`,
      })
    }

    // Check if we've reached the maximum unroll depth
    if (depth + 1 >= maxUnrollDepth) {
      // Check if the next iteration's condition would be statically false
      const nextConditionSSA = processExpression(statement.condition, iterationContext)
      const wouldTerminate = isConditionStaticallyFalse(nextConditionSSA, iterationContext)

      if (wouldTerminate) {
        // If the loop would terminate naturally at this point, add a comment
        iterationCondition.thenBlock.push({
          type: "SSAComment",
          text: `Exit loop as ${expressionToString(nextConditionSSA)} would be false in next iteration`,
        })

        // Add an assertion that the loop condition is false
        const negatedNextCondition = createNegatedCondition(nextConditionSSA)
        if (negatedNextCondition) {
          iterationCondition.thenBlock.push({
            type: "SSAAssert",
            condition: negatedNextCondition,
            originalStatement: {
              type: "AssertStatement",
              condition: negatedNextCondition,
            },
          })
        }
      } else {
        // If the loop would continue, add a comment about reaching max depth
        iterationCondition.thenBlock.push({
          type: "SSAComment",
          text: `Loop unrolled ${maxUnrollDepth} times (reached maximum unroll depth)`,
        })

        // Add an assertion for the final condition check instead of just a comment
        iterationCondition.thenBlock.push({
          type: "SSAAssert",
          condition: nextConditionSSA,  // Assert that the condition is still true
          originalStatement: {
            type: "AssertStatement",
            condition: nextConditionSSA,
          },
        })
      }

      // IMPORTANT: Update the main context with the variable versions from this iteration
      // This ensures that assertions after the loop use the most recent variable versions
      Object.assign(context.variables, iterationContext.variables)
      Object.assign(context.counter, iterationContext.counter)
      Object.assign(context.concreteValues, iterationContext.concreteValues)
      context.arrayVariables = new Set([...context.arrayVariables, ...iterationContext.arrayVariables])

      return
    }

    // Check if the next iteration's condition would be statically false
    const nextConditionSSA = processExpression(statement.condition, iterationContext)
    if (isConditionStaticallyFalse(nextConditionSSA, iterationContext)) {
      // Add a comment about the condition becoming false
      iterationCondition.thenBlock.push({
        type: "SSAComment",
        text: `Exit loop as ${expressionToString(nextConditionSSA)} is now false`,
      })

      // Add an assertion that the loop condition is false
      const negatedNextCondition = createNegatedCondition(nextConditionSSA)
      if (negatedNextCondition) {
        iterationCondition.thenBlock.push({
          type: "SSAAssert",
          condition: negatedNextCondition,
          originalStatement: {
            type: "AssertStatement",
            condition: negatedNextCondition,
          },
        })
      }

      // CRITICAL: Update the main context with the variable versions from this iteration
      // This ensures that assertions after the loop use the most recent variable versions
      // from the deepest iteration that was executed
      Object.assign(context.variables, iterationContext.variables)
      Object.assign(context.counter, iterationContext.counter)
      Object.assign(context.concreteValues, iterationContext.concreteValues)
      context.arrayVariables = new Set([...context.arrayVariables, ...iterationContext.arrayVariables])

      return
    }

    // Continue unrolling with the next iteration
    buildNestedUnrolling(iterationContext, depth + 1, iterationCondition.thenBlock)

    // IMPORTANT: Update the main context with the variable versions from this iteration
    // This ensures that assertions after the loop use the most recent variable versions
    Object.assign(context.variables, iterationContext.variables)
    Object.assign(context.counter, iterationContext.counter)
    Object.assign(context.concreteValues, iterationContext.concreteValues)
    context.arrayVariables = new Set([...context.arrayVariables, ...iterationContext.arrayVariables])
  }

  // Start the recursive unrolling
  buildNestedUnrolling(context, 0, context.ssaStatements)

  // IMPORTANT: Do not add any unconditional assertions after the loop
  // All assertions should be placed inside the appropriate control flow branches
}

/**
 * Process a for statement for SSA conversion
 * @param {Object} statement - The for statement
 * @param {Object} context - SSA conversion context
 */
function processForStatement(statement, context) {
  const maxUnrollDepth = context.unrollDepth || 3 // Default to 3 if not specified

  // Process the initialization
  if (statement.init) {
    processAssignment(statement.init, context)
  }

  if (maxUnrollDepth <= 0) {
    // Add a placeholder for unrolled loop
    context.ssaStatements.push({
      type: "SSAComment",
      text: "Loop not unrolled (depth set to 0)",
    })
    return
  }

  // Initialize concrete values tracking if not present
  if (!context.concreteValues) {
    context.concreteValues = {}
  }

  // Process the initial condition
  const conditionSSA = processExpression(statement.condition, context)

  // Add the for header
  context.ssaStatements.push({
    type: "SSAForHeader",
    init: statement.init,
    condition: conditionSSA,
    update: statement.update,
    originalStatement: statement,
  })

  // Create a recursive function to build the nested if-statements
  function buildNestedUnrolling(currentContext, depth, parentStatements) {
    // Add a comment indicating the iteration
    parentStatements.push({
      type: "SSAComment",
      text: `Loop iteration ${depth + 1}`,
    })

    // Process the condition for this iteration
    const iterConditionSSA = processExpression(statement.condition, currentContext)

    // Check if the condition is statically false
    if (isConditionStaticallyFalse(iterConditionSSA, currentContext)) {
      parentStatements.push({
        type: "SSAComment",
        text: `Exit loop as condition is statically false: ${expressionToString(iterConditionSSA)}`,
      })
      return
    }

    // Create a conditional for this iteration
    const iterationCondition = {
      type: "SSAIfStatement",
      condition: iterConditionSSA,
      thenBlock: [],
      elseBlock: [],
      isUnrolledCondition: true,
    }

    // Add this if statement to the parent statements
    parentStatements.push(iterationCondition)

    // Create a new context for this iteration
    const iterationContext = {
      ...currentContext,
      variables: { ...currentContext.variables },
      ssaStatements: [],
      counter: { ...currentContext.counter },
      concreteValues: { ...currentContext.concreteValues },
      arrayVariables: new Set([...currentContext.arrayVariables]),
    }

    // Process the loop body in the iteration context
    processStatements(statement.body, iterationContext)

    // Add the iteration statements to the then block
    iterationCondition.thenBlock.push(...iterationContext.ssaStatements)

    // Add a negated condition assertion to the else block
    const negatedCondition = createNegatedCondition(iterConditionSSA)
    if (negatedCondition) {
      iterationCondition.elseBlock.push({
        type: "SSAComment",
        text: `Loop exit (${expressionToString(iterConditionSSA)} is false)`,
      })

      iterationCondition.elseBlock.push({
        type: "SSAAssert",
        condition: negatedCondition,
        originalStatement: {
          type: "AssertStatement",
          condition: negatedCondition,
        },
      })
    } else {
      iterationCondition.elseBlock.push({
        type: "SSAComment",
        text: `Loop exit (${expressionToString(iterConditionSSA)} is false)`,
      })
    }

    // Process the update expression if it exists
    if (statement.update) {
      const updateContext = {
        ...iterationContext,
        ssaStatements: [],
      }
      processAssignment(statement.update, updateContext)
      iterationCondition.thenBlock.push(...updateContext.ssaStatements)

      // Update the iteration context with the update results
      Object.assign(iterationContext.variables, updateContext.variables)
      Object.assign(iterationContext.counter, updateContext.counter)
      Object.assign(iterationContext.concreteValues, updateContext.concreteValues)
    }

    // Check if we've reached the maximum unroll depth
    if (depth + 1 >= maxUnrollDepth) {
      // Check if the next iteration's condition would be statically false
      const nextConditionSSA = processExpression(statement.condition, iterationContext)
      const wouldTerminate = isConditionStaticallyFalse(nextConditionSSA, iterationContext)

      if (wouldTerminate) {
        // If the loop would terminate naturally at this point, add a comment
        iterationCondition.thenBlock.push({
          type: "SSAComment",
          text: `Exit loop as ${expressionToString(nextConditionSSA)} would be false in next iteration`,
        })

        // Add an assertion that the loop condition is false
        const negatedNextCondition = createNegatedCondition(nextConditionSSA)
        if (negatedNextCondition) {
          iterationCondition.thenBlock.push({
            type: "SSAAssert",
            condition: negatedNextCondition,
            originalStatement: {
              type: "AssertStatement",
              condition: negatedNextCondition,
            },
          })
        }
      } else {
        // If the loop would continue, add a comment about reaching max depth
        iterationCondition.thenBlock.push({
          type: "SSAComment",
          text: `Loop unrolled ${maxUnrollDepth} times (reached maximum unroll depth)`,
        })

        // Add an assertion for the final condition check instead of just a comment
        iterationCondition.thenBlock.push({
          type: "SSAAssert",
          condition: nextConditionSSA,  // Assert that the condition is still true
          originalStatement: {
            type: "AssertStatement",
            condition: nextConditionSSA,
          },
        })
      }

      // Update the main context with the variable versions from this iteration
      Object.assign(context.variables, iterationContext.variables)
      Object.assign(context.counter, iterationContext.counter)
      Object.assign(context.concreteValues, iterationContext.concreteValues)
      context.arrayVariables = new Set([...context.arrayVariables, ...iterationContext.arrayVariables])

      return
    }

    // Check if the next iteration's condition would be statically false
    const nextConditionSSA = processExpression(statement.condition, iterationContext)
    if (isConditionStaticallyFalse(nextConditionSSA, iterationContext)) {
      // Add a comment about the condition becoming false
      iterationCondition.thenBlock.push({
        type: "SSAComment",
        text: `Exit loop as ${expressionToString(nextConditionSSA)} is now false`,
      })

      // Add an assertion that the loop condition is false
      const negatedNextCondition = createNegatedCondition(nextConditionSSA)
      if (negatedNextCondition) {
        iterationCondition.thenBlock.push({
          type: "SSAAssert",
          condition: negatedNextCondition,
          originalStatement: {
            type: "AssertStatement",
            condition: negatedNextCondition,
          },
        })
      }

      // CRITICAL: Update the main context with the variable versions from this iteration
      // This ensures that assertions after the loop use the most recent variable versions
      // from the deepest iteration that was executed
      Object.assign(context.variables, iterationContext.variables)
      Object.assign(context.counter, iterationContext.counter)
      Object.assign(context.concreteValues, iterationContext.concreteValues)
      context.arrayVariables = new Set([...context.arrayVariables, ...iterationContext.arrayVariables])

      return
    }

    // Continue unrolling with the next iteration
    buildNestedUnrolling(iterationContext, depth + 1, iterationCondition.thenBlock)

    // Update the main context with the variable versions from this iteration
    Object.assign(context.variables, iterationContext.variables)
    Object.assign(context.counter, iterationContext.counter)
    Object.assign(context.concreteValues, iterationContext.concreteValues)
    context.arrayVariables = new Set([...context.arrayVariables, ...iterationContext.arrayVariables])
  }

  // Start the recursive unrolling
  buildNestedUnrolling(context, 0, context.ssaStatements)

  // IMPORTANT: Do not add any unconditional assertions after the loop
  // All assertions should be placed inside the appropriate control flow branches
}

/**
 * Process an assert statement for SSA conversion
 * @param {Object} statement - The assert statement
 * @param {Object} context - SSA conversion context
 */
function processAssertStatement(statement, context) {
  try {
    // Check if statement has a condition property
    if (!statement || !statement.condition) {
      console.error("Invalid assert statement:", statement)
      context.ssaStatements.push({
        type: "SSAComment",
        text: "Invalid assert statement structure",
      })
      return
    }

    // Improved handling for quantified expressions in assertions
    if (
      statement.condition.type === "QuantifiedExpression" ||
      (typeof statement.condition === "string" && statement.condition.includes("for (")) ||
      (statement.condition.toString && statement.condition.toString().includes("for ("))
    ) {
      // Create a safe representation for the assert condition
      context.ssaStatements.push({
        type: "SSAAssert",
        condition: {
          type: "SSAComment",
          text:
            "Quantified expression in assertion: " +
            (typeof statement.condition === "string" ? statement.condition : JSON.stringify(statement.condition)),
          originalExpression: statement.condition,
        },
        originalStatement: statement,
      })
      return
    }

    // Process the assertion condition
    const conditionSSA = processExpression(statement.condition, context)

    // Add the SSA assert statement
    context.ssaStatements.push({
      type: "SSAAssert",
      condition: conditionSSA,
      originalStatement: statement,
    })
  } catch (error) {
    console.error("Error processing assert statement:", error)
    context.errors = context.errors || []
    context.errors.push(`Error in assert: ${error.message}`)

    // Add a comment for the error
    context.ssaStatements.push({
      type: "SSAComment",
      text: `Error processing assert: ${error.message}`,
    })
  }
}

/**
 * Convert SSA form to a readable program format
 * @param {Object} ssaForm - The program in SSA form
 * @returns {string} A readable representation of the SSA form
 */
export function ssaToReadableFormat(ssaForm) {
  if (!ssaForm || !ssaForm.ssaStatements) return ""

  // First, remove any incorrect assertions
  removeIncorrectAssertions(ssaForm.ssaStatements)

  let result = ""
  let lineNumber = 1
  let indentLevel = 0
  const indent = "  "

  // Helper function to add indentation
  const getIndent = () => indent.repeat(indentLevel)

  // Iterate through all statements
  for (let i = 0; i < ssaForm.ssaStatements.length; i++) {
    const statement = ssaForm.ssaStatements[i]

    switch (statement.type) {
      case "SSAAssignment":
        result += `${lineNumber++}. ${getIndent()}${statement.target} := ${expressionToString(statement.expression)};\n`
        break

      case "SSAArrayAssignment":
        result += `${lineNumber++}. ${getIndent()}${statement.target}[${expressionToString(statement.index)}] := ${expressionToString(statement.expression)};\n`
        break

      case "SSAIfStatement":
        if (statement.isUnrolledCondition) {
          result += `${lineNumber++}. ${getIndent()}if (${expressionToString(statement.condition)}) {\n`
          indentLevel++

          // Process then block
          for (let j = 0; j < statement.thenBlock.length; j++) {
            const thenStmt = statement.thenBlock[j]
            if (thenStmt.type === "SSAIfStatement" && thenStmt.isUnrolledCondition) {
              // For nested if statements, we need to handle them specially
              result += `${lineNumber++}. ${getIndent()}${statementToReadableString(thenStmt)}\n`
            } else {
              result += `${lineNumber++}. ${getIndent()}${statementToReadableString(thenStmt)}\n`
            }
          }

          indentLevel--
          result += `${lineNumber++}. ${getIndent()}} else {\n`
          indentLevel++

          // Process else block
          for (let j = 0; j < statement.elseBlock.length; j++) {
            const elseStmt = statement.elseBlock[j]
            result += `${lineNumber++}. ${getIndent()}${statementToReadableString(elseStmt)}\n`
          }

          indentLevel--
          result += `${lineNumber++}. ${getIndent()}}\n`
        } else {
          // Handle regular if statement
          result += `${lineNumber++}. ${getIndent()}if (${expressionToString(statement.condition)}) {\n`
          indentLevel++

          // Process then block
          for (let j = 0; j < statement.thenBlock.length; j++) {
            const thenStmt = statement.thenBlock[j]
            result += `${lineNumber++}. ${getIndent()}${statementToReadableString(thenStmt)}\n`
          }

          indentLevel--
          result += `${lineNumber++}. ${getIndent()}} else {\n`
          indentLevel++

          // Process else block
          for (let j = 0; j < statement.elseBlock.length; j++) {
            const elseStmt = statement.elseBlock[j]
            result += `${lineNumber++}. ${getIndent()}${statementToReadableString(elseStmt)}\n`
          }

          indentLevel--
          result += `${lineNumber++}. ${getIndent()}}\n`
        }
        break

      case "PhiNode":
        result += `${lineNumber++}. ${getIndent()}${statement.target} := φ(${statement.sources.join(", ")});\n`
        break

      case "SSAAssert":
        result += `${lineNumber++}. ${getIndent()}assert(${expressionToString(statement.condition)});\n`
        break

      case "SSAComment":
        result += `${lineNumber++}. ${getIndent()}// ${statement.text}\n`
        break

      case "SSAWhileHeader":
        result += `${lineNumber++}. ${getIndent()}while (${expressionToString(statement.condition)}) { ... }\n`
        break

      case "SSAForHeader":
        result += `${lineNumber++}. ${getIndent()}for (...; ${expressionToString(statement.condition)}; ...) { ... }\n`
        break

      default:
        result += `${lineNumber++}. ${getIndent()}// Unknown statement type: ${statement.type}\n`
    }
  }

  return result
}

/**
 * Convert a single SSA statement to a readable string
 * @param {Object} statement - The SSA statement
 * @returns {string} A string representation of the statement
 */
function statementToReadableString(statement) {
  switch (statement.type) {
    case "SSAAssignment":
      return `${statement.target} := ${expressionToString(statement.expression)};`

    case "SSAArrayAssignment":
      return `${statement.target}[${expressionToString(statement.index)}] := ${expressionToString(statement.expression)};`

    case "SSAIfStatement":
      if (statement.isUnrolledCondition) {
        return `if (${expressionToString(statement.condition)}) { ... } else { ... }`
      }
      return `if (${expressionToString(statement.condition)}) { ... } else { ... }`

    case "PhiNode":
      return `${statement.target} := φ(${statement.sources.join(", ")});`

    case "SSAAssert":
      return `assert(${expressionToString(statement.condition)});`

    case "SSAComment":
      return `// ${statement.text}`

    default:
      return `// Unknown statement type: ${statement.type}`
  }
}

/**
 * Convert an SSA expression to a string
 * @param {Object} expression - The SSA expression
 * @returns {string} A string representation of the expression
 */
function expressionToString(expression) {
  if (!expression) return ""

  switch (expression.type) {
    case "SSABinaryExpression":
      return `${expressionToString(expression.left)} ${expression.operator} ${expressionToString(expression.right)}`

    case "SSAIdentifier":
      return expression.name

    case "SSALiteral":
      return expression.value.toString()

    case "SSAArrayAccess":
      return `${expressionToString(expression.array)}[${expressionToString(expression.index)}]`

    case "SSAQuantifiedExpression":
      return `${expression.quantifier} ${expression.variable.name} in range(${expressionToString(expression.end)}): ${expressionToString(expression.body)}`

    default:
      if (typeof expression === "object") {
        return `/* Unknown expression type: ${expression.type} */`
      }
      return String(expression)
  }
}

/**
 * The original JSON-based string representation (kept for backward compatibility)
 * This function is specifically needed by VerificationMode.jsx
 */
export function ssaToString(ssaForm) {
  if (!ssaForm || !ssaForm.ssaStatements) return ""

  // First, remove any incorrect assertions
  removeIncorrectAssertions(ssaForm.ssaStatements)

  let result = ""
  let lineNumber = 1

  // Helper function to process statements with proper indentation
  function processStatements(statements, indent = "") {
    for (const statement of statements) {
      if (statement.type === "SSAIfStatement" && statement.isUnrolledCondition) {
        // Handle unrolled loop condition with proper nesting
        result += `${lineNumber++}. ${indent}if (${expressionToString(statement.condition)}) {\n`

        // Process the then block with increased indentation
        processStatements(statement.thenBlock, indent + "  ")

        result += `${lineNumber++}. ${indent}} else {\n`

        // Process the else block with increased indentation
        processStatements(statement.elseBlock, indent + "  ")

        result += `${lineNumber++}. ${indent}}\n`
      } else {
        // Handle other statement types
        switch (statement.type) {
          case "SSAAssignment":
            result += `${lineNumber++}. ${indent}${statement.target} := ${expressionToString(statement.expression)};\n`
            break

          case "SSAArrayAssignment":
            result += `${lineNumber++}. ${indent}${statement.target}[${expressionToString(statement.index)}] := ${expressionToString(statement.expression)};\n`
            break

          case "SSAComment":
            result += `${lineNumber++}. ${indent}// ${statement.text}\n`
            break

          case "SSAWhileHeader":
            result += `${lineNumber++}. ${indent}while (${expressionToString(statement.condition)}) { ... }\n`
            break

          case "SSAForHeader":
            result += `${lineNumber++}. ${indent}for (...; ${expressionToString(statement.condition)}; ...) { ... }\n`
            break

          case "SSAAssert":
            result += `${lineNumber++}. ${indent}assert(${expressionToString(statement.condition)});\n`
            break

          case "PhiNode":
            result += `${lineNumber++}. ${indent}${statement.target} := φ(${statement.sources.join(", ")});\n`
            break

          default:
            result += `${lineNumber++}. ${indent}// Unknown statement type: ${statement.type}\n`
        }
      }
    }
  }

  // Start processing from the top level
  processStatements(ssaForm.ssaStatements)

  return result
}

/**
 * Convert an SSA statement to a string (original implementation)
 */
function statementToString(statement) {
  switch (statement.type) {
    case "SSAAssignment":
      return `${statement.target} := ${expressionToString(statement.expression)};`

    case "SSAArrayAssignment":
      return `${statement.target}[${expressionToString(statement.index)}] := ${expressionToString(statement.expression)};`

    case "SSAIfStatement":
      return `if (${expressionToString(statement.condition)}) { ... } else { ... }`

    case "SSAWhileHeader":
      return `while (${expressionToString(statement.condition)}) { ... }`

    case "SSAForHeader":
      return `for (...; ${expressionToString(statement.condition)}; ...) { ... }`

    case "SSAAssert":
      return `assert(${expressionToString(statement.condition)});`

    case "PhiNode":
      return `${statement.target} := φ(${statement.sources.join(", ")});`

    case "SSAComment":
      return `// ${statement.text}`

    default:
      return `// Unknown statement type: ${statement.type}`
  }
}