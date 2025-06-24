/**
 * Apply optimizations to SSA form
 * @param {Object} ssaForm - The program in SSA form
 * @returns {Object} The optimized SSA form
 */
export function optimizeSSA(ssaForm) {
  let optimized = { ...ssaForm }

  // Apply optimizations in sequence
  optimized = constantPropagation(optimized)
  optimized = deadCodeElimination(optimized)
  optimized = commonSubexpressionElimination(optimized)

  return optimized
}

/**
 * Perform constant propagation optimization
 * @param {Object} ssaForm - The program in SSA form
 * @returns {Object} The optimized SSA form
 */
function constantPropagation(ssaForm) {
  const constants = {}
  const result = {
    ssaStatements: [],
    phiNodes: [...ssaForm.phiNodes],
  }

  // First pass: identify constants
  ssaForm.ssaStatements.forEach((statement) => {
    if (statement.type === "SSAAssignment" && statement.expression.type === "SSALiteral") {
      constants[statement.target] = statement.expression.value
    }
  })

  // Second pass: propagate constants
  ssaForm.ssaStatements.forEach((statement) => {
    const optimizedStatement = propagateConstantsInStatement(statement, constants)
    result.ssaStatements.push(optimizedStatement)
  })

  return result
}

/**
 * Propagate constants in a statement
 * @param {Object} statement - The SSA statement
 * @param {Object} constants - Map of variable names to constant values
 * @returns {Object} The optimized statement
 */
function propagateConstantsInStatement(statement, constants) {
  switch (statement.type) {
    case "SSAAssignment":
      return {
        ...statement,
        expression: propagateConstantsInExpression(statement.expression, constants),
      }

    case "SSAArrayAssignment":
      return {
        ...statement,
        index: propagateConstantsInExpression(statement.index, constants),
        expression: propagateConstantsInExpression(statement.expression, constants),
      }

    case "SSAIfStatement":
      return {
        ...statement,
        condition: propagateConstantsInExpression(statement.condition, constants),
        thenBlock: statement.thenBlock.map((s) => propagateConstantsInStatement(s, constants)),
        elseBlock: statement.elseBlock.map((s) => propagateConstantsInStatement(s, constants)),
      }

    case "SSAAssert":
      return {
        ...statement,
        condition: propagateConstantsInExpression(statement.condition, constants),
      }

    default:
      return statement
  }
}

/**
 * Propagate constants in an expression
 * @param {Object} expression - The SSA expression
 * @param {Object} constants - Map of variable names to constant values
 * @returns {Object} The optimized expression
 */
function propagateConstantsInExpression(expression, constants) {
  if (!expression) return null

  switch (expression.type) {
    case "SSAIdentifier":
      if (constants[expression.name] !== undefined) {
        return {
          type: "SSALiteral",
          value: constants[expression.name],
          originalExpression: expression.originalExpression,
        }
      }
      return expression

    case "SSABinaryExpression":
      const left = propagateConstantsInExpression(expression.left, constants)
      const right = propagateConstantsInExpression(expression.right, constants)

      // If both operands are literals, evaluate the expression
      if (left.type === "SSALiteral" && right.type === "SSALiteral") {
        const result = evaluateBinaryExpression(left.value, expression.operator, right.value)
        if (result !== null) {
          return {
            type: "SSALiteral",
            value: result,
            originalExpression: expression.originalExpression,
          }
        }
      }

      return {
        ...expression,
        left,
        right,
      }

    case "SSAArrayAccess":
      return {
        ...expression,
        array: propagateConstantsInExpression(expression.array, constants),
        index: propagateConstantsInExpression(expression.index, constants),
      }

    default:
      return expression
  }
}

/**
 * Evaluate a binary expression with constant operands
 * @param {number} left - The left operand
 * @param {string} operator - The operator
 * @param {number} right - The right operand
 * @returns {number|null} The result of the evaluation, or null if not evaluable
 */
function evaluateBinaryExpression(left, operator, right) {
  switch (operator) {
    case "+":
      return left + right
    case "-":
      return left - right
    case "*":
      return left * right
    case "/":
      return right !== 0 ? left / right : null
    case "==":
      return left === right ? 1 : 0
    case "!=":
      return left !== right ? 1 : 0
    case "<":
      return left < right ? 1 : 0
    case "<=":
      return left <= right ? 1 : 0
    case ">":
      return left > right ? 1 : 0
    case ">=":
      return left >= right ? 1 : 0
    case "&&":
      return left && right ? 1 : 0
    case "||":
      return left || right ? 1 : 0
    default:
      return null
  }
}

/**
 * Perform dead code elimination optimization
 * @param {Object} ssaForm - The program in SSA form
 * @returns {Object} The optimized SSA form
 */
function deadCodeElimination(ssaForm) {
  const result = {
    ssaStatements: [],
    phiNodes: [...ssaForm.phiNodes],
  }

  // Find all used variables
  const usedVariables = new Set()
  const usedArrays = new Set()

  // First, mark all variables used in assertions as used
  ssaForm.ssaStatements.forEach((statement) => {
    if (statement.type === "SSAAssert") {
      findUsedVariablesInExpression(statement.condition, usedVariables, usedArrays)
    }
  })

  // Then, work backwards to find all variables that contribute to used variables
  let size
  do {
    size = usedVariables.size + usedArrays.size

    ssaForm.ssaStatements.forEach((statement) => {
      if (statement.type === "SSAAssignment") {
        if (usedVariables.has(statement.target)) {
          findUsedVariablesInExpression(statement.expression, usedVariables, usedArrays)
        }
      } else if (statement.type === "SSAArrayAssignment") {
        // For array assignments, if any element of the array is used, consider the whole array used
        const arrayName = statement.target.split("_")[0]
        if (usedArrays.has(arrayName)) {
          findUsedVariablesInExpression(statement.index, usedVariables, usedArrays)
          findUsedVariablesInExpression(statement.expression, usedVariables, usedArrays)
        }
      } else if (statement.type === "SSAIfStatement") {
        // Variables in conditions are always considered used
        findUsedVariablesInExpression(statement.condition, usedVariables, usedArrays)
      }
    })

    // Also check phi nodes
    ssaForm.phiNodes.forEach((node) => {
      if (usedVariables.has(node.target)) {
        node.sources.forEach((source) => {
          // Check if this is an array variable
          const baseName = source.split("_")[0]
          if (
            ssaForm.ssaStatements.some((s) => s.type === "SSAArrayAssignment" && s.target.startsWith(baseName + "_"))
          ) {
            usedArrays.add(baseName)
          } else {
            usedVariables.add(source)
          }
        })
      }
    })
  } while (size !== usedVariables.size + usedArrays.size)

  // Keep only statements that define or use used variables
  ssaForm.ssaStatements.forEach((statement) => {
    if (statement.type === "SSAAssignment") {
      if (usedVariables.has(statement.target)) {
        result.ssaStatements.push(statement)
      }
    } else if (statement.type === "SSAArrayAssignment") {
      const arrayName = statement.target.split("_")[0]
      if (usedArrays.has(arrayName)) {
        result.ssaStatements.push(statement)
      }
    } else {
      // Keep all non-assignment statements
      result.ssaStatements.push(statement)
    }
  })

  return result
}

/**
 * Find all variables used in an expression
 * @param {Object} expression - The SSA expression
 * @param {Set} usedVariables - Set to collect used variables
 * @param {Set} usedArrays - Set to collect used array base names
 */
function findUsedVariablesInExpression(expression, usedVariables, usedArrays) {
  if (!expression) return

  switch (expression.type) {
    case "SSAIdentifier":
      usedVariables.add(expression.name)
      break

    case "SSABinaryExpression":
      findUsedVariablesInExpression(expression.left, usedVariables, usedArrays)
      findUsedVariablesInExpression(expression.right, usedVariables, usedArrays)
      break

    case "SSAArrayAccess":
      findUsedVariablesInExpression(expression.array, usedVariables, usedArrays)
      findUsedVariablesInExpression(expression.index, usedVariables, usedArrays)

      // Mark the array as used
      if (expression.array && expression.array.name) {
        const arrayName = expression.array.name.split("_")[0]
        usedArrays.add(arrayName)
      }
      break
  }
}

/**
 * Perform common subexpression elimination
 * @param {Object} ssaForm - The program in SSA form
 * @returns {Object} The optimized SSA form
 */
function commonSubexpressionElimination(ssaForm) {
  const result = {
    ssaStatements: [],
    phiNodes: [...ssaForm.phiNodes],
  }

  const expressionMap = new Map()

  // Process statements in order
  ssaForm.ssaStatements.forEach((statement) => {
    if (statement.type === "SSAAssignment") {
      const expr = statement.expression

      if (expr.type === "SSABinaryExpression") {
        // Create a key for this expression
        const key = expressionToKey(expr)

        if (expressionMap.has(key)) {
          // Replace with existing variable
          const existingVar = expressionMap.get(key)
          result.ssaStatements.push({
            ...statement,
            expression: {
              type: "SSAIdentifier",
              name: existingVar,
              originalName: existingVar.split("_")[0],
              originalExpression: expr.originalExpression,
            },
          })
        } else {
          // Add to map and keep original assignment
          expressionMap.set(key, statement.target)
          result.ssaStatements.push(statement)
        }
      } else {
        // Keep non-binary expressions as is
        result.ssaStatements.push(statement)
      }
    } else if (statement.type === "SSAArrayAssignment") {
      // For array assignments, we can optimize the index and value expressions
      const indexExpr = statement.index
      const valueExpr = statement.expression

      let optimizedIndex = indexExpr
      let optimizedValue = valueExpr

      // Check if index is a binary expression that can be reused
      if (indexExpr.type === "SSABinaryExpression") {
        const indexKey = expressionToKey(indexExpr)
        if (expressionMap.has(indexKey)) {
          optimizedIndex = {
            type: "SSAIdentifier",
            name: expressionMap.get(indexKey),
            originalName: expressionMap.get(indexKey).split("_")[0],
            originalExpression: indexExpr.originalExpression,
          }
        }
      }

      // Check if value is a binary expression that can be reused
      if (valueExpr.type === "SSABinaryExpression") {
        const valueKey = expressionToKey(valueExpr)
        if (expressionMap.has(valueKey)) {
          optimizedValue = {
            type: "SSAIdentifier",
            name: expressionMap.get(valueKey),
            originalName: expressionMap.get(valueKey).split("_")[0],
            originalExpression: valueExpr.originalExpression,
          }
        }
      }

      result.ssaStatements.push({
        ...statement,
        index: optimizedIndex,
        expression: optimizedValue,
      })
    } else {
      // Keep non-assignment statements as is
      result.ssaStatements.push(statement)
    }
  })

  return result
}

/**
 * Convert an expression to a string key for comparison
 * @param {Object} expression - The SSA expression
 * @returns {string} A string key representing the expression
 */
function expressionToKey(expression) {
  if (!expression) return ""

  switch (expression.type) {
    case "SSABinaryExpression":
      return `(${expressionToKey(expression.left)}${expression.operator}${expressionToKey(expression.right)})`

    case "SSAIdentifier":
      return expression.name

    case "SSALiteral":
      return expression.value.toString()

    case "SSAArrayAccess":
      return `${expressionToKey(expression.array)}[${expressionToKey(expression.index)}]`

    default:
      return `unknown_${expression.type}`
  }
}
