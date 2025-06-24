/**
 * Process an SSA expression to create nodes and edges for a data flow graph
 * @param {Object} expression - The SSA expression
 * @param {Object} targetNode - The target node
 * @param {Map} variableNodes - Map of variable names to nodes
 * @param {Array} edges - Array to collect edges
 * @param {number} nodeId - Current node ID counter
 * @param {Array} nodes - Array to collect nodes
 * @returns {number} Updated node ID counter
 */
function processExpressionForDataFlow(expression, targetNode, variableNodes, edges, nodeId, nodes) {
  if (!expression) return nodeId

  switch (expression.type) {
    case "SSAIdentifier":
      if (variableNodes.has(expression.name)) {
        edges.push({
          id: `edge_${variableNodes.get(expression.name).id}_${targetNode.id}`,
          source: variableNodes.get(expression.name).id,
          target: targetNode.id,
        })
      }
      break

    case "SSABinaryExpression":
      // Create a node for the binary operation
      const opNode = {
        id: `node_${nodeId++}`,
        type: "operation",
        data: { label: expression.operator },
      }
      nodes.push(opNode)

      // Connect operation to target
      edges.push({
        id: `edge_${opNode.id}_${targetNode.id}`,
        source: opNode.id,
        target: targetNode.id,
      })

      // Process left and right operands
      nodeId = processExpressionForDataFlow(expression.left, opNode, variableNodes, edges, nodeId, nodes)
      nodeId = processExpressionForDataFlow(expression.right, opNode, variableNodes, edges, nodeId, nodes)
      break

    case "SSAArrayAccess":
      // Create a node for the array access
      const accessNode = {
        id: `node_${nodeId++}`,
        type: "array_access",
        data: { label: "array access" },
      }
      nodes.push(accessNode)

      // Connect access to target
      edges.push({
        id: `edge_${accessNode.id}_${targetNode.id}`,
        source: accessNode.id,
        target: targetNode.id,
      })

      // Process array and index
      nodeId = processExpressionForDataFlow(expression.array, accessNode, variableNodes, edges, nodeId, nodes)
      nodeId = processExpressionForDataFlow(expression.index, accessNode, variableNodes, edges, nodeId, nodes)
      break

    case "SSAQuantifiedExpression":
      // Create a node for the quantifier
      const quantNode = {
        id: `node_${nodeId++}`,
        type: "quantifier",
        data: { label: expression.quantifier },
      }
      nodes.push(quantNode)

      // Connect quantifier to target
      edges.push({
        id: `edge_${quantNode.id}_${targetNode.id}`,
        source: quantNode.id,
        target: targetNode.id,
      })

      // Create a node for the variable
      const varNode = {
        id: `node_${nodeId++}`,
        type: "quantifier_var",
        data: { label: expression.variable.name },
      }
      nodes.push(varNode)

      // Connect variable to quantifier
      edges.push({
        id: `edge_${varNode.id}_${quantNode.id}`,
        source: varNode.id,
        target: quantNode.id,
        label: "variable",
      })

      // Process range end and body
      nodeId = processExpressionForDataFlow(expression.end, quantNode, variableNodes, edges, nodeId, nodes)
      nodeId = processExpressionForDataFlow(expression.body, quantNode, variableNodes, edges, nodeId, nodes)
      break
  }

  return nodeId
}

/**
 * Generate a data flow graph for a quantified expression
 * @param {Object} expression - The quantified expression
 * @returns {Object} Nodes and edges for the data flow graph
 */
export function generateQuantifiedExpressionGraph(expression) {
  const nodes = []
  const edges = []
  let nodeId = 0

  // Create root node for the quantified expression
  const rootNode = {
    id: `node_${nodeId++}`,
    type: "quantifier_root",
    data: { label: `${expression.quantifier} expression` },
  }
  nodes.push(rootNode)

  // Map to track nodes for variables
  const variableNodes = new Map()

  // Process the quantified expression
  processExpressionForDataFlow(expression, rootNode, variableNodes, edges, nodeId, nodes)

  return { nodes, edges }
}

/**
 * Generate a control flow graph from an AST
 * @param {Object} ast - The AST of the program
 * @returns {Object} Nodes and edges for the control flow graph
 */
export function generateControlFlowGraph(ast) {
  console.log("Generating control flow graph for AST:", ast)

  const nodes = []
  const edges = []
  let nodeId = 0

  const entryNode = {
    id: `node_${nodeId++}`,
    type: "entry",
    data: { label: "Entry" },
  }
  nodes.push(entryNode)

  const exitNode = {
    id: `node_${nodeId++}`,
    type: "exit",
    data: { label: "Exit" },
  }

  let lastNode = entryNode

  if (ast && ast.statements) {
    lastNode = processStatements(ast.statements, nodes, edges, lastNode, exitNode, nodeId)
  } else {
    console.error("Invalid AST structure for graph generation:", ast)
  }

  edges.push({
    id: `edge_${lastNode.id}_${exitNode.id}`,
    source: lastNode.id,
    target: exitNode.id,
  })

  nodes.push(exitNode)

  console.log("Generated graph:", { nodes, edges })
  return { nodes, edges }
}

function processStatements(statements, nodes, edges, lastNode, exitNode, nodeId) {
  let currentNode = lastNode

  statements.forEach((statement) => {
    switch (statement.type) {
      case "AssignmentStatement":
        const assignNode = {
          id: `node_${nodeId++}`,
          type: "assignment",
          data: {
            label:
              statement.variable.type === "ArrayAccess"
                ? `${statement.variable.array.name}[${expressionToString(statement.variable.index)}] := ${expressionToString(statement.expression)}`
                : `${statement.variable.name} := ${expressionToString(statement.expression)}`,
          },
        }
        nodes.push(assignNode)
        edges.push({ id: `edge_${currentNode.id}_${assignNode.id}`, source: currentNode.id, target: assignNode.id })
        currentNode = assignNode
        break

      case "IfStatement":
        const conditionNode = {
          id: `node_${nodeId++}`,
          type: "condition",
          data: { label: `if (${expressionToString(statement.condition)})` },
        }
        nodes.push(conditionNode)
        edges.push({
          id: `edge_${currentNode.id}_${conditionNode.id}`,
          source: currentNode.id,
          target: conditionNode.id,
        })

        const thenEntryNode = { id: `node_${nodeId++}`, type: "then_entry", data: { label: "Then" } }
        nodes.push(thenEntryNode)
        edges.push({
          id: `edge_${conditionNode.id}_${thenEntryNode.id}`,
          source: conditionNode.id,
          target: thenEntryNode.id,
          label: "true",
        })

        const thenExitNode = processStatements(statement.thenBlock, nodes, edges, thenEntryNode, exitNode, nodeId)

        const elseEntryNode = { id: `node_${nodeId++}`, type: "else_entry", data: { label: "Else" } }
        nodes.push(elseEntryNode)
        edges.push({
          id: `edge_${conditionNode.id}_${elseEntryNode.id}`,
          source: conditionNode.id,
          target: elseEntryNode.id,
          label: "false",
        })

        const elseExitNode = processStatements(statement.elseBlock, nodes, edges, elseEntryNode, exitNode, nodeId)

        const mergeNode = { id: `node_${nodeId++}`, type: "merge", data: { label: "Merge" } }
        nodes.push(mergeNode)
        edges.push({ id: `edge_${thenExitNode.id}_${mergeNode.id}`, source: thenExitNode.id, target: mergeNode.id })
        edges.push({ id: `edge_${elseExitNode.id}_${mergeNode.id}`, source: elseExitNode.id, target: mergeNode.id })
        currentNode = mergeNode
        break

      case "WhileStatement":
        const whileNode = {
          id: `node_${nodeId++}`,
          type: "while",
          data: { label: `while (${expressionToString(statement.condition)})` },
        }
        nodes.push(whileNode)
        edges.push({ id: `edge_${currentNode.id}_${whileNode.id}`, source: currentNode.id, target: whileNode.id })

        const loopEntryNode = { id: `node_${nodeId++}`, type: "loop_entry", data: { label: "Loop Body" } }
        nodes.push(loopEntryNode)
        edges.push({
          id: `edge_${whileNode.id}_${loopEntryNode.id}`,
          source: whileNode.id,
          target: loopEntryNode.id,
          label: "true",
        })

        const loopExitNode = processStatements(statement.body, nodes, edges, loopEntryNode, exitNode, nodeId)
        edges.push({ id: `edge_${loopExitNode.id}_${whileNode.id}`, source: loopExitNode.id, target: whileNode.id })

        const afterLoopNode = { id: `node_${nodeId++}`, type: "after_loop", data: { label: "After Loop" } }
        nodes.push(afterLoopNode)
        edges.push({
          id: `edge_${whileNode.id}_${afterLoopNode.id}`,
          source: whileNode.id,
          target: afterLoopNode.id,
          label: "false",
        })
        currentNode = afterLoopNode
        break

      case "ForStatement":
        // Create initialization node
        const initNode = {
          id: `node_${nodeId++}`,
          type: "for_init",
          data: {
            label:
              statement.init.variable.type === "ArrayAccess"
                ? `${statement.init.variable.array.name}[${expressionToString(statement.init.variable.index)}] := ${expressionToString(statement.init.expression)}`
                : `${statement.init.variable.name} := ${expressionToString(statement.init.expression)}`,
          },
        }
        nodes.push(initNode)
        edges.push({ id: `edge_${currentNode.id}_${initNode.id}`, source: currentNode.id, target: initNode.id })

        // Create condition node
        const forCondNode = {
          id: `node_${nodeId++}`,
          type: "for_cond",
          data: { label: `for condition: ${expressionToString(statement.condition)}` },
        }
        nodes.push(forCondNode)
        edges.push({ id: `edge_${initNode.id}_${forCondNode.id}`, source: initNode.id, target: forCondNode.id })

        // Create loop body entry
        const forBodyNode = { id: `node_${nodeId++}`, type: "for_body", data: { label: "For Loop Body" } }
        nodes.push(forBodyNode)
        edges.push({
          id: `edge_${forCondNode.id}_${forBodyNode.id}`,
          source: forCondNode.id,
          target: forBodyNode.id,
          label: "true",
        })

        // Process loop body
        const forBodyExitNode = processStatements(statement.body, nodes, edges, forBodyNode, exitNode, nodeId)

        // Create update node
        const updateNode = {
          id: `node_${nodeId++}`,
          type: "for_update",
          data: {
            label:
              statement.update.variable.type === "ArrayAccess"
                ? `${statement.update.variable.array.name}[${expressionToString(statement.update.variable.index)}] := ${expressionToString(statement.update.expression)}`
                : `${statement.update.variable.name} := ${expressionToString(statement.update.expression)}`,
          },
        }
        nodes.push(updateNode)
        edges.push({
          id: `edge_${forBodyExitNode.id}_${updateNode.id}`,
          source: forBodyExitNode.id,
          target: updateNode.id,
        })

        // Loop back to condition
        edges.push({ id: `edge_${updateNode.id}_${forCondNode.id}`, source: updateNode.id, target: forCondNode.id })

        // Exit loop
        const afterForNode = { id: `node_${nodeId++}`, type: "after_for", data: { label: "After For Loop" } }
        nodes.push(afterForNode)
        edges.push({
          id: `edge_${forCondNode.id}_${afterForNode.id}`,
          source: forCondNode.id,
          target: afterForNode.id,
          label: "false",
        })
        currentNode = afterForNode
        break

      case "AssertStatement":
        const assertNode = {
          id: `node_${nodeId++}`,
          type: "assert",
          data: { label: `assert(${expressionToString(statement.condition)})` },
        }
        nodes.push(assertNode)
        edges.push({ id: `edge_${currentNode.id}_${assertNode.id}`, source: currentNode.id, target: assertNode.id })
        currentNode = assertNode
        break
    }
  })

  return currentNode
}

function expressionToString(expression) {
  if (!expression) return ""
  switch (expression.type) {
    case "BinaryExpression":
      return `${expressionToString(expression.left)} ${expression.operator} ${expressionToString(expression.right)}`
    case "Identifier":
      return expression.name
    case "Literal":
      return expression.value.toString()
    case "ArrayAccess":
      return `${expressionToString(expression.array)}[${expressionToString(expression.index)}]`
    case "QuantifiedExpression":
      return `${expression.quantifier} ${expression.variable.name} in range(${expressionToString(expression.end)}): ${expressionToString(expression.body)}`
    default:
      return `unknown_${expression.type}`
  }
}

/**
 * Generate a control flow graph from SSA form
 * @param {Object|Array} ssaForm - The program in SSA form (object or array)
 * @returns {Object} Nodes and edges for the control flow graph
 */
export function generateSSAControlFlowGraph(ssaForm) {
  const nodes = []
  const edges = []
  let nodeId = 0

  const entryNode = {
    id: `node_${nodeId++}`,
    type: "entry",
    data: { label: "Entry" },
  }
  nodes.push(entryNode)

  const exitNode = {
    id: `node_${nodeId++}`,
    type: "exit",
    data: { label: "Exit" },
  }

  const statements = Array.isArray(ssaForm) ? ssaForm : ssaForm?.ssaStatements || []
  const lastNode = processSSAStatements(statements, nodes, edges, entryNode, exitNode, nodeId)

  edges.push({ id: `edge_${lastNode.id}_${exitNode.id}`, source: lastNode.id, target: exitNode.id })
  nodes.push(exitNode)
  return { nodes, edges }
}

function processSSAStatements(statements, nodes, edges, lastNode, exitNode, nodeId) {
  let currentNode = lastNode
  statements.forEach((statement) => {
    switch (statement.type) {
      case "SSAAssignment":
        const assignNode = {
          id: `node_${nodeId++}`,
          type: "ssa_assignment",
          data: { label: `${statement.target} := ${ssaExpressionToString(statement.expression)}` },
        }
        nodes.push(assignNode)
        edges.push({ id: `edge_${currentNode.id}_${assignNode.id}`, source: currentNode.id, target: assignNode.id })
        currentNode = assignNode
        break

      case "SSAArrayAssignment":
        const arrayAssignNode = {
          id: `node_${nodeId++}`,
          type: "ssa_array_assignment",
          data: {
            label: `${statement.target}[${ssaExpressionToString(statement.index)}] := ${ssaExpressionToString(statement.expression)}`,
          },
        }
        nodes.push(arrayAssignNode)
        edges.push({
          id: `edge_${currentNode.id}_${arrayAssignNode.id}`,
          source: currentNode.id,
          target: arrayAssignNode.id,
        })
        currentNode = arrayAssignNode
        break

      case "SSAIfStatement":
        const conditionNode = {
          id: `node_${nodeId++}`,
          type: "ssa_condition",
          data: { label: `if (${ssaExpressionToString(statement.condition)})` },
        }
        nodes.push(conditionNode)
        edges.push({
          id: `edge_${currentNode.id}_${conditionNode.id}`,
          source: currentNode.id,
          target: conditionNode.id,
        })

        // If this is an unrolled condition, handle it differently
        if (statement.isUnrolledCondition) {
          const thenNode = { id: `node_${nodeId++}`, type: "ssa_then", data: { label: "Continue Loop" } }
          nodes.push(thenNode)
          edges.push({
            id: `edge_${conditionNode.id}_${thenNode.id}`,
            source: conditionNode.id,
            target: thenNode.id,
            label: "true",
          })

          const elseNode = { id: `node_${nodeId++}`, type: "ssa_else", data: { label: "Break Loop" } }
          nodes.push(elseNode)
          edges.push({
            id: `edge_${conditionNode.id}_${elseNode.id}`,
            source: conditionNode.id,
            target: elseNode.id,
            label: "false",
          })

          currentNode = thenNode // Continue with the then branch
        } else {
          // Regular if statement
          const thenEntryNode = { id: `node_${nodeId++}`, type: "ssa_then_entry", data: { label: "Then" } }
          nodes.push(thenEntryNode)
          edges.push({
            id: `edge_${conditionNode.id}_${thenEntryNode.id}`,
            source: conditionNode.id,
            target: thenEntryNode.id,
            label: "true",
          })

          const thenExitNode = processSSAStatements(statement.thenBlock, nodes, edges, thenEntryNode, exitNode, nodeId)

          const elseEntryNode = { id: `node_${nodeId++}`, type: "ssa_else_entry", data: { label: "Else" } }
          nodes.push(elseEntryNode)
          edges.push({
            id: `edge_${conditionNode.id}_${elseEntryNode.id}`,
            source: conditionNode.id,
            target: elseEntryNode.id,
            label: "false",
          })

          const elseExitNode = processSSAStatements(statement.elseBlock, nodes, edges, elseEntryNode, exitNode, nodeId)

          const mergeNode = { id: `node_${nodeId++}`, type: "ssa_merge", data: { label: "Merge" } }
          nodes.push(mergeNode)
          edges.push({ id: `edge_${thenExitNode.id}_${mergeNode.id}`, source: thenExitNode.id, target: mergeNode.id })
          edges.push({ id: `edge_${elseExitNode.id}_${mergeNode.id}`, source: elseExitNode.id, target: mergeNode.id })
          currentNode = mergeNode
        }
        break

      case "SSAAssert":
        const assertNode = {
          id: `node_${nodeId++}`,
          type: "ssa_assert",
          data: { label: `assert(${ssaExpressionToString(statement.condition)})` },
        }
        nodes.push(assertNode)
        edges.push({ id: `edge_${currentNode.id}_${assertNode.id}`, source: currentNode.id, target: assertNode.id })
        currentNode = assertNode
        break

      case "PhiNode":
        const phiNode = {
          id: `node_${nodeId++}`,
          type: "phi_node",
          data: { label: `${statement.target} := ϕ(${statement.sources.join(", ")})` },
        }
        nodes.push(phiNode)
        edges.push({ id: `edge_${currentNode.id}_${phiNode.id}`, source: currentNode.id, target: phiNode.id })
        currentNode = phiNode
        break

      case "SSAComment":
        const commentNode = {
          id: `node_${nodeId++}`,
          type: "ssa_comment",
          data: { label: `// ${statement.text}` },
        }
        nodes.push(commentNode)
        edges.push({ id: `edge_${currentNode.id}_${commentNode.id}`, source: currentNode.id, target: commentNode.id })
        currentNode = commentNode
        break

      case "SSAWhileHeader":
        const whileHeaderNode = {
          id: `node_${nodeId++}`,
          type: "ssa_while_header",
          data: { label: `while (${ssaExpressionToString(statement.condition)})` },
        }
        nodes.push(whileHeaderNode)
        edges.push({
          id: `edge_${currentNode.id}_${whileHeaderNode.id}`,
          source: currentNode.id,
          target: whileHeaderNode.id,
        })
        currentNode = whileHeaderNode
        break

      case "SSAForHeader":
        const forHeaderNode = {
          id: `node_${nodeId++}`,
          type: "ssa_for_header",
          data: { label: `for (...; ${ssaExpressionToString(statement.condition)}; ...)` },
        }
        nodes.push(forHeaderNode)
        edges.push({
          id: `edge_${currentNode.id}_${forHeaderNode.id}`,
          source: currentNode.id,
          target: forHeaderNode.id,
        })
        currentNode = forHeaderNode
        break
    }
  })
  return currentNode
}

function ssaExpressionToString(expression) {
  if (!expression) return ""
  switch (expression.type) {
    case "SSABinaryExpression":
      return `${ssaExpressionToString(expression.left)} ${expression.operator} ${ssaExpressionToString(expression.right)}`
    case "SSAIdentifier":
      return expression.name
    case "SSALiteral":
      return expression.value.toString()
    case "SSAArrayAccess":
      return `${ssaExpressionToString(expression.array)}[${ssaExpressionToString(expression.index)}]`
    case "SSAQuantifiedExpression":
      return `${expression.quantifier} ${expression.variable.name} in range(${ssaExpressionToString(expression.end)}): ${ssaExpressionToString(expression.body)}`
    default:
      return `unknown_${expression.type}`
  }
}

/**
 * Generate a data flow graph from SSA form
 * @param {Object} ssaForm - The program in SSA form
 * @returns {Object} Nodes and edges for the data flow graph
 */
export function generateDataFlowGraph(ssaForm) {
  const nodes = []
  const edges = []
  let nodeId = 0

  // Map to track nodes for each variable
  const variableNodes = new Map()

  // Process all statements to create nodes and edges
  ssaForm.ssaStatements.forEach((statement) => {
    switch (statement.type) {
      case "SSAAssignment":
        // Create node for the target variable
        const targetNode = {
          id: `node_${nodeId++}`,
          type: "variable",
          data: { label: statement.target },
        }
        nodes.push(targetNode)
        variableNodes.set(statement.target, targetNode)

        // Create edges from source variables to target
        addDataFlowEdges(statement.expression, targetNode, variableNodes, edges)
        break

      case "SSAArrayAssignment":
        // Create node for the array variable
        const arrayNode = {
          id: `node_${nodeId++}`,
          type: "array_variable",
          data: { label: `${statement.target}[${ssaExpressionToString(statement.index)}]` },
        }
        nodes.push(arrayNode)
        variableNodes.set(`${statement.target}[${ssaExpressionToString(statement.index)}]`, arrayNode)

        // Create edges from index expression variables
        addDataFlowEdges(statement.index, arrayNode, variableNodes, edges)

        // Create edges from value expression variables
        addDataFlowEdges(statement.expression, arrayNode, variableNodes, edges)
        break

      case "PhiNode":
        // Create node for the phi result
        const phiNode = {
          id: `node_${nodeId++}`,
          type: "phi_variable",
          data: { label: `${statement.target} (φ)` },
        }
        nodes.push(phiNode)
        variableNodes.set(statement.target, phiNode)

        // Create edges from source variables to phi node
        statement.sources.forEach((source) => {
          if (variableNodes.has(source)) {
            edges.push({
              id: `edge_${variableNodes.get(source).id}_${phiNode.id}`,
              source: variableNodes.get(source).id,
              target: phiNode.id,
              label: "phi input",
            })
          }
        })
        break
    }
  })

  return { nodes, edges }
}

/**
 * Add data flow edges from an expression to a target node
 * @param {Object} expression - The SSA expression
 * @param {Object} targetNode - The target node
 * @param {Map} variableNodes - Map of variable names to nodes
 * @param {Array} edges - Array to collect edges
 */
function addDataFlowEdges(expression, targetNode, variableNodes, edges) {
  if (!expression) return

  switch (expression.type) {
    case "SSAIdentifier":
      if (variableNodes.has(expression.name)) {
        edges.push({
          id: `edge_${variableNodes.get(expression.name).id}_${targetNode.id}`,
          source: variableNodes.get(expression.name).id,
          target: targetNode.id,
        })
      }
      break

    case "SSABinaryExpression":
      addDataFlowEdges(expression.left, targetNode, variableNodes, edges)
      addDataFlowEdges(expression.right, targetNode, variableNodes, edges)
      break

    case "SSAArrayAccess":
      // Add edge from array variable
      if (expression.array && expression.array.name && variableNodes.has(expression.array.name)) {
        edges.push({
          id: `edge_${variableNodes.get(expression.array.name).id}_${targetNode.id}`,
          source: variableNodes.get(expression.array.name).id,
          target: targetNode.id,
          label: "array access",
        })
      }

      // Add edges from index expression
      addDataFlowEdges(expression.index, targetNode, variableNodes, edges)
      break

    case "SSAQuantifiedExpression":
      // Add edges from range end expression
      addDataFlowEdges(expression.end, targetNode, variableNodes, edges)

      // Add edges from body expression
      addDataFlowEdges(expression.body, targetNode, variableNodes, edges)
      break
  }
}
