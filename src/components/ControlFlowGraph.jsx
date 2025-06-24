import React from 'react';
import ReactFlow, { 
  Background, 
  Controls, 
  MiniMap,
  Handle,
  Position
} from 'react-flow-renderer';
import styled from 'styled-components';

const GraphContainer = styled.div`
  height: 600px;
  border: 1px solid #ccc;
  border-radius: 4px;
  margin-bottom: 20px;
`;

const Title = styled.h3`
  margin-bottom: 10px;
`;

// Helper function to create a node wrapper with handles
const createNodeWithHandles = (backgroundColor, borderColor, Component) => {
  return ({ data }) => (
    <div style={{ 
      padding: '10px', 
      borderRadius: '5px', 
      background: backgroundColor, 
      border: `1px solid ${borderColor}`,
      maxWidth: '250px',
      position: 'relative',
      overflow: 'hidden',
      textOverflow: 'ellipsis',
      whiteSpace: 'normal',
      wordBreak: 'break-word',
      color: 'black'
    }}>
      <Handle
        type="target"
        position={Position.Top}
        id={`${data.id}-target`}
        style={{ background: '#555', top: 0 }}
      />
      
      {Component ? <Component data={data} /> : data.label}
      
      <Handle
        type="source"
        position={Position.Bottom}
        id={`${data.id}-source`}
        style={{ background: '#555', bottom: 0 }}
      />
    </div>
  );
};

// Define node colors and styles with consistent theme
const nodeStyles = {
  // General nodes
  entry: { bg: '#e3f2fd', border: '#90caf9', centered: true },
  exit: { bg: '#ffebee', border: '#ef9a9a', centered: true },
  
  // Regular control flow nodes
  assignment: { bg: '#f1f8e9', border: '#c5e1a5' },
  condition: { bg: '#fff8e1', border: '#ffe082' },
  assert: { bg: '#e8eaf6', border: '#9fa8da' },
  then_entry: { bg: '#e8f5e9', border: '#a5d6a7', centered: true },
  else_entry: { bg: '#fce4ec', border: '#f48fb1', centered: true },
  merge: { bg: '#f3e5f5', border: '#ce93d8', centered: true },
  while: { bg: '#fff8e1', border: '#ffe082' },
  loop_entry: { bg: '#e8f5e9', border: '#a5d6a7', centered: true },
  after_loop: { bg: '#f3e5f5', border: '#ce93d8', centered: true },
  for_init: { bg: '#e0f2f1', border: '#80cbc4' },
  for_cond: { bg: '#fff8e1', border: '#ffe082' },
  for_body: { bg: '#e8f5e9', border: '#a5d6a7', centered: true },
  for_update: { bg: '#e0f2f1', border: '#80cbc4' },
  after_for: { bg: '#f3e5f5', border: '#ce93d8', centered: true },

  // SSA-specific nodes
  ssa_assignment: { bg: '#f1f8e9', border: '#c5e1a5' },
  ssa_array_assignment: { bg: '#f1f8e9', border: '#c5e1a5' },
  phi_node: { bg: '#e0f7fa', border: '#80deea' },
  ssa_condition: { bg: '#fff8e1', border: '#ffe082' },
  ssa_then: { bg: '#e8f5e9', border: '#a5d6a7', centered: true },
  ssa_else: { bg: '#fce4ec', border: '#f48fb1', centered: true },
  ssa_then_entry: { bg: '#e8f5e9', border: '#a5d6a7', centered: true },
  ssa_else_entry: { bg: '#fce4ec', border: '#f48fb1', centered: true },
  ssa_merge: { bg: '#f3e5f5', border: '#ce93d8', centered: true },
  ssa_assert: { bg: '#e8eaf6', border: '#9fa8da' },
  ssa_comment: { bg: '#efebe9', border: '#bcaaa4', italic: true },
  ssa_while_header: { bg: '#fff8e1', border: '#ffe082' },
  ssa_for_header: { bg: '#fff8e1', border: '#ffe082' },
  
  // Data flow graph nodes
  variable: { bg: '#e1f5fe', border: '#81d4fa' },
  array_variable: { bg: '#e1f5fe', border: '#81d4fa' },
  phi_variable: { bg: '#e0f7fa', border: '#80deea' },
  operation: { bg: '#fff3e0', border: '#ffcc80' },
  array_access: { bg: '#f3e5f5', border: '#ce93d8' },
  quantifier: { bg: '#e8eaf6', border: '#9fa8da' },
  quantifier_var: { bg: '#e1f5fe', border: '#81d4fa' },
  quantifier_root: { bg: '#e8eaf6', border: '#9fa8da', centered: true },
};

// Generate node types from node styles
const generateNodeTypes = () => {
  const nodeTypes = {};
  
  Object.entries(nodeStyles).forEach(([type, style]) => {
    nodeTypes[type] = createNodeWithHandles(
      style.bg, 
      style.border, 
      style.centered || style.italic ? 
        ({ data }) => (
          <div style={{ 
            textAlign: style.centered ? 'center' : 'left',
            fontStyle: style.italic ? 'italic' : 'normal'
          }}>
            {data.label}
          </div>
        ) : 
        null
    );
  });
  
  return nodeTypes;
};

const nodeTypes = generateNodeTypes();

// Enhanced layout algorithm to handle different graph types
const layoutGraph = (elements, graphType) => {
  const nodes = [...elements.nodes];
  
  if (graphType === 'data-flow') {
    return layoutDataFlowGraph(elements);
  } else if (graphType === 'ssa-control-flow') {
    return layoutControlFlowGraph(elements, true);
  } else {
    return layoutControlFlowGraph(elements, false);
  }
};

// Layout algorithm specifically for data flow graphs
const layoutDataFlowGraph = (elements) => {
  const nodes = [...elements.nodes];
  const edges = [...elements.edges];
  
  // Create a dependency map to determine node levels
  const dependencies = {};
  nodes.forEach(node => {
    dependencies[node.id] = {
      dependsOn: [],
      level: 0
    };
  });
  
  // Build dependency tree
  edges.forEach(edge => {
    if (dependencies[edge.target]) {
      dependencies[edge.target].dependsOn.push(edge.source);
    }
  });
  
  // Calculate node levels (distance from root nodes)
  const calculateLevels = (nodeId, visited = new Set()) => {
    if (visited.has(nodeId)) return dependencies[nodeId].level;
    
    visited.add(nodeId);
    const deps = dependencies[nodeId].dependsOn;
    
    if (deps.length === 0) {
      dependencies[nodeId].level = 0;
      return 0;
    }
    
    const maxLevel = Math.max(...deps.map(depId => 
      calculateLevels(depId, visited)
    ));
    
    dependencies[nodeId].level = maxLevel + 1;
    return dependencies[nodeId].level;
  };
  
  // Calculate levels for all nodes
  nodes.forEach(node => {
    calculateLevels(node.id);
  });
  
  // Group nodes by level
  const nodesByLevel = {};
  nodes.forEach(node => {
    const level = dependencies[node.id].level;
    if (!nodesByLevel[level]) nodesByLevel[level] = [];
    nodesByLevel[level].push(node);
  });
  
  // Position nodes by level
  const levelCount = Object.keys(nodesByLevel).length;
  const ySpacing = 120;
  const baseX = 400;
  const layoutNodes = [];
  
  Object.entries(nodesByLevel).forEach(([level, levelNodes]) => {
    const nodeCount = levelNodes.length;
    const xSpacing = 200;
    const levelY = parseInt(level) * ySpacing + 50;
    
    levelNodes.forEach((node, index) => {
      const xOffset = (nodeCount - 1) * xSpacing / 2;
      const x = baseX + index * xSpacing - xOffset;
      
      layoutNodes.push({
        ...node,
        position: { x, y: levelY },
        style: { ...node.style }
      });
    });
  });
  
  return { nodes: layoutNodes, edges };
};

// Layout algorithm for control flow graphs
const layoutControlFlowGraph = (elements, isSSA) => {
  const nodes = [...elements.nodes];
  const edges = [...elements.edges];
  
  // Track branch information
  const branches = [];
  let currentY = 50;
  const xCenter = 400;
  const xStep = 150;
  const yStep = 100;
  
  // First pass: identify branches and loops
  const nodeBranchMap = {};
  
  for (let i = 0; i < nodes.length; i++) {
    const node = nodes[i];
    const nodeType = node.type;
    
    // Condition nodes start branches
    if (nodeType.includes('condition')) {
      // Find the matching branches
      const thenBranch = { nodes: [] };
      const elseBranch = { nodes: [] };
      
      // Find merge node by analyzing targets of condition node
      const conditionOutEdges = edges.filter(e => e.source === node.id);
      const thenEdge = conditionOutEdges.find(e => e.label === 'true');
      const elseEdge = conditionOutEdges.find(e => e.label === 'false');
      
      // Add branch info
      if (thenEdge && elseEdge) {
        const branch = {
          condition: node.id,
          thenStart: thenEdge.target,
          elseStart: elseEdge.target,
          thenNodes: [],
          elseNodes: [],
          mergeNode: null  // Will be filled in second pass
        };
        
        branches.push(branch);
      }
    }
    
    // Loop nodes are special cases
    if (nodeType.includes('while') || nodeType.includes('for_cond')) {
      // Find the loop body and exit path
      const loopOutEdges = edges.filter(e => e.source === node.id);
      const bodyEdge = loopOutEdges.find(e => e.label === 'true');
      const exitEdge = loopOutEdges.find(e => e.label === 'false');
      
      if (bodyEdge && exitEdge) {
        const loop = {
          header: node.id,
          bodyStart: bodyEdge.target,
          exitNode: exitEdge.target,
          bodyNodes: []
        };
        
        // Find all nodes in the loop body by looking for back edge
        const backEdge = edges.find(e => e.target === node.id && e.source !== branches[branches.length - 1]?.condition);
        if (backEdge) {
          loop.backEdgeSource = backEdge.source;
        }
        
        branches.push(loop);
      }
    }
  }
  
  // Layout algorithm
  const layoutNodes = [];
  const positions = {};
  let branchLevels = [0]; // Stack to track current branch levels
  
  // Create a node dependency map
  const nodeDeps = {};
  nodes.forEach(node => {
    nodeDeps[node.id] = { 
      inEdges: edges.filter(e => e.target === node.id).map(e => e.source),
      outEdges: edges.filter(e => e.source === node.id).map(e => e.target)
    };
  });
  
  // Helper to determine if a node is in a branch
  const getNodeBranch = (nodeId) => {
    for (const branch of branches) {
      if (branch.thenNodes?.includes(nodeId)) return { branch, side: 'then' };
      if (branch.elseNodes?.includes(nodeId)) return { branch, side: 'else' };
      if (branch.bodyNodes?.includes(nodeId)) return { branch, side: 'body' };
    }
    return null;
  };
  
  // Position nodes
  for (let i = 0; i < nodes.length; i++) {
    const node = nodes[i];
    const nodeType = node.type;
    let x = xCenter;
    let y = currentY;
    
    // Handle branching
    if (nodeType.includes('condition')) {
      // Find the current branch
      const branch = branches.find(b => b.condition === node.id);
      
      if (branch) {
        branchLevels.push(branchLevels[branchLevels.length - 1] + 1);
        x = xCenter;
      }
    } 
    // Handle entering then branch
    else if (nodeType.includes('then') || nodeType === 'loop_entry' || nodeType === 'for_body') {
      x = xCenter - xStep;
    }
    // Handle entering else branch
    else if (nodeType.includes('else')) {
      x = xCenter + xStep;
    }
    // Handle merge nodes
    else if (nodeType.includes('merge') || nodeType === 'after_loop' || nodeType === 'after_for') {
      if (branchLevels.length > 1) {
        branchLevels.pop();
      }
      x = xCenter;
    }
    // Handle other nodes based on their parent branch
    else {
      const prevNode = i > 0 ? nodes[i-1] : null;
      
      if (prevNode && positions[prevNode.id]) {
        if (positions[prevNode.id].x !== xCenter) {
          x = positions[prevNode.id].x;
        }
      }
    }
    
    positions[node.id] = { x, y };
    layoutNodes.push({
      ...node,
      position: { x, y },
      style: { ...node.style }
    });
    
    currentY += yStep;
  }
  
  // Second pass: adjust branch lengths and positions
  let maxY = currentY;
  
  // Adjust branch node positions
  const finalNodes = layoutNodes.map(node => {
    const pos = positions[node.id];
    if (!pos) return node;
    
    // Keep node within max height
    const y = Math.min(pos.y, maxY);
    
    return {
      ...node,
      position: { x: pos.x, y }
    };
  });
  
  return { nodes: finalNodes, edges };
};

const ControlFlowGraph = ({ graph, graphType = 'control-flow' }) => {
  if (!graph || !graph.nodes || !graph.edges) {
    return <div>No graph data available</div>;
  }

  // Layout the graph
  const { nodes, edges } = layoutGraph(graph, graphType);

  // Style edges based on type
  const styledEdges = edges.map(edge => ({
    ...edge,
    type: 'default',
    animated: edge.label === 'false', // Animate false condition edges
    style: { 
      stroke: edge.label === 'false' ? '#f44336' : 
              edge.label === 'true' ? '#4caf50' : 
              edge.label === 'phi input' ? '#2196f3' : '#000', 
      strokeWidth: edge.label ? 2 : 1.5 
    },
    markerEnd: {
      type: 'arrowclosed',
      color: edge.label === 'false' ? '#f44336' : 
             edge.label === 'true' ? '#4caf50' : 
             edge.label === 'phi input' ? '#2196f3' : '#000'
    },
    label: edge.label || ''
  }));

  // Determine title based on graph type
  const graphTitle = () => {
    switch(graphType) {
      case 'data-flow': return 'Data Flow Graph';
      case 'ssa-control-flow': return 'SSA Control Flow Graph';
      case 'quantified-expression': return 'Quantified Expression Graph';
      default: return 'Control Flow Graph';
    }
  };

  return (
    <>
      <Title>{graphTitle()}</Title>
      <GraphContainer>
        <ReactFlow
          nodes={nodes}
          edges={styledEdges}
          nodeTypes={nodeTypes}
          fitView
          elementsSelectable={true}
          nodesConnectable={false}
          defaultZoom={0.8}
        >
          <Background color="#aaa" gap={16} />
          <Controls />
          <MiniMap
            nodeStrokeColor={(n) => "#000000"}
            nodeColor={(n) => {
              const style = nodeStyles[n.type] || { bg: '#f5f5f5' };
              return style.bg;
            }}
          />
        </ReactFlow>
      </GraphContainer>
    </>
  );
};

export default ControlFlowGraph;