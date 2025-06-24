import React, { useState } from 'react';
import styled from 'styled-components';
import CodeEditor from './CodeEditor';
import SSADisplay from './SSADisplay';
import SMTDisplay from './SMTDisplay';
import ResultDisplay from './ResultDisplay';
import ControlFlowGraph from './ControlFlowGraph';
import FMPlaygroundSolver from './FMPlaygroundSolver';
import { parseProgram } from '../utils/parser';
import { transformToSSA, ssaToString } from '../utils/ssaTransformer';
import { optimizeSSA } from '../utils/optimizations';
import { generateSMT } from '../utils/smtGenerator';
import { verifyProgram } from '../utils/z3Solver';
import { generateControlFlowGraph, generateSSAControlFlowGraph } from '../utils/graphGenerator';

const Container = styled.div`
  padding: 20px;
`;

const Title = styled.h2`
  margin-bottom: 20px;
`;

const Section = styled.div`
  margin-bottom: 30px;
`;

const SectionTitle = styled.h3`
  margin-bottom: 10px;
`;

const Button = styled.button`
  background-color: #4caf50;
  color: white;
  padding: 10px 15px;
  border: none;
  border-radius: 4px;
  cursor: pointer;
  font-size: 16px;
  margin-top: 10px;
  margin-right: 10px;
  
  &:hover {
    background-color: #45a049;
  }
  
  &:disabled {
    background-color: #cccccc;
    cursor: not-allowed;
  }
`;

const InputGroup = styled.div`
  margin-bottom: 15px;
`;

const Label = styled.label`
  display: block;
  margin-bottom: 5px;
  font-weight: bold;
`;

const Input = styled.input`
  padding: 8px;
  border: 1px solid #ccc;
  border-radius: 4px;
  width: 100px;
`;

const ErrorMessage = styled.div`
  color: #c62828;
  margin-top: 10px;
  padding: 10px;
  background-color: #ffebee;
  border-radius: 4px;
  border: 1px solid #ef9a9a;
`;

const GraphContainer = styled.div`
  display: flex;
  flex-direction: column;
  gap: 30px;
  margin-top: 20px;
`;

const VerificationMode = () => {
  const [code, setCode] = useState('x := 3;\nif (x < 5) {\n  y := x + 1;\n} else {\n  y := x - 1;\n}\nassert(y > 0);');
  const [unrollDepth, setUnrollDepth] = useState(3);
  const [ast, setAst] = useState(null);
  const [ssaForm, setSSAForm] = useState(null);
  const [optimizedSSA, setOptimizedSSA] = useState(null);
  const [smtCode, setSmtCode] = useState('');
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [cfgGraph, setCfgGraph] = useState(null);
  const [ssaCfgGraph, setSSACfgGraph] = useState(null);
  const [isLoading, setIsLoading] = useState(false);

  const handleCodeChange = (value) => {
    setCode(value);
    setAst(null);
    setSSAForm(null);
    setOptimizedSSA(null);
    setSmtCode('');
    setResult(null);
    setError('');
    setCfgGraph(null);
    setSSACfgGraph(null);
  };

  const handleUnrollDepthChange = (e) => {
    const value = parseInt(e.target.value, 10);
    if (!isNaN(value) && value >= 0) {
      setUnrollDepth(value);
    }
  };

  const handleParse = () => {
    try {
      const parseResult = parseProgram(code);
      if (parseResult.success) {
        setAst(parseResult.ast);
        setError('');
        const graph = generateControlFlowGraph(parseResult.ast);
        setCfgGraph(graph);
      } else {
        setError(`Parse error: ${parseResult.error.message}`);
        setAst(null);
        setCfgGraph(null);
      }
    } catch (err) {
      setError(`Error parsing code: ${err.message}`);
      setAst(null);
      setCfgGraph(null);
    }
  };

  const handleTransformToSSA = () => {
    if (!ast) {
      setError('Please parse the code first.');
      return;
    }

    try {
      // Pass the unrollDepth parameter to transformToSSA
      const result = transformToSSA(ast, unrollDepth);
      
      // Create a properly structured SSA form object
      const wrappedSSA = {
        ssaStatements: result.ssaStatements,
        phiNodes: result.phiNodes || []
      };
      
      setSSAForm(wrappedSSA);

      // Apply optimizations
      const optimized = optimizeSSA(wrappedSSA);
      setOptimizedSSA(optimized);

      // Generate SSA control flow graph
      const graph = generateSSAControlFlowGraph(wrappedSSA);
      setSSACfgGraph(graph);

      setError('');
    } catch (err) {
      setError(`Error transforming to SSA: ${err.message}`);
      setSSAForm(null);
      setOptimizedSSA(null);
      setSSACfgGraph(null);
    }
  };

  const handleGenerateSMT = () => {
    if (!ssaForm) {
      setError('Please transform the code to SSA first.');
      return;
    }

    try {
      const smt = generateSMT(optimizedSSA || ssaForm);
      setSmtCode(smt);
      setError('');
    } catch (err) {
      setError(`Error generating SMT: ${err.message}`);
      setSmtCode('');
    }
  };

  const handleVerify = async () => {
    if (!smtCode) {
      setError('Please generate SMT constraints first.');
      return;
    }

    setIsLoading(true);
    setResult(null);
    
    try {
      // Call the external solver to verify the program
      const verificationResult = await verifyProgram(smtCode);
      
      console.log("Verification result:", verificationResult);
      setResult(verificationResult);
      
      if (verificationResult.error) {
        setError(`Verification error: ${verificationResult.error}`);
      } else {
        setError('');
      }
    } catch (err) {
      console.error("Error during verification:", err);
      setError(`Error during verification: ${err.message}`);
      setResult({
        verified: false,
        counterexample: null,
        error: err.message
      });
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <Container>
      <Title>Verification Mode</Title>
      <Section>
        <SectionTitle>Input Program</SectionTitle>
        <CodeEditor value={code} onChange={handleCodeChange} language="javascript" />
        <InputGroup>
          <Label>Loop Unrolling Depth:</Label>
          <Input type="number" value={unrollDepth} onChange={handleUnrollDepthChange} min="0" />
        </InputGroup>
        <Button onClick={handleParse}>Parse Program</Button>
      </Section>

      {error && <ErrorMessage>{error}</ErrorMessage>}

      {ast && (
        <>
          <Section>
            <SectionTitle>Abstract Syntax Tree</SectionTitle>
            <CodeEditor value={JSON.stringify(ast, null, 2)} readOnly={true} language="json" />
            <Button onClick={handleTransformToSSA}>Transform to SSA</Button>
          </Section>

          {cfgGraph && (
            <Section>
              <SectionTitle>Control Flow Graph</SectionTitle>
              <GraphContainer>
                <ControlFlowGraph graph={cfgGraph} isSSA={false} />
              </GraphContainer>
            </Section>
          )}
        </>
      )}

      {ssaForm && (
        <>
          <Section>
            <SSADisplay ssaForm={ssaForm} optimizedSSA={optimizedSSA} />
            <Button onClick={handleGenerateSMT}>Generate SMT Constraints</Button>
          </Section>

          {ssaCfgGraph && (
            <Section>
              <SectionTitle>SSA Control Flow Graph</SectionTitle>
              <GraphContainer>
                <ControlFlowGraph graph={ssaCfgGraph} isSSA={true} />
              </GraphContainer>
            </Section>
          )}
        </>
      )}

      {smtCode && (
        <Section>
          <SMTDisplay smtCode={smtCode} />
          <Button onClick={handleVerify} disabled={isLoading}>
            {isLoading ? 'Preparing Verification...' : 'Verify Program'}
          </Button>
        </Section>
      )}

{result && (
  <Section>
    <SectionTitle>Verification Result</SectionTitle>
    {result.externalLink ? (
      <FMPlaygroundSolver 
        smtCode={result.smtCode} 
        externalLink={result.externalLink}
        mode="verification"
        examples={result.examples}
      />
    ) : (
      <ResultDisplay result={result} mode="verification" isLoading={isLoading} />
    )}
  </Section>
)}
    </Container>
  );
};

export default VerificationMode;