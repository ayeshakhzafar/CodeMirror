import React, { useState } from 'react';
import styled from 'styled-components';
import CodeEditor from './CodeEditor';
import SSADisplay from './SSADisplay';
import SMTDisplay from './SMTDisplay';
import ResultDisplay from './ResultDisplay';
import FMPlaygroundSolver from './FMPlaygroundSolver';
import { parseProgram } from '../utils/parser';
import { transformToSSA } from '../utils/ssaTransformer';
import { optimizeSSA } from '../utils/optimizations';
import { generateEquivalenceSMT } from '../utils/smtGenerator';
import { checkEquivalence } from '../utils/z3Solver';

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

const ProgramContainer = styled.div`
  display: flex;
  gap: 20px;
  margin-bottom: 20px;
  
  @media (max-width: 768px) {
    flex-direction: column;
  }
`;

const ProgramColumn = styled.div`
  flex: 1;
`;

const EquivalenceMode = () => {
  const [code1, setCode1] = useState('x := 0;\nwhile (x < 4) {\n  x := x + 1;\n}\nassert(x == 4);');
  const [code2, setCode2] = useState('x := 0;\nfor (i := 0; i < 4; i := i + 1) {\n  x := x + 1;\n}\nassert(x == 4);');
  const [unrollDepth, setUnrollDepth] = useState(3);
  const [ast1, setAst1] = useState(null);
  const [ast2, setAst2] = useState(null);
  const [ssaForm1, setSSAForm1] = useState(null);
  const [ssaForm2, setSSAForm2] = useState(null);
  const [optimizedSSA1, setOptimizedSSA1] = useState(null);
  const [optimizedSSA2, setOptimizedSSA2] = useState(null);
  const [smtCode, setSmtCode] = useState('');
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [isLoading, setIsLoading] = useState(false);

  const handleCode1Change = (value) => {
    setCode1(value);
    // Reset results when code changes
    setAst1(null);
    setSSAForm1(null);
    setOptimizedSSA1(null);
    setSmtCode('');
    setResult(null);
    setError('');
  };

  const handleCode2Change = (value) => {
    setCode2(value);
    // Reset results when code changes
    setAst2(null);
    setSSAForm2(null);
    setOptimizedSSA2(null);
    setSmtCode('');
    setResult(null);
    setError('');
  };

  const handleUnrollDepthChange = (e) => {
    const value = parseInt(e.target.value, 10);
    if (!isNaN(value) && value >= 0) {
      setUnrollDepth(value);
    }
  };

  const handleParse = () => {
    try {
      const parseResult1 = parseProgram(code1);
      const parseResult2 = parseProgram(code2);
      
      if (parseResult1.success && parseResult2.success) {
        setAst1(parseResult1.ast);
        setAst2(parseResult2.ast);
        setError('');
      } else {
        if (!parseResult1.success) {
          setError(`Parse error in Program 1: ${parseResult1.error.message}`);
        } else {
          setError(`Parse error in Program 2: ${parseResult2.error.message}`);
        }
        setAst1(null);
        setAst2(null);
      }
    } catch (err) {
      setError(`Error parsing code: ${err.message}`);
      setAst1(null);
      setAst2(null);
    }
  };

  const handleTransformToSSA = () => {
    if (!ast1 || !ast2) {
      setError('Please parse both programs first.');
      return;
    }
    
    try {
      // Pass the unrollDepth parameter to transformToSSA for both programs
      const ssa1 = transformToSSA(ast1, unrollDepth);
      const ssa2 = transformToSSA(ast2, unrollDepth);
      
      setSSAForm1(ssa1);
      setSSAForm2(ssa2);
      
      // Apply optimizations
      const optimized1 = optimizeSSA(ssa1);
      const optimized2 = optimizeSSA(ssa2);
      
      setOptimizedSSA1(optimized1);
      setOptimizedSSA2(optimized2);
      
      setError('');
    } catch (err) {
      setError(`Error transforming to SSA: ${err.message}`);
      setSSAForm1(null);
      setSSAForm2(null);
      setOptimizedSSA1(null);
      setOptimizedSSA2(null);
    }
  };

  const handleGenerateSMT = () => {
    if (!ssaForm1 || !ssaForm2) {
      setError('Please transform both programs to SSA first.');
      return;
    }
    
    try {
      const smt = generateEquivalenceSMT(
        optimizedSSA1 || ssaForm1,
        optimizedSSA2 || ssaForm2
      );
      setSmtCode(smt);
      setError('');
    } catch (err) {
      setError(`Error generating SMT: ${err.message}`);
      setSmtCode('');
    }
  };

  const handleCheckEquivalence = async () => {
    if (!smtCode) {
      setError('Please generate SMT constraints first.');
      return;
    }
    
    setIsLoading(true);
    setResult(null);
    
    try {
      // Call the external solver to check program equivalence
      const equivalenceResult = await checkEquivalence(smtCode);
      
      console.log("Equivalence result:", equivalenceResult);
      setResult(equivalenceResult);
      
      if (equivalenceResult.error) {
        setError(`Equivalence check error: ${equivalenceResult.error}`);
      } else {
        setError('');
      }
    } catch (err) {
      console.error("Error checking equivalence:", err);
      setError(`Error checking equivalence: ${err.message}`);
      setResult({
        equivalent: false,
        counterexample: null,
        error: err.message
      });
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <Container>
      <Title>Equivalence Mode</Title>
      
      <Section>
        <SectionTitle>Input Programs</SectionTitle>
        <ProgramContainer>
          <ProgramColumn>
            <Label>Program 1</Label>
            <CodeEditor value={code1} onChange={handleCode1Change} language="javascript" />
          </ProgramColumn>
          
          <ProgramColumn>
            <Label>Program 2</Label>
            <CodeEditor value={code2} onChange={handleCode2Change} language="javascript" />
          </ProgramColumn>
        </ProgramContainer>
        
        <InputGroup>
          <Label>Loop Unrolling Depth:</Label>
          <Input 
            type="number" 
            value={unrollDepth} 
            onChange={handleUnrollDepthChange} 
            min="0"
          />
        </InputGroup>
        
        <Button onClick={handleParse}>Parse Programs</Button>
      </Section>
      
      {error && <ErrorMessage>{error}</ErrorMessage>}
      
      {ast1 && ast2 && (
        <Section>
          <SectionTitle>Abstract Syntax Trees</SectionTitle>
          <ProgramContainer>
            <ProgramColumn>
              <Label>AST for Program 1</Label>
              <CodeEditor value={JSON.stringify(ast1, null, 2)} readOnly={true} language="json" />
            </ProgramColumn>
            
            <ProgramColumn>
              <Label>AST for Program 2</Label>
              <CodeEditor value={JSON.stringify(ast2, null, 2)} readOnly={true} language="json" />
            </ProgramColumn>
          </ProgramContainer>
          
          <Button onClick={handleTransformToSSA}>Transform to SSA</Button>
        </Section>
      )}
      
      {ssaForm1 && ssaForm2 && (
        <Section>
          <SectionTitle>SSA Forms</SectionTitle>
          <ProgramContainer>
            <ProgramColumn>
              <Label>SSA for Program 1</Label>
              <SSADisplay ssaForm={ssaForm1} optimizedSSA={optimizedSSA1} />
            </ProgramColumn>
            
            <ProgramColumn>
              <Label>SSA for Program 2</Label>
              <SSADisplay ssaForm={ssaForm2} optimizedSSA={optimizedSSA2} />
            </ProgramColumn>
          </ProgramContainer>
          
          <Button onClick={handleGenerateSMT}>Generate SMT Constraints</Button>
        </Section>
      )}
      
      {smtCode && (
        <Section>
          <SMTDisplay smtCode={smtCode} />
          <Button onClick={handleCheckEquivalence} disabled={isLoading}>
            {isLoading ? 'Preparing Equivalence Check...' : 'Check Equivalence'}
          </Button>
        </Section>
      )}
      


{result && (
  <Section>
    <SectionTitle>Equivalence Result</SectionTitle>
    {result.externalLink ? (
      <FMPlaygroundSolver 
        smtCode={result.smtCode} 
        externalLink={result.externalLink}
        mode="equivalence"
        examples={result.examples}
      />
    ) : (
      <ResultDisplay result={result} mode="equivalence" isLoading={isLoading} />
    )}
  </Section>
)}
    </Container>
  );
};

export default EquivalenceMode;