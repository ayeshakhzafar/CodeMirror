import React, { useState } from 'react';
import styled from 'styled-components';
import CodeEditor from './CodeEditor';
import { parseProgram } from '../utils/parser';
import { transformToSSA, ssaToString } from '../utils/ssaTransformer';

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

const LoopUnrolling = () => {
  const [code, setCode] = useState('x := 0;\nwhile (x < 4) {\n  x := x + 1;\n}\nassert(x == 4);');
  const [unrollDepth, setUnrollDepth] = useState(3);
  const [unrolledSSA, setUnrolledSSA] = useState(null);
  const [error, setError] = useState('');

  const handleCodeChange = (value) => {
    setCode(value);
    setUnrolledSSA(null);
    setError('');
  };

  const handleUnrollDepthChange = (e) => {
    const value = parseInt(e.target.value, 10);
    if (!isNaN(value) && value >= 0) {
      setUnrollDepth(value);
    }
  };

  const handleUnroll = () => {
  try {
    const parseResult = parseProgram(code);
    
    if (parseResult.success) {
      // Pass unrollDepth to transformToSSA
      const ssa = transformToSSA(parseResult.ast, unrollDepth);
      setUnrolledSSA(ssa);
      setError('');
    } else {
      setError(`Parse error: ${parseResult.error.message}`);
      setUnrolledSSA(null);
    }
  } catch (err) {
    setError(`Error unrolling loops: ${err.message}`);
    setUnrolledSSA(null);
  }
};

  return (
    <Container>
      <Title>Loop Unrolling</Title>
      
      <Section>
        <SectionTitle>Input Program</SectionTitle>
        <CodeEditor value={code} onChange={handleCodeChange} language="javascript" />
        
        <InputGroup>
          <Label>Unrolling Depth:</Label>
          <Input 
            type="number" 
            value={unrollDepth} 
            onChange={handleUnrollDepthChange} 
            min="0"
          />
        </InputGroup>
        
        <Button onClick={handleUnroll}>Unroll Loops</Button>
      </Section>
      
      {error && <ErrorMessage>{error}</ErrorMessage>}
      
      {unrolledSSA && (
        <Section>
          <SectionTitle>Unrolled SSA Form</SectionTitle>
          <CodeEditor 
            value={ssaToString(unrolledSSA)} 
            readOnly={true} 
            language="javascript" 
          />
        </Section>
      )}
    </Container>
  );
};

export default LoopUnrolling;