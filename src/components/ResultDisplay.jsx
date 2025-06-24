import React from 'react';
import styled from 'styled-components';
import CodeEditor from './CodeEditor';

const Container = styled.div`
  margin-bottom: 20px;
`;

const Title = styled.h3`
  margin-bottom: 10px;
`;

const ResultBox = styled.div`
  padding: 15px;
  border-radius: 4px;
  margin-bottom: 15px;
  background-color: ${props => props.$verified ? '#e8f5e9' : '#ffebee'};
  border: 1px solid ${props => props.$verified ? '#a5d6a7' : '#ef9a9a'};
`;

const ResultText = styled.div`
  font-size: 18px;
  font-weight: bold;
  margin-bottom: 10px;
  color: ${props => props.$verified ? '#2e7d32' : '#c62828'};
`;

const LoadingText = styled.div`
  font-size: 16px;
  color: #666;
  margin: 20px 0;
`;

const ExampleTitle = styled.h4`
  margin-top: 15px;
  margin-bottom: 10px;
`;

const ExampleContainer = styled.div`
  margin-bottom: 20px;
  padding: 10px;
  border: 1px solid #ddd;
  border-radius: 4px;
  background-color: #f9f9f9;
`;

const ExampleRow = styled.div`
  display: flex;
  margin-bottom: 5px;
`;

const ExampleLabel = styled.div`
  font-weight: bold;
  width: 120px;
`;

const ExampleValue = styled.div`
  flex: 1;
`;

const ProgramOutputs = styled.div`
  display: flex;
  gap: 20px;
  margin-top: 10px;
`;

const ProgramOutput = styled.div`
  flex: 1;
  padding: 10px;
  border: 1px solid #ddd;
  border-radius: 4px;
  background-color: #fff;
`;

const ProgramTitle = styled.div`
  font-weight: bold;
  margin-bottom: 5px;
`;

const ResultDisplay = ({ result, mode, isLoading }) => {
  if (isLoading) {
    return (
      <Container>
        <Title>Result</Title>
        <LoadingText>Processing with Z3 solver...</LoadingText>
      </Container>
    );
  }

  if (!result) {
    return null;
  }

  if (result.error) {
    return (
      <Container>
        <Title>Error</Title>
        <ResultBox $verified={false}>
          <ResultText $verified={false}>Error during {mode}</ResultText>
          <div>{result.error}</div>
        </ResultBox>
      </Container>
    );
  }

  if (mode === 'verification') {
    return (
      <Container>
        <Title>Verification Result</Title>
        <ResultBox $verified={result.verified}>
          <ResultText $verified={result.verified}>
            {result.verified 
              ? 'Program is verified! All assertions hold.' 
              : 'Verification failed! Assertion can be violated.'}
          </ResultText>
          
          {result.verified ? (
            <>
              <ExampleTitle>Example where assertion holds:</ExampleTitle>
              {result.examples && result.examples.length > 0 && (
                <ExampleContainer>
                  {Object.entries(result.examples[0]).map(([key, value]) => (
                    <ExampleRow key={key}>
                      <ExampleLabel>{key}:</ExampleLabel>
                      <ExampleValue>{value}</ExampleValue>
                    </ExampleRow>
                  ))}
                </ExampleContainer>
              )}
            </>
          ) : (
            <>
              <ExampleTitle>Counterexamples where assertion fails:</ExampleTitle>
              {result.examples && result.examples.map((example, index) => (
                <ExampleContainer key={index}>
                  <div style={{ marginBottom: '5px', fontWeight: 'bold' }}>Counterexample {index + 1}:</div>
                  {Object.entries(example).map(([key, value]) => (
                    <ExampleRow key={key}>
                      <ExampleLabel>{key}:</ExampleLabel>
                      <ExampleValue>{value}</ExampleValue>
                    </ExampleRow>
                  ))}
                </ExampleContainer>
              ))}
              
              {result.counterexample && (
                <>
                  <ExampleTitle>Full Model:</ExampleTitle>
                  <CodeEditor 
                    value={JSON.stringify(result.counterexample, null, 2)} 
                    readOnly={true} 
                    language="json" 
                  />
                </>
              )}
            </>
          )}
        </ResultBox>
      </Container>
    );
  } else if (mode === 'equivalence') {
    return (
      <Container>
        <Title>Equivalence Result</Title>
        <ResultBox $verified={result.equivalent}>
          <ResultText $verified={result.equivalent}>
            {result.equivalent 
              ? 'Programs are equivalent! They produce the same outputs for all inputs.' 
              : 'Programs are not equivalent! Found inputs that produce different outputs.'}
          </ResultText>
          
          {result.equivalent ? (
            <>
              <ExampleTitle>Example where programs behave the same:</ExampleTitle>
              {result.examples && result.examples.length > 0 && (
                <ExampleContainer>
                  <div style={{ fontWeight: 'bold', marginBottom: '10px' }}>Inputs:</div>
                  {Object.entries(result.examples[0].inputs).map(([key, value]) => (
                    <ExampleRow key={key}>
                      <ExampleLabel>{key}:</ExampleLabel>
                      <ExampleValue>{value}</ExampleValue>
                    </ExampleRow>
                  ))}
                  
                  <div style={{ fontWeight: 'bold', marginTop: '15px', marginBottom: '10px' }}>Outputs:</div>
                  <ProgramOutputs>
                    <ProgramOutput>
                      <ProgramTitle>Program 1</ProgramTitle>
                      {Object.entries(result.examples[0].outputs.program1).map(([key, value]) => (
                        <ExampleRow key={key}>
                          <ExampleLabel>{key}:</ExampleLabel>
                          <ExampleValue>{value}</ExampleValue>
                        </ExampleRow>
                      ))}
                    </ProgramOutput>
                    
                    <ProgramOutput>
                      <ProgramTitle>Program 2</ProgramTitle>
                      {Object.entries(result.examples[0].outputs.program2).map(([key, value]) => (
                        <ExampleRow key={key}>
                          <ExampleLabel>{key}:</ExampleLabel>
                          <ExampleValue>{value}</ExampleValue>
                        </ExampleRow>
                      ))}
                    </ProgramOutput>
                  </ProgramOutputs>
                </ExampleContainer>
              )}
            </>
          ) : (
            <>
              <ExampleTitle>Counterexamples where programs behave differently:</ExampleTitle>
              {result.examples && result.examples.map((example, index) => (
                <ExampleContainer key={index}>
                  <div style={{ fontWeight: 'bold', marginBottom: '10px' }}>Counterexample {index + 1} - Inputs:</div>
                  {Object.entries(example.inputs).map(([key, value]) => (
                    <ExampleRow key={key}>
                      <ExampleLabel>{key}:</ExampleLabel>
                      <ExampleValue>{value}</ExampleValue>
                    </ExampleRow>
                  ))}
                  
                  <div style={{ fontWeight: 'bold', marginTop: '15px', marginBottom: '10px' }}>Different Outputs:</div>
                  <ProgramOutputs>
                    <ProgramOutput>
                      <ProgramTitle>Program 1</ProgramTitle>
                      {Object.entries(example.outputs.program1).map(([key, value]) => (
                        <ExampleRow key={key}>
                          <ExampleLabel>{key}:</ExampleLabel>
                          <ExampleValue>{value}</ExampleValue>
                        </ExampleRow>
                      ))}
                    </ProgramOutput>
                    
                    <ProgramOutput>
                      <ProgramTitle>Program 2</ProgramTitle>
                      {Object.entries(example.outputs.program2).map(([key, value]) => (
                        <ExampleRow key={key}>
                          <ExampleLabel>{key}:</ExampleLabel>
                          <ExampleValue>{value}</ExampleValue>
                        </ExampleRow>
                      ))}
                    </ProgramOutput>
                  </ProgramOutputs>
                </ExampleContainer>
              ))}
              
              {result.counterexample && (
                <>
                  <ExampleTitle>Full Model:</ExampleTitle>
                  <CodeEditor 
                    value={JSON.stringify(result.counterexample, null, 2)} 
                    readOnly={true} 
                    language="json" 
                  />
                </>
              )}
            </>
          )}
        </ResultBox>
      </Container>
    );
  }

  return null;
};

export default ResultDisplay;