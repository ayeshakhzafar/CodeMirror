import React from 'react';
import styled from 'styled-components';
import CodeEditor from './CodeEditor';

const Container = styled.div`
  margin-bottom: 20px;
`;

const Title = styled.h3`
  margin-bottom: 10px;
`;

const SMTDisplay = ({ smtCode }) => {
  return (
    <Container>
      <Title>SMT Constraints</Title>
      <CodeEditor value={smtCode} readOnly={true} language="lisp" />
    </Container>
  );
};

export default SMTDisplay;