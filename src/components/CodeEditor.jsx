import React from 'react';
import Editor from '@monaco-editor/react';
import styled from 'styled-components';

const EditorContainer = styled.div`
  height: 300px;
  border: 1px solid #ccc;
  border-radius: 4px;
  overflow: hidden;
`;

const CodeEditor = ({ value, onChange, language = 'javascript', readOnly = false }) => {
  return (
    <EditorContainer>
      <Editor
        height="100%"
        language={language}
        value={value}
        onChange={onChange}
        options={{
          minimap: { enabled: false },
          scrollBeyondLastLine: false,
          fontSize: 14,
          readOnly
        }}
      />
    </EditorContainer>
  );
};

export default CodeEditor;