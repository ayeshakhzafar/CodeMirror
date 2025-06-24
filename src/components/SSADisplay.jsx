import React from 'react';
import styled from 'styled-components';
import CodeEditor from './CodeEditor';
import { ssaToReadableFormat, ssaToString } from '../utils/ssaTransformer';

const Container = styled.div`
  margin-bottom: 20px;
`;

const Title = styled.h3`
  margin-bottom: 10px;
`;

const FormatToggle = styled.div`
  display: flex;
  align-items: center;
  margin-bottom: 10px;
`;

const SSADisplay = ({ ssaForm, optimizedSSA }) => {
  const [showReadableFormat, setShowReadableFormat] = React.useState(true);

  // Safely convert SSA form to readable text format
  const getSsaReadable = (ssa) => {
    if (!ssa) return '';
    try {
      return ssaToReadableFormat(ssa);
    } catch (error) {
      console.error("Error formatting SSA:", error);
      // Fall back to string format if readable format fails
      try {
        return ssaToString(ssa);
      } catch (innerError) {
        console.error("Error converting SSA to string:", innerError);
        return `Error formatting SSA: ${error.message}`;
      }
    }
  };

  const ssaReadable = getSsaReadable(ssaForm);
  const optimizedReadable = getSsaReadable(optimizedSSA);

  // Safely convert to JSON
  const getSsaJson = (ssa) => {
    if (!ssa || !ssa.ssaStatements) return '';
    try {
      return JSON.stringify(ssa.ssaStatements, null, 2);
    } catch (error) {
      console.error("Error stringifying SSA:", error);
      return `Error formatting SSA JSON: ${error.message}`;
    }
  };

  const ssaJson = getSsaJson(ssaForm);
  const optimizedJson = getSsaJson(optimizedSSA);

  return (
    <Container>
      <FormatToggle>
        <label>
          <input
            type="checkbox"
            checked={showReadableFormat}
            onChange={() => setShowReadableFormat(!showReadableFormat)}
          />
          Show readable format
        </label>
      </FormatToggle>

      <Title>SSA Form</Title>
      <CodeEditor 
        value={showReadableFormat ? ssaReadable : ssaJson} 
        readOnly={true} 
        language={showReadableFormat ? "text" : "json"} 
      />
      
      {optimizedSSA && (
        <>
          <Title>Optimized SSA Form</Title>
          <CodeEditor 
            value={showReadableFormat ? optimizedReadable : optimizedJson} 
            readOnly={true} 
            language={showReadableFormat ? "text" : "json"} 
          />
        </>
      )}
    </Container>
  );
};

export default SSADisplay;