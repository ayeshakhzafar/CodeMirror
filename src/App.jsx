import * as React from 'react';
const { useState, useEffect } = React;

import { Tabs, TabList, Tab, TabPanel } from './components/CustomTabs.jsx';
import styled from 'styled-components';
import VerificationMode from './components/VerificationMode';
import EquivalenceMode from './components/EquivalenceMode';
import LoopUnrolling from './components/LoopUnrolling';

const AppContainer = styled.div`
  max-width: 1200px;
  margin: 0 auto;
  padding: 20px;
  font-family: Arial, sans-serif;
`;

const Header = styled.header`
  text-align: center;
  margin-bottom: 30px;
`;

const Title = styled.h1`
  color: #333;
`;

const Subtitle = styled.p`
  color: #666;
  font-size: 18px;
`;

const StyledTabs = styled(Tabs)`
  .react-tabs__tab-list {
    border-bottom: 1px solid #ddd;
    margin: 0 0 20px;
    padding: 0;
  }

  .react-tabs__tab {
    display: inline-block;
    border: 1px solid transparent;
    border-bottom: none;
    bottom: -1px;
    position: relative;
    list-style: none;
    padding: 12px 20px;
    cursor: pointer;
    font-size: 16px;
  }

  .react-tabs__tab--selected {
    background: #fff;
    border-color: #ddd;
    color: #4caf50;
    border-radius: 5px 5px 0 0;
  }

  .react-tabs__tab-panel {
    display: none;
  }

  .react-tabs__tab-panel--selected {
    display: block;
  }
`;

function App() {
  const [tabIndex, setTabIndex] = useState(0);

  return (
    <AppContainer>
      <Header>
        <Title>CodeMirror</Title>
        <Subtitle>Analyze and verify programs using formal methods</Subtitle>
      </Header>
      
      <StyledTabs selectedIndex={tabIndex} onSelect={index => setTabIndex(index)}>
        <TabList>
          <Tab>Verification Mode</Tab>
          <Tab>Equivalence Mode</Tab>
          <Tab>Loop Unrolling</Tab>
        </TabList>
        
        <TabPanel>
          <VerificationMode />
        </TabPanel>
        
        <TabPanel>
          <EquivalenceMode />
        </TabPanel>
        
        <TabPanel>
          <LoopUnrolling />
        </TabPanel>
      </StyledTabs>
    </AppContainer>
  );
}

export default App;