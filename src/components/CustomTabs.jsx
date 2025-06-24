import React, { useState, Children, cloneElement, createElement } from 'react';


export function Tabs({ children }) {
  const [activeIndex, setActiveIndex] = useState(0);

  const tabList = [];
  const tabPanels = [];

  Children.forEach(children, (child) => {
    if (child.type.displayName === 'TabList') {
      tabList.push(...Children.toArray(child.props.children));
    } else if (child.type.displayName === 'TabPanel') {
      tabPanels.push(child);
    }
  });

  return (
    <div>
      {tabList.map((list, i) =>
        cloneElement(list, { activeIndex, setActiveIndex, key: i })
      )}
      {tabPanels.map((panel, i) =>
        cloneElement(panel, { activeIndex, index: i, key: i })
      )}
    </div>
  );
}

export function TabList({ children }) {
  return <div style={{ display: 'flex', gap: '1rem' }}>{children}</div>;
}
TabList.displayName = 'TabList';

export function Tab({ children, activeIndex, setActiveIndex, index }) {
  const isActive = index === activeIndex;
  return (
    <button
      onClick={() => setActiveIndex(index)}
      style={{
        padding: '0.5rem 1rem',
        fontWeight: isActive ? 'bold' : 'normal',
        borderBottom: isActive ? '2px solid black' : 'none',
        background: 'none',
        border: 'none',
        cursor: 'pointer'
      }}
    >
      {children}
    </button>
  );
}
Tab.displayName = 'Tab';

export function TabPanel({ children, activeIndex, index }) {
  if (activeIndex !== index) return null;
  return <div style={{ marginTop: '1rem' }}>{children}</div>;
}
TabPanel.displayName = 'TabPanel';
