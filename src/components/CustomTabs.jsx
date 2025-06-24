// src/components/CustomTabs.jsx

import React, { useState, Children, cloneElement } from 'react';

export function Tabs({ children }) {
  const [activeIndex, setActiveIndex] = useState(0);

  let tabList = null;
  const tabPanels = [];

  Children.forEach(children, (child) => {
    if (child.type.displayName === 'TabList') {
      tabList = child;
    } else if (child.type.displayName === 'TabPanel') {
      tabPanels.push(child);
    }
  });

  const processedTabList = tabList
    ? cloneElement(tabList, {
        children: Children.map(tabList.props.children, (tab, i) =>
          cloneElement(tab, {
            index: i,
            activeIndex,
            setActiveIndex,
            key: i,
          })
        ),
      })
    : null;

  return (
    <div>
      {processedTabList}
      {tabPanels.map((panel, i) =>
        cloneElement(panel, { activeIndex, index: i, key: i })
      )}
    </div>
  );
}

export function TabList({ children }) {
  return (
    <div
      style={{
        display: 'flex',
        gap: '0.75rem',
        padding: '0.5rem 0',
        borderBottom: '2px solid #ccc',
        marginBottom: '1rem',
      }}
    >
      {children}
    </div>
  );
}
TabList.displayName = 'TabList';

export function Tab({ children, activeIndex, setActiveIndex, index }) {
  const isActive = index === activeIndex;
  return (
    <button
      onClick={() => setActiveIndex(index)}
      style={{
        padding: '0.5rem 1rem',
        borderRadius: '6px 6px 0 0',
        fontWeight: isActive ? 'bold' : 'normal',
        backgroundColor: isActive ? '#d8b4f8' : '#f3e8ff', // light purple and lavender
        color: isActive ? '#4b0082' : '#333',              // indigo text for active
        border: 'none',
        borderBottom: isActive ? '2px solid #d8b4f8' : '2px solid transparent',
        cursor: 'pointer',
        transition: 'background-color 0.3s ease',
      }}
    >
      {children}
    </button>
  );
}
Tab.displayName = 'Tab';

export function TabPanel({ children, activeIndex, index }) {
  if (activeIndex !== index) return null;
  return (
    <div style={{ padding: '1rem', border: '1px solid #ddd', borderRadius: '0 0 6px 6px' }}>
      {children}
    </div>
  );
}
TabPanel.displayName = 'TabPanel';
