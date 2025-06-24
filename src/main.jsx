import React from 'react';
import ReactDOM from 'react-dom/client';
import App from './App.jsx';
import './index.css';
// Fix the import statement for z3-solver
import * as wasmTransformer from '@wasmer/wasm-transformer';

// Preload Z3
async function preloadZ3() {
  console.log("Preloading Z3...");
  try {
    // Instead of trying to preload Z3 here, let's just check if the files exist
    const wasmResponse = await fetch('/z3/z3-built.wasm');
    const jsResponse = await fetch('/z3/z3-built.js');
    
    if (wasmResponse.ok && jsResponse.ok) {
      console.log("Z3 files found and accessible");
    } else {
      console.error("Z3 files not found or not accessible");
    }
    
    console.log("Z3 preload check completed");
  } catch (error) {
    console.error("Failed to check Z3 files:", error);
  }
}

// Preload Z3 before rendering the app
preloadZ3().then(() => {
  ReactDOM.createRoot(document.getElementById('root')).render(
    <React.StrictMode>
      <App />
    </React.StrictMode>
  );
});