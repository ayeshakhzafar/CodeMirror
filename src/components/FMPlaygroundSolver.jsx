import React, { useState } from 'react';

// Main component with dark, high-contrast text
const FMPlaygroundSolver = () => {
  const [showSMT, setShowSMT] = useState(false);
  const [copied, setCopied] = useState(false);
  const [showExamples, setShowExamples] = useState(true);
  
  const handleCopy = () => {
    // Simulate copy action
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  };
  
  return (
    <div className="p-6 bg-gray-100 border border-gray-300 rounded-md">
      <h2 className="text-2xl font-bold text-gray-900 mb-4">FM Playground Z3 Solver</h2>
      
      <p className="text-gray-900 mb-4 font-medium">
        Follow these steps to verify your program using FM Playground Z3:
      </p>
      
      <ol className="mb-6 text-gray-900 list-decimal pl-6">
        <li className="mb-2 font-medium">Click the "Copy SMT Constraints" button below</li>
        <li className="mb-2 font-medium">
          <span className="font-bold text-blue-700">Open FM Playground Z3 in a new tab</span>
        </li>
        <li className="mb-2 font-medium">Paste the constraints into the input area</li>
        <li className="mb-2 font-medium">Click "Run" or "Solve" button on the FM Playground</li>
        <li className="mb-2 font-medium">Check the result in the output area</li>
        <li className="mb-2 font-medium">Look for the model in the output to find examples/counterexamples</li>
      </ol>
      
      <div className="flex gap-3 mb-6">
        {copied ? (
          <button 
            className="px-4 py-2 bg-green-600 text-white font-bold rounded-md"
            onClick={handleCopy}
          >
            Copied!
          </button>
        ) : (
          <button 
            className="px-4 py-2 bg-blue-700 text-white font-bold rounded-md"
            onClick={handleCopy}
          >
            Copy SMT Constraints
          </button>
        )}
        
        <button 
          className="px-4 py-2 bg-gray-200 text-gray-900 font-medium border border-gray-400 rounded-md"
          onClick={() => setShowSMT(!showSMT)}
        >
          {showSMT ? 'Hide' : 'Show'} SMT Constraints
        </button>
        
        <button 
          className="px-4 py-2 bg-gray-200 text-gray-900 font-medium border border-gray-400 rounded-md"
          onClick={() => setShowExamples(!showExamples)}
        >
          {showExamples ? 'Hide' : 'Show'} Example Scenarios
        </button>
      </div>
      
      {showSMT && (
        <pre className="p-3 bg-gray-200 border border-gray-300 rounded-md overflow-auto max-h-64 text-gray-900 mb-4">
          {`(declare-const x Int)
(declare-const y Int)
(assert (not (=> (and (>= x 0) (>= y 0)) (>= (+ x y) 0))))
(check-sat)
(get-model)`}
        </pre>
      )}
      
      <div className="mt-4 mb-6">
        <p className="text-gray-900 font-bold mb-2">
          How to interpret results:
        </p>
        <ul className="text-gray-900 list-disc pl-6">
          <li className="mb-1 font-medium">If the result is "unsat", the verification passes (property holds for all inputs)</li>
          <li className="mb-1 font-medium">If the result is "sat", the verification fails (counterexample exists)</li>
          <li className="mb-1 font-medium">If the result includes a model, it shows a counterexample that violates the property</li>
        </ul>
      </div>
      
      {showExamples && (
        <>
          <div className="p-4 bg-green-100 border border-green-300 rounded-md mb-4">
            <h3 className="text-xl font-bold text-gray-900 mb-2">Example Scenario Where Postcondition Holds</h3>
            <p className="text-gray-900 mb-3 font-medium">Here's an example input where the program's postcondition should be satisfied:</p>
            
            <table className="w-full border-collapse mb-3">
              <thead>
                <tr>
                  <th className="border border-gray-300 p-2 bg-gray-200 text-gray-900">x</th>
                  <th className="border border-gray-300 p-2 bg-gray-200 text-gray-900">y</th>
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td className="border border-gray-300 p-2 text-gray-900">3</td>
                  <td className="border border-gray-300 p-2 text-gray-900">4</td>
                </tr>
              </tbody>
            </table>
            
            <p className="text-gray-700 text-sm font-medium">
              Note: If the solver returns "unsat", the postcondition holds for all inputs, including this example.
            </p>
          </div>
          
          <div className="p-4 bg-red-100 border border-red-300 rounded-md mb-4">
            <h3 className="text-xl font-bold text-gray-900 mb-2">Potential Counterexamples</h3>
            <p className="text-gray-900 mb-3 font-medium">If the solver returns "sat", look for values in the model that might resemble these counterexamples:</p>
            
            <table className="w-full border-collapse mb-3">
              <thead>
                <tr>
                  <th className="border border-gray-300 p-2 bg-gray-200 text-gray-900">x</th>
                  <th className="border border-gray-300 p-2 bg-gray-200 text-gray-900">y</th>
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td className="border border-gray-300 p-2 text-gray-900">-5</td>
                  <td className="border border-gray-300 p-2 text-gray-900">-6</td>
                </tr>
                <tr>
                  <td className="border border-gray-300 p-2 text-gray-900">-10</td>
                  <td className="border border-gray-300 p-2 text-gray-900">-11</td>
                </tr>
              </tbody>
            </table>
            
            <p className="text-gray-700 text-sm font-medium">
              Note: The actual counterexample from the solver may differ. Look for variable assignments in the model.
            </p>
          </div>
        </>
      )}
      
      <div className="p-4 bg-blue-100 border border-blue-300 rounded-md">
        <p className="text-gray-900 font-bold mb-1">
          How to Extract Examples from Z3 Output:
        </p>
        <ul className="text-gray-900 list-disc pl-6 mb-0">
          <li className="mb-1 font-medium">Look for the model section in the Z3 output (appears after "sat")</li>
          <li className="mb-1 font-medium">Find variable assignments like <code className="bg-gray-200 px-1 rounded">define-fun x () Int 3</code></li>
          <li className="mb-1 font-medium">For verification, focus on variables in the postcondition</li>
          <li className="mb-1 font-medium">For equivalence, look for variables with different values between programs</li>
          <li className="font-medium">Variables may have suffixes like "_1" or "_2" - these are SSA versions</li>
        </ul>
      </div>
    </div>
  );
};

export default FMPlaygroundSolver;