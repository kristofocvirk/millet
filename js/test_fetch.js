const fs = require('fs');
const { promisify } = require('util');

const readFile = promisify(fs.readFile);

async function loadAndRunWasm(wasmFilePath) {
  try {
    // Read the WASM file
    const wasmBuffer = await readFile(wasmFilePath);
    
    // Instantiate the WebAssembly module
    const wasmModule = await WebAssembly.instantiate(wasmBuffer);
    
    // Get the exported functions
    const exports = wasmModule.instance.exports;
    
    // Now you can use the exported functions
    const start = performance.now();
    const result = exports.run_0(); // Assuming run_0 is the exported function
    const end = performance.now();
    
    console.log('Result:', result);
    console.log('Time in ms:', end - start);
  } catch (error) {
    console.error('Error loading or running WASM:', error);
  }
}

// Check for the CLI argument
const wasmFilePath = process.argv[2]; // The third element is the CLI argument for the wasm file path

if (!wasmFilePath) {
  console.error('Please provide the path to the WASM file as an argument.');
  process.exit(1); // Exit the program with a failure code
}

// Usage
loadAndRunWasm(wasmFilePath);