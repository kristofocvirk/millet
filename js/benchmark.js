const fs = require('fs');
const { run } = require('node:test');
const { promisify } = require('util');
const readFile = promisify(fs.readFile);

function calculateMean(numbers) {
  return numbers.reduce((sum, num) => sum + num, 0) / numbers.length;
}

function calculateStandardDeviation(numbers, mean) {
  const squaredDifferences = numbers.map(num => Math.pow(num - mean, 2));
  const variance = calculateMean(squaredDifferences);
  return Math.sqrt(variance);
}

async function loadAndRunWasm(wasmFilePath, n = 100, fibArg = 40) {
  try {
    // Read the WASM file
    const wasmBuffer = await readFile(wasmFilePath);
    
    // Instantiate the WebAssembly module
    const wasmModule = await WebAssembly.instantiate(wasmBuffer);
    
    // Get the exported functions
    const { call_gcd_1000_times } = wasmModule.instance.exports;
    const { fact } = wasmModule.instance.exports;
    const { fib } = wasmModule.instance.exports;
    
    const times = [];
    let result;

    console.log(`Running ${n} trials of function (${fibArg})...`);

    for (let i = 0; i < n; i++) {
      const start = performance.now();
      result = call_gcd_1000_times(10);
      const end = performance.now();
      times.push(end - start);
    }

    const mean = calculateMean(times);
    const stdDev = calculateStandardDeviation(times, mean);

    console.log(`Result: ${result}`);
    console.log(`Mean execution time: ${mean.toFixed(4)} ms`);
    console.log(`Standard deviation: ${stdDev.toFixed(4)} ms`);

  } catch (error) {
    console.error('Error loading or running WASM:', error);
  }
}

// Usage
const trials = 100;  // Number of trials
const fibArg = 10;   // Argument for Fibonacci function
loadAndRunWasm('gcd_1000.wasm', trials, fibArg);