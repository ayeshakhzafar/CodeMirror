import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

function rawLoader() {
  return {
    name: 'vite-plugin-custom-raw',
    transform(src, id) {
      if (/\.(pegjs|txt|md)$/i.test(id)) {
        return `export default ${JSON.stringify(src)}`;
      }
    }
  };
}

export default defineConfig({
  plugins: [
    react(), // Add React plugin
    rawLoader(), // Your custom plugin
  ],
  esbuild: {
    loader: 'jsx',
    include: /\.jsx?$/,
  },
  worker: {
    format: 'es', // Use ES modules for workers
    plugins: [] // No plugins for workers
  },
  optimizeDeps: {
    exclude: ['z3-solver'] // Exclude z3-solver from dependency optimization
  },
  build: {
    commonjsOptions: {
      include: [] // Don't process any files with commonjs
    }
  },
  server: {
    headers: {
      // Add headers for WebAssembly and SharedArrayBuffer support
      'Cross-Origin-Opener-Policy': 'same-origin',
      'Cross-Origin-Embedder-Policy': 'require-corp'
    }
  },
  resolve: {
    // Make sure Vite can resolve the worker file
    extensions: ['.mjs', '.js', '.jsx', '.ts', '.tsx', '.json']
  }
});