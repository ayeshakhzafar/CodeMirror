import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import path from 'path';

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
    react({
      jsxRuntime: 'classic', // ✅ Avoid jsxs/jsx errors
    }),
    rawLoader(),
  ],
  esbuild: {
    loader: 'jsx',
    include: /\.jsx?$/,
  },
  worker: {
    format: 'es',
    plugins: []
  },
  optimizeDeps: {
    include: [
      'react',
      'react-dom',
      'react/jsx-runtime',
      'react/index.js'
    ],
    exclude: ['z3-solver']
  },
  ssr: {
    noExternal: ['react-tabs', 'styled-components']
  },
  build: {
    commonjsOptions: {
      include: [/node_modules/] // ✅ allow parsing styled-components/react-tabs
    },
    rollupOptions: {
      external: [] // leave empty to bundle all except node built-ins
    }
  },
  server: {
    headers: {
      'Cross-Origin-Opener-Policy': 'same-origin',
      'Cross-Origin-Embedder-Policy': 'require-corp'
    }
  },
  resolve: {
    alias: {
      react: path.resolve('./node_modules/react'),
      'react-dom': path.resolve('./node_modules/react-dom'),
      'react/jsx-runtime': path.resolve('./node_modules/react/jsx-runtime.js')
    },
    extensions: ['.mjs', '.js', '.jsx', '.ts', '.tsx', '.json']
  }
});
