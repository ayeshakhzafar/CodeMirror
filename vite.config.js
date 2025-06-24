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
    react(),
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
    include: ['react', 'react-dom', 'react-tabs'],
    exclude: ['z3-solver']
  },
  ssr: {
    noExternal: ['react-tabs']
  },
  build: {
    commonjsOptions: {
      include: []
    }
  },
  server: {
    headers: {
      'Cross-Origin-Opener-Policy': 'same-origin',
      'Cross-Origin-Embedder-Policy': 'require-corp'
    }
  },
  resolve: {
    extensions: ['.mjs', '.js', '.jsx', '.ts', '.tsx', '.json']
  }
});
