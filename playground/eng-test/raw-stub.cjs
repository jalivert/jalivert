// Node CJS hook so `npm run test:engines` can load Vite `?raw` imports.
// Resolves them against the real vendor/ tree.
const Module = require('module');
const path = require('path');
const fs = require('fs');

const origLoad = Module._load;
Module._load = function (request, parent, isMain) {
  if (typeof request === 'string' && request.includes('?raw')) {
    const rel = request.split('?')[0];
    const dir = path.dirname(parent.filename);
    let full = path.resolve(dir, rel);
    full = full.replace(`node_modules${path.sep}.eng-test`, '');
    full = path.normalize(full);
    if (!fs.existsSync(full)) {
      // ad-hoc tsc out dirs (e.g. /tmp): fall back to the web-demo tree
      // containing this stub (eng-test/..).
      const root = path.resolve(__dirname, '..');
      full = path.normalize(path.join(root, rel.replace(/^(\.\.\/)+/, '')));
    }
    return fs.readFileSync(full, 'utf8');
  }
  return origLoad.call(this, request, parent, isMain);
};
