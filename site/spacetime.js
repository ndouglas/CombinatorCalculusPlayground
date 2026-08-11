// The spacetime figure: x = fire number, y = position in the leaf string,
// anchored to the tail so emitted junk keeps its place and reads as the
// frozen field that sc_swap_revolution proves it to be.

import { march, leafSeq } from './sc.js';

const S_COLOUR = [255, 196, 64];
const C_COLOUR = [72, 160, 255];

const VIRIDIS = [[68, 1, 84], [59, 82, 139], [33, 145, 140], [94, 201, 98], [253, 231, 37]];

function ramp(u) {
  const x = Math.max(0, Math.min(1, u)) * (VIRIDIS.length - 1);
  const i = Math.floor(x);
  if (i >= VIRIDIS.length - 1) return VIRIDIS[VIRIDIS.length - 1];
  const f = x - i, a = VIRIDIS[i], b = VIRIDIS[i + 1];
  return [0, 1, 2].map((k) => Math.round(a[k] + (b[k] - a[k]) * f));
}

export function spacetimeRaster(term, opts = {}) {
  const fires = opts.fires ?? 520;
  const mode = opts.mode ?? 'atom';
  const { states, fate } = march(term, fires, { leafCap: opts.leafCap ?? 20000 });

  const rows = states.map(leafSeq);
  const width = rows.length;
  const height = rows.reduce((m, r) => Math.max(m, r.length), 0);
  const maxDepth = rows.reduce((m, r) => r.reduce((n, l) => Math.max(n, l.depth), m), 1);

  const pixels = new Uint8ClampedArray(width * height * 4);
  for (let x = 0; x < width; x++) {
    const row = rows[x];
    const offset = height - row.length; // tail-anchored
    for (let j = 0; j < row.length; j++) {
      const leaf = row[j];
      const [r, g, b] = mode === 'depth'
        ? ramp(leaf.depth / maxDepth)
        : (leaf.atom === 'S' ? S_COLOUR : C_COLOUR);
      const i = ((j + offset) * width + x) * 4;
      pixels[i] = r; pixels[i + 1] = g; pixels[i + 2] = b; pixels[i + 3] = 255;
    }
  }
  return { width, height, pixels, fate };
}

/** The only part that touches a canvas. Nearest-neighbour, never smoothed. */
export function drawSpacetime(canvas, raster) {
  const src = document.createElement('canvas');
  src.width = raster.width;
  src.height = raster.height;
  src.getContext('2d').putImageData(
    new ImageData(raster.pixels, raster.width, raster.height), 0, 0,
  );

  const ctx = canvas.getContext('2d');
  ctx.imageSmoothingEnabled = false;
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.drawImage(src, 0, 0, canvas.width, canvas.height);
}
