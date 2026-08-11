// The phase atlas. Position from `coords` (leftmost-march geometry),
// colour from `screenKind` (census phase). The upper-right region is the
// subject of the figure, so it is drawn and labelled, not left as absence.

import { parse } from './sc.js';
import {
  sampleBatch, mulberry32, coords, QUADRANT_WIDTH, QUADRANT_DROP,
} from './sample.js';
import { FOUND_CORRIDORS, CLIMBER } from './specimens.js';

/**
 * Constructed, not sampled. Uniform sampling at n=10 yields ~2 corridors per
 * 1,000 terms and almost none with the deep drops that define the corridor
 * arm, so the arm is populated deliberately and labelled as such.
 */
export const KNOWN_CORRIDORS = [
  { name: 'the climber (scMt5T)', source: CLIMBER },
  ...FOUND_CORRIDORS.map((c) => ({ name: `found corridor, drop ${c.drop}`, source: c.source })),
];

export function knownCorridorPoints(opts = {}) {
  return KNOWN_CORRIDORS.map(({ name, source }) => {
    const c = coords(parse(source), { horizon: opts.horizon ?? 1200, ...opts });
    return { name, width: c.width, drop: c.drop, phase: 'corridor', constructed: true };
  });
}

export function project(p, box) {
  const w = Math.max(1, p.width);
  const lx = Math.log(w) / Math.log(box.maxWidth);
  const ly = p.drop / box.maxDrop;
  return {
    x: box.x + Math.max(0, Math.min(1, lx)) * box.w,
    y: box.y + box.h - Math.max(0, Math.min(1, ly)) * box.h,
  };
}

const PHASE_COLOUR = {
  halt: 'rgba(140,150,170,0.45)',
  branch: 'rgba(72,160,255,0.55)',
  corridor: 'rgba(255,196,64,0.95)',
};

export function drawAtlas(canvas, points, opts = {}) {
  const ctx = canvas.getContext('2d');
  const pad = 48;
  const box = {
    x: pad, y: pad,
    w: canvas.width - pad * 2,
    h: canvas.height - pad * 2,
    maxWidth: opts.maxWidth ?? 1000,
    maxDrop: opts.maxDrop ?? 250,
  };

  ctx.clearRect(0, 0, canvas.width, canvas.height);

  // The empty quadrant, drawn because it is the subject.
  const q = project({ width: QUADRANT_WIDTH, drop: box.maxDrop }, box);
  const qb = project({ width: QUADRANT_WIDTH, drop: QUADRANT_DROP }, box);
  ctx.fillStyle = 'rgba(255,80,80,0.07)';
  ctx.fillRect(q.x, q.y, box.x + box.w - q.x, qb.y - q.y);
  ctx.strokeStyle = 'rgba(255,80,80,0.45)';
  ctx.setLineDash([4, 4]);
  ctx.strokeRect(q.x, q.y, box.x + box.w - q.x, qb.y - q.y);
  ctx.setLineDash([]);

  for (const p of points) {
    const { x, y } = project(p, box);
    if (p.constructed) {
      ctx.strokeStyle = PHASE_COLOUR.corridor;
      ctx.lineWidth = 1.5;
      ctx.beginPath();
      ctx.moveTo(x - 4, y); ctx.lineTo(x + 4, y);
      ctx.moveTo(x, y - 4); ctx.lineTo(x, y + 4);
      ctx.stroke();
    } else {
      ctx.fillStyle = PHASE_COLOUR[p.phase] ?? PHASE_COLOUR.halt;
      ctx.fillRect(x - 1, y - 1, 2, 2);
    }
  }
  return box;
}

/**
 * Progressive sampling under a frame budget, so the page stays responsive and
 * the reader watches the quadrant stay empty rather than being told it is.
 */
export function runAtlas(canvas, opts = {}) {
  const seed = opts.seed ?? 20260810;
  const total = opts.total ?? 4000;
  const budgetMs = opts.budgetMs ?? 12;
  const rnd = mulberry32(seed);
  const points = knownCorridorPoints();
  let done = 0;
  let stopped = false;

  function tick() {
    if (stopped || done >= total) return;
    const start = Date.now();
    while (Date.now() - start < budgetMs && done < total) {
      const batch = sampleBatch(rnd, 25, { size: opts.size ?? 10 });
      for (const s of batch) {
        points.push({ width: s.width, drop: s.drop, phase: s.phase, constructed: false });
      }
      done += batch.length;
    }
    drawAtlas(canvas, points, opts);
    opts.onProgress?.(done, total, points);
    requestAnimationFrame(tick);
  }

  requestAnimationFrame(tick);
  return { stop() { stopped = true; } };
}
