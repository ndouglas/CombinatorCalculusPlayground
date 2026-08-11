// The phase atlas. Position from `coords` (leftmost-march geometry),
// colour from `screenKind` (census phase). The upper-right region is the
// subject of the figure, so it is drawn and labelled, not left as absence.

import { parse } from './sc.js';
import {
  sampleBatch, mulberry32, coords, QUADRANT_WIDTH, QUADRANT_DROP,
} from './sample.js';
import { FOUND_CORRIDORS, CLIMBER } from './specimens.js';

/** Chosen to contain the data: deepest point anywhere is 109 (the climber). */
export const DEFAULT_MAX_DROP = 120;
/** Widest observed sampled term is 3343. */
export const DEFAULT_MAX_WIDTH = 4000;
/** How many terms the published figure samples. Tests MUST cover at least this. */
export const ATLAS_TOTAL = 4000;

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

const AXIS = 'rgba(128,134,148,0.95)';
const AXIS_FAINT = 'rgba(128,134,148,0.26)';

function drawAxes(ctx, box) {
  ctx.font = '19px ui-monospace, Menlo, monospace';
  ctx.lineWidth = 1;
  ctx.strokeStyle = AXIS;
  ctx.fillStyle = AXIS;

  ctx.beginPath();
  ctx.moveTo(box.x, box.y);
  ctx.lineTo(box.x, box.y + box.h);
  ctx.lineTo(box.x + box.w, box.y + box.h);
  ctx.stroke();

  ctx.textAlign = 'right';
  ctx.textBaseline = 'middle';
  for (const d of [0, 40, 80, 120]) {
    if (d > box.maxDrop) continue;
    const y = box.y + box.h - (d / box.maxDrop) * box.h;
    ctx.strokeStyle = AXIS;
    ctx.beginPath();
    ctx.moveTo(box.x - 6, y);
    ctx.lineTo(box.x, y);
    ctx.stroke();
    ctx.fillText(String(d), box.x - 12, y);
    if (d > 0) {
      ctx.strokeStyle = AXIS_FAINT;
      ctx.beginPath();
      ctx.moveTo(box.x, y);
      ctx.lineTo(box.x + box.w, y);
      ctx.stroke();
    }
  }

  ctx.strokeStyle = AXIS;
  ctx.textBaseline = 'top';
  for (const w of [1, 2, 10, 100, 1000, 4000]) {
    if (w > box.maxWidth) continue;
    const x = box.x + (Math.log(Math.max(1, w)) / Math.log(box.maxWidth)) * box.w;
    ctx.beginPath();
    ctx.moveTo(x, box.y + box.h);
    ctx.lineTo(x, box.y + box.h + 6);
    ctx.stroke();
    ctx.textAlign = w === box.maxWidth ? 'right' : (w === 1 ? 'left' : 'center');
    ctx.fillText(String(w), x, box.y + box.h + 12);
  }

  ctx.fillText('median late branching width  (log scale)', box.x + box.w / 2, box.y + box.h + 40);
  ctx.save();
  ctx.translate(box.x - 58, box.y + box.h / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.textAlign = 'center';
  ctx.textBaseline = 'bottom';
  ctx.fillText('max drop from running peak', 0, 0);
  ctx.restore();
}

export function drawAtlas(canvas, points, opts = {}) {
  const ctx = canvas.getContext('2d');
  const padL = 84, padR = 28, padT = 28, padB = 84;
  const box = {
    x: padL, y: padT,
    w: canvas.width - padL - padR,
    h: canvas.height - padT - padB,
    maxWidth: opts.maxWidth ?? DEFAULT_MAX_WIDTH,
    maxDrop: opts.maxDrop ?? DEFAULT_MAX_DROP,
  };

  ctx.clearRect(0, 0, canvas.width, canvas.height);
  drawAxes(ctx, box);

  // The empty quadrant, drawn because it is the subject.
  const q = project({ width: QUADRANT_WIDTH, drop: box.maxDrop }, box);
  const qb = project({ width: QUADRANT_WIDTH, drop: QUADRANT_DROP }, box);
  ctx.fillStyle = 'rgba(255,80,80,0.07)';
  ctx.fillRect(q.x, q.y, box.x + box.w - q.x, qb.y - q.y);
  ctx.strokeStyle = 'rgba(255,80,80,0.45)';
  ctx.setLineDash([4, 4]);
  ctx.strokeRect(q.x, q.y, box.x + box.w - q.x, qb.y - q.y);
  ctx.setLineDash([]);

  const sampled = points.filter((p) => !p.constructed);
  const inRegion = sampled.filter(
    (p) => p.width >= QUADRANT_WIDTH && p.drop >= QUADRANT_DROP,
  ).length;
  ctx.fillStyle = 'rgba(220,60,60,0.85)';
  ctx.font = '18px ui-monospace, Menlo, monospace';
  ctx.textAlign = 'right';
  ctx.textBaseline = 'top';
  ctx.fillText(
    `branching AND descending: ${inRegion} of ${sampled.length}`,
    box.x + box.w - 8, q.y + 12,
  );

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
  const total = opts.total ?? ATLAS_TOTAL;
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
