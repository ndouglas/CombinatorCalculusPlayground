import { parse, show, leaves } from './sc.js';
import { spacetimeRaster, drawSpacetime } from './spacetime.js';
import { runAtlas } from './atlas.js';
import { SPECIMENS } from './specimens.js';

const $ = (id) => document.getElementById(id);

/** The render cap. A storm reaches it at fire 62; that wedge is the point. */
const RENDER_LEAF_CAP = 1200;

for (const [i, s] of SPECIMENS.entries()) {
  const opt = document.createElement('option');
  opt.value = String(i);
  opt.textContent = s.label;
  $('term-pick').append(opt);
}

function renderSpacetime() {
  const text = $('term-text').value.trim();
  const chosen = SPECIMENS[Number($('term-pick').value)];
  let term;
  try {
    term = text ? parse(text) : parse(chosen.source);
    $('parse-error').textContent = '';
  } catch (e) {
    $('parse-error').textContent = e.message;
    return;
  }
  const fires = Number($('fires').value);
  const raster = spacetimeRaster(term, {
    fires, mode: $('mode-pick').value, leafCap: RENDER_LEAF_CAP,
  });
  const canvas = $('spacetime');
  canvas.width = raster.width;
  canvas.height = raster.height;
  drawSpacetime(canvas, raster);
  const capped = raster.height >= RENDER_LEAF_CAP;
  $('spacetime-caption').textContent =
    `${show(term)} — ${leaves(term)} leaves, ${raster.width - 1} fires, ` +
    `growing to ${raster.height} leaves` +
    (capped ? `, cut off at the ${RENDER_LEAF_CAP}-leaf render cap.` : '.');
}

$('term-pick').addEventListener('input', () => {
  $('term-text').value = '';
  $('fires').value = String(SPECIMENS[Number($('term-pick').value)].fires);
  renderSpacetime();
});
for (const id of ['mode-pick', 'fires']) {
  $(id).addEventListener('input', renderSpacetime);
}
$('term-go').addEventListener('click', renderSpacetime);
$('term-text').addEventListener('keydown', (e) => { if (e.key === 'Enter') renderSpacetime(); });
renderSpacetime();

let atlas = null;
function startAtlas(seed) {
  atlas?.stop();
  $('seed-shown').textContent = String(seed);
  const url = new URL(location.href);
  url.searchParams.set('seed', String(seed));
  history.replaceState(null, '', url);
  atlas = runAtlas($('atlas'), {
    seed,
    onProgress: (done, total) => { $('atlas-progress').textContent = `${done} / ${total} terms`; },
  });
}
$('reseed').addEventListener('click', () => startAtlas((Math.random() * 1e9) | 0));
$('atlas-stop').addEventListener('click', () => atlas?.stop());
startAtlas(Number(new URL(location.href).searchParams.get('seed')) || 20260810);
