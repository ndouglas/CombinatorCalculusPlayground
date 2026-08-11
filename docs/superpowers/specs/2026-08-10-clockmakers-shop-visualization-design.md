# The Clockmaker's Shop — a visual essay on `{S,C}`

**Date**: 2026-08-10
**Status**: design approved, not yet implemented

## Purpose

A public-facing essay, deployed to GitHub Pages, that shows what `{S,C}` reduction
actually looks like and argues a specific thesis:

> In the orderly eternal phase — where all of the Class-4 cellular-automaton scenery
> lives — the structures provably never interact. That is *why* the universality
> question migrated into the storm regime, which has no scenery at all.

The essay must not overclaim. C14 (the storm floor) is **open**; the walls at Stages
260–267 are partial. "There is no computer in `{S,C}`" is not a result this program
has, and the page must not imply it.

## Thesis and honesty constraints

Three tiers, kept visually distinct on the page:

- **Proved** — cited by Lean name. The mill cycle (`sc_mill_cycle`), the eternal
  spiral (`sc_mill_eternal`), the corridor's infinitude (`sc_corridor_unbounded`),
  the line (`sc_mt5T_line`), the ridden revolution (`sc_swap_revolution`), the unit
  drop law (`sc_unit_drop`), the cold law (`sc_cold_law`), the minting law
  (`sc_minting_law`, `sc_minting_run`).
- **Probed** — measured, not proved. Storm digs ≤ 26 from peaks of 700–1500
  (Stage 256); median late forced-fraction 0.00 for storms (Stage 253); the dig
  budget tracking C-redex inventory, median 9 (Stage 260).
- **Open** — C14, and therefore the central question.

The status box near the end of the essay carries all three explicitly. Any figure
derived from sampling is labelled as sampled, with its seed shown.

## Deployment

- New top-level `site/` directory. `docs/` is left untouched (it holds specs and
  plans, and folding the essay in there would publish those too).
- New `.github/workflows/pages.yml`: `actions/upload-pages-artifact` on `site/`,
  then `actions/deploy-pages`. Does not disturb `lean_action_ci.yml`.
- Pages source set to "GitHub Actions" (`build_type: workflow`). The repo is
  public and Pages is not currently enabled; enabling it is an outward-facing
  act and is confirmed with the user before it happens, not assumed from this spec.

## Components

Four files, each with one job. Separate files rather than one inlined blob
specifically so the engine is testable under `node --test`.

### `site/sc.js` — the engine

A direct port of `SCStep` / `scSucc` (root ++ appL ++ appR), mirroring the 24-line
reference implementation already validated in the scratchpad.

Exports:

- `step(t) -> Term[]` — all one-step successors, in Lean's order.
- `leaves(t) -> number` — leaf count.
- `leafSeq(t) -> {atom, depth}[]` — in-order leaf sequence with bracket depth.
  This is the spatial axis of the spacetime panel.
- `parse(s) -> Term` / `show(t) -> string` — the `C (S C C) S` surface syntax
  used throughout the lab notebook.
- `march(t, n) -> {states, fates}` — leftmost march with a leaf cap.

Terms are nested two-element arrays with `'S'`/`'C'` atoms. No classes, no
dependencies.

**Interface contract**: `sc.js` knows nothing about rendering, sampling, or the
DOM. It can be exercised entirely from Node.

### `site/panels.js` — the two figures

Depends on `sc.js` and a canvas. Two independent entry points.

**`spacetime(canvas, term, opts)`**
- Computes the leftmost march, recording `leafSeq` per fire.
- Renders: `x` = fire number, `y` = index in the leaf string **anchored to the tail**
  (so emitted junk keeps its position and reads as the frozen field it provably is),
  colour = atom (`S` gold / `C` blue) in mode A, or bracket depth on a perceptual
  ramp in mode C.
- Head-anchoring was rejected: insertions shift every later position, smearing the
  static tail into diagonals that misrepresent what is actually static.
- The left spine was rejected as the spatial axis — the climber's spine is only 6
  deep and all 422 of its spine subterms across 420 fires are distinct. Growth
  happens *inside* spine elements, so the spine carries almost no signal.

**`atlas(canvas, opts)`**
Each sampled term gets **two independent measurements**. They answer different
questions and must not be conflated:

- **Phase** (`screenKind`) — the census reproduction. A cheap forcedness screen
  (still exactly one redex after 30 fires) rejects ~99.8% of terms at ~5 fires
  each; survivors get a deep march. Yields halt / branch / corridor at roughly
  67 / 33 / 0.2. This measures *whether the term ever branches*.
- **Geometry** (`coords`) — the atlas position. A bounded leftmost march gives
  `x` = median branching width over the last 50 states (log scale) and
  `y` = maximum drop from the running peak.

These are genuinely different: under a leftmost march ~96% of terms normalize
(Stage 252 records 88.2% of BRANCH terms leftmost-normalizing within 1000 fires),
so the leftmost march does *not* reproduce the 67/33 split and must not be used
for it. The atlas plots position from `coords` and colour from `screenKind`.
- Sampling is progressive: `requestAnimationFrame` chunks under a ~12 ms budget,
  points drawn as they land, with a Stop button. A live counter shows the
  halt/branch/corridor split converging.
- Terms exceeding the leaf cap are recorded as `big` rather than chased.
- The known corridor family (climber, mill, swapmill, spiral) is plotted with a
  **distinct glyph** and labelled as constructed and over-represented ~500×.
  Uniform sampling at n=10 yields roughly 2 corridors per 1,000 terms and almost
  none with the deep 200+ drops that define the corridor arm, so without this the
  arm is simply unpopulated — and pretending otherwise would be dishonest.
- The upper-right region is drawn as an explicitly shaded, labelled zone. It is
  the subject of the figure, so it is marked as such rather than left as absence.

**`rng(seed)`** — mulberry32. The seed is shown in the UI and is a URL parameter,
so every figure in the essay is reproducible by any reader.

### `site/index.html` — the essay

Structure:

1. **The resemblance.** Open on the spacetime figure. It looks like a Class-4
   spacetime diagram: particles, periodic engines, emitted debris.
2. **What is actually there.** The mill and swapmill as certified engines; the
   accelerating comb (period `6(m+1)`, `+4` per revolution); the junk block that
   turns out to be a parked copy of the driver.
3. **The turn.** The particles never collide. In the corridor phase this is a
   theorem, not an observation — the rider stack is untouched, the junk is inert.
   Rule 110's glider collisions are named here as the contrast; no panel is built
   for it.
4. **Where could a computer be?** It would need branching *and* descent. The atlas.
   The quadrant is empty — 1,500 sampled terms give branchy survivors reaching
   width 857 with maximum drop 28, while the deep-descending survivors all have
   width exactly 1.
5. **The honest ending.** So the question moved into the storms, which have none of
   the scenery — ~3.5% of term space, nothing to look at, C14 open. The pretty part
   of the calculus is the part that is closed.
6. **Status box.** Proved / probed / open, as above.

Controls: curated term menu (climber `scMt5T`, mill, swapmill, a storm, a
normalizer), a free-text term box using the notebook's surface syntax, the A↔C
encoding toggle, a fire-count slider, and the atlas seed + reseed button.

### `site/style.css`

Light and dark via `prefers-color-scheme`, both painted explicitly. Figures scroll
inside their own containers; the page body never scrolls horizontally.

## Testing

`site/sc.test.mjs`, run with `node --test`. Three groups:

1. **Engine agreement with Lean.** All four values below were verified against the
   reference implementation before being written down:
   - `scMt5T.leafCount = 12`, and the climber is forced for 400 fires
     (`scForcedMarch scMt5T 400` has length 400). Measured: forced for at least
     2,000 fires, reaching 624 leaves.
   - `scMillK` has 9 leaves; `scMillT m` has `9 + 3m`.
   - **`sc_mill_descent` re-checked from JS**: six fires take
     `((L x) (C (L x))) y` to `((x (C x)) y` exactly, for arbitrary payloads
     `x`, `y`. This is a Lean theorem verified by the page's own engine.
   - The descent generalizes: `scMillG a m` reaches `scMillG 0 m` in exactly
     `6a` fires (confirmed at `(a,m) = (1,2), (2,3), (3,1), (4,5)`).

   The `141 + 25j` over `117 + 19j` staircase is **not** used as an engine test.
   It belongs to `scNoNFPeak` / the spiral generations, not to the climber's raw
   leaf trace, whose peaks are 33, 41, 45, 55, … with a maximum drop of 121 over
   1,400 fires. Asserting it against a climber march would have been wrong.

   This is the point of a separate engine file — the page's numbers are checked
   against the proofs rather than being a parallel implementation nobody audits.
2. **Census reproduction.** At a fixed seed, the sampler's split matches Stage 241
   within tolerance (observed: 67.2% halt / 32.6% branch / 0.20% corridor against
   the recorded 67 / 33 / 0.15).
3. **The thesis assertion.** At a fixed seed, the upper-right quadrant is empty.
   If this ever fails, the essay's central claim has been falsified by its own
   figure, and the test suite says so loudly instead of the page quietly lying.

Manual check: load the page, exercise both panels, confirm both colour schemes.

## Error handling

- No canvas or no JS: the essay text stands alone; figures degrade to a note
  saying they require a browser with canvas.
- Free-text parse failure: inline message naming the position, term unchanged.
- Sampling is interruptible and never blocks the main thread for more than a frame
  budget.

## Explicitly out of scope

The three other sketched panels — skyline overlay, road vs. firework, ledger
dashboard — and a Rule 110 foil panel. They may be worth building later; they are
not in this pass. Rule 110 appears in prose only.

## Risks

- **Storm memory.** Storms grow exponentially; the leaf cap is what keeps the
  atlas bounded. Cap value needs tuning against real timings during implementation.
- **Corridor arm sparsity.** Handled by the marked constructed series, but the
  labelling has to be unmissable or the figure misleads.
- **Overclaim drift.** The prose is the risk surface. Every claim in the essay
  carries its tier, and the status box is not optional.
