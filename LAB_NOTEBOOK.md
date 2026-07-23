# Lab Notebook — the Fable-vs-Lean meta-experiment

One dated entry per work session: what was attempted, what Lean resisted,
what automation could and couldn't do. This file is a first-class deliverable
(spec: if Stage 5 never terminates, the notebook is the result).

## 2026-07-23 — Stage 0

- Module split + census slice implemented: 9 tasks, 9 commits (~1 commit per
  task), each executed by a dispatched subagent with per-task review before
  the next task was dispatched.
- Proof friction encountered:
  - `stepOnce_sound` (Task 3): the plan's candidate script
    (`first | ... | simp_all`) failed because `simp_all` made progress
    without actually closing the descent-case goals. Fix: `fun_induction
    stepOnce t`, naming the binders explicitly in the descent cases. Proved
    by an Opus-tier agent.
  - `stepOnce` completeness / `stepOnce_isSome_of_step` (Task 4, the hardest
    proof in the slice): compiled on the *first* full attempt, by a
    Fable-tier agent. The `appR` descent case needed one extra step beyond
    the plan's script: `cases hst : stepOnce t <;> simp_all`. The plan's
    3-attempt escape hatch was never triggered.
  - `normalize_sound` (Task 5): the plan's induction-on-fuel candidate failed
    because the step count `k` wasn't generalized in the induction motive.
    `fun_induction normalize` worked, mirroring the Task 3 precedent — the
    second time in this slice that `fun_induction` succeeded where a
    hand-written induction principle didn't generalize enough on its own.
  - No `sorry` ever committed; zero-warning builds held throughout; every
    `#guard` passed as planned with one exception caught in pre-flight, not
    in a subagent run: a leftmost-wins guard in the plan itself expected
    `I x → x` in one step, when `I x` (i.e. `S K K x`) actually takes two
    steps to reach `x`. Corrected in the plan before Task 1 was dispatched.
  - Task 9 (this entry, the census runs themselves) hit its own piece of
    automation friction, worth recording as a tooling lesson rather than a
    proof one: `lake exe ccp 10 1000`, redirected straight to a file, was
    killed by a 10-minute timeout with **zero** output recovered — not
    because nothing had been computed, but because C stdio fully
    block-buffers stdout when it isn't a tty, so a `SIGTERM`'d process never
    flushes anything written to a redirected file. Wrapping the call in
    `stdbuf -oL -eL` (line-buffered) fixed recovery of partial output for
    subsequent runs. Separately, fuel=1000 turned out to be genuinely
    intractable at this term size within any reasonable budget — not a
    buffering artifact, since a fuel=1000 run at the *smaller* n=9 also
    exceeded 5 minutes partway through n=8 — so the census plan's fallback
    ("reduce fuel or size, say so") was exercised for real: the definitive
    numbers below come from `ccp 12 200` (fuel held at 200, size pushed to
    12), not `ccp 10 1000` as originally scripted.
- Census headline (see CONJECTURES.md for the full table and methodology
  caveats):
  - First fuel-exhausted terms appear at n=7 (2 of 132 terms, fuel 200);
    growth of the exhausted count is fast: 41 at n=8, 276 at n=9, 1484 at
    n=10, 6842 at n=11, 29337 at n=12 (of 58786 total n=12 terms).
  - No `CYCLE FOUND` line at any size, n=1 through n=12, fuel 200 — the
    S-cycle question stays open but unrefuted at these sizes.
  - Max reduction length among terminating terms (`maxSteps`) climbs from 15
    (n=7, n=8) to 174 (n=12) — reduction sequences get much longer well
    before any term fails to terminate at all.
  - Raising fuel from 200 to 1000 at fixed n=7 makes the fuel-exhausted
    candidates' final leaf count explode from 120112 to 25740409924 — real
    evidence of explosive (not merely slow) growth along those trajectories,
    though still not a divergence proof.
- Next: Stage 1 (confluence) / Stage 2 (conservation) / Stage 3 (taxonomy)
  are all unblocked per the DAG.

## 2026-07-23 — Stage 1: Confluence

- Church–Rosser for SK reduction proved via Par + complete development
  (Takahashi triangle): `Par`, `Par.rfl`, `Par.of_step`, `Par.to_steps`,
  `dev`, `Par.K_inv`/`Par.S_inv`, `Par.triangle`, `Par.diamond`, `Pars`,
  `Pars.strip`, `Pars.diamond`, `Steps.to_pars`/`Pars.to_steps`,
  `confluence`, `nf_unique` (Confluence.lean), plus `normalize_normal`
  (Census/Eval.lean) closing out the census certificate. 6 tasks, one
  commit per task, sorry-free throughout; zero deps held.
- Proof friction, task by task (per-task subagent reports and reviewer
  notes):
  - Task 1 (NormalForm move to Step.lean + congruence lemmas): candidate
    scripts worked verbatim — a pure refactor plus straightforward
    inductions.
  - Task 2 (`Par` + the Step/Steps sandwich): candidates also worked
    verbatim; independent review confirmed the Takahashi-form `S_red`
    (with `x` duplicated into the reduced term, not left as one copy) and
    that `Par.rfl` only needs induction on atoms and `app` — no redex
    cases required for reflexivity.
  - Task 3 (`dev`, the complete development): compiled on the first
    attempt with all eight hand-derived match-arm guards passing; no
    guard corrections needed.
  - Task 4 (`Par.triangle`, the summit of the stage): proved on the first
    full attempt by a Fable-tier agent. The real friction wasn't the
    induction shape but the plan's helper-lemma sketches — `Par.K_inv`/
    `Par.S_inv` were written assuming bare `K`/`S` would resolve to the
    `Term` constructors, but inside the `Par` namespace bare `K`/`S`
    resolve to `Par`'s own constructors instead, so the lemma statements
    needed explicit `Term.K`/`Term.S` qualification. Once qualified, the
    app-case's nested redex inversions (two levels of `cases hl with`
    to peel back to the K- or S-head) closed by definitional equality —
    no extra `dev`-rewriting steps were needed beyond the `simp only
    [dev]` already in the sketch.
  - Task 5 (the ladder: `Pars`, `Pars.strip`, `Pars.diamond`,
    `Steps.to_pars`/`Pars.to_steps`, `confluence`, `nf_unique`): all
    seven candidate scripts compiled verbatim, including the one piece
    flagged as risky beforehand — `Pars.strip`'s induction generalizing
    over the one-step side (`generalizing u`) while inducting on the
    many-step side. `#print axioms confluence` came back `[propext]`
    only, independently re-verified in this task's review.
  - Task 6 (`normalize_normal`, this entry): the brief's `first | ... |
    simp_all | simp_all` sketch was replaced with named `fun_induction`
    cases before ever trying the catch-all — Stage 0 already burned that
    lesson twice, so it wasn't re-litigated here. Mirroring
    `normalize_sound`'s four named cases (`case1`..`case4`) matched
    the goals exactly on the first try: the success arm reduces directly
    to `stepOnce_none_normal`, the recursive arm is the IH applied to the
    inner equation (`ih hrec`, matching `normalize_sound`'s
    `ih hrec`/`Steps.tail` pattern exactly), and the two fuel/propagated-
    `none` arms are `simp at h`. Zero-warning build on the first full
    compile of the real (non-sorry) proof — no red/fail cycle beyond
    the initial `sorry` placeholder.
- The sandwich (Step ⊆ Par ⊆ Steps) and the census payoff
  (`normalize_normal` + `nf_unique`) landed as planned, no deviations
  from the task DAG or the stated theorem signatures. `#print axioms
  normalize_normal` reports `[propext, Quot.sound]` — the `Quot.sound`
  is not new to this stage; it's inherited from Stage 0's
  `stepOnce_isSome_of_step` (via `stepOnce_none_normal`), which already
  carried it. `confluence` and `nf_unique` themselves stay at
  `[propext]` only, unaffected.
- Next per the DAG: Stage 2 (conservation laws) and Stage 3 (taxonomy)
  both remain unblocked.
