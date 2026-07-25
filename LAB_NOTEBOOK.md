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

## 2026-07-23 — Stage 2: Conservation laws

- The S-fragment's conservation story, machine-checked in `SFragment.lean`:
  `KFree`/`kFree`/`kFree_iff` (K-freeness, executable twin, and their proven
  agreement), `KFree.of_step`/`of_steps` (closure under reduction),
  `leafCount_pos`/`leafCount_le_of_step`/`of_steps` (no erasure),
  `cycle_leafCount_eq` (a bonus constraint on C2), and `SNF`/`SNF_iff` (the
  shape of K-free normal forms). Five tasks, one commit per task, sorry-free
  throughout.
- Proof friction, task by task:
  - Task 1 (`KFree`/`kFree`/`kFree_iff`): candidate scripts worked verbatim.
    The one real snag wasn't in the proof but in the plan's own docstring —
    the reviewer caught a citation error: "Church–Kleene 1936" misattributed
    the λI-calculus's total-completeness result. Corrected to Church 1941 /
    Barendregt §9.5, and propagated across the spec, the plan, and the
    `SFragment.lean` module docstring by the controller before the next
    task was dispatched.
  - Task 2 (`KFree.of_step`/`of_steps`, closure under reduction): candidates
    also worked verbatim. The `K_red` case is the interesting one — it
    closes not by doing anything, but by genuine inversion-to-absurdity:
    a K-free term can't contain the `K` a `K_red` step requires, so
    `cases hk`/`cases hl`/`cases hK` bottoms out in a case with no
    constructor to match, discharging the goal for free.
  - Task 3 (no-erasure: `leafCount_pos`, `leafCount_le_of_step`/`of_steps`):
    one real deviation from the brief. The plan's closers for the `appL`/
    `appR` descent cases called for `Nat.add_le_add_right`/`_left` to lift
    the inductive hypothesis across the shared addend; both failed as
    written, because `simp [leafCount]` had already cancelled the shared
    addend out of the goal before the lemma could apply to it. Bare
    `exact ih` closed both cases once that was noticed.
  - Task 4 (`SNF`/`SNF_iff`, the fiddly one): first-try success on the
    strongest model available, with case-nesting never exceeding depth 2.
    `#print axioms SNF_iff` comes back with ZERO axioms — not even
    `propext` — independently re-verified by the reviewer. The instructive
    moment was in `SNF.normal`'s inversion: Lean's elimination on indexed
    families silently discards cases whose constructor's argument-count
    (pattern depth) can't match the shape at hand, so the `K_red`/`S_red`
    redex cases never even needed to be written out as absurdities inside
    the `app1`/`app2` branches — they were dismissed before the `cases s
    with` block had to consider them, leaving only the `appL`/`appR`
    structural cases to actually discharge against the IHs.
  - Task 5 (`snf` Bool twin + census guards, this entry): candidate
    scripts weren't the mechanism here — `snf` is a plain executable def,
    not a proof, and its epistemic status is deliberately weaker than
    `kFree`'s: `snf ↔ SNF` is NOT proven, by design, only cross-validated
    against the certified `stepOnce` by a `#guard` over all 42 six-leaf
    K-free terms. That agreement guard passed on the first try, with no
    adaptation needed — the tuple-lambda guard syntax from the brief
    (`fun (a, b) => ...` over `tr.zip tr.tail`) also compiled as written,
    no `⟨a, b⟩` rewrite required.
- Running two-stage theme, now visible across both stages: candidate
  scripts for structural inductions (KFree closure, leaf monotonicity,
  the SNF shapes) survive largely verbatim; in both Stage 1 and Stage 2,
  each stage's single hardest proof (`Par.triangle` in Stage 1, `SNF`'s
  characterization in Stage 2) has landed on the first attempt when run
  on the strongest model, with the real friction concentrated instead in
  smaller things: a misattributed citation, a `simp` that already did a
  lemma's job for it, an indexed-family elimination quietly pruning cases
  nobody had to write.
- Next per the DAG: Stage 3 (taxonomy) is unblocked; C1/C2/C3 (see
  CONJECTURES.md) all remain open, with C2 now carrying a proven
  size-preservation constraint on any hunted cycle.

## 2026-07-23 — Stage 3: The universality taxonomy

- The universality definitions are now formal objects: `RS.lean` (abstract
  rewriting systems, generic `Steps`/`Conv` closures, instances `RS.SK`/
  `RS.PureS`/`RS.Tag`), `Universality/Defs.lean` (`Simulation`,
  `PreservesNormalizes`/`PreservesConv`, `UniversalReach`/`UniversalNorm`/
  `UniversalConv`), `Universality/Taxonomy.lean` (the implication lattice:
  `RS.SK_churchRosser`, `Simulation.conv_preserve`/`conv_reflect`/
  `preservesConv`/`normalizes_preserve`, `Simulation.toUniversalConv` — renamed from `UniversalReach.toUniversalConv` by the final-review fix, see addendum).
  Six tasks, sorry-free throughout; several tasks carried additional
  review-fix commits (comment precision, the .rec why-comment).
- Proof friction, task by task:
  - Task 1 (warm-ups: `snf_iff_SNF`, `SNF.spineLength_le`): both candidates
    compiled verbatim on the first try. The catch-all case everyone was
    braced for — `fun_induction snf`'s `case4` (the shapes `SNF` can't
    inhabit) — was the feared fight-site carried over from Stage 0/1; it
    never materialized as an explosion. `fun_induction` produced exactly
    four clean cases, mirroring `snf`'s four match arms, and the planned
    closer dispatched `case4` in one shot. `#print axioms snf_iff_SNF`
    reports `[propext, Quot.sound]` (inherited, same trail as
    `stepOnce_isSome_of_step`); `SNF.spineLength_le` reports `[propext]`
    only. Separately, review caught a stale comment in `Enumerate.lean`
    still describing `snf ↔ SNF` as unproven; fixed. The controller then
    went a step further and tightened the wording to state the snf/
    stepOnce agreement as the corollary chain it actually is — it needs
    `snf_iff_SNF` plus `SNF_iff` plus `stepOnce`'s own soundness/
    completeness certificates, and only holds for K-free terms.
  - Task 2 (`RS` interface): the plan's own prose miscounted its own code
    block — it said "six lemmas," the stubbed block (and the candidates)
    contained seven (`Steps.single`/`trans`, `Conv.of_steps`/`trans`/
    `snoc_fwd`/`snoc_bwd`/`symm`). The implementer followed the literal
    code, which is authoritative, and flagged the miscount rather than
    silently absorbing it. The toy `countdown` sanity examples needed
    `@[reducible]` on the local `RS` def plus explicit type ascriptions
    (`RS.Steps.refl (0 : countdown.Carrier)`) before numeral elaboration
    would resolve through a concrete instance — an artifact of the toy
    example, not of the `RS` interface itself.
  - Task 3 (instances `RS.SK`/`RS.PureS`/`RS.Tag`): the real Lean friction
    of this stage. `induction` on `RS.Steps` FAILS at a concrete carrier
    (`RS.SK.Steps`, `RS.PureS.Steps`) with an `mkElimApp` "expected first
    3 arguments of motive" error — the same tactic works fine when the
    `RS` is a bound variable (as in `RS.Steps.trans`), so the motive
    generator only chokes on a concrete literal. `unfold`,
    `induction … using RS.Steps.rec`, and `induction … with` all hit the
    identical error. Workaround: drive the recursor by hand
    (`h.rec (fun a => _root_.Steps.refl a) (fun s _ ih => ...)`), commented
    at both call sites as a regression trap for future readers who reach
    for `induction` there. The reviewer hand-verified both motives
    independently. The subtype `refl` case in `PureS_steps_iff` — flagged
    beforehand as a likely second fight-site needing `Subtype.ext` — closed
    for free instead: `⟨t, ht⟩` and `⟨t, hu⟩` are definitionally equal
    because `KFree` is a `Prop` (definitional proof irrelevance), exactly
    as the plan had predicted as the optimistic case.
  - Task 4 (`Universality/Defs.lean`): byte-exact against the brief, first
    try, zero deviations. Reviewer's mathematical audit (not just a diff
    check): `bwd`'s image-restricted quantification (reachability between
    encoded states, not encoded-to-arbitrary) is the right strength for
    blocking the answer-smuggling form of the 2007 dispute; the
    reflexive-`fwd` slack is confined to self-loops and doesn't leak into
    anything provable; even a degenerate one-state source still forces an
    antichain-shaped demand on the host under `dec_enc`. Conclusion: the
    definitions are not accidentally vacuous.
  - Task 5 (`Universality/Taxonomy.lean`, the lattice): all 8 candidates
    compiled verbatim (the brief's prose miscounted again — "seven" vs. 8
    theorem statements in its own code block, same pattern as Task 2;
    followed the code). Axiom audit: `RS.SK_churchRosser` carries
    `[propext]` (inherited from Stage 1's `confluence`); the generic
    lattice results audited directly — `Simulation.preservesConv` and
    `UniversalReach.toUniversalConv` (since renamed `Simulation.toUniversalConv`, see addendum) — depend on ZERO axioms.
  - Task 6 (this entry): the definitions ledger in CONJECTURES.md and this
    notebook entry. All cited theorem/instance names re-verified by grep
    against the actual tree before writing, per the brief's instruction.
- Running theme, three stages into this taxonomy work now: plan candidate
  scripts survive close to verbatim at the variable-abstraction level
  (`{A : RS}`-scoped lemmas, generic inductions); concrete-instance
  elaboration is consistently where Lean pushes back — numeral
  elaboration through a reducible local def (Task 2), the `mkElimApp`
  motive bug on `induction` at a literal `RS` (Task 3). Both stages'
  hardest-looking proof sites (the `snf` catch-all, the subtype `refl`)
  turned out easier than feared; the actual fights were elsewhere.
- Design decision, registered rather than formalized: computability of
  `enc`/`dec` in `Simulation` is NOT internally pinned. Every Lean `def`
  is computable by construction, but that is a metatheoretic fact about
  the ambient language, not a hypothesis these definitions can state or
  test from inside a zero-dependency development. A full internal answer
  to that half of the 2007 dispute would need a computability theory in
  the repo; short of that, the honest move is to say so in the docstring
  and the ledger rather than either silently assuming it or omitting the
  gap.
- Next per the DAG: Stage 4 (closing `UniversalReach`/`UniversalNorm`/
  `UniversalConv` cells for `RS.SK` against `RS.Tag`, per the ledger) is
  unblocked. C1/C2/C3 remain open.

### Addendum, 2026-07-23 — whole-branch review caught two Critical definitional flaws

- A final review of the whole branch (as opposed to the per-task reviews
  above) found two Critical problems that every per-task review had
  passed:
  1. `UniversalNorm`/`UniversalConv` quantified over a BARE encoding
     function, and that makes them classically trivial: a classical
     oracle encoder — decide the source term's fate, ship a canned
     answer — witnesses the bare property for ANY source system, which
     the reviewer machine-checked. Fixed by making all three Universal*
     definitions quantify over `Simulation` (step-faithful, decodable);
     the trivialization itself is now IN the tree as a negative control
     (`bareEncNorm_trivial`, Universality/Defs.lean), so the definitions
     can't be quietly re-loosened without someone noticing what the
     pinning buys. (The lattice edge was also restated at the witness
     level — `Simulation.toUniversalConv` replaces the ∀-image-closure
     `UniversalReach.toUniversalConv` — so Stage 4 can use it with one
     good simulation in hand.)
  2. `TagSystem` fixed the alphabet to `Bool` and varied only the
     deletion number m, while citing Cocke–Minsky 1964 — which is about
     deletion-number-2 tag systems over ARBITRARY finite alphabets, a
     class the `Bool`-fixed structure does not cover. Fixed by
     generalizing the alphabet to a `Sym : Type` field; the sanity
     examples instantiate `Sym := Bool`.
- Why per-task review couldn't see these: each task matched its brief
  exactly — the flaws lived in the plan's definitions themselves, and
  only a review holding the whole branch up against the external
  literature and against adversarial witness constructions had the
  altitude to catch them.

## 2026-07-23 — Stage 4: Calibration (completeness proven, iota refuted)

- The headline, worth stating plainly because it's the point of the whole
  census-first method: pre-planning analysis PREDICTED the iota
  refutation before a single line of proof code existed — the size
  argument (every first-order ι-step grows leaf count by +8, while SK has
  a genuine reduction cycle) was written into the plan up front. The plan
  then built a STOP gate around it: Task 4's `#guard` probes had to
  confirm the growth numbers empirically, cheaply, before any proof
  effort was spent. The probes passed. The proofs then landed on the
  FIRST full attempt — the third stage overall (after Stage 1's
  `Par.triangle`, Stage 2's `SNF` characterization) where this project's
  summit proof compiled first-try on the strongest model available.
- Task 1 (simulation algebra: `Simulation.id`, `Simulation.comp`,
  `UniversalReach.of_sim`): candidate scripts worked verbatim.
- Task 2 (`TermV`, `Bracket.lean`'s term layer): byte-exact transcription
  from the brief. Reviewer verified the four closure lemmas
  (`StepsV.trans`/`congL`/`congR`/`congApp`) are honest mirrors of
  `Step.lean`'s `Steps.trans`/`congL`/`congR`/`congApp` — same shape,
  same proof pattern, ported to the variable-carrying syntax.
- Task 3 (`combinatory_completeness`, `bracket_beta`): the REAL fight of
  the stage. `occurs_bracket`'s `var` case needed Nat-`beq` bookkeeping
  that a naive `simp` couldn't close cleanly — early attempts either left
  goals open or triggered the `unusedSimpArgs` linter flip-flopping under
  `<;>` (an arg needed in one branch of the case split was flagged unused
  in the other). Closed with `grind` — the first `grind` use in this
  project — which pulls `[Classical.choice, Quot.sound]` into
  `combinatory_completeness`'s axiom trail (confirmed by `#print axioms`:
  `[propext, Classical.choice, Quot.sound]`). The reviewer probed three
  alternative closers looking for a choice-free route; none was cheap —
  a manual `[propext]`-only proof of the same lemma is possible but is
  deliberate additional work, logged here for future triage rather than
  done under this stage's budget. `bracket_beta` itself, the theorem the
  stage actually needed, stays at `[propext]` only — the `grind` cost is
  fully contained in `occurs_bracket`, a supporting lemma.
- Task 4 (`Iota.lean`, the census-style probes): byte-exact against the
  brief. One empirical surprise: `fun_induction` on `stepOnce` for
  `IotaTerm` produced case arities that didn't match `Eval.lean`'s
  `Term`-level precedent — `IotaTerm` has one redex pattern
  (`app .iota x`) where `Term` has two (`K_red`/`S_red`), so
  `fun_induction`'s case count came out different from what the Stage-0
  memory of "that tactic gives four cases" predicted. Discovered
  empirically rather than by re-deriving it on paper first; corrected
  once the actual case list was in front of us.
- Task 5 (`Universality/Calibration.lean`, the refutation): both risk
  sites flagged ahead of time turned out quiet. `iota_steps_le`'s `.rec`
  call needed no explicit motive beyond what the brief's sketch already
  supplied — the concrete-instance `induction`-fails-on-`RS.Steps` bug
  from Stage 3 was worked around the same way (hand-driven `.rec`), and
  the motive Lean needed matched the plan's hand-derived one on the first
  try. The `Wdup`/`omegaSK`/`Mcycle` reduction-cycle chains
  (`omega_to_M`, `M_to_omega`) elaborated exactly as written, each step
  firing on the definitional unfolding the plan predicted (`I = S K K`
  behind the scenes). `omega_ne_M` closed by plain `decide` on the
  derived `DecidableEq` — no `native_decide` needed or used.
- Axiom audit (`#print axioms`, re-run directly against the built tree
  for this entry): `bracket_beta` → `[propext]`;
  `combinatory_completeness` → `[propext, Classical.choice, Quot.sound]`
  (the `grind` cost, see Task 3 above); `no_sim_SK_iota` /
  `iota_not_universal_for_SK` / `iota_step_lt` / `iota_steps_le` → all
  `[propext, Quot.sound]` (the `Quot.sound` here is the same inherited
  trail riding `RS.Steps`/`RS.SK_steps_iff` since Stage 3, not new).
- Meta-observation for the notebook: this is the first stage where the
  PLAN itself did original mathematics — the iota refutation wasn't a
  known result being formalized, it was discovered during pre-planning
  analysis of the leaf-count arithmetic — rather than a formalization
  exercise over an already-known theorem. The census-first gate (probe
  the growth numbers cheaply before committing proof effort) is exactly
  what made that safe: if the `#guard` probes in Task 4 had disagreed
  with the pre-planning arithmetic, the stage would have stopped there
  instead of chasing a false refutation through two proof-heavy tasks.
- How this differs from the Stage 3 atlas's own expectation: the
  Definitions ledger going into this stage listed `RS.SK` vs. the
  tag-system reference as the Stage 4 target, with iota mentioned only as
  a secondary calibration point ("under the taxonomy"). What actually
  shipped is the reverse emphasis — Tag→SK reach stays open (Stage
  5-adjacent), while iota went from "a basis to eventually calibrate
  against" to "the stage's proven negative result," entirely because the
  size argument, once looked at directly, forced the conclusion before
  any Tag-system work was even started.
- Next: `lake build` clean, zero warnings; ledger and this entry committed
  together per the task brief. Two items explicitly registered rather
  than closed this stage (see CONJECTURES.md's deviation register):
  Waldmann 2000's normalization-decidability result remains
  cited-not-formalized, and the λI ({S,B,C,I}) stretch goal was not
  attempted.
- Final review, two notes carried forward for Stage 5: (a) the
  `no_sim_SK_iota` refutation never uses `Simulation.bwd` (the
  host-steps-imply-source-steps direction) — it goes through on `enc`,
  `fwd` (via `fwd_steps`), and `dec`/`dec_enc` (via `enc_injective`)
  alone, so it survives any future weakening or removal of `bwd` from
  the `Simulation` class for free; this could be stated as an explicit
  lemma later, but isn't needed now. (b) the
  suggested first nontrivial `Simulation` inhabitant for Stage 5 is the
  PureS→SK inclusion (`enc := Subtype.val`, `bwd` via the `KFree`
  closure) — cheap to build, and landing it would blunt any
  "`Simulation` is near-vacuous" objection before harder positive work
  (e.g. Tag→SK) is attempted.

## 2026-07-24 — Stage 5, Slice 1: bounded reachability

- Where this slice came from: an ideonomy shake over the program's open
  questions surfaced a latent asset that had been sitting in the tree
  since Stage 2 — `leafCount_le_of_steps` (no K-free step ever shrinks a
  term) doesn't just explain why erasure-based encodings fail, it also
  confines any path from `t` to `u` inside the FINITE universe of terms
  with at most `leafCount u` leaves. That is a bounded-search argument
  for reachability decidability, for free, off a lemma proved for an
  unrelated reason two stages ago. The slice plan was built around
  formalizing that observation and searching honestly for where it runs
  out (the abstract `Decidable` instance; C2's theorem-level form).
- Task 1 (`succs` + the CENSUS-FIRST STOP gate): all four probes (A ×2,
  B, C) passed on the first build, confirming the bounded-path premise
  empirically before any proof effort was spent — the gate did its job
  by finding nothing wrong, which is itself useful information. The one
  real slip was in the plan's own prose: Probe C's comment described a
  stronger one-step-closure claim than what its actual guard checked;
  the controller caught and reworded it to match before Task 1 was
  dispatched, rather than letting a probe's comment silently overstate
  what it verifies.
- Task 2 (`succs_sound`/`succs_complete`): `fun_induction` — the tactic
  that had repeatedly bailed out proof friction in Stages 0-3 — turned
  out to be unavailable here because `rootRed` isn't a recursive
  function (it's a single non-recursive match), so plain `unfold` +
  `split` did the job instead. The more interesting friction was a
  reviewer catch, not an implementer one: the reviewer traced Lean core
  source to confirm `++`'s left-associativity (and the resulting
  `List.mem_append` nesting), which corrected an assumption baked into
  the controller's own prompt for this task rather than into the
  candidate proof script.
- Task 3 (`closureStep`/`boundedClosure` + membership lemmas): Lean core
  4.28 has no `mem_eraseDups`, so a small helper
  (`mem_of_mem_eraseDups`, length-recursive) had to be written from
  scratch. More consequentially: the plan's own fuel-0 guard instance
  would have FAILED as written — the closure it names saturates
  instantly at that bound, so the guard's expected verdict was wrong —
  and the implementer's replacement instance was independently
  hand-verified as necessary by the reviewer before being accepted.
- Task 4 (`mem_of_saturated`/`reachable?_correct`, the slice's summit):
  compiled on the first full attempt by a Fable-tier agent. The one
  adjustment needed was procedural, not mathematical: Lean 4's
  `induction h` on the `Steps` hypothesis auto-reverts `KFree t` into the
  motive (it depends on the moving left endpoint) and reintroduces it as
  an inaccessible hypothesis per case, so the `tail` case needed
  `rename_i hk` to reclaim it before continuing — no `generalizing`
  clause was needed, contrary to what the brief's caution suggested might
  be required.
- Task 5 (`onCycle?` + the ≤6-leaves cycle-freedom guard): this slice's
  best epistemics moment, and it was the IMPLEMENTER, not a downstream
  reviewer, who caught it. The plan's draft prose called the guard's
  result "kernel-checked"; the implementer read Lean 4.28's own doc
  comment for `#guard` (`Init/Guard.lean` — "this uses the untrusted
  evaluator, so `#guard` passing is *not* a proof") and flagged the
  mismatch before it shipped. Fixed: the guard's comment now says
  "evaluator-checked... NOT a kernel proof," and two genuine kernel-level
  theorems were added alongside it for concrete 4- and 5-leaf instances
  (`S S S S`, `S S S S S`), each via `succs_complete` + `by rfl` +
  `reachable?_correct`, so the file carries both an honest
  evaluator-level sweep and real per-instance kernel proofs, clearly
  distinguished. The stretch theorem (`no_small_cycle`, the general form
  over `⟶⁺`) was attempted 3 times and escape-hatched exactly where the
  brief had predicted it might be: it needs an `sTerms`-completeness
  theorem that doesn't exist, and attempting it further exposed a deeper
  reason why not — `sTermsTable`'s `Id.run do`/`Array`/range-loop
  definition isn't `rfl`/`decide`/`simp`-transparent even at the smallest
  instance (`sTerms 1 = [S]` doesn't close by plain `rfl`). Registered in
  CONJECTURES.md as a blocked chain, not silently dropped.
- Task 6 (the convertibility trichotomy: `Joinable`, `conv_iff_joinable`,
  `joinable_normalizes`, `joinable_iff_nf_eq`): all three theorems land at
  axiom footprint `[propext]` only. The one bookkeeping note: `nf_unique`'s
  actual orientation (`u = v` from `t ⟶* u`, `t ⟶* v`, both normal) gave
  `joinable_iff_nf_eq`'s forward direction directly — `nt = nu` in exactly
  the goal's orientation — where the brief's rough candidate had reached
  for a `.symm ▸ rfl` that turned out unnecessary. Simpler than sketched,
  not harder.
- Task 7 (`pureS_in_SK`, the `Simulation` class's first nontrivial
  inhabitant): compiled close to verbatim, `[propext]` only. Review
  caught a real gap, not a cosmetic one: the def's doc comment claimed
  the inclusion was "nontrivial" but nothing in the tree exhibited an
  actual `PureS` step — the claim was asserted, not evidenced. Fixed by
  adding a concrete machine-checked witness
  (`RS.PureS.step ⟨S S S S, ...⟩ ⟨(S S)(S S), ...⟩ := Step.S_red S S S`)
  and by replacing a vacuous "composes with itself" example with a
  genuine composition through `Simulation.id`.
- Axiom audits across the slice, `#print axioms` re-run against the built
  tree: `mem_of_saturated`/`reachable?_correct` → `[propext, Quot.sound]`
  (the `Quot.sound` is inherited, not new); `conv_iff_joinable`/
  `joinable_normalizes`/`joinable_iff_nf_eq` → `[propext]`; `pureS_in_SK`
  → `[propext]`. No `sorry`, no `native_decide`, no `Classical.choice`
  anywhere in the slice.
- Meta: this is the third time in the program that a review-or-shake
  process — not the prover — did real research work. First was Stage 3's
  whole-branch review catching the `UniversalNorm`/`UniversalConv`
  trivialization and the `TagSystem` alphabet flaw, both invisible to
  every per-task review that had already passed. Second was this slice's
  own premise: the ideonomy shake surfacing the bounded-path argument
  latent in Stage 2's monotonicity lemma before any Reachability code
  existed. Third is inside this same slice — an episode of three distinct
  within-slice catches, counted here as one event: Task 3's fuel-0 guard
  was caught as wrong and replaced under reviewer hand-verification,
  Task 5's implementer caught the plan's own "kernel-checked" overclaim
  against Lean's own `#guard` documentation, and Task 7's review caught
  an asserted-not-evidenced nontriviality claim. (The census-first STOP
  gate, by contrast, CONFIRMED the premise rather than catching an error
  — it did its job by finding nothing wrong, and belongs in a different
  column of the ledger than the catches.) None of these were prover failures — every candidate proof
  script that reached the kernel, reached it cleanly — the friction was
  entirely in catching what the plan's prose claimed versus what the
  code and the trusted kernel actually established. The process keeps
  finding the gaps between what's true and what's merely asserted; that
  is the slice's real product, alongside the theorems.

## 2026-07-24 — Stage 5, Slice 2: the isometric fragment (C2 resolved)

- Where this slice came from: an ideonomy pass over the program's open
  questions, this time explicitly cross-domain — the general technique of
  proving term-rewriting termination via a polynomial (weighted)
  interpretation was brought to bear on C2's cycle question, rather than
  growing out of a lemma already sitting in the tree (Slice 1's origin
  story). The head-weight measure τ was derived on paper first: each
  leaf's weight doubles per left-edge on its root path, so an S-redex
  firing at the head burns weight even when leaf count is flat. The
  arithmetic (τ(S S S S) = 15, τ((S S)(S S)) = 9, a drop of exactly 6) was
  hand-checked twice independently before Task 1 was dispatched, and the
  whole slice was built behind a STOP gate: no proof effort until cheap
  `#guard` probes confirmed the arithmetic empirically.
- Task 1 (`tau` + the STOP-gate probes): both probes passed on the first
  build. Probe A (τ strictly drops on every size-preserving successor
  over all ≤6-leaf pure-S terms) held unweakened. Probe B (the root
  isometric redex drops τ by exactly 6) was checked for non-vacuousness
  with a scratch probe outside the tracked tree: exactly one size-4
  pure-S term matches the root-redex pattern, and it is `S S S S` — the
  classic case the file's header comment names — so Probe B genuinely
  exercised the claimed arithmetic rather than passing on an empty case.
- Task 2 (`tau_pos`, `KFree.leafCount_eq_one`, `tau_lt_of_isometric_step`):
  the brief's named-binder `cases` syntax for the K-freeness lemma
  (`| app (t := l) (u := r) hl hr`) is not valid Lean 4 `cases` syntax;
  fixed by matching `| app hl hr` and naming the subterms afterward with
  `rename_i l r`. The real catch was the reviewer's, not the
  implementer's: a scratch `#print axioms` run showed
  `tau_lt_of_isometric_step` pulling in `Classical.choice`, traced by
  bisecting the proof's `simp` call sites down to the `appL`/`appR`
  congruence cases — the default `simp` set (not the hand-written
  arithmetic) was the source. Swapping `simp [leafCount]`/`simp [tau]`
  for `simp only [leafCount]`/`simp only [tau]` at those four call sites
  eliminated the choice dependency; re-audited at `[propext, Quot.sound]`
  only. Fixed within the same task, before the commit landed.
- Task 3 (`tau_lt_of_steps_size_eq`, `no_pure_S_cycle` — C2 itself): the
  first full attempt at this theorem. The new proofs use no `simp` at
  all (`omega`, `rcases`, `rw`, term-mode), so no choice-leak risk arose
  here in the first place. The brief's equality-orientation warning
  proved accurate: in `no_pure_S_cycle`'s case split the size-preserving
  disjunct arrives as `v = t` (the return leg's endpoint equated to the
  starting term), exactly the orientation the brief flagged as the one
  to watch rather than its mirror `t = v` — `rw [heq] at hdrop` and
  `Nat.lt_irrefl` closed it as anticipated.
- Task 4 (`Steps.head_of_ne`, `no_sim_SK_pureS`, and the three
  `pureS_not_universal*_for_SK` corollaries — the prize-adjacent
  refutation): also a first full attempt. The only adaptation needed was
  a binder rename: the brief's `fun ⟨S, _⟩ => ...` destructuring pattern
  for the Norm/Conv corollaries collided with `Term.S` under the file's
  `open Term`, so the elaborator resolved the bound name to the
  constructor instead of a fresh `Simulation` variable. Renamed the
  binder to `Sim`; the statements themselves needed no change.
- Milestone: **this is the program's first conjecture RESOLUTION** — C2
  moves from open to PROVED, and the theorem (`no_pure_S_cycle`) is
  strictly stronger than the census conjecture that produced it on both
  the strategy and size axes. It is also the second time the SK Ω ↔ M
  reduction cycle has served as the refuting witness in this taxonomy:
  Stage 4 used it against iota (strict growth means no injective
  encoding can carry a cycle into a strictly-growing system), and this
  slice reuses the exact same cycle against pure S (acyclicity means no
  injective encoding can carry a cycle into a cycle-free system). One
  mechanism — a cyclic source cannot be hosted by a system whose
  reduction order admits no return trips — with two independent causes
  now machine-checked to trigger it.
- Note for the future: C1 (the smallest non-normalizing pure-S term)
  remains the natural next research target, and it needs the other
  polarity of this slice's toolbox — NON-termination tools, not
  termination ones (a divergence proof, not a decrease measure). That
  sits alongside the two items already queued from Slice 1: the
  finite-pigeonhole saturation argument for the abstract `Decidable (t
  ⟶* u)` instance, and the `sTerms`-completeness chain blocking
  `no_small_cycle`'s general kernel form.

## 2026-07-24 — Stage 5, Slice 3: the invariant observatory (reconnaissance)

- Where this slice came from: two ideonomy passes, not one. The first —
  a notation lens run over C1's candidate strings — asked what a change
  of representation could surface that the census's rendered output
  couldn't; it produced the loop-route framing (self-embedding as the
  standard rewriting-theory non-termination witness) and named the slots
  a real divergence proof would need (a self-embedding witness, plus the
  conservation theorem to upgrade it to non-termination). The second — a
  timeline-crossing pass over the taxonomy's own history — noticed that
  Stage 4's iota refutation and Slice 2's pure-S refutation, written
  months apart against different mechanisms, were secretly the same
  argument wearing two causes (strict growth, τ-termination); that
  crossing produced this slice's one consolidation theorem. Both passes
  are exploratory by construction, so the slice was scoped up front as
  reconnaissance — maps, not resolutions — and every task brief carried
  an explicit both-outcome template so no probe could pass silently
  without the artifact saying what it actually found.
- Task 1 (`isSubterm`, the four-direction embedding hunt): three of the
  four directions returned honest negatives at fuel 120 (no self-embedding
  for either candidate, c2 nowhere in c1's trace). The
  fourth returned something nobody had predicted: `stepOnce c2 = some
  c1`, confirmed by kernel-checked `rfl` and hand-traced independently by
  review before the guard was trusted. The two "independent" C1
  candidates from the original census turn out to be one leftmost-outermost
  step apart on a single trajectory — C1 effectively collapses to one
  candidate. Prior entries record several review-shaped catches of
  overclaims and one ideation-shake discovery; this is the first time an
  EMPIRICAL EXPLORATION PROBE discovered a fact nobody had hypothesized —
  while the thing it hunted (a loop) simply wasn't there. No ordinal
  claimed; the ledger's earlier events are enumerable by the reader.
- Task 2 (plateau-nesting probe, C6): the probe tested the census's own
  n≥10 "+1 plateau" reading against n=7..9 data and returned a clean
  honest negative — no subterm nesting, no rider-append match in either
  direction, and leaf-count deltas that explode (×3, then ×7) rather than
  staying small. A controller-authored hypothesis died under direct
  census contact (no ordinal claimed — the ledger has no verifiable
  earlier instance of this exact failure mode; the Stage 4 iota flip
  was killed by pre-planning analysis, not census data) — the
  plateau-nesting reading was a real, reasonable extrapolation from six
  data points, and testing it against three more killed it cleanly rather
  than confirming it. The one surviving positive fact, `m7 == c1` exactly,
  did not propagate to n=8 or n=9. C6 (divergence density) was registered
  as a separate, still-open finding from the same task: 1.5% at n=7 rising
  monotonically to 49.9% at n=12 — six points, consistent with the
  monotone-to-1 conjecture but nowhere near enough to distinguish
  "accelerating" from "leveling off" from "regime change at the plateau
  threshold."
- Task 3 (`Simulation.refute_of_acyclic`): the opposite experience from
  Tasks 1-2 — no exploration needed, the candidates worked essentially
  as given. The generic theorem is AXIOM-FREE (`#print axioms` against
  the built tree), which is worth stating plainly: the mechanism itself
  (an injective step-faithful simulation can't carry a cycle into an
  acyclic host) is pure logic over the `Simulation`/`RS.Acyclic`
  definitions, with no dependency on `no_pure_S_cycle`'s or
  `iota_step_lt`'s machinery until the two concrete instances
  (`RS.PureS_acyclic`, `RS.Iota_acyclic`) invoke them — and those two
  instances carry exactly the `[propext, Quot.sound]` trail their
  underlying theorems already carried, nothing new. Both existing
  refutations (`no_sim_SK_iota`, `no_sim_SK_pureS`) recover as one-line
  `example`s through the generic mechanism; the originals are untouched
  — this consolidates, it does not deprecate.
- Task 4 (this entry; C5, the unbounded-trajectory corollary, the C1
  strategy note, the Slice 3 section): registered C5 (WN ⇒ SN
  conservation for pure S — external, erasure-free calculi territory,
  not formalized here) and its corollary (unbounded trajectory size),
  both explicitly blocked/dependent rather than claimed. Closed the
  numbering gap between C4 and C6 that Task 2's reviewer had flagged.
  The C1 strategy note now states, precisely: the loop route has no
  cheap witness in the fuel-120 explored prefix (three honest negatives),
  and the invariant route (a decidable reduction-preserved predicate,
  none known yet) is the other live option — with C5 as the piece that
  would turn a future loop witness into an actual divergence proof rather
  than just one infinite trajectory.
- Expectation-setting, checked against what actually happened: the slice
  was billed up front as maps, not resolutions, and it held — C1 remains
  open (a discovery about adjacency, not a resolution: one-step relation
  is not a loop, and a loop would not by itself be divergence), C3 remains
  open (an honest negative on one reading of the plateau, not a refutation
  of C3 itself, which was never that specific claim), C6 opened and stays
  open. The one THEOREM to land, `Simulation.refute_of_acyclic`, is a
  consolidation of two already-proved refutations, not a new resolution
  of anything previously open. Nothing here was stretched past its
  epistemic level: kernel-pinned facts (`stepOnce c2 = some c1`, the two
  acyclic instances, the axiom-free generic theorem) are stated as such;
  fuel-bounded census data (the embedding hunt's three negatives, the
  plateau-nesting probe, C6's table) is labeled fuel-bounded throughout;
  C5 and the corollary are registered-open, not claimed.
- Axiom audits, `#print axioms` against the built tree (all scratch,
  since removed): `Simulation.refute_of_acyclic` → no axioms;
  `RS.PureS_acyclic` → `[propext, Quot.sound]`; `RS.Iota_acyclic` →
  `[propext, Quot.sound]` (both inherited from `no_pure_S_cycle`/
  `iota_step_lt`+`iota_steps_le`, nothing new this slice).
- Next-target ranking, as it now stands: (1) the C1 invariant route — a
  decidable leftmost-outermost-preserved predicate mined from trajectory
  data, since the loop route just came up empty within fuel 120 and needs
  C5 anyway even if it succeeds later; (2) C5 formalization itself (the
  λI conservation theorem) — external routes exist, genuinely
  cross-cutting value since it also unblocks the unbounded-trajectory
  corollary; (3) the diverging-pairs core — convertibility between two
  non-normalizing S-terms, the open frontier `Joinable` narrowed to back
  in Slice 1; (4) the pigeonhole queue — `sTerms`-completeness, still
  blocking `no_small_cycle`'s general kernel form and the abstract
  `Decidable (t ⟶* u)` instance, unchanged priority since Slice 1.

## 2026-07-24 — Stage 5, Slice 4: audit, widen, repair (nothing resolved)

- Where this slice came from: an ideonomy pass aimed at the PROGRAM rather
  than at the mathematics. The tuple was negation + combination over a
  chart, with animacy/size/materiality as the dimension prompts, and the
  three prompts turned out to read the project unusually well. Animacy
  named the epistemic register as a life-ladder (settled theorems vs.
  quasi-alive build-time guards vs. alive census observations vs. external
  citations) and made visible that the entire SETTLED block is negative or
  structural — one acyclicity theorem and four things resting on it, with
  nothing positive about pure S settled at all. Size showed every alive row
  resting on a sample of one to six (C3.1 is literally a sample of one
  after Slice 3 collapsed the two candidates). Materiality was the
  uncomfortable one: "runtime-prohibitive" appears as the reason for
  not-knowing in three separate places, so wall-clock — down to a
  block-buffering accident that ate a whole 10-minute run in Slice 0-era
  tooling — has decided more of this project's open/closed boundary than
  any mathematical obstruction has.
- The operative finding was a negation over the census's definitional
  properties: **every conjecture that became a theorem did so by escaping
  one of them, and everything still open is still trapped inside at least
  one.** C2 escaped leftmost-outermost AND bounded size; τ escaped
  fuel-boundedness; `refute_of_acyclic` escaped per-system-ness. C1 is
  trapped inside three at once (one strategy, one fuel, one trajectory).
  That gave a ranked worklist directly, and it matched Slice 3's own
  next-target ranking on item (1), so the two agreed independently.
- Task 1 (the under-claim). Reading `Simulation.refute_of_acyclic` against
  its own proof showed it consumes only `enc_injective` and `fwd_steps` —
  `bwd` is untouched, and `fwd` was ALREADY many-step (`A.step a a' →
  B.Steps (enc a) (enc a')`), so "step-faithful" had never been the right
  word for the hypothesis in the first place. Verified by grep before
  believing it: the only consumers of `Simulation.bwd` anywhere in the tree
  are `conv_reflect` and `comp`. Extracted `PathEncoding`, restated the
  mechanism there, kept `Simulation.refute_of_acyclic` as a
  name-and-statement-preserving corollary so no citation broke.
- The part that mattered methodologically: a widening like this is worth
  nothing if the wider class is secretly the same class, and asserting
  otherwise would have been exactly the sort of overclaim this notebook
  keeps catching. So the widening carries a proof obligation —
  `pathEncoding_strictly_weaker` exhibits a step-free two-point system
  mapped onto SK's Ω/M cycle whose encoder extends to no `Simulation`,
  because `bwd` would reflect a real host path into a source that has
  none. `Simulation.toPathEncoding` is therefore not surjective. Written
  as a theorem, not a remark.
- Task 2 (C1, non-size measures). Term.lean's measures section says in so
  many words that "leaf count is the only size measure we need" — true of
  size, and precisely why every C1 attempt had been a size argument. Four
  other measures along the trajectory produced one regularity strong
  enough to prove outright: from step 8 the head FREEZES to `S A ·` for a
  fixed 9-leaf normal form, and `S A B` with A normal provably admits only
  steps inside B, under every strategy. `frozen_normalizes_iff` relocates
  C1 exactly onto the payload. All six theorems axiom-free.
- Two negatives from that task earned their place. `isoRedexCount` is 0
  from step 6 on, so τ — the machinery that RESOLVED C2 — governs nothing
  on the C1 trajectory; that answers "why not just reuse τ?" by
  measurement instead of by hand-waving. And the recurrence hunt was re-run
  at the frozen granularity, where Slice 3's could not have succeeded:
  Slice 3 looked for `c1` (spine 5) recurring, but after step 8 every
  reduct has spine 2, so `c1` cannot reappear at all. Twenty fresh starting
  points, twenty negatives.
- Honest register on Task 2: the relocated payload has 15 leaves against
  `c1`'s 7. The target got BIGGER. Recorded in the theorem's own doc
  comment, in CONJECTURES.md, and in the commit message, because a reader
  skimming "C1 relocated onto a payload" could easily take it for progress
  toward a divergence proof, and it is not one.
- Task 3 (C6 fuel test) is where materiality bit again, in exactly the way
  the review predicted. `lake exe ccp 10 800` — this time line-buffered
  through `stdbuf -oL`, so the old buffering trap could not repeat, and it
  didn't — reached n=8 in ~9 minutes and stalled on n=9. Diagnosis: at fuel
  800 the extremal trajectories reach ~2.3e9 and ~2.7e9 LOGICAL leaves.
  Terms are shared DAGs in memory so they fit comfortably; `classify`
  computing `leafCount` over them is what costs. The fix was to stop
  measuring the thing C6 never needed — `exhaustedCount` uses only
  `(normalize fuel t).isNone` — after which n=10 at both fuel values
  finished quickly. Result: exhausted counts identical at fuel 200 and 800
  for n = 7..10 (2, 41, 276, 1484), so C6's table survives a 4× fuel test
  with not one of 6,853 terms changing verdict. Bonus: the n=9 and n=10
  rows had been cited from this notebook without recomputation since Slice
  3, and both reproduced exactly — that caveat is discharged.
- Task 4 (the ledger). The review noticed the status vocabulary had no
  demotion state: C3.2's own Slice 3 probe had come back against it, yet it
  sat at plain "open", indistinguishable from C5 which has never been
  tested at all. Added `probed` and `weakened`, with an explicit note that
  neither carries proof content — they track the state of the evidence, not
  of the logic. C3 is now weakened on both halves (C3.1 picked up a second
  dent this slice: spine-length 5 is a property of the STARTING term only
  and does not survive its own trajectory). C1 and C6 are probed.
- Score for the slice: two strengthenings, one structural reduction, one
  ledger repair, four honest negatives, zero conjectures resolved. C1, C3,
  C4, C5, C6 all still open. The one thing this slice did NOT do that it
  should be judged against: it never attempted C5, which remains the
  single highest-leverage unformalized item, since the loop route to C1
  needs it even if a loop witness ever turns up.
- Next-target ranking, revised: (1) C5 formalization (λI conservation) —
  now unambiguously first, since Slice 4 exhausted the cheap structural
  probes on C1 and the frozen-head result sharpens what a divergence
  argument would have to do without changing the fact that C5 gates the
  loop route; (2) construct-don't-search for C1 — the one census property
  the review named that this slice did NOT negate, and the only remaining
  route that doesn't wait on C5: design a pure-S term together with an
  invariant forcing a redex, rather than hunting for one and hoping a
  certificate exists; (3) the diverging-pairs core (`Joinable`, Slice 1);
  (4) the pigeonhole queue (`sTerms`-completeness), unchanged.

## 2026-07-24 — Stage 5, Slice 5: C1 split, minimality proved

- Where this slice came from: a second ideonomy pass, aimed at the program's
  own trajectory rather than at its mathematics. The tuple was
  organon-construction + substitution on a timeline, with
  discovery-vs-invention, predictability and cyclicity as the prompts. The
  timeline was built from real numbers — Lean and prose line counts across
  all 89 commits — and it said three uncomfortable things: the prose/Lean
  ratio had sat between 0.23 and 0.48 for six stages and then inverted at
  Slice 3 (2.33) and stayed near parity at Slice 4; the invention/discovery
  mix had drifted toward invention, with Slice 4 two-thirds invention by
  item count; and one conjecture had been resolved in nine stages, by the
  late-program slice with the LOWEST prose ratio.
- The operative move was substitution on the discovery-vs-invention axis.
  The census frame is discovery-shaped — "which existing term is the
  smallest diverging one?" Substituting an invention frame — "build a term
  that provably diverges" — exposed that C1 was never one claim. It bundles
  EXISTENCE with MINIMALITY, and the bundle is what made both halves look
  uniformly hard. Nine stages of attacking the bundle; nobody had written
  the two lines separately.
- What fell out immediately once split: minimality is FINITE. 65 terms
  (1+1+2+5+14+42), census-recorded maxSteps of 4 over that range, and
  `normalize` already certified on both ends since Stage 1. The only gap was
  `sTerms`-completeness — the chain blocked since Slice 1, escape-hatched
  after three attempts, and standing at priority FOUR in this notebook's own
  ranking. That ranking was an artifact of the unsplit conjecture: the
  chain's standing description said it blocked `no_small_cycle` and the
  abstract `Decidable` instance, and never once mentioned that it also gated
  half of C1, because with C1 unsplit there was no "half of C1" to gate.
- Route that worked, after three previous failures on the other route: stop
  trying to make `sTermsTable`'s `Id.run do`/`Array`/range-loop definition
  transparent, and prove both directions about a structurally-recursive twin
  instead. The trick that makes `enum` structural is a depth budget as the
  first argument — a two-sided size recursion cannot be seen to decrease
  through `List.range`, but the budget can. `enum_sound` and `enum_complete`
  went through without drama; the whole module typechecks in 1.7s. The
  imperative enumerator is untouched and still runs the census, with
  `#guard`s pinning agreement in length and both containment directions for
  n ≤ 7 so the two cannot silently drift apart.
- Then `no_small_divergence` in a few lines: completeness places a small
  term in a finite list, a `decide`d `List.all` over sizes 0..6 discharges
  it, `normalize_sound`/`normalize_normal` convert the success into a
  genuine normal form. Fuel 10, comfortably above the observed maxSteps of
  4. No `native_decide`.
- The catch worth recording, because the tree's axiom discipline nearly
  slipped: the first version of `enum_complete` reported
  `[propext, Classical.choice, Quot.sound]` — `Classical.choice` would have
  been the FIRST use of it anywhere in this tree. Bisected it to a single
  site: `omega` discharging a non-arithmetic goal (`∃ d', d = d' + 1`) out
  of contradictory hypotheses. Replaced with an explicit witness via
  `Nat.succ_pred_eq_of_pos`, where `omega` only ever proves arithmetic. Same
  failure mode and same fix as Slice 2's choice-free τ decrease, which is
  the second time this exact leak has appeared — worth remembering that
  `omega` proving a NON-arithmetic goal is the smell.
- Register: C1(b) is the program's first proved POSITIVE result about pure
  S. Every previously settled result is negative (two hosting refutations)
  or structural (acyclicity, the consolidation, the frozen head). Stated
  plainly in the ledger, along with the limit — minimality gives zero
  leverage on existence, and if pure S is strongly normalizing then C1(b)
  stays true while C1(a) is simply false.
- What this says about method, which is the part I would keep: the
  resolution came from neither a new probe nor a new definition. It came
  from noticing that a conjecture was two conjectures. Slices 3 and 4 were
  both honest and both produced good artifacts, and neither could have found
  this, because both took the conjecture list as given. Reviewing the
  PROGRAM rather than the mathematics was what surfaced it — and the review
  that did it was cheap.
- Next-target ranking, revised (the C5 demotion is deliberate and the reason
  matters): (1) **construct-don't-search for C1(a)** — now the highest-value
  live item, and the one census property no slice has yet negated. Under an
  invention frame the witness need not be `c1`: any diverging pure-S term
  settles existence, so a construction may pick a convenient, self-similar,
  large term designed alongside its own invariant, rather than the smallest
  one, which is the term least likely to have exploitable structure. Nine
  stages went after the hardest possible witness for reasons of taste rather
  than necessity. (2) **C5** (λI conservation) — unchanged in value,
  demoted in order: it is a known classical theorem, so its information gain
  is zero and it is labour rather than inquiry. It still gates the loop route
  to C1(a), so it is not optional, only not urgent. (3) the pigeonhole /
  abstract `Decidable (t ⟶* u)` item — cheaper now that `enum_complete`
  exists, since the finiteness ingredient it wanted is exactly what
  completeness supplies; worth re-scoping before attempting. (4) the
  diverging-pairs core (`Joinable`, Slice 1). Note that item (3) moved up
  by two places purely as a side effect of this slice, which is the second
  thing the split bought.

## 2026-07-24 — Stage 6: the spec's goals, and the check nobody ran

- Where this came from: not an ideonomy pass this time but a plain
  re-reading of the design spec, prompted by noticing that two consecutive
  strategy answers had ranked work against the C-conjecture list. The spec
  does not have a C-list. Its Goal 3 is "is reachability between pure S-terms
  decidable?", and I had ranked that item THIRD after having just written the
  note explaining that Slice 5 made it tractable. Third time the same failure
  shape: taking a derived artifact (first C1-as-one-conjecture, then the
  C-list, then my own queue) as the fixed target while the spec sat there
  being the actual authority.
- Goal 3 went through cleanly and fast. The whole content is that
  `enum_complete` supplies the finiteness the Slice 1 gap needed:
  `smallTerms` as the finite universe, `deficit` as the measure,
  `deficit_lt` for the pigeonhole step, then saturation by induction on fuel
  rather than well-founded recursion (the deficit bound is threaded as a
  hypothesis, which keeps it structural). Two generic list lemmas had to be
  written — filtering one list by two comparable predicates, both the ≤ and
  the < form — neither in core 4.28.
- Lean friction worth recording: core 4.28 has only ONE direction of
  `eraseDups` membership, and the project had already hand-written that one
  (`mem_of_mem_eraseDups`, Slice 1). I needed the other direction and
  briefly started writing it, then realised the proof does not need it —
  take the pigeonhole witness from the DEDUPED frontier via `eraseDups_cons`
  and the existing direction covers the rest. Cheaper than adding a lemma.
- Also: `cases h : e with` substitutes the scrutinee into the goal, so a
  follow-up `rw [h]` fails with "pattern not found". Cost two iterations.
  And `by_contra` is Mathlib, not core — `Nat.lt_or_ge` plus `absurd` is the
  zero-dependency replacement, same as Slice 5 needed.
- **The literature check, which is the real result of this stage and is
  uncomfortable.** Under an hour of searching established that BOTH halves of
  C1 have been known externally the whole time. Wolfram states plainly that
  "at size 7 and above there are S combinator expressions that do not
  terminate", and the Wolfram Data Repository ships the non-halting S
  expressions for leaf counts 1 through 10 as a dataset. Waldmann's
  decidability result — cited in this project's own spec Background since
  Stage 0 — is the underlying technology. So the census independently
  rediscovered a known threshold, and this file recorded the rediscovery as
  an open conjecture for nine stages.
- What makes that a process failure rather than bad luck: this project
  maintains a meticulous external/internal register. Cocke–Minsky, Waldmann,
  Church/Barendregt and Barker are all cited precisely, with "EXTERNAL fact,
  not machine-checked" attached. The register was applied to every
  background fact the program LEANED on and to none of the facts it was
  trying to establish. There was no **external** status available for a
  conjecture, so an externally-settled claim had nowhere to sit except
  "open". Added that status this stage; it is the missing primitive.
- Honest limit on the check: I did not extract the explicit leaf-7
  expressions from the dataset to compare with `c1`/`c2` term by term. The
  agreement established is on existence and on the threshold, not on the
  identity of the witnesses. Cheap to finish and worth finishing.
- Consequences taken rather than deferred: C1(a) re-labelled external
  (transcription, not research); the "first proved positive result" claim on
  C1(b) corrected in place rather than deleted, so the overreach stays
  visible; C2's folklore hedge sharpened from "may be folklore" to "assume
  external until the primary source is read", since secondary sources credit
  Waldmann with no-ground-loops for CL(S).
- Goal 2 criterion (a): assessed and deliberately not attempted. The
  encoding machinery needed is substantial but mechanical; the blocker is
  `bwd`, which for a real encoder is a full adequacy theorem (no spurious SK
  path between encoded words). `bwd` was free for `pureS_in_SK` only because
  that encoder is inclusion — which in hindsight makes `pureS_in_SK` a much
  weaker demonstration of the Simulation class than it reads as. Recorded
  the blocker instead of leaving a half-built encoding in the tree.
- One cheap real finding fell out of that assessment: `Simulation.id` makes
  all three Universal* predicates trivially true on the diagonal. Added as a
  negative control beside `bareEncNorm_trivial`. It does not affect any
  ledger row (all have R = Tag ≠ B) but it closes the reflexive analogue of
  the oracle-encoder cheat.
- C3 retired as a census artifact. Both halves weakened, never a claim about
  S-reduction, and carrying it was inviting re-probing.
- Next-target ranking, revised again and now anchored to the spec rather
  than to the C-list: (1) **spec Goal 2 criterion (a)** — the only stated
  spec goal still open, and the taxonomy is the spec's declared intellectual
  centre; needs to be scoped as a multi-slice project with `bwd` as the
  known hard part, not attempted opportunistically. (2) **C4** — genuinely
  open, genuinely ours, and the one conjecture on the list with no external
  answer found; it generalises the iota refutation to all strictly-growing
  one-rule bases and `PathEncoding` already gives the right hypothesis
  shape. (3) C6 — open, ours, cheap to extend. (4) transcription work
  (C1(a), C5) — real deliverables under Goals 1 and 4, now correctly
  labelled as importing rather than discovering. Note that C1 has left the
  top of this list for the first time since Stage 0, and that the two items
  now above it are the two nobody has found an external answer for.
- Meta-goal note (spec Goal 4): the spec says "if Stage 5 never terminates,
  the notebook is the result." Three stages of strategy advice in this
  notebook were mis-ranked in the same way, and each time the correction came
  from re-reading a document that was already in the repo rather than from
  new mathematics. That is a finding about this working setup, and it belongs
  in the meta-goal's record as much as any proof-friction note does.

## 2026-07-24 — Stage 7: C4 reduced, and a plan that broke on contact

- Where this came from: a third ideonomy pass, tuple tree-finding +
  cross-domain re-instantiation on a cycle, prompts homogeneity / side-effect
  / polarity. Two of its findings survived execution and one did not, which
  is the entry's main content.
- **The finding that held: an altitude diagnosis.** Walking the tree upward
  from "is S universal?" gives: do small S-terms diverge -> is S universal ->
  is this one-combinator basis universal -> which minimal systems are
  universal -> what does universal MEAN for a rewriting system -> when is a
  translation between systems faithful rather than smuggling the answer. Prior
  art is DENSE at the bottom and thin at the top. Counted the tree's own
  theorems by area: 36 in Universality/ plus 11 in its RS substrate, with
  Calibration.lean the single densest file. So the program's mass is at the
  top while nine stages of effort went to the bottom — and of course prior art
  is dense down there, because the bottom is the level enumeration reaches.
  That single observation explains all three prior mis-rankings at once: they
  were not three mistakes but one closed loop at the wrong altitude, sampled
  three times. C1-as-one-conjecture, the C-list, and my own queue are all
  bottom-level artifacts.
- **The cycle diagnosis, also held.** Drawing the working loop from the commit
  history: census -> conjecture -> attack -> prove-or-negative -> ledger ->
  back to conjecture. The loop closes on `conjecture`, never on `spec`. So
  after Stage 0 emitted the C-list, the spec sat outside the cycle for nine
  stages and every correction required manually breaking out to re-read a
  document that had been in the repo since day one. Two phases were missing
  entirely — calibrate-against-prior-art and materiality-check, both belonging
  between conjecture and attack. Both are now ledger fields.
- **The finding that did NOT survive, which is the useful part.** The pass's
  headline recommendation was to restate spec Goal 2 criterion (a) at
  PathEncoding strength, since the refutations only need PathEncoding and the
  blocker is `bwd`. It sounded strong enough that I led with it. It is wrong.
  Positive and negative claims want OPPOSITE classes: not-exists-encoding
  strengthens as the class grows, exists-encoding strengthens as the class
  shrinks. Criterion (a) is positive, and its entire purpose is showing the
  DEMANDING definition is satisfiable, so weakening the class weakens the
  claim in the direction where weakness is not wanted. The spec's own
  quantifier-asymmetry note says this, in different words, and I had read it
  two stages earlier.
- What I did about it: formalized the correction rather than deleting the
  suggestion. UniversalReach.toPathEncoding gives the inclusion, and with
  pathEncoding_strictly_weaker the two levels provably differ, so the
  direction is substantive rather than bookkeeping. Recorded in the ledger as
  superseding the suggestion, with the wrong reasoning left visible. The
  outcome is that Goal 2's blocker is now known to be PRINCIPLED — `bwd` is
  load-bearing — which is more useful than the bypass would have been if it
  had worked.
- **C4 went the way C1 went.** Same bundling: a semantic claim (strictly
  growing measure ⇒ cannot host SK) fused to a syntactic class
  (one-combinator, single-rule, first-order). The semantic half is two lines
  given RS.Acyclic.of_strict_measure plus SK's cycle, and it is STRONGER than
  C4 — any host, one-combinator or not. The syntactic half needs a
  rule-schema formalism nobody has built. Registered as reduced, not resolved.
  Third time now that splitting a bundled conjecture was the whole trick;
  worth treating as a standing first move rather than a lucky one.
- Confirmation the generalization is right: RS.Iota_acyclic and Stage 4's
  refutation both drop out as one-line instances. Strict growth was never a
  property of iota, only of its measure. Stage 4 had written a bespoke
  argument for what turns out to be a corollary.
- Proof-friction note: Classical.choice leaked again, in
  no_sim_SK_of_strict_measure, from opening a Nonempty with Classical.choice
  when destructuring into a Prop goal needs nothing. THIRD leak in three
  slices (Slice 2: omega in congruence cases; Slice 5: omega on a
  non-arithmetic goal; here: Nonempty elimination). All three were caught by
  the axiom audit, none by review. The audit is doing real work and should
  stay a per-slice ritual.
- Cross-domain note worth keeping, since it produced the materiality field:
  re-instantiating "apparatus for deciding when a translation is faithful"
  into audit standards surfaced the pairing this file was missing.
  Scope-honesty and materiality travel together in auditing; this project had
  built an excellent attestation layer and no materiality test at all. Sport
  rules-committees suggested a second move not yet taken — publish the test
  battery separately from any particular ruling — which is the extraction
  question below.
- Extraction assessment (asked, answered honestly, not acted on): the
  calibration suite (Simulation, PathEncoding, the strictness witness, the
  three observation modes, bareEncNorm_trivial, the diagonal controls,
  refute_of_acyclic, the measure engine) is coherent, portable, and its
  natural peer set is encoding-legitimacy disputes across several fields
  rather than combinator papers. It is NOT ready to stand alone, for one
  concrete reason: it has no positive certification. Every calibration result
  in it is negative or a triviality control, and a suite that only ever says
  "not this" is a critic, not a standard. Goal 2 criterion (a) is exactly the
  missing piece, which is a second and independent argument for ranking it
  first. Extraction after (a), not before.
- Next-target ranking, unchanged in order from Stage 6 and now better
  motivated: (1) **spec Goal 2 criterion (a)** — the only open stated spec
  goal, the taxonomy's missing positive side, and a prerequisite for the
  suite standing alone. Needs scoping as a multi-slice project with `bwd` as
  the known and now provably-necessary hard part. (2) **C4's syntactic
  residue** — a rule-schema formalism; genuinely ours, no prior art found,
  mathematics already done. (3) transcription work (C1(a), C5) — real
  deliverables under Goals 1 and 4, correctly labelled as importing.
  (4) C6, explicitly NOT promoted despite being cheap, because cheapness is
  what made C1 attractive for nine stages.

## 2026-07-24 — Stage 8: attack the blocker, not the encoding

- Continued straight down the Stage 7 ranking: spec Goal 2 criterion (a),
  the only open stated spec goal. The obvious move is to start building a
  Tag → SK encoding. I did not, and the reasoning is the entry's point: the
  encoding's hard field is `bwd`, so anything built before `bwd` is derivable
  is built on top of an unsolved problem. Make `bwd` derivable first.
- What went in: the classic adequacy technique, proved once at the taxonomy
  level. An abstraction function on ALL host states, each host step either
  stuttering or advancing the abstraction by exactly one source step, yields
  `bwd` (`RS.abstraction_tracks`, `RS.bwd_of_abstraction`) and packages into
  `Simulation.ofAbstraction`, which also absorbs `dec_enc` since the
  abstraction doubles as the decoder. All axiom-free, and the proof is short —
  induction on the host path carrying "the abstraction of the current state is
  some source state reachable from the start."
- Register, stated in the module header and the commit: this does NOT remove
  the blocker. It changes its KIND — from "characterise every path between
  encoded states", which is open-ended, to "define the abstraction and check
  each rule stutters or advances", which is mechanical per machine. Worth
  being precise because "bwd blocker solved" is exactly the overclaim this
  notebook keeps catching, and it would be wrong.
- Non-vacuity check chosen deliberately: rebuild `pureS_in_SK` through the new
  constructor. It works, and it is degenerate in an instructive way — no step
  ever stutters, because every SK step out of a K-free term advances the
  source by exactly one PureS step (Stage 2's KFree.of_step). So the example
  exercises the interface and NOT the hard case, since a real machine
  encoding stutters on most steps and advances on few. Recorded as such
  rather than presented as evidence the technique scales.
- **The structural finding, which I did not expect and which reframes the
  Stage 4 result.** Checking what Bracket.lean could contribute, I found there
  is no bridge from `TermV` to `Term` and no transfer from `StepsV` to
  `Steps`. Bracket.lean is a closed universe. So `combinatory_completeness` —
  the program's headline POSITIVE calibration result since Stage 4 — has never
  been in the same language as any of its negative results, all of which live
  in the RS/Term layer. CONJECTURES.md had flagged it as "a theorem about
  TermV, not routed through Simulation", which reads as a stylistic caveat;
  the gap is structural. The positive and negative halves of this program's
  calibration have never met. That is a much better argument for criterion
  (a)'s priority than the one I gave in Stage 7, and it was sitting in the
  import graph the whole time.
- Criterion (a) decomposed into six pieces with difficulty named (recorded in
  CONJECTURES.md). Five are mechanical-but-bulky; the residual risk is
  concentrated in the last, where `abs` must be total on SK terms including
  garbage and tracking must survive every intermediate state the driver
  passes through. That is the piece to prototype first if this is picked up,
  because it is the one that can fail in kind rather than in volume.
- Meta-goal note: this is the first stage in a while where the right move was
  to build infrastructure for a problem rather than attack the problem, and
  the reason it was identifiable is that Stage 7 had already proved `bwd`
  load-bearing. A blocker that is known to be principled is worth building
  against; one that might be incidental is worth trying to route around
  first. Those are different responses and the distinction came from a
  theorem, not from judgement.
- Ranking unchanged: (1) criterion (a), now with piece (vi) flagged as the
  prototype-first risk; (2) C4's syntactic residue; (3) transcription
  (C1(a), C5); (4) C6, still deliberately not promoted.

## 2026-07-24 — Stage 9: the bridge, and a claim weakened instead of an axiom paid

- Continued down the ranking. Criterion (a)'s prototype-first risk is piece
  (vi), but Stage 8's structural finding made piece (i) the better move: it
  repairs a real defect in the program's centrepiece and is on the critical
  path regardless.
- First confirmation was worse than the Stage 8 write-up: Bracket.lean did not
  merely lack a bridge, it had **no import line at all**. A completely
  standalone file holding the program's only positive calibration result. The
  Stage 8 entry said "closed universe"; it was literally closed.
- The bridge went in cleanly. The pleasant surprise: `step_toTerm` needs NO
  closedness hypothesis. `StepV`'s four rules are `Step`'s four rules,
  `toTerm` is a homomorphism for application, and variables are inert on both
  sides — so every variable-level step projects to a genuine `Term` step
  unconditionally. Both transfer lemmas are axiom-free. I had budgeted for a
  closedness side-condition threaded through every proof and it never
  materialised.
- Placement was a deliberate choice: `combinatory_completeness_RS` went into
  Calibration.lean rather than Bracket.lean, so the positive result physically
  sits beside the refutations it is supposed to be comparable with, and
  Bracket.lean stops at `Term`/`Step` without importing the conservation
  layer. Calibration.lean now reads as one sandwich in one language, with a
  comment stating what the sandwich still does NOT contain — the positive side
  is about realizing λ-bodies, criterion (a) wants hosting a MACHINE. Making a
  gap legible is not closing it and the file says so.
- **The fourth Classical.choice leak, and the first one I did not fix.** The
  stronger faithfulness lemma — `ClosedV v → ofTerm (toTerm v) = v`, i.e.
  `toTerm` is faithful on every variable-free TermV and not just on ofTerm's
  image — needs `(n == n) = true` in its `var` case. Four routes tried:
  `beq_self_eq_true` (leaks), `simp` finding it (leaks), a hand-rolled
  `Nat.beq n n = true` by structural recursion (axiom-free, but will not
  connect to `==` — the `BEq Nat` instance does not reduce `succ k == succ k`
  to `k == k`), and the same at the `==` level (same wall). The leak is in the
  BEq/LawfulBEq instance layer, not in my proof.
- The three-attempt rule applied, so I stopped and reassessed instead of
  finding a fifth route. The reassessment is the useful part: the lemma is
  DECORATIVE — nothing in the tree depends on it — and the bridge only ever
  transfers FROM `Term`s, so what is actually needed is that `toTerm` inverts
  `ofTerm`, which was already axiom-free. Weakened the claim to
  `ofTerm_injective` and wrote the dropped claim, the reason, and the four
  failed routes into the doc comment. Whole bridge reports [propext] or less.
- Worth stating as a rule, since this is the first time the choice: when a
  decorative lemma costs an axiom the tree has never used, weaken the claim.
  When a load-bearing one does, pay it and register it loudly. The previous
  three leaks were all in load-bearing proofs and all had rewrites available;
  this one had neither property, which is why it read differently.
- Ranking, unchanged in order: (1) criterion (a) — piece (i) DONE, next is
  (ii) multi-variable bracket abstraction, then (vi) as the prototype-first
  risk before the bulk of (iii)–(v); (2) C4's syntactic residue; (3)
  transcription (C1(a), C5); (4) C6, still not promoted.

## 2026-07-24 — Stage 10: the prototype failed, which is why it was a prototype

- Two ordering decisions, both against my own written list and both for the
  same reason. Piece (ii) was next; I skipped it. First because it is
  mis-scoped — Stage 8 called it "one iteration lemma" and it is not, since
  iterating `bracket` needs substitution to commute with bracketing and that
  holds only up to reduction (`subst x u (bracket y (var x))` is `K u`;
  `bracket y (subst x u (var x))` is `bracket y u`; reduction-equivalent, not
  equal, so the induction does not close syntactically). Second because (ii)
  is investment and (vi) was flagged as the piece that could invalidate it.
  The list said (ii) then (vi); the list's own justification said prototype
  first. Followed the justification.
- The prototype: `Itower n = I (I (... S))`, a countdown where one source step
  costs two host steps. Chosen because it is the smallest encoding that is a
  genuine multi-step machine rather than an inclusion, and because it has real
  nondeterminism — `Itower 3` has three redexes, so reduction can go
  outside-in, inside-out, or interleaved. `pureS_in_SK` had neither property,
  which is exactly why the Stage 8 non-vacuity check could not have caught
  this.
- It failed, and the failure is clean enough to state as a theorem:
  `naiveAbs_not_stuttering`. The obvious structural abstraction — count
  pending I-layers, recognise intact `I u` and half-consumed `(K u)(K u)` —
  admits a step out of an abstracted state whose target abstracts to `none`.
  Concretely `(K (I S))(K (I S)) → (K ((K S)(K S)))(K (I S))`: one step inside
  the LEFT copy only, and the two copies no longer match.
- Cause, and it is not incidental to this test machine: `S f g x → (f x)(g x)`
  duplicates `x`, so the copies reduce independently. Any abstraction reading
  a duplicated subterm syntactically has to cope with drift, and the drifted
  state space is combinatorial in the live redexes inside the duplicated part.
  This is the failure-in-kind Stage 8 was worried about, found where Stage 8
  predicted it would be.
- **The payoff, which is why this was worth doing before piece (v).** There
  are two fixes and the second is a design constraint, not a proof technique:
  constrain the encoding so duplication only ever hits NORMAL FORMS. If `x` is
  normal when `S f g x` fires, neither copy can step, so drift is impossible
  by construction and the syntactic abstraction is fine. `sync_step` checks
  this: the same shape over a normal payload advances 1 → 0 exactly as
  required. So piece (v)'s driver must duplicate only already-normal arguments
  — achievable, since encoded words and symbols are data and data can be kept
  normal, but it constrains how the machine is built and cannot be retrofitted.
- Revised difficulty, and the honest correction to Stage 8: (vi) is mechanical
  only CONDITIONAL on (v) obeying that discipline. Stage 8's decomposition
  listed (i)–(vi) as independent pieces; (v) and (vi) are coupled, and the
  coupling runs from the later piece back to the earlier one. That is the kind
  of thing that would have been discovered halfway through building (v), at
  which point (v) would have needed rewriting.
- Cheap methodological note: this is the third stage in a row where the useful
  output was a NEGATIVE about the program's own plan — Stage 7 corrected a
  recommendation, Stage 9 weakened a claim rather than paying an axiom, Stage
  10 falsified a difficulty estimate. All three were cheap, and all three would
  have been expensive to discover later. The pattern is worth naming: the
  program's plans have been consistently over-optimistic about mechanical
  pieces and consistently right about which piece is risky. Trusting the risk
  flags and distrusting the difficulty ratings looks like the correct posture.
- Ranking, unchanged in order but with (v) and (vi) now coupled: (1) criterion
  (a) — (i) done, (vi) prototyped and its constraint known, (ii) needs a
  commutation-up-to-reduction lemma, (iii)–(v) must be built under the
  normal-forms-only discipline; (2) C4's syntactic residue; (3) transcription
  (C1(a), C5); (4) C6, still not promoted.

## 2026-07-24 — Stage 11: checking a constraint before building on it

- Direct application of the posture named at the end of Stage 10: trust the
  risk flags, distrust the difficulty ratings. Stage 10 handed down a design
  constraint — duplication must only ever hit normal forms — and the obvious
  next flag is whether that constraint can be met at all. If it cannot,
  pieces (ii)–(v) are wasted work, and finding out costs an hour now versus a
  rewrite later. Same shape as Stage 10's own reasoning, one level up.
- The reasoning that made it cheap: the first thing any machine duplicates is
  its own CODE, through the self-application inside a fixpoint. All of this
  program's code comes from `bracket`. So the question reduces to "are bracket
  outputs normal?" — and inspecting the four cases of `bracket` answers it
  immediately: it only ever emits `K` with ONE argument and `S` with TWO, and
  neither is a redex. `normalForm_bracket` compiled first try.
- That is a genuinely reassuring result and it was invisible before the Stage 9
  bridge existed, because the statement is about `Term`-level normal forms and
  `bracket` lives in `TermV`. Worth noting: the bridge paid off one stage after
  it was built, on a question nobody had in mind when building it.
- Four shape lemmas fell out (`normalForm_S`/`_K`, `normalForm_app_K`,
  `normalForm_app_S_one`/`_two`). These are the kind of small reusable facts
  piece (v) will need constantly, so they are cheap infrastructure acquired as
  a side effect rather than as a project.
- Also upgraded Stage 10's diagnosis from an observation to a theorem:
  `step_app_K_pair` shows the half-consumed shape over a NORMAL payload has
  exactly one successor. Stage 10 had `sync_step`, a single instance. The
  general form is what actually licenses the design constraint.
- **The honest half: the constraint is only HALF satisfiable so far.** Code is
  normal, so fixpoint self-application is safe. But a fixpoint's reduct
  `f (x x f)` hands the step function a pending recursive call, which is not
  normal, and if the driver duplicates that then drift is back. So piece (v)
  needs a strict discipline — force before duplicating. Recorded as the
  sharpest known requirement on the remaining work rather than waved at.
- Pattern check, since Stage 10 named one: this is the FIRST stage in four
  where the output was positive rather than a negative about the plan. It was
  found by the same move that produced the three negatives — ask what the plan
  assumes, then check the cheapest assumption first. The move is not
  pessimistic; it is just ordering. Stages 7, 9 and 10 happened to find breaks;
  this one found a foundation.
- Ranking: (1) criterion (a) — (i) done, (vi) prototyped, code-duplication
  safety proved, and the live requirement is now a strict-evaluation discipline
  on piece (v)'s driver; the next buildable item is (ii), which needs the
  commutation-up-to-reduction lemma; (2) C4's syntactic residue; (3)
  transcription (C1(a), C5); (4) C6, still not promoted.

## 2026-07-24 — Stage 12: piece (ii), shrunk by two design choices

- Piece (ii) was rated "one iteration lemma" in Stage 8, corrected in Stage 10
  to "needs commutation up to reduction". Both were wrong about the shape of
  the work. What it actually needed was two decisions, after which one lemma
  did the job:
- **Decision 1: don't build n-variable abstraction.** A driver needs a
  fixpoint self-reference and a state — two variables — and any further
  arguments can be tupled into the state. Two nested abstractions is exactly
  the case the commutation lemma handles in ONE application, with no
  iteration and no induction over a variable list. The general n-variable
  development would have been several times the work for something nothing
  needs. Recorded as a YAGNI call in the same spirit as the file's existing one.
- **Decision 2: state the lemmas for encoded data, not for abstract closed
  terms.** The argument being substituted is always in the image of `ofTerm`,
  so `subst_ofTerm` and `bracket_subst_applied` quantify over `ofTerm p`. This
  deletes the `var` case from both proofs — and the `var` case is precisely
  where Stage 9's `Classical.choice` trap lives (deriving a contradiction from
  `ClosedV (var n)` needs `(n == n) = true`). So the Stage 9 leak, which cost
  four failed attempts and a weakened claim, ended up steering a design two
  stages later toward a cleaner formulation. Worth noting: the leak was not
  just an obstacle, it was information about which shapes to avoid.
- The lemma itself went in without drama once framed that way — four cases,
  each a couple of lines, and the `app` case is just S_red plus `congApp` on
  the two IHs. `abs2_beta` is then `congL` of `bracket_beta` composed with it.
- Lean friction, minor but repeated: `simp only [..., h]` where `h : ¬ (z = y)`
  rewrites the CONDITION to `False` but does not reduce `if False then a else b`.
  Needs `ite_false`/`ite_true` alongside. Cost two iterations and produced a
  crop of unused-simp-argument warnings while I found the minimal set; cleared
  them all, build is warning-free again.
- Small honest finding from clearing those warnings: the `unused variable h`
  lint on `combinatory_completeness_Term` is telling the truth. Its
  single-variable hypothesis is VESTIGIAL — the `Term`-level statement does not
  assert closedness, and `toTerm` erases variables anyway, so the theorem holds
  for any body. Renamed to `_h` rather than dropped, to keep parity with the
  `TermV` version where the hypothesis genuinely is needed for `ClosedV`.
  Flagged in the ledger rather than silently kept, since a vestigial hypothesis
  makes a theorem look narrower than it is.
- Where criterion (a) stands: (i) and (ii) done, (vi) prototyped with its
  constraint half-discharged, (iii)–(v) remaining under the
  force-before-duplicate discipline. The residual risk is unchanged and
  specific — a fixpoint's reduct hands the step function a pending recursive
  call, which is not normal. That is the next thing worth prototyping, and by
  the Stage 10/11 pattern it should be prototyped before (iii)–(v) get built,
  not after.

## 2026-07-24 — Stage 13: the third revision of one difficulty estimate

- Followed the Stage 10/11 rule: prototype the known risk before building on
  it. The risk was the pending recursive call. It broke, and it took Stage 10's
  preferred fix down with it.
- The mechanism is embarrassingly simple in hindsight. `bracket` is the NAIVE
  algorithm — the file's own comment says so, and says the tradeoff is bigger
  terms for smaller proofs. What nobody had noticed is that "bigger terms"
  means DUPLICATED ARGUMENTS: `[x](a b) = S ([x]a) ([x]b)` sends the argument
  to both branches whether or not `x` occurs in them, and `S A B u → (A u)(B u)`
  copies `u`. So the abstracted argument is duplicated once per application node
  in the body. I demonstrated it on a body that uses its variable exactly once.
- That kills route (2) as a standalone fix. Stage 10 framed the choice as
  "define the abstraction up to Joinable (hard)" versus "constrain the encoding
  so duplication only hits normal forms (a design constraint)", and preferred
  the latter. But route (2) assumed the driver's author controls what gets
  duplicated. They do not — the abstraction algorithm decides, and it duplicates
  unconditionally.
- Worse, and this is the part that makes it a real result rather than a bug
  report: transient duplicates are not fixable by a better abstraction
  algorithm. In SK, `S f g x → (f x)(g x)` is the ONLY way to move a value into
  two positions, and it always duplicates the third argument. Occurs-check
  optimization reduces the NUMBER of copies; it cannot reach zero, because
  getting a value past another value costs a copy. So some window always exists
  in which a doomed copy is live and can drift.
- Third revision of the same estimate, which is worth stating plainly: Stage 8
  said piece (vi) was mechanical. Stage 10 said mechanical conditional on (v)'s
  design. Stage 13 says not mechanical. Each revision came from probing one
  level deeper, and each was cheap. The estimate has moved monotonically in one
  direction, which is itself a signal — I should have weighted the first
  revision as evidence about the second.
- Where that leaves criterion (a): the abstraction has to be insensitive to
  doomed subterms, either up to `Joinable` (Slice 1 has it, and SK confluence is
  proved, so the machinery exists) or by reading only the live spine. That is a
  research-shaped obligation, not a bulk one, and it is now the honest cost of
  the criterion. Pieces (i) and (ii) are unaffected and still needed; Stage 11's
  `normalForm_bracket` still holds and still matters, because CODE being normal
  is what makes fixpoint self-application safe. The problem is narrowly the
  pending recursive call.
- Methodological note, and the reason I am not discouraged: four stages of
  prototyping have cost roughly one stage of building and have prevented two
  rewrites of piece (v). The alternative history — build (iii)–(v) on Stage 8's
  "mechanical" rating, then discover in (vi) that the abstraction cannot be
  written — would have wasted far more. The prototypes keep finding bad news
  because they are aimed at the places most likely to contain it, which is what
  they are for.
- Ranking, revised in emphasis rather than order: (1) criterion (a), where the
  next real decision is which of the two route-(1) variants to attempt — up to
  `Joinable`, or live-spine-only — and that decision should itself be prototyped
  on the Stage 10 countdown machine before any encoding work; (2) C4's syntactic
  residue, which is now comparatively more attractive, being bulk work with no
  hidden research problem in it; (3) transcription (C1(a), C5); (4) C6.

## 2026-07-24 — Stage 14: taking my own advice and switching targets

- Stage 13 ended with two facts I had written down and not acted on: the piece
  (vi) difficulty estimate had been revised upward three times MONOTONICALLY,
  and C4's residue was "bulk work with no hidden research problem in it". The
  first is evidence the estimate will move again; the second is a target with
  known cost. Continuing on (a) would have been walking down the same corridor
  for a fourth revision. Switched to C4.
- Worth being explicit about the reasoning, since it is the same move I have
  been recommending and then not following: a monotone sequence of upward
  revisions is information. I noted it in Stage 13 as a lesson about the SECOND
  revision. Applying it forward instead of backward is the actual use.
- C4's residue turned out much cheaper than expected once I looked at arity. The
  general-arity case needs occurrence VECTORS and sums over `i < n`; the arity-1
  case needs a single coefficient and no sums at all. And arity 1 is exactly
  ι's arity — so the arity-1 theorem generalizes the instance C4 was abstracted
  from, which is the most useful part of the whole class to have.
- The satisfying part: C4's informal English collapses into two `decide`-able
  counts. "Each rule variable occurs at least once in the reduct" is
  `1 ≤ countVar rhs`. "The reduct is strictly larger even at the minimal
  instantiation" is `2 ≤ countC rhs`. The bridge is one lemma —
  `Pat1.leafCount_inst`, that instantiation is linear in the argument's size —
  and everything else is arithmetic. A conjecture stated in prose for eleven
  stages turned out to be two inequalities.
- Non-vacuity handled carefully, because there was an easy overclaim available:
  `RS.Mono1 iotaRhs` is ι's rule SHAPE over the abstract carrier `Mono`, NOT the
  `RS.Iota` instance whose carrier is `IotaTerm`. They are isomorphic but nothing
  here re-derives `no_pathEncoding_SK_iota`. Said so in the file, because
  "C4 proved and it recovers the iota refutation" would have read better and been
  wrong.
- Lean friction, one item: `omega` cannot distribute a variable product, so
  `(a.countVar + b.countVar) * |x|` had to be broken up with `Nat.add_mul` in the
  simp set before `omega` could close the `app` case. One iteration.
- Honest scope on the headline: C4 is PROVED for arity 1 and OPEN for arity ≥ 2.
  The remaining obstacle is list-sum algebra in a Mathlib-free tree — additivity,
  an indicator-sum lemma, and a partition lemma — not anything about
  combinators. That matches Stage 13's assessment of the residue as bulk work,
  and it is the first time in five stages that a difficulty estimate has held up
  on contact.
- Ranking: (1) **C4 general arity** — now the most attractive item on the board:
  known cost, no research risk, and the arity-1 case has already validated the
  proof shape, so the only question is the list algebra. (2) criterion (a),
  where the open decision is still which route-(1) variant to attempt for the
  abstraction, and which should be prototyped before any encoding work.
  (3) transcription (C1(a), C5). (4) C6.

## 2026-07-24 — Stage 15: C4 closed, and Stage 14's obstacle was imaginary

- Stage 14 registered general-arity C4 as blocked on "list-sum algebra" and
  named three needed lemmas, one of them a partition lemma to split a variable
  list across an application node. It took about an hour to find that both
  halves of that framing were wrong.
- **The lists were self-inflicted.** I had assumed a rule's arguments arrive as a
  `List Mono`, which forces `getD` indexing and then a cons/append mismatch
  against `List.range`-based sums. Taking the assignment as a FUNCTION
  `σ : Nat → Mono` and defining the left-hand side by recursion on the arity
  (`applyVars`) removes every list from the development. That is a
  representation choice, not a mathematical fact, and I had let the first
  representation I thought of become the estimate.
- **The partition lemma was never needed.** It is only needed if you try to
  prove the INEQUALITY directly, where "every variable occurs" fails to
  decompose over `app`. Proving the exact size formula instead makes the `app`
  case pure additivity. I had actually worked this out in Stage 14 — the note in
  that file says the formula "decomposes fine over app" — and then still listed
  the partition lemma as required. Reading my own note more carefully would have
  saved the pessimism.
- What was genuinely needed: seven small facts about `Σ_{i<n}` (`sumTo` and six
  lemmas), then `Pat.leafCount_inst` and three lines of arithmetic. The whole
  general-arity section is shorter than the arity-1 section's prose.
- Lean friction, two items. `sumTo_congr` made `rw` unify against the wrong
  function inside the sum, so distributivity got its own lemma
  (`sumTo_add_mul`) — worth remembering that congruence-style lemmas over
  higher-order arguments are unreliable for `rw`. And `interval_cases` is
  Mathlib-only; `rcases i with _|_|_|k` with an `omega` tail is the
  zero-dependency replacement.
- Kept the superseded Stage 14 "what remains" section in the file, marked as
  such, with the correction beneath it. A mis-framing that produced a wrong
  difficulty estimate is more useful preserved than deleted, and this file
  already does that for C2's pre-resolution text.
- **C4 was the last conjecture on the list that was both open and unambiguously
  ours.** What is left: C6 (ours, but low materiality and cheap, deliberately
  not promoted), criterion (a) (blocked on the adequacy abstraction — Stages
  10–13, and the difficulty estimate there has moved upward three times), the
  transcription items (C1(a), C5), and the prize question itself.
- Pattern check across the last two stages: Stage 14's estimate was the first to
  hold up on contact, and Stage 15's was wrong in the OPTIMISTIC direction's
  mirror — I over-estimated the cost. So the running tally is now: four
  under-estimates of difficulty (Stages 8, 10, 13 on piece vi; and the original
  C4 framing) and one over-estimate (Stage 14 on general arity). The common
  cause is the same in both directions: I was estimating from the first
  representation that came to mind rather than from the problem. Worth carrying
  forward as "estimate after choosing the representation, not before".

## 2026-07-24 — Stage 16: reading the spec's actual words, and writing up

- Three items this stage, all from a fourth ideonomy pass whose matrix put
  "write the program up" as the highest-weight row — an action that had never
  appeared on any of my rankings, because I had been ranking conjectures, then
  pieces, and never deliverables.
- **The criterion (a) resolution, which came out sharper than the review that
  prompted it.** The review framed it as a letter-vs-spirit ambiguity: the
  criterion says "certify known-universal systems" without naming a host, so a
  cheap reading was available. Reading the spec's actual sentence killed that
  framing and produced a better one. It says "certify known-universal systems
  INCLUDING ONE-COMBINATOR BASES" — it names its targets, and one of those
  targets is something this program REFUTED. C4 at every arity says no
  first-order one-combinator one-rule system meeting the growth condition can
  host SK. So criterion (a) as written is unsatisfiable in first-order scope, and
  the reason was sitting in the spec's own Background section the whole time
  (Barker's ι universality is λ-level and erasing). Stage 4 had registered the
  deviation; nobody had connected it to whether the criterion could be met.
- That is a better outcome than the cheap reading would have been, and it is
  worth noting why: the review's framing was built from the LEDGER'S PARAPHRASE
  of the criterion, not from the criterion. Fourth time now that going back to
  the source document beat reasoning from the accreted summary.
- **The general clause discharged**, with the cheapest honest instance: a tag
  system embeds in a tag system over `Option Sym`. Both sides are m = 2 tag
  systems, hence known-universal externally. Two properties `pureS_in_SK` did
  not have — the source is known-universal, and `bwd` is EARNED rather than free,
  since the encoder is not an inclusion. And it is the first non-degenerate use
  of Stage 8's `Simulation.ofAbstraction`: Stage 8's own use was the
  `pureS_in_SK` rebuild, where nothing stutters because the encoder is the
  identity on carriers. Eight stages later the machinery had a real customer.
- Scoped hard in the file, because the overclaim was available and attractive:
  this says NOTHING about SK. It shows the positive side is not vacuous when the
  source must be known-universal. Tag → SK stays research-blocked.
- Lean friction, one item: `List.drop_cons_eq_cons_drop_of_pos` does not exist,
  and is not needed — taking the source step in `stepRel`'s own canonical form
  (`w.drop m ++ rule a`, with `w = x :: t` left intact) means the `drop` never
  has to be decomposed. I had reached for the decomposition automatically. Same
  failure shape as Stage 15's list-vs-function representation choice.
- **STATUS.md**, the write-up. The ledger and this notebook are both
  chronological and together run to several thousand lines, so neither answers
  "what is settled?" — a reader would have to reconstruct it from sixteen stage
  sections. STATUS.md answers it by spec goal, with theorem names, and I checked
  all thirty cited names resolve against the tree before committing. README now
  points at it.
- **The Mathlib decision, made once.** The spec lists zero-dependency as a
  non-goal with an escape hatch, and the hatch had never been considered in
  sixteen stages. Tax counted: four `Classical.choice` traps, two Mathlib tactics
  replaced, one `eraseDups` direction, two list-filter lemmas, a seven-lemma
  `sumTo` battery. Decision: KEEP zero dependencies — nothing open is blocked on
  Mathlib, since the remaining items are a research problem, transcription, and
  C6. Recorded so "we never decided" stops being the state.
- Where the program is: Goal 1 done, Goal 2 built-and-calibrated with one open
  instance, Goal 3 closed, Goal 4 ongoing-by-design. One substantive item left
  (Tag → SK adequacy) and it is research-blocked. The C-list is exhausted apart
  from C6, which three consecutive reviews have declined to promote.

## 2026-07-24 — Stage 17: the ladder was in the spec the whole time

- The fifth ideonomy pass asked how many things were left. The answer was one
  research problem and no portfolio — which is why the previous three reviews had
  felt thin: with cardinality one at the top there is no ranking problem, only a
  do-or-don't decision. The substitution test on cardinality ("what would the
  swarm form be?") is what found the ladder, and the ladder was not my invention:
  it is the second component of the spec's Stage 5, one paragraph below the north
  star I closed in Stage 6.
- Fifth time going to the source document beat the accreted summary — and the
  first time it produced a whole workstream rather than a correction. Worth
  separating those two outcomes in the record, because they call for different
  habits: corrections argue for re-reading before claiming, a missed workstream
  argues for re-reading before PLANNING.
- **Rung choice was deliberate and not by ease.** {S,I} is where the program's
  only negative mechanism dies. Every refutation in the tree — pure S, ι, C4 at
  every arity — routes through `RS.Acyclic.of_strict_measure`. If {S,I} has a
  cycle then that hypothesis is unsatisfiable there, so the rung tests the main
  tool at its boundary instead of applying it again. Testing a tool where it
  should fail is more informative than another success.
- It has a cycle: `(S I I)(S I I)` in three steps, `I` primitive. Axiom-free, and
  it went in without friction. Then two strictly stronger statements: NO monotone
  measure exists in either direction. That is worth the extra two theorems —
  "there is no such measure" is a very different claim from "we did not find one",
  and the second is what a reader would otherwise assume.
- **The finding I did not expect**, and it corrects something the ledger has
  implicitly allowed since Stage 2: erasure-freeness is NOT what keeps pure S
  acyclic. {S,I} erases nothing either — neither rule discards an argument — and
  it cycles. The Stage 2 conservation laws (K-freeness closed under reduction, no
  erasure) sit right next to C2's acyclicity in the ledger, and it would be easy
  to read the first as explaining the second. It does not. Whatever τ measures is
  specific to S-only reduction.
- Scoped rungs two and three rather than attempting them, and got one real data
  point for free: the obvious Ω attempt for {S,B} TERMINATES, because `B` with
  fewer than three arguments is stuck, so `S B B (SBB)` reduces to a normal form.
  That is weak evidence {S,B} may be acyclic and therefore refutable by the
  EXISTING mechanism — the opposite verdict from rung one. If that holds, rungs
  one and two disagree, which is exactly the kind of contrast that "narrows where
  universality is lost".
- Arithmetic recorded for both: {S,B} and {S,C} pair a strictly decreasing rule
  (−1) with S's (+|x|−1 ≥ 0), so leafCount is non-monotone in both directions and
  a combined τ-style measure is needed. That is a C2-sized slice each, and now the
  next slice knows the shape before starting — which is the thing my difficulty
  estimates have most consistently failed at.
- Lean friction, one repeat: `induction` on `RS.Steps` at a concrete instance hits
  the mkElimApp motive error for the third time in this tree. Raw recursor as
  before. Worth noting it is now a known local idiom rather than a surprise —
  `iota_steps_le`, `RS.Discrete2_steps_eq`, and now `SI_no_decreasing_measure`.
- Ranking: (1) **rung two, {S,B}** — has a plausible verdict (acyclic) and would
  make the ladder's first contrast; (2) rung three, {S,C}; (3) Tag → SK, still
  research-blocked and still the only other irreversible item; (4) transcription
  (C1(a), C5); (5) C6, declined a fifth time.

## 2026-07-24 — Stage 18: a five-line theorem and an honesty correction

- Sixth ideonomy pass. Its operator pair repeated from the fourth, so all its
  value came from the fresh organon and prompts — worth recording, because it
  says the picker's organon/prompt axes are now carrying more than the operator
  axis. Three items, two of them corrections to Stage 17, which I had shipped
  one stage earlier.
- **The hierarchy, from the hierarchicalness prompt.** I had written the ladder up
  as a flat set of independent rungs. Basis inclusion was sitting on it the whole
  time, and the machinery was already in the tree: the contrapositive of
  `PathEncoding.refute_of_acyclic` says cycles propagate along path encodings.
  Five lines, axiom-free. Rung one goes from one basis to an upward-closed family.
- Built the concrete witness rather than asserting the propagation: `{S,I}`
  path-encodes into SK by sending primitive `I` to `S K K`, and
  `SK_not_acyclic_via_rung1` re-derives SK's non-acyclicity from rung one. That
  fact was already known here by the Ω ↔ M cycle, so this is a second independent
  route to it — which is the point. A generic theorem whose first instance
  re-proves something already known by another route is a theorem you can trust.
- Injectivity needed one helper I had not anticipated: `siToTerm_ne_K`. `I`'s
  image is `S K K`, which contains `K`s, so injectivity is not immediate — it
  holds because nothing in the SOURCE maps to `K`, there being no `K` in `{S,I}`.
  Small, but it is the kind of thing that would have blocked the encoding if the
  source basis had contained K.
- **The correction that matters: the ladder answers ACYCLICITY, not
  universality.** The spec says "classify universality of bases". What the program
  can deliver per rung is acyclicity, which bounds only refutability. Rung one
  does not say {S,I} is or is not universal — it says the refutation tool cannot
  reach it. Stage 17's write-up omitted this, and rung one reads like a
  universality result without it.
- That is worth dwelling on because of the timing: in Stage 16 I explicitly
  scoped the `Tag → Tag` result against exactly this misreading, wrote a SCOPE
  paragraph before the theorem, and said in the notebook that the overclaim was
  "available and attractive". One stage later I made the same class of overclaim
  in a different place and did not notice until a review asked. The discipline is
  not transferring between stages on its own; it is transferring because the
  reviews keep asking. Something to keep in mind if the reviews stop.
- Also wrote the rung procedure down, with the ordering rationale — step 3 before
  step 4, because a cycle makes step 4 provably futile. Rung one got that right by
  luck. And named rung 2's step-4 tool concretely: a lexicographic measure, since
  neither component is monotone alone on {S,B} or {S,C}. That is a sharper start
  than "τ-style combined measure", which is what Stage 17 left.
- Not attempted, and registered: the joinability-insensitive abstraction lifter
  that the modularity prompt identified as the missing module for Tag → SK. The
  reasoning there is sound — the program's modular parts all finished cheaply and
  its one monolithic part is the one blocked — and the ingredients are present
  (`ChurchRosser`, `Joinable`, SK confluence). It is the honest route to Goal 2's
  open instance and it is a research-grade attempt, not bulk work.
- Ranking: (1) **rung two, {S,B}**, now with a written procedure and a named tool;
  (2) the joinability-insensitive abstraction lifter, as the modular route to
  Tag → SK; (3) rung three, {S,C}; (4) transcription (C1(a), C5); (5) C6,
  declined a sixth time.

## 2026-07-24 — Stage 19: the procedure earned its keep immediately

- First stage run against the written-down rung procedure, and it caught me. Step
  3 says "hunt for a cycle"; Stage 17 had done ONE hand-traced Ω attempt and
  recorded it as weak evidence, then let that single trace carry a verdict into
  the STATUS.md table. The procedure says a hunt, so I built the census — and the
  census disagreed with the trace's implications within two minutes of running.
- What changed: up to 6 leaves everything normalizes, which is what the Ω trace
  suggested. At SEVEN leaves, 6 of 16896 terms do not normalize at fuel 200, and
  still 6 at fuel 1000. So {S,B} is not plausibly strongly normalizing at all. It
  is plausibly ACYCLIC and plausibly NON-NORMALIZING — which is exactly pure S's
  profile, C1 plus C2.
- The Stage 17 error was small but instructive: I wrote "weak evidence it may be
  acyclic and therefore refutable by the existing mechanism". The first clause was
  fine. The second silently assumed acyclic ⇒ terminating, and this project has a
  theorem saying otherwise — pure S is acyclic and (externally) has
  non-normalizing terms. I had the counterexample in my own tree and still made
  the inference.
- **The free cross-validation is the nicest thing here.** Pure-S terms are
  {S,B}-terms, so the rung-2 census strictly contains the rung-0 census. Two of the
  six exhausted terms at 7 leaves are exactly C1's candidates, and
  `S S S (S S) S S` came back with 120112 leaves after 200 steps — the identical
  figure CONJECTURES.md has recorded for `c1` since Stage 0, now reproduced by a
  reducer written independently for a different term type. Neither census was
  built to check the other; the containment made it happen for free.
- Also refined Stage 17's headline finding. Stage 17 ruled out erasure-freeness as
  the explanation for pure S's acyclicity but did not say what replaced it. The
  rung-2 data does: **arity**. `I` takes one argument, so `S I I x → (I x)(I x) →
  x x` fires and returns. `B` takes three, so `S B B x → (B x)(B x)` leaves
  everything one argument short and stalls. Rung one cycles and rung two does not,
  and the discriminator is neither erasure nor duplication.
- Step 4's target got sharper as a side effect: not a termination measure — the
  fuel-outs rule that out — but a τ-style ACYCLICITY measure, which is precisely
  what C2 needed and got for pure S. That is a much better-specified slice than
  "combined measure", which is where Stage 17 left it.
- Register kept: all of this is unverified census tooling plus build-enforced
  `#guard`s over a bounded search. "No cycle found up to 7 leaves" is not
  acyclicity, exactly as the pure-S census's fuel-outs are not divergence. Written
  into the module header.
- Ranking: (1) **rung two step 4** — the τ-style acyclicity measure for {S,B}, now
  the best-specified open item on the board and a direct analogue of a slice that
  already succeeded once; (2) the joinability-insensitive abstraction lifter for
  Tag → SK; (3) rung three {S,C}, which the same census tooling extends to almost
  for free; (4) transcription; (5) C6, declined a seventh time.

## 2026-07-24 — Stage 20: my own step-4 specification was wrong

- Stage 19 ended by sharpening step 4's target to "a τ-style acyclicity measure,
  lexicographic". One stage later that specification is disproved. This is the
  second consecutive stage where the previous stage's forward-looking claim did not
  survive contact, and both times the claim was mine and made confidently.
- The arithmetic is short enough that I should have done it before specifying.
  Under `S_red` the third argument is DUPLICATED, so any count of anything present
  in that argument can rise; under `B_red` a `B` is consumed and nothing is
  duplicated, so B-count falls. Those two facts alone make every counting measure
  non-monotone. `no_monotone_counting_measure` proves it for all weights `a, b` at
  once, and the proof is entirely witness selection — four concrete terms, chosen
  by which of `a`, `b` is positive.
- **Why this matters more than a corrected note:** C2's argument is a SQUEEZE, not
  a decreasing measure, and I had been carrying it forward as though the hard part
  were "find the τ analogue". The hard part is step (a) — having a monotone
  quantity at all so that a cycle is forced to be constant on it. Pure S has one
  for free (leafCount, by non-erasure). {S,B} has none. Naming the load-bearing
  step of a past success turned out to be what identified why it does not transfer.
- Also killed "lexicographic" specifically, which I had offered as the fix in Stage
  19: a lexicographic order needs its first component monotone. There is no
  monotone first component. So the fix was ruled out by the same theorem that
  ruled out the original.
- What is left is honestly named rather than optimistically scoped: a non-counting
  STRUCTURAL measure (τ weights by POSITION — `2τ(a) + τ(b)` — which is not a
  count, and that distinction is the live hint), an interpretation argument, or the
  census is wrong about there being no cycle. I gave that last option real weight
  in the write-up, because the hunt reached 7 leaves and rung one's cycle lives at
  6. Two consecutive over-confident forward claims is enough reason to stop rating
  "nearly done".
- Runtime: the 8-leaf hunt (109824 terms) died at 10 minutes. Diagnosed rather than
  just reported — `sbOnCycle` keeps a seen-LIST and calls `contains`, so it is
  quadratic per term. Same class of problem as the Stage 6 census, where dropping
  the measurement C6 did not need made n=10 reachable. A faster detector is a
  cheap unblock if the hunt is worth extending.
- Estimate tally, updated: five under-estimates, one over-estimate, and now two
  wrong forward SPECIFICATIONS (Stage 19's lexicographic target, Stage 17's
  "refutable" inference). The pattern has shifted — I am no longer mostly
  mis-rating difficulty, I am mis-specifying the next step. The fix is the same
  one that worked for representations: do the cheap arithmetic before naming the
  target.
- Ranking: (1) a faster cycle detector, then extend the rung-two hunt — cheap, and
  it tests the possibility I am now giving real weight; (2) the
  joinability-insensitive abstraction lifter for Tag → SK; (3) rung three {S,C},
  which the census tooling extends to nearly for free; (4) transcription; (5) C6,
  declined an eighth time.

## 2026-07-24 — Stage 21: the validation step justified itself

- Ranked task was "a faster cycle detector, then extend the hunt". Floyd
  tortoise-and-hare was the obvious fix — `sbStepOnce` is a function, so the
  trajectory is a functional graph and O(1) memory suffices. It worked: n=8 went
  from a ten-minute abandonment to 6 seconds, and n=9 (732160 terms) to 38.
- I wrote it GENERICALLY rather than for `SBTerm` specifically, so it could be
  instantiated on {S,I}. The only reason was to validate the true-positive path —
  I said in Stage 19's write-up that an untested detector reporting "no cycles
  found" is worthless, and rung one supplies a kernel-PROVED cycle to test against.
  That single decision is what produced the stage's finding.
- **The detector did not find rung one's cycle.** For about a minute I assumed a
  bug. It is not: the proved cycle closes with `appR (I_red)` — an INNER redex —
  and leftmost-outermost fires the head S-redex instead. The LO trajectory from
  `omegaSI` goes 6, 8, 7, 10, 9, 8, 12, 11, 10, 9, 14, … growing forever, never
  returning. So a cycle can exist in the RELATION and be completely invisible to a
  leftmost-outermost hunt, and rung one is a worked example.
- That devalues the data I had just spent the stage producing, which is the right
  outcome and worth being blunt about. The {S,B} figures rule out LO cycles. They
  say nothing about the relation. Stages 19 and 20 both leaned on them as evidence
  for acyclicity and both leaned too hard.
- **The part I keep turning over:** Stage 0 already knew this. CONJECTURES.md's C2
  entry has carried "cycle-freedom under ALL strategies is a stronger, separate
  claim; this census only ever runs leftmost-outermost" since the first census. I
  rebuilt that census on a new rung, inherited the identical limitation, and did not
  transfer the caveat. Twenty stages of ledger discipline and the caveat was in the
  file I edit most often.
- Two consolations, neither of which cancels it. First, the caveat is now backed by
  a witness rather than a worry — that is a genuine upgrade, and it is the kind of
  thing that makes a caveat stick. Second, pure S is untouched, because C2 proved
  acyclicity with a measure and never depended on the census. Which is itself the
  lesson: the census generates conjectures, measures settle them, and I have twice
  now let census output stand in for a settled question.
- Tally, updated honestly: five under-estimates of difficulty, one over-estimate, two
  wrong forward specifications, and now one un-transferred caveat. The failure modes
  have moved outward — from rating work, to specifying work, to noticing that a
  method's known limits apply to its reuse. The common thread is that all four were
  cheap to check and none was checked before being relied on.
- Ranking: (1) **rung two under a non-LO strategy** — the hunt should be re-run
  reducing innermost or by a redex-fair strategy, since that is exactly where rung
  one's cycle hides and the tooling now runs fast enough to afford it; (2) the
  joinability-insensitive abstraction lifter for Tag → SK; (3) rung three {S,C};
  (4) transcription; (5) C6, declined a ninth time.

## 2026-07-24 — Stage 22: the right search, and validation before use

- Stage 21's ranking said "re-run the hunt under a non-leftmost-outermost strategy".
  On reflection that was still the wrong framing — swapping one strategy for another
  would have inherited the same class of blindness. Acyclicity is a property of the
  RELATION, so the search has to range over ALL one-step successors. The project
  already had that shape for pure S in Reachability.lean (`succs` + bounded closure +
  `onCycle?`), so this was reuse rather than invention.
- **Validated it before running it**, which is the direct consequence of Stage 21
  and the first time I have done this in the right order. `onCycleAny` finds
  `omegaSI`'s cycle — the kernel-proved one the LO detector provably misses. Two true
  negatives alongside so it is not just answering `some true` to everything. That took
  five minutes and it is the difference between data and noise.
- The result is a genuine upgrade, not just more of the same: every {S,B}-term up to
  8 leaves gets a VERDICT (nothing ran out of fuel) and none is on a cycle within a
  30-leaf cap, under any strategy. And it is cap-insensitive — n=7 gives identical
  verdicts at caps 30, 60 and 120. Fast, too: n=8 in about fifteen seconds where
  Stage 20's quadratic LO detector had been abandoned after ten minutes.
- **The limit is now in a different place, and that is the interesting part.** The
  remaining gap is the size cap: a cycle that swells past 120 leaves and returns is
  not excluded. For pure S that gap would not exist, because leafCount monotonicity
  confines every path inside a finite universe — which is exactly what makes
  Reachability.lean's bounded closure a genuine decision procedure there. {S,B} has
  no monotone quantity (Stage 20's theorem), so the same construction only gives a
  cap-relative verdict. **The absence of a monotone quantity degrades the census, not
  just the proof.** I had been treating Stage 20's negative as a fact about proof
  strategies; it is also a fact about how far searching can get.
- That connection is worth keeping because it says something about the ladder as a
  whole: rungs where a monotone quantity exists admit both proofs and decision
  procedures; rungs where none exists admit neither, and the census degrades in
  exactly the same way the proof does. Rung zero has one, rung two provably does not.
- Ranking: (1) test the cap limit directly — hunt for {S,B} cycles that EXCEED the
  cap by searching from larger seed terms, since that is the only remaining hole and
  the tooling is fast enough; (2) the joinability-insensitive abstraction lifter for
  Tag → SK; (3) rung three {S,C}, where the same tooling transfers immediately;
  (4) transcription (C1(a), C5); (5) C6, declined a tenth time.

## 2026-07-24 — Stage 23: the computational route closed, the analytic one opened

- Ranked task was "test the cap limit directly". Tested it, and it failed
  informatively: raising the census cap from 30 to 200 on the six explosive 7-leaf
  terms did not finish in ten minutes. That is the expected shape — those terms grow
  to ~130k leaves and the all-strategies closure under a generous cap explores
  enormous numbers of interleavings — but it is worth having measured rather than
  assumed, because it converts "the cap is a limitation" into "the cap is not
  liftable by brute force", which is what justifies switching approaches.
- So I switched to the analytic route, and Stage 20 had already left the pointer:
  its theorem rules out linear COUNTING measures, and τ is not a count. τ weights by
  POSITION — `2τ(a) + τ(b)` — which is exactly why it escaped that theorem. I had
  written that sentence in Stage 20 as a hint and then not followed it for three
  stages.
- τ turns out to behave beautifully on B and awkwardly on S, which is the useful
  asymmetry. On a B-reduction it strictly drops by `2τ(x) + 8 ≥ 10`, always — `B`
  duplicates nothing so there is no compensating term. On an S-reduction it moves by
  exactly `2τ(x) - 8`, so it drops iff the duplicated argument is light. Both are
  one-line `omega` proofs once the definition is unfolded; the content is entirely in
  choosing τ.
- That gives the C2 shape back. C2 could not use τ globally on pure S either — it
  isolated the ISOMETRIC fragment and dropped τ there. Here the isolable fragment is
  the τ-LIGHT one, and `sbLight_acyclic` is the analogue. It is a genuine positive
  result about rung two, and it narrows the remaining question from "is there a
  cycle anywhere" to "is there a cycle firing an S-reduction on a τ-heavy argument".
- Worth noticing how the three stages compose rather than repeat: Stage 20's negative
  (no counting measure) told me which class to leave; Stage 22's census bounded where
  a cycle can be; Stage 23's fragment bounds what a cycle must DO. None of them
  settles rung two and each narrows it differently. That is what a ladder rung is
  supposed to look like, and it is the first time in this program that three
  consecutive stages have accumulated instead of one correcting the next.
- Small tidy: added `RS.Acyclic.of_decreasing_measure` to Taxonomy as the dual of
  `of_strict_measure`. Stage 17 had inlined an ad-hoc copy inside
  `SI_no_decreasing_measure`; now there is one general lemma and both users take it.
- Ranking: (1) **hunt specifically for τ-heavy cycles** — the search space is now
  named, so seed the strategy-independent hunt only from terms that can fire an
  S-reduction on a τ-heavy argument, which should be far cheaper than the
  unrestricted cap-lift that just timed out; (2) rung three {S,C}, where τ should be
  computed the same way and may behave differently, since `C x y z → x z y`
  duplicates nothing either; (3) the joinability-insensitive abstraction lifter for
  Tag → SK; (4) transcription; (5) C6, declined an eleventh time.

## 2026-07-24 — Stage 24: the measure that can tell two rungs apart

- Ranked task was "hunt specifically for τ-heavy cycles". I started on it and the
  arithmetic pulled me somewhere better. Generalising τ to `τ_k(app a b) = k·τ_k(a) +
  τ_k(b)` gives S-delta `k(τ_k(x) − k²)`, so the light fragment GROWS with k — `S (S
  S)` is heavy at k=2 and light at k=3. Attractive, but the general-k lemmas are
  nonlinear in k and `omega` cannot do them; `ring` would, and this tree has no
  Mathlib. Tested that before building on it, which is the habit finally sticking.
  Recorded the family as arithmetic and moved on rather than triplicating the k=2
  machinery for k=3 and 4.
- Where it led instead: I noticed while computing deltas that `C x y z → x z y` has
  the SAME leafCount delta as `B x y z → x (y z)`. Both remove one leaf. So no
  counting measure can distinguish rungs two and three at all — which given Stage
  20's theorem (no counting measure is monotone on {S,B}) means counts are useless
  twice over here.
- τ distinguishes them, and sharply. B always lowers τ, by `2τ(x) + 8`. C's delta is
  `τ(z) − τ(y) − 8`, which is POSITIVE whenever the third argument is much heavier
  than the second — because permuting moves a heavy term from the outer position
  (weight 1) into an inner one (weight 2). I found two C-reductions with identical
  leafCount deltas and opposite τ deltas, 29→35 and 43→21, and guarded both. That
  pair is the whole point of the stage in two lines.
- Consequence for rung three: its light fragment needs TWO conditions where rung
  two's needed one, since the permuting rule also has to be restricted. So
  `scLight_acyclic` is a weaker foothold than `sbLight_acyclic`, and rung three is
  further from a proof than rung two — which is the opposite of what I would have
  guessed from the rules' surface similarity.
- Stage 22's genericity paid off exactly as hoped: `onCycleAny` is generic over the
  term type, so rung three's strategy-independent hunt cost one successor function.
  No cycle up to 6 leaves, every term verdicted. Writing that detector generically
  two stages ago to enable a validation has now also given a whole rung for free.
- The theme across 20, 23 and 24 is worth naming: **counts see size, positional
  measures see structure.** Stage 20 proved counts cannot settle rung two. Stage 23
  found τ handles B. Stage 24 finds τ also SEPARATES B from C where counts cannot.
  Three stages, one moral, and it arrived by accumulation rather than correction —
  the second such run in this program.
- Ranking: (1) the τ-heavy cycle hunt for rung two, which I deferred this stage and
  which is now the only narrowing left there; (2) rung three's C-heavy analogue of
  the same question; (3) the joinability-insensitive abstraction lifter for Tag → SK;
  (4) transcription (C1(a), C5); (5) C6, declined a twelfth time.

## 2026-07-24 — Stage 25: the highest-ranked item did not apply

- The seventh review put "read the tree-automata papers" first, with a sharp
  argument: Stage 6 surfaced them, I registered them, and then hand-rolled 1980s
  polynomial interpretations for eighteen stages without going back. That critique was
  fair. The papers still turn out not to apply, and finding that out took two fetches.
- The 2024 paper is **sole-combinator only** — one combinator, explicitly. My rungs
  are all two-combinator systems, so it is out on scope alone. Endrullis-Zantema is
  general TRS and does cover {S,B} and {S,C}, and even works on the S-rule. But:
- **both prove NON-TERMINATION, and my open questions are ACYCLICITY.** That is the
  crux and it took me a minute to see, because I had been treating "the literature's
  tooling for this problem class" as one bucket. It is not. Non-termination is about
  infinite paths; acyclicity is about returning ones. This program contains the proof
  they come apart — pure S is acyclic (C2, proved here) and non-terminating (external,
  Stage 6). A regular language closed under rewriting with no normal forms certifies
  an infinite path; it says nothing about return.
- So the eighteen-stage "gap" the review identified was not a gap. The field's
  automata methods target a neighbouring property, and measures are the right tool for
  mine. That is a better outcome than either "the papers solve it" or "I wasted
  eighteen stages" — but I could not have known which without reading them, and the
  review was right to insist.
- Worth keeping as a distinction I will need again: **a technique's problem CLASS and
  a technique's target PROPERTY are separate filters.** I checked class (does it handle
  two combinators?) and would have stopped there if the 2024 paper had been general.
  Property is the filter that actually excluded both.
- Item 2 went in: the τ threshold bootstraps. Chaining τ against leafCount — heavy
  S-reds need |x| ≥ 3, so they raise leafCount by ≥ 2, so a cycle needs at least two
  B-reductions per heavy S-reduction, so the τ budget forces average τ(x) ≥ 14, not
  4. Per-step facts proved; the summation is arithmetic and left informal, because
  classifying every step of a path needs a path-indexed induction with an accumulator
  per class.
- **And I wrote down why it stops**, which I think is the more valuable half.
  Iterating gives `T' = 5·f(T) − 1` where f is the least size admitting τ ≥ T. Max τ
  on n leaves is 2ⁿ−1, so f is logarithmic, so T' grows logarithmically and the
  iteration fixes around τ ≥ 24. τ grows exponentially in size while the constraint
  grows linearly. Recording the limit of an argument family costs a paragraph and
  saves someone re-deriving it — the same reason Stage 14's mis-framing was kept.
- Item 3 answered cheaply and negatively: no {S,B}-term up to 7 leaves acts as an
  identity on four structurally distinct probes. So rung one's cycle has no transport
  route into rung two at small size, which closes the chart's emptiest cell and is
  consistent with {S,B} being acyclic.
- Item 4, and I think it is the quiet correction of the stage: the spec says a rung is
  *"a publishable partial result that narrows where universality is lost"*. I have been
  reporting rungs 2 and 3 as OPEN, which is true and reads as failure. Against the
  stated purpose they are DELIVERED — rung 2 alone has a proved impossibility, an
  acyclic fragment, a bootstrapped necessary condition, a closed transport route, and a
  strategy-independent census. STATUS.md now leads with what each rung ESTABLISHED.
  Fifth time re-reading the spec changed how I was reporting rather than what I was
  doing.
- Ranking: (1) formalize the cycle summation, converting the bootstrap from arithmetic
  into a theorem — it is the last piece of rung two that is clearly reachable;
  (2) rung three's C-heavy analogue of the bootstrap; (3) the joinability-insensitive
  abstraction lifter for Tag → SK; (4) transcription (C1(a), C5); (5) C6, declined a
  thirteenth time.

## 2026-07-24 — Stage 26: redirected before building, and it paid

- Ranked task was formalising the τ ≥ 14 summation. I did the arithmetic first — the
  habit that has now caught three stages in a row — and it said: per-class path
  accounting, one accumulator per step kind, ~150 lines, to TIGHTEN a bound whose
  argument family I had myself proved caps near τ ≈ 24 one stage earlier. Tightening a
  known-capped bound is the least valuable thing available. Redirected.
- What I redirected to came from re-reading my own Stage 20 arithmetic: B-reduction is
  the only shrinking rule, so on the S-ONLY fragment leafCount is monotone. And
  monotone leafCount is exactly the ingredient C2 needed and {S,B} as a whole lacks
  (Stage 20's theorem). So C2's squeeze transplants to the sub-fragment verbatim: cycle
  forces leafCount constant, constancy forces atomic arguments, τ drops by 6.
- The formalisation detail worth keeping: the per-step lemma has to state BOTH halves
  in one conjunction — "leafCount never shrinks" AND "if leafCount is unchanged then τ
  strictly drops". Stating them separately does not work, because the path induction
  needs to pin leafCount across the whole path first and then reach back into the FIRST
  step for the strict drop. I tried it as two lemmas, saw the induction fail to close,
  and merged them. That is a small piece of proof-engineering knowledge that
  generalises to any squeeze argument.
- Result: `sbCycle_needs_B` — any {S,B} cycle contains a B-reduction. New, and
  independent of everything else known about rung two.
- **What I like about the state of rung two now is that the constraints COMPOSE.** A
  cycle must contain a B-reduction (26), must fire a τ-heavy S-reduction (23), and needs
  at least two B-reductions per heavy S-reduction (25). Three independent derivations,
  one joint condition. That is different from the earlier stretches where each stage
  corrected the last; this is the third accumulating run and the longest.
- Fourth occurrence of the mkElimApp motive error on `RS.Steps` at a concrete instance.
  Raw recursor, as in `iota_steps_le`, `RS.Discrete2_steps_eq`, `SI_no_decreasing_measure`.
  It is fully a known local idiom now and cost nothing.
- Ranking: (1) rung three's analogue — does {S,C} have an acyclic S-only fragment too?
  It should, by the identical argument, since C is also the only shrinking rule there;
  cheap and it would give rung three its second constraint; (2) the joint condition on
  rung two is now specific enough to guide a targeted search — hunt for cycles among
  terms that can host both a B-reduction and a τ-heavy S-reduction; (3) the
  joinability-insensitive abstraction lifter for Tag → SK; (4) transcription (C1(a),
  C5); (5) C6, declined a fourteenth time.

## 2026-07-24 — Stage 27: a second transplant, and a claim I checked before making

- Ranked task was rung three's S-only fragment, predicted to work "by the identical
  argument". Checked the arithmetic first: C's leafCount delta is −1, same as B, so C is
  {S,C}'s only shrinking rule and the S-only fragment has monotone leafCount. Prediction
  held, and the Stage 26 proof transplanted with only the names changed.
- I duplicated rather than abstracted, and wrote down why. The two S-only fragments are
  literally the same system — pure S over a two-symbol alphabet — so the honest
  generalisation is a term type parameterised by its atom set, plus transport lemmas.
  That is more code than the copy and adds indirection for exactly two instances. If a
  fourth rung appears I would abstract; at two, copying is right. Recording the judgment
  matters more than the judgment, since the next reader will notice the duplication and
  should know it was chosen.
- Rung three now has two constraints (τ-light fragment acyclic, and cycles need a
  C-reduction) plus the structural finding about τ separating it from rung two. That is
  a rung, by the spec's definition.
- **The part I am most pleased about is a negative I nearly skipped.** Stage 26's
  ranking said the composed condition on rung two "is now specific enough to guide a
  targeted search". Before building that search I measured whether the condition
  actually prunes. It does not: filtering seeds to terms containing a B with ≥ 5 leaves
  keeps 99.6% of 8-leaf terms. The reason is structural, not a bad filter choice — the
  condition constrains the STEPS a cycle contains, not the SEEDS a search starts from,
  and almost any moderate term can in principle reach such a step.
- That distinction is worth carrying: **a necessary condition on a path is not
  automatically a filter on starting points.** I had conflated them in the Stage 26
  ranking, and the conflation would have produced a "targeted" search identical in cost
  to the untargeted one, which I would then have reported as a targeted search finding
  nothing. The condition could drive pruning DURING exploration, which is a genuinely
  different algorithm.
- Score for the session's habit: three stages running where doing the cheap check first
  changed what I built (25: the papers didn't apply; 26: the ranked task was tightening
  a capped bound; 27: the composed condition doesn't prune). The habit is no longer
  occasional.
- Ranking: (1) pruning-during-exploration for rung two — the one use the composed
  condition genuinely has, and a real change to `onCycleAny` rather than a filter on its
  input; (2) the joinability-insensitive abstraction lifter for Tag → SK, still the only
  route to Goal 2's open instance; (3) transcription (C1(a), C5); (4) C6, declined a
  fifteenth time.

## 2026-07-24 — Stage 28: the accounting I kept deferring was not needed

- Ranked task was pruning-during-exploration, the one use Stage 27 had left the composed
  condition. Checked it first — fourth stage running — and it is not available. Sound
  pruning needs a localizable certificate that the seed is unreachable from a state, and
  every constraint I have on rung two is a global sum over a whole cycle. Global sums do
  not localize. So both uses I had claimed for the composed condition (seed filtering in
  Stage 26, exploration pruning in Stage 27) are gone.
- Then the useful part. While working out WHY the sums don't localize, I noticed the
  composed condition itself does not need the sums. I had been carrying "Σ over S-reds of
  #B(x) = #B-reds" as an unformalised summation since Stage 25 and treating its
  formalisation as a 150-line accounting job I kept deferring. The contrapositive is a
  squeeze: if no S-reduction duplicates a B, #B never rises and strictly falls on every
  B-reduction, so a cycle has no B-reduction, so it lives in the S-only fragment, which I
  proved acyclic two stages ago.
- **So the accounting was never needed.** Three stages of deferring a formalisation I had
  mis-scoped, and the fix was to state the negation as a fragment and squeeze it. That is
  the same move as Stages 26 and 27, applied one level deeper — three levels now: #B, then
  leafCount, then τ, each pinning the next.
- The engineering lesson from Stage 26 held and sharpened: the levels MUST travel in one
  invariant. I wrote it as three nested conjunctions and it went through; separating any
  level fails, because the path induction pins the outer measure across the whole path and
  then has to reach back into the first step for the inner strictness. Now confirmed at
  depth three, so it is a pattern rather than a coincidence.
- Pleasing side effect I did not plan: the no-B-duplication fragment strictly contains the
  S-only fragment, since it admits every B-reduction as well. So Stage 26's
  `sbSOnly_acyclic` is now a corollary of Stage 28's theorem rather than an independent
  result. The ladder's rung-two evidence got simpler as it got stronger, which is unusual
  and worth noting.
- Standing on the "check first" habit: four consecutive stages where checking changed the
  work (25 papers, 26 capped bound, 27 seed pruning, 28 exploration pruning). In three of
  the four, the check ALSO surfaced the better target — the checking is not just avoidance,
  it is where the redirection comes from.
- Ranking: (1) the joinability-insensitive abstraction lifter for Tag → SK — now clearly
  first, since rung two's constraints have converged to a proved syntactic condition and
  the remaining narrowing there needs a genuinely new idea rather than another fragment;
  (2) transfer the three-level squeeze to rung three ({S,C}'s no-C-duplication fragment),
  which should work by the same pattern; (3) transcription (C1(a), C5); (4) C6, declined a
  sixteenth time.

## 2026-07-24 — Stage 29: the deferred proposal, checked and refuted

- The joinability-insensitive abstraction lifter had sat at or near the top of my ranking
  since Stage 10 — nineteen stages — always as "the honest route to Goal 2's open
  instance", always deferred as research-grade. This stage finally checked it, fifth
  consecutive stage where checking came before building, and it does not work.
- What I built first, because any version of the proposal needs it: the abstraction as a
  RELATION rather than a function. `bwd_of_abstraction_rel`, with Stage 8's function
  version recovered as the special case `absR b a := (abs b = some a)`. That
  generalisation is correct, axiom-free, and genuinely required — a joinability-style
  abstraction cannot be a computed function, since "decodes to" becomes a semantic
  condition. So the infrastructure stands regardless.
- The relaxation has a price I had not anticipated: the relation must be FUNCTIONAL ON
  THE IMAGE of `enc`. With a function that was free (`abs (enc a) = some a` gives it
  immediately). With a relation it is a real hypothesis. And it is precisely where
  joinability dies.
- **`Joinable · (enc ·)` relates an encoded state to every source state it came from.**
  One line to prove: if `a` steps to `a'` then `enc a` reaches `enc a'`, so `enc a'` is
  joinable with `enc a` — and trivially with itself. So it relates `enc a'` to two
  distinct source states, and functionality fails as soon as the source has any
  nontrivial step. The proposal fixes drift by being so coarse that it cannot tell
  machine states apart at all.
- **The shape of the whole obstruction, which is what I want on record.** The two
  candidate abstractions fail in opposite directions. Syntactic is too FINE — copies
  drift, it loses track. Joinability is too COARSE — it collapses the trajectory. A
  workable abstraction sits strictly between and neither obvious construction is there.
  That is a much better description of Goal 2's blocker than "research-blocked", which is
  what I had been writing for ten stages without knowing which way it was blocked.
- Worth noting what this cost and bought: one stage, four axiom-free theorems, and the
  retirement of a proposal that had been consuming the top of my ranking for nineteen
  stages without ever being examined. Deferring it was defensible each individual time —
  it always looked expensive next to a cheap ladder rung — but nineteen consecutive
  defers of the same item is a pattern, and the item turned out to be cheap to REFUTE
  even though it would have been expensive to BUILD. Refuting is often the cheaper half
  and I should test that first more often.
- Ranking: (1) transfer the three-level squeeze to rung three's no-C-duplication
  fragment — cheap, mechanical, and gives rung three parity with rung two;
  (2) transcription (C1(a), C5), now the largest remaining item that is definitely
  achievable; (3) C6, declined a seventeenth time. Note criterion (a) has left the
  ranking: it is a stated obstruction now, not a task, and it should return only if
  someone has a candidate abstraction that is neither syntactic nor joinability-based.

## 2026-07-24 — Stage 30: abstracting at the right threshold, one stage late

- Ranked task was rung three's no-C-duplication fragment. Checked the arithmetic first
  (sixth stage running): `#C` falls by 1 on a C-reduction and rises by `#C(x)` on an
  S-reduction, exactly like `#B`, because C permutes without duplicating. So Stage 28's
  three-level squeeze transfers.
- But this would have been the FOURTH hand-written copy of the same argument, and in Stage
  27 I had written "if a fourth rung appears I would abstract; at two, copying is right."
  That threshold was wrong: what matters is the number of INSTANCES, not the number of
  rungs. Two rungs have produced four instances. So I abstracted before adding the fourth.
- The abstraction is `RS.Acyclic.of_three_level`, and finding it clarified what had
  actually been duplicated: the path lemma and the final contradiction, every time. The
  per-step lemmas were always genuinely different. So the generic lemma takes the per-step
  invariant as its hypothesis and all four instances collapse to one line each.
- **The part I did not expect: this is C2's argument.** C2 — pure-S acyclicity, the
  program's first resolved conjecture, Stage 5 Slice 2 — is a two-level squeeze
  (leafCount monotone, then τ strictly dropping on the isometric fragment). It is the same
  lemma with `m1` constant. Nine stages of ladder fragments have been re-deriving the
  shape of the program's own earliest theorem without my noticing, and abstracting made
  it visible. That is a better argument for abstracting than the line count was.
- Rung three now has the same three constraints as rung two, and at both rungs the
  no-X-duplication fragment strictly contains the S-only one, so the S-only results are
  corollaries. The evidence got simpler at both rungs as it got stronger — same effect as
  Stage 28 noted at rung two, now symmetric.
- Cost note for honesty: the refactor touched three working proofs. I did it in two steps,
  building between them, and both builds stayed green. Refactoring proofs is cheap when
  the generic lemma's hypothesis is exactly the existing per-step lemma's statement — and
  I chose the generic lemma's shape to make that true, which is worth doing deliberately
  rather than discovering afterwards.
- Ranking: (1) transcription — C1(a) (import the known 7-leaf non-normalization result)
  and C5 (λI conservation); the largest remaining definitely-achievable work, and both are
  labelled external so the deliverable is a machine-checked import, not a discovery;
  (2) C6, declined an eighteenth time. The ladder has converged: both rungs have three
  constraints, the shared machinery is factored, and further narrowing needs a genuinely
  new idea rather than another fragment — the same place criterion (a) reached in Stage 29.

## 2026-07-24 — Stage 31: the "external" label was hiding a five-line proof

- Ranked task was transcription: import C1(a) and C5. Checked feasibility first, seventh
  stage running, and C5 turned out not to be transcription at all. The tree can prove it.
- The argument assembled itself once I listed what was available. Confluence (Stage 1) plus
  a NORMAL target forces every term on an infinite sequence to reach that normal form.
  Monotonicity (Stage 2) then caps their sizes. `enum_complete` (Stage 6) makes the capped
  universe a finite LIST. Pigeonhole gives a repeat. C2 forbids repeats. Five ingredients,
  four of them already proved for other reasons, and the fifth a standard combinatorial
  lemma.
- **What strikes me is that every ingredient was built for something else.** Confluence was
  Stage 1's own goal; monotonicity was Stage 2's conservation-laws slice; `enum_complete`
  was built to unblock C1's minimality half in Slice 5 and reused for Goal 3's decidability;
  C2 was Slice 2's resolved conjecture. None was aimed at C5. The theorem was latent in the
  tree for roughly twenty-five stages.
- Fifth Classical.choice near-miss and the same trap as Stage 9. The natural pigeonhole uses
  `List.erase`, and both core erase lemmas report choice, because synthesising `LawfulBEq`
  from `DecidableEq` routes through it. I bisected rather than guessed — two three-line
  test theorems — then rebuilt on `List.filter` with `decide`, which never touches `BEq`.
  Also stated the pigeonhole NEGATIVELY, which keeps it constructive: the conservation
  proof wants a contradiction, not an existential, so `¬ (∀ i j, i < j → f i ≠ f j)` is
  exactly the right shape and needs no classical step.
- Lean note: `set ... with` is Mathlib, not core. Inlined the predicate.
- **The ledger lesson, which I think is the more important half.** The `external` status
  was added in Stage 6 to stop untested claims sitting as "open", and it worked — it caught
  C1 after nine stages. But C5 shows it can be wrong in the OTHER direction: a claim marked
  external because a famous theorem covers it, when a cheaper route existed inside the
  development. Marking something external closed my inquiry into whether the tree could
  prove it. So: an `external` label should record where a claim is KNOWN, not settle
  whether this development can prove it. I have updated the ledger's wording accordingly.
- Consequence for C1(a): its loop route has been waiting on C5 since Slice 3. It is no
  longer waiting. `no_normalForm_of_infiniteRed` means an infinite reduction sequence now
  suffices for non-normalization, with no external dependency.
- Ranking: (1) **C1(a) via an explicit infinite reduction** — build the sequence for `c1`
  directly. The frozen head (Slice 4) says the trajectory is `S A B` with `A` a fixed normal
  form forever, and `frozen_normalizes_iff` reduces the question to the payload; combined
  with C5 the target is now a Nat-indexed sequence rather than a self-embedding witness,
  which is a different and possibly easier object; (2) C6, declined a nineteenth time.

## 2026-07-24 — Stage 32: C1(a) down to one arithmetic gap

- C5 changed what C1(a) needs. Before Stage 31 the loop route waited on an external
  theorem; now `no_normalForm_of_infiniteRed` means an infinite reduction sequence is
  enough, so the whole remaining task is a reducibility invariant `P` with `P c1` and
  `P t → ∃ u, t ⟶ u ∧ P u`.
- Two things came out clean. First, the reducibility criterion: for K-free terms head spine
  ≥ 3 implies reducible, because the only leaf is `S`, so the head of any application chain
  is `S` and three arguments fire it. Second, the preservation arithmetic: firing `S f g x`
  leaves head spine `spineLength f + 2`, and with `k` trailing arguments,
  `spineLength f + 2 + k`.
- **So the gap is now one inequality.** If the redex sits under at least one further
  argument (`k ≥ 1`), the reduct has spine ≥ 3 unconditionally and reducibility propagates
  for free. Only the `k = 0` case — redex at the very head — needs `spineLength f ≥ 1`, and
  nothing in the tree bounds the first argument's spine below. That is a much sharper
  statement of C1(a)'s remaining difficulty than "no invariant is known", which is what the
  ledger has said since Slice 3.
- Measured it rather than assuming: `c1`'s payload spine along the frozen trajectory runs
  3,4,4,3,3,4,4,3,5,6,6,5,5,8,8,7,9,10,10,9. Never below 3, so the invariant holds
  empirically — and the awkward case does occur, so the gap is real rather than vacuous.
- Extended the self-embedding hunt to the LITERATURE's term, which I had not done before:
  the classic 14-leaf `S A A (S A A)` with `A = S S S` does not self-embed within 40 steps
  either, sizes growing 14, 20, 26, 35, 44, 53, 65. So the self-embedding route is
  witness-free at the canonical example too, not just at ours. Worth knowing — I had been
  half-assuming the literature's term would have the nice structure ours lacks.
- **A process failure to record.** My first draft of this stage had a fourth theorem
  claiming "spine falls by at most one per step", with a `sorry` in it. It is overreach:
  the reduct's spine is not determined without knowing which redex fired, and
  `reducible_of_head_spine` returns *some* reduct without controlling that. I removed it
  rather than trying to patch it. But I should not have written a `sorry` at all — thirty-one
  stages with a sorry-free tree and I nearly broke it by drafting a theorem before checking
  it was true. The habit that has served this project is checking BEFORE building, and I
  skipped it for that one lemma because it felt like an obvious corollary.
- Ranking: (1) the `k = 0` spine bound — the single remaining gap for C1(a), and now a
  self-contained arithmetic question rather than an open-ended invariant hunt;
  (2) C6, declined a twentieth time.

## 2026-07-24 — Stage 33: my own gap was an artefact

- Ranked task was the `k = 0` spine bound, which Stage 32 had called "the single remaining
  gap for C1(a)". Checked it before attacking it — eighth stage running, and the stage right
  after I nearly broke the sorry-free streak by *not* checking — and the gap dissolved.
- The error was mine and precise: `reducible_of_head_spine` says head spine ≥ 3 IMPLIES
  reducible. It does not say the converse. A term like `(S x)(g x)` has head spine 2 and can
  still reduce inside. So when I demanded head spine ≥ 3 be *preserved*, I was asking for
  strictly more than reducibility, and the `k = 0` case was the cost of that surplus rather
  than a fact about pure S. I had turned a sufficient condition into a required one without
  noticing.
- The replacement dropped out of C5's own proof. Inside `conservation` I had used: if `t`
  reaches a normal form then confluence sends every reduct there too, and monotonicity caps
  every reduct's size. Extracted, that is `leafCount_le_of_normalizes`, and its
  contrapositive is a criterion needing no invariant at all — **unbounded reduct sizes imply
  no normal form**.
- **Why this matters more than the theorem count suggests: the goal and the evidence now
  agree.** For thirty-odd stages the census measured SIZES — 120112 leaves at step 200,
  25.7 billion at fuel 1000 — while the stated target was an INVARIANT, and no invariant was
  ever observed. Those were different currencies. `bounded_of_normalizes` converts the
  census's own numbers into the right currency: any bound on those sizes would have been a
  normalization proof, so the explosion is evidence of exactly the right kind.
- And the new target is cumulative in a way the old one was not. Every larger reduct found is
  progress toward unboundedness. Slices 3, 4 and 32 all hunted invariants and produced
  nothing that composed — three separate negatives. That asymmetry is worth remembering when
  choosing between two formulations of the same open problem: prefer the one where partial
  results accumulate.
- Still open: the growth step — from any reduct, reach a strictly larger one. I want to be
  clear that this is not obviously easier than the invariant, only better aimed. What has
  improved is that partial progress now counts.
- Ranking: (1) the growth step for `c1` — from any reduct of `c1`, reach a strictly larger
  reduct. The frozen head (Slice 4) may help here in a way it did not help the invariant:
  `frozen_normalizes_iff` reduces `c1` to its payload, and the payload's sizes are what grow;
  (2) C6, declined a twenty-first time.

## 2026-07-24 — Stage 34: built a theorem, measured it, threw it away

- Ranked task was the growth step. It split into two halves with very different characters,
  and the interesting part of the stage is that I kept one and deleted the other.
- The half I kept, `normalizes_of_no_growth`, is choice-free and says the essential thing:
  a pure-S term whose reducts never grow must normalize, so **growth is necessary for
  non-termination**. τ does all the work — each step on a size plateau strictly drops it,
  and a Nat cannot drop forever. The only care needed was recursing on `stepOnce` instead of
  case-splitting on `NormalForm`: `stepOnce` is computable and certified on both ends, so
  "normal or reducible" is decided rather than assumed. That one choice of formulation is
  what kept the proof constructive.
- The half I deleted completed the equivalence — no normal form implies unbounded reducts.
  It compiled. Then the axiom audit reported `Classical.choice` in all three theorems, and
  the cause is intrinsic rather than accidental: the hypothesis is NEGATIVE (`¬ ∃ normal
  form`) and the conclusion POSITIVE (`∃ arbitrarily large reduct`), so it needs
  `¬∀ → ∃`. Five earlier `Classical.choice` encounters in this project were all
  instance-layer accidents that a rewrite fixed. This was the first genuine one.
- I removed it. The reasoning: the tree has advertised no `Classical.choice` since Stage 0,
  in STATUS.md and README and every axiom audit; the equivalence is a nice-to-have rather
  than a tool; and the direction that IS a tool was already choice-free. Shipping a
  clearly-labelled classical theorem would have been defensible, but it would have cost a
  property I have repeatedly claimed, for something nothing else depends on. Not worth it.
- **What I did instead of leaving a gap: worked the constructive route out and wrote it
  down.** Replace the negative hypothesis with the positive "every reduct is reducible";
  build the trajectory from `stepOnce`, which is computable so no choice is needed; prove
  `leafCount (f k) = leafCount t → tau (f k) + k ≤ tau t` by induction on k; instantiate at
  `k = tau t + 1` where the bound is contradictory. The refuted proposition is DECIDABLE, so
  monotonicity upgrades it to strict growth constructively. So the equivalence is
  constructively true and the file now says how — which is a better artefact than either the
  classical proof or an unexplained hole.
- Worth noting how the two halves differ in what they need. Necessity of growth reasons
  FORWARD from a term (constructive). Sufficiency of unbounded growth reasons forward from a
  bound (constructive, Stage 33). Only the negative-to-positive direction needs classical
  logic — and that is precisely the direction nothing uses.
- Ranking: (1) the constructive equivalence, now fully specified — three steps, all
  mechanical, no research content; (2) C6, declined a twenty-second time. Note C1(a) itself
  is unchanged: it still needs a proof that some specific term's reducts are unbounded, and
  Stages 33-34 have only made the target precise and shown it is the right target.

## 2026-07-24 — Stage 35: the obstruction I declared intrinsic was not

- Ranked task was building the constructive route Stage 34 had specified. It worked, and it
  also corrected Stage 34's diagnosis, which is the part worth recording.
- Stage 34 said the converse direction was intrinsically classical because it goes from a
  negative hypothesis to a positive conclusion, needing `¬∀ → ∃`. That was too coarse. The
  `by_cases` I had written was on `∃ u, t ⟶* u ∧ leafCount t < leafCount u` — a statement
  about ALL reducts, and yes, undecidable. But the thing I actually needed was `∃ v, u ⟶ v`
  for a FIXED `u`, and that is decided by `stepOnce`. Routing through "every reduct is
  reducible" makes the whole chain constructive.
- So the lesson is narrower and more useful than "negative-to-positive needs choice": it
  depends on WHICH quantifier. A quantifier over one term's successors is decidable; one over
  all reducts is not. I had lumped them together and generalised from the wrong one.
- Stage 34's decision still looks right to me. Removing the classical proof preserved a
  property I had claimed since Stage 0, and it cost one stage. Had I shipped it with a label,
  the tree would now carry a `Classical.choice` dependency that this stage shows was never
  necessary — and nobody would have gone back to remove it, because a labelled axiom looks
  settled. **Declining to ship kept the question open, and the question had a good answer.**
- The proof itself is pleasant. `iter` is the trajectory as a total function, stalling at a
  normal form. `tau_budget` says: if the trajectory has not grown by step k, τ has paid k
  units, because every plateau step strictly drops τ. Then the growth step is found by simply
  LOOKING at index `tau t + 1`, where the budget is exhausted. No search, no case analysis —
  an index computed from the measure.
- Result: **for a K-free term, no normal form is the same thing as unbounded reducts.** That
  closes the framing question Stages 32-35 have circled. The census's currency and the
  conjecture's currency are the same currency, proved.
- Ranking: (1) C1(a) itself — with the equivalence in hand, the remaining task is exactly
  "exhibit a K-free term whose reducts are unbounded", and `unbounded_of_all_reducible` says
  it suffices to show every reduct of that term is reducible. That is a positive, decidable-
  per-term condition, which is a better target than either the invariant (Stage 32) or the
  raw size claim (Stage 33); (2) C6, declined a twenty-third time.

## 2026-07-25 — Stage 36: four stages of reformulating one problem

- Ranked task was C1(a) via "every reduct is reducible", which Stage 35 had called a better
  target than the invariant or the size claim. Checked it first — ninth stage running — and
  the claim was wrong in a way worth making permanent.
- All three are equivalent, and so is the invariant form. The sharpest bit: if every reduct of
  `t` is reducible, then `fun u => t ⟶* u` IS a reducibility invariant, with `stepOnce` as its
  successor function. So the invariant route (Slices 3, 4, Stage 32) and the positive route
  (Stage 35) were never different problems. Nor was the size route (Stage 33), by Stage 35's
  equivalence.
- **So Stages 32, 33 and 35 each swapped C1(a) for a provably equivalent statement and I read
  each swap as progress.** Each felt like progress for a real reason — the size criterion did
  match the census's currency, the positive form is decidable per term — but matching the
  evidence better is not the same as being closer to a proof. I want that distinction on
  record because it is the subtlest error this project has produced. It is not an overclaim, a
  mis-estimate, or an untransferred caveat. It is mistaking a change of coordinates for
  motion.
- Made it a theorem rather than a note. `c1a_formulations` proves the four-way equivalence
  constructively, which means the cycle cannot repeat: any further reformulation along these
  lines is provably a restatement. Closing C1(a) needs a new fact about pure-S reduction — a
  SOURCE, not another bridge. The tree now has every bridge and no source.
- Also wrote down, in the same place, what the program has actually contributed to C1(a):
  C1(b) proved, C5 proved, the frozen head proved, this equivalence, and three honest
  negatives. That matters because "the reformulations were not progress" could be misread as
  "nothing was achieved", and the two are quite different. The bridges are real theorems; they
  just are not the thing.
- Ranking, and I want to be careful here rather than name another reformulation:
  (1) **a source, not a bridge** — the only untried route with genuinely new content is
  constructing a term with a self-embedding by design rather than searching for one, which
  pass 2 registered as "construct-don't-search" and which no stage has attempted. It is the
  one item on the board that could produce an infinite reduction rather than relate the ways
  of describing one; (2) C6, declined a twenty-fourth time.

## 2026-07-25 — Stage 37: the last untried route, tried

- Stage 36 had cleared away the reformulations and left exactly one item with new content:
  construct a self-embedding rather than search for one. Registered as "construct-don't-search"
  in the second ideonomy pass, never attempted in thirty-five stages.
- Before attempting a construction I searched the design space, because Slices 3 and 4 had only
  ever checked `c1` and `c2` — two terms, one strategy, 120 steps. A systematic sweep is cheap
  with the existing tooling and it settles whether construction is even needed. It found
  nothing: no pure-S term up to 8 leaves reappears inside its own leftmost-outermost trajectory
  within 200 steps, and — the row that matters — no term up to 6 leaves does so under ANY
  strategy.
- I included the all-strategies row specifically because of Stage 21, where validating a
  leftmost-outermost cycle detector revealed it provably misses cycles that exist in the
  relation. An LO-only negative here would have inherited exactly that weakness, and I would
  have reported it as stronger than it was. Using the bounded closure costs more but the
  evidence is of a different kind.
- **What the result does and does not do.** It upgrades the loop route from "unexplored" to
  "searched and empty where searchable", which is a real change in the ledger's standing. It
  does not show self-embedding is impossible, and I want to be careful there: no obstruction is
  proved and none is apparent to me. C2 rules out the trivial context and nothing more.
- So C1(a) is in an unusually well-characterised position for an open problem. Every bridge
  between its formulations is proved (Stage 36). Its dependency is discharged (C5, Stage 31).
  Its minimality half is proved (Slice 5). Its trajectory's structure is proved (frozen head,
  Slice 4). And all three candidate sources — invariant, self-embedding, unbounded growth — have
  been searched at the sizes searchable and come back empty. What remains is genuinely a
  research question about pure-S reduction, not a gap in this development.
- Worth recording as the honest summary of thirty-seven stages on C1: the program has
  contributed a great deal AROUND the conjecture and nothing that closes it, and it can now say
  precisely why — the missing ingredient is a source of infinite reduction, and none exists at
  any size a search reaches.
- Ranking: (1) prove self-embedding IMPOSSIBLE in pure S — the only remaining move that would
  change C1(a)'s status, since it would close the loop route for good and force any future
  attempt onto unbounded growth without a witness. Genuinely open, and I have no candidate
  argument; (2) C6, declined a twenty-fifth time.

## 2026-07-25 — Stage 38: "none is apparent" was wrong, at depth one

- I ranked "prove self-embedding impossible" first while writing that I had no candidate
  argument. Attempting it anyway found one immediately for the one-step case, which is a small
  embarrassment worth recording: I had reached for measures, found the space closed (correctly —
  a decreasing measure would refute C1(a)), and concluded *no obstruction is apparent* rather
  than *no measure obstruction is apparent*. The structural argument was two lines of thought
  away and I had not tried it because the previous eleven stages had all been measure work.
  The lesson is the same one Stage 36 taught in a different costume: the technique I last used
  is not the technique the problem wants.
- The argument itself is short. The reduct of a redex never contains that redex — the reduct's
  subterms are enumerable (`f x`, `g x`, the reduct, and subterms of the three arguments) and
  every candidate forces `x = g x` or `f = S f g`, which no term satisfies. Congruence lifts it,
  and the lifting works because subterm is transitive: `app f u` inside `f'` gives `f` inside
  `f'`, which is the induction hypothesis. No arithmetic beyond "a proper subterm is smaller".
- Two conveniences fell out. `selfEmbed_leafCount_lt` turns Stage 37's prose ("C2 forces the
  context to be non-trivial") into a theorem, and `isSubterm_iff_Subterm` retro-fits kernel
  meaning onto Slice 3's and Stage 37's Bool guards — they were always about a search routine
  and are now about the relation.
- Naming note: `Sub` is core Lean's subtraction class, so the relation is `Subterm`. The clash
  surfaced as "`Sub` has already been declared", which failed the whole inductive and cascaded
  into fifteen downstream errors — a reminder that a name collision in an `inductive` is not a
  local problem.
- **I want to be precise about what did not lift.** The multi-step induction has a clean shape:
  split the occurrence of `t` by position relative to the last redex; off the redex you get a
  shorter self-embedding and minimality closes it. Three residual shapes survive — `t` contains
  the reduct, `t = f x`, `t = g x` — and none is contradictory on its face. Size cannot kill
  them because self-embeddings are allowed to grow, and acyclicity cannot because those `t` need
  not recur. So this is a base case with no inductive step, and I should not represent it as
  nearly-done. Recording the three shapes is the useful output: anyone resuming knows what to
  attack.
- One thing the failure does settle, and it is worth stating positively: the missing ingredient
  is **not** a measure. That is now an argument rather than an observation, since a measure
  falling on every pure-S step would prove strong normalization and hence refute C1(a).
- Ranking: (1) attack the three residual shapes — specifically `t = f x` and `t = g x`, which
  are the constrained ones, since they say the whole self-embedding term is a *one-application*
  combination of pieces of the last redex, and that is a strong structural demand that may well
  be contradictory when combined with `t ⟶⁺ v`; (2) C6, declined a twenty-sixth time.

## 2026-07-25 — Stage 39: I ranked the empty half first

- Formalizing Stage 38's prose went cleanly. The organising fact is smaller than I had it in my
  head: a step rewrites ONE position, so a subterm of the result is classified by its position
  relative to that one — disjoint, above, below. That is `Step.subterm_split`, and the three
  residual shapes are just the "above" and "below" branches after the redex's own arguments are
  pushed back into the source. Axiom-free, including `propext`, which is unusual in this tree and
  reflects that nothing here touches arithmetic.
- Then I measured, and the measurement inverted my own ranking from yesterday. I had ranked
  shapes B and C (`t = f x`, `t = g x`) first, on the reasoning that requiring the whole
  self-embedding term to be a one-application combination of pieces of the last redex is a strong
  structural demand likely to be contradictory. **The demand is so strong the shapes are empty** —
  zero instances at every size up to 8 leaves, and empty without the side condition too. Shape A
  meanwhile has 1, 4, 19 instances at 6, 7, 8 leaves and is growing.
- So my reasoning was correct and my conclusion was backwards. "This shape is heavily constrained"
  argues that it is *cheap to eliminate*, not that eliminating it is *valuable*. Value depends on
  whether the shape is carrying the difficulty, and a constrained shape is exactly the one that
  is not. I had conflated tractability with importance — and had I not measured first, I would
  have spent the stage proving two shapes impossible and reported "residue narrowed from three to
  one" as progress toward closing the induction, when it narrows nothing that matters.
- This is the ninth or tenth consecutive stage where checking the cheap thing before building
  changed what got built. I should stop treating that as a happy accident.
- Getting the probe's QUESTION right took a false start worth recording. My first instinct was to
  search for full residual configurations `t ⟶* v ⟶ w` with `t ⊴ w` and `t ⋬ v`. That is
  guaranteed to return zero, and not for an interesting reason: the residual case is a case
  analysis OF the self-embedding hypothesis, so any instance would BE a self-embedding, which
  Stage 37 already searched for. The measurable question is the weaker one — is each shape's own
  structural demand satisfiable among a term's reducts at all — and only that one distinguishes
  the shapes.
- Lean note: `cases` on an indexed hypothesis whose index IS one of the constructor's fields (as
  `r' = x` is for the K root-redex) silently refuses to name that field, and reports it as an
  unknown identifier at the use site rather than as a binder error. Cost three attempts before I
  extracted the shape as a disjunction of equations instead. Third entry in the "when `cases`
  fights the indices, go around it" family, after the `mkElimApp` motive failures.
- Ranking: (1) shape A — the surviving one. A self-embedding's last step must put `t` strictly
  ABOVE the reduct it fires, meaning `t` contains `f x (g x)` while `S f g x` sits in `t`'s own
  ancestor `v`. I have no argument, and the honest note is that the 1/4/19 growth means this is
  not going to be emptied by measurement either; (2) C6, declined a twenty-seventh time.

## 2026-07-25 — Stage 40: the argument was in what I had thrown away

- Yesterday I ranked shape A first and wrote that I had no argument. The argument was already in
  the tree, discarded. `Step.subterm_split`'s middle disjunct says "s contains the reduct" — I
  wrote that lemma, and I wrote it too weak. What is actually true is that a subterm sitting above
  the redex is the image of the subterm of `v` at the same position, under the very step being
  fired. So it is not "t contains something", it is `∃ u ⊴ v, u ⟶ t`. Once stated that way the
  case kills itself: `u` self-embeds one step earlier than `t`, and backward steps cannot recur
  because leaf count never rises and τ falls when it stalls.
- The pattern is worth naming because it is now the third time: **I lost the result by recording a
  consequence instead of the fact.** Stage 38 recorded "no obstruction is apparent" when it meant
  "no measure obstruction". Stage 39 recorded three shapes as prose before turning them into a
  theorem. Here I recorded "contains the reduct" when the position argument gave something
  strictly stronger for free. Each time the weakening was invisible because the weaker statement
  was true and sufficient for the immediate goal.
- The descent needed no new theory, which surprised me. `tau_lt_of_isometric_step` is the engine
  of C2, `smallTerms` and `length_filter_lt_of_witness` are Goal 3's decidability plumbing, and
  `mem_smallTerms` rests on the census's `enum_complete`. Four separate pieces of the tree, all
  built for other reasons, and the rank falls out of composing them. This is the second time (C5
  was the first) that a result arrived by assembling existing parts rather than by adding.
- One design choice paid off. My first plan needed a SHORTEST path so that `t ⋬ v` came for free,
  which would have meant a length-indexed reduction relation and a nested induction. Then I noticed
  the case `t ⊴ v` also descends — the TARGET moves back one step, and the rank is a function of
  the target. So one measure covers both cases and there is no path-length bookkeeping at all. I
  should look for that simplification earlier; "which of my hypotheses am I only using to make the
  induction go" is a question worth asking before writing the induction.
- Seventh Classical.choice encounter, and two new variants, both from `omega`. Case-splitting a
  disjunctive HYPOTHESIS costs the axiom; so does a disjunctive GOAL once a conjunction is nested
  in it, though a bare disjunctive goal is fine. `#print axioms` caught both, as it has caught all
  seven; review has caught none. Fixed by splitting by hand and giving the witnesses as terms.
- **Where this leaves C1(a).** The loop route is down to one shape, and it is the shape with zero
  instances up to eight leaves. That is a much better position than Stage 37's, and I want to be
  careful not to oversell it: `HalfShape` being empty is a MEASUREMENT, and the route being closed
  requires a proof. Nor would closing the loop route prove C1(a) false — an infinite reduction need
  not be periodic, so pure S could still diverge with no self-embedding anywhere.
- Ranking: (1) prove `HalfShape` uninhabited. It is a sharp, self-contained question with no
  reduction theory left in it: can a term `f x` have a reduct containing `S f g x`? The size
  arithmetic is tight (the redex outweighs the term by `1 + |g|`) and `f`, `x` are `t`'s own
  children, so there is more structure here than in anything shape A offered. If it goes through,
  the loop route to C1(a) is dead outright and that is a publishable negative; (2) C6, declined a
  twenty-eighth time.

## 2026-07-25 — Stage 41: the guard read stronger than it was

- Before attempting the proof I re-read what the `HalfShape` measurement actually guarantees, and
  found I had overstated it. `closureStep` filters reducts by `leafCount ≤ bound`, so a capped
  closure reports SATURATION after silently discarding everything bigger. The cap-24 guard
  therefore says "no witness among reducts reachable through terms of ≤ 24 leaves", and I had been
  reading it as "no witness". That matters here more than it usually would, because a `HalfShape`
  witness must be `1 + |g|` leaves heavier than `t` — the ceiling is precisely where one would sit.
- Raising it: cap 40 to eight leaves, cap 60 to seven, and a leftmost-outermost probe running 300
  steps under a 4000-leaf ceiling. All empty. The LO probe is worth keeping alongside the closure
  because the trajectories genuinely explode — the largest reduct visited has 3994 leaves — so it
  reaches a size range no closure search here can, at the cost of covering one strategy. The pair
  of probes has complementary blind spots, which is the most I can get cheaply.
- I should generalize the lesson rather than just fix the number. Every capped search in this tree
  reports "clean" the same way, and "clean" always means "clean below the cap". Stage 21 taught the
  strategy version of this (an LO hunt is blind to cycles that exist in the relation) and I
  transferred that one. I did not transfer the size version, even though it is the same shape of
  error. When a probe has a parameter, the finding is about the parameter.
- On the proof: backward induction along the path is right, and it comes down to an invariant on
  the requirement. `|requirement| > |t|` survives three of four sub-cases, and the two interesting
  ones are pleasantly rigid — a reduct half FORCES the bigger redex's third argument to be `x`
  itself and grows by two leaves, and a root redex FORCES the shape `S (S f) b g` with `x = b g`,
  which shrinks the third argument. Both are the kind of tight forcing that usually means an
  argument is close.
- It is not close, and I want to say why rather than leave the impression. The fourth sub-case is a
  step *inside* the requirement, and pure-S reduction grows, so the predecessor can be much lighter
  than what it produces — exactly the mechanism the invariant needs to exclude and exactly the
  mechanism C1(a) is about. Three controlled cases plus the hard one is not most of a proof; it is
  the easy three quarters. Every hard case in this development has been the growth case, and I
  should stop being surprised by that.
- Ranking: (1) the fourth sub-case — can a term of at most `|t|` leaves reduce, at its own root,
  into the left spine of `S f g x` where `t = f x`? It is a sharper question than any of the three
  shapes were, and the forcing lemmas suggest the answer is no; I have no argument. (2) C6, declined
  a twenty-ninth time.

## 2026-07-25 — Stage 42: the linkage clause I nearly shipped without

- Two results, and one near-miss that is the more useful entry.
- The results. `step_growth_eq` says a pure-S step grows a term by exactly `|c| - 1` for the
  duplicated argument `c`. That is Stage 2's monotonicity made quantitative, it was four lines by
  induction on the step, and it should have existed twenty stages ago — every size argument in this
  tree has been reaching for it and settling for the inequality. And `reduct_half_lt` collapses
  Stage 41's `app3_S_reduct_half_grows` to a general fact needing nothing about S-shapes: a reduct
  half is always lighter than its redex. I had proved the special case because I was looking at
  `S f g x` specifically, which is the third time this week that looking at the instance cost me
  the general statement.
- Together they turn Stage 41's "fourth sub-case, open" into a size condition on one subterm: going
  backwards is safe unless the step duplicated something at least `|s| + 1 - |t|` leaves heavy. That
  is a better-shaped gap. It is also, unmistakably, the gap where the actual difficulty of C1(a)
  lives — big duplication is the only way pure S grows.
- **The near-miss.** I first stated the invariant theorem as "one step back there is still some
  requirement in `v'` outweighing `t`", and it built, and it was nearly vacuous. Every reduct of `t`
  outweighs `t`, so `s' = v'` satisfies that at every point of the path except the start. I caught
  it while writing the ledger entry, not while writing the proof, and only because I asked what the
  theorem would let me DO. The fix is the linkage clause: the new requirement must be `s` itself, or
  reduce to `s`, or be the redex `s` is a half of. With linkage the induction is real, because at
  the path's start the requirement must be a subterm of `t`.
- This is the fourth instance of the same failure in five stages: recording something true but too
  weak to use. "No obstruction is apparent" (38), three shapes as prose (39), "contains the reduct"
  (40), and now an unlinked existential. The pattern is specific enough to test for: after stating a
  lemma, ask whether a TRIVIAL witness satisfies it. `s' = v'` would have failed that test
  instantly. I am adding that check to how I write these, because reading the proof does not catch
  it — the proof of the weak statement is perfectly correct.
- Also strengthened `selfEmbed_imp_halfShape` to bound its witness by the size of the self-embedding
  term. Free from the descent's structure, and it opens a second route: chase the requirement's shape
  instead of its size, and the path's start yields a self-embedding of something strictly smaller
  than `t`, which the size bound converts into an induction on term size. Two of three start-cases
  work; the third does not, so I am recording it as a route.
- Ranking: (1) the third start-case of the shape route — the requirement hiding inside `x` rather
  than being `t` or inside `f`. It is the one place where `P ⊴ x` gives no relation between `P` and
  the term `P` reduces to, and closing it would complete an induction on term size rather than
  leaving a size condition to check. That is the better of the two routes because its remaining gap
  is combinatorial rather than about growth; (2) C6, declined a thirtieth time.

## 2026-07-25 — Stage 43: the hour, and what it cost not to have spent it

- Nathan asked whether the frustration in these entries was the problem being hard or the approach
  being wrong. Reviewing it properly: the approach was wrong, in one specific way. Every stage's
  ranking came from the previous stage's proof structure, so the selection of what to work on was a
  closed loop with no external check. C1(a) had the best local gradient — clean theorem, clean next
  question, every time — and I followed the gradient for ten stages into a census artifact that my
  own STATUS.md describes as low-materiality with prior art "discoverable in an hour". Stage 39
  caught me conflating tractability with importance at the object level; I was doing the same thing
  one level up, to my own ranking, and did not notice.
- The hour took about ten minutes. Endrullis and Zantema state the ground-loop theorem as a known
  fact in the second example of their paper, citing Waldmann 2000. Stages 37–42 re-derived it and
  stopped one size condition short.
- And then the same paper handed over the tool. Their Theorem 4 — non-termination iff a recurrence
  set exists — plus a five-state tree automaton for the S-rule. **C1(a) is now proved here.** The
  entry that has said `external` since Stage 0 says `PROVED`.
- The one engineering decision worth recording: I determinized their automaton by hand before
  formalizing. Their version is nondeterministic, so the interpretation of a term is a SET of
  states, and the quasi-model condition is a set inclusion — which in a zero-dependency development
  means building list-based set machinery, distributivity of the transition over unions, and
  monotonicity lemmas for all of it. Determinizing costs exactly one state (six instead of five)
  and deletes all of that: the interpretation is a function, the order is on six elements, and every
  side condition is `cases <;> decide`. It built on the first attempt. Sixteen lines of
  paper-arithmetic beforehand replaced what I estimate was a day of list lemmas.
- Second decision: I did not take the paper's route for "every accepted term has a redex". They
  build a product automaton and check language inclusion. But reaching the accepting state forces a
  left spine of at least three, and this tree already proves that a K-free term with spine ≥ 3
  cannot be normal (`SNF.spineLength_le`, Stage 2). Reading the shape off the transition table was
  three small lemmas. Reusing what is already proved beat importing the general construction, which
  is the same lesson C5 taught at Stage 31.
- The cross-check matters to me and I made it a guard rather than a remark. The certificate is a
  claim about an automaton; the census evaluator is separate code. Running the witness shows leaf
  count climbing 12 → 776 in forty steps. If those two mechanisms disagreed, one would be wrong,
  and I would rather the build say so than a comment claim it.
- Honest limits. The certificate is not tight — twelve leaves against C1(b)'s proved floor of seven
  — and the automaton rejects `c1` and `c2`, so the two census candidates are still individually
  open. And the prize question is untouched by all of this: divergence is not universality.
- Process change, and this one is the actual deliverable of the day: the end-of-stage ranking gets
  checked against STATUS.md and the spec, not against the last proof. The four goals are the
  external check that ideonomy used to provide and that I stopped applying.
- Ranking, now from the spec rather than from the last proof: (1) **ladder rungs 2 and 3** — spec
  Stage 5's second component, "each rung a publishable partial result". The tool is the one this
  stage just built. My notebook's moral was "counts see size, positional measures see structure",
  and I proved no monotone counting measure exists for {S,B} and closed the τ route; the missing
  third category is FINITE-STATE invariants, and Geser–Hofbauer–Waldmann–Zantema (Inf. Comput. 2007)
  is the termination-direction literature for exactly that. (2) Goal 2's `Simulation` gap, left
  legible on purpose in `Calibration.lean`. (3) C6, declined a thirty-first time.

## 2026-07-25 — Stage 44: the new process rule earns its keep immediately

- Yesterday's process fix was to rank against the spec rather than against the last proof. Its first
  output was rungs two and three, which is right. Its first lesson is that ranking correctly does
  not make the plan correct: my stated tool for those rungs was wrong, and one search plus one
  theorem showed it.
- I said finite-state invariants were the missing third category after counts and positional
  measures. So I searched for them exhaustively at up to three states before writing any Lean. They
  exist in quantity — 154 for {S,B} with a strictly dropping step — and I was wrong that they would
  all reduce to facts already here. Only 58 of the 154 factor through B-freeness and capped spine
  length. There is real structure in the other 96.
- Then I worked out what one would BUY, which is the step I should have done before the search and
  certainly before the ranking. A non-increasing measure excludes its strictly-dropping steps from
  cycles and nothing more. Emptying the cycle space would need every step to drop, and C1(a) now
  makes that impossible for anything containing S. So the whole category is a constraint generator,
  not a proof method, for this problem. Both facts are theorems now rather than remarks
  (`RS.no_decreasing_measure_of_infinite`, `RS.no_return_of_strict_drop`), because I have learned
  what happens when I leave that kind of claim in prose.
- The satisfying by-product: `no_decreasing_measure_pureS` says C2's three-level squeeze was FORCED.
  At the time it felt like an ingenious construction; it was the only available shape. That is worth
  knowing about the other rungs before spending stages hoping for something simpler.
- The underlying mistake was conflating two literatures under "tree automata". Endrullis–Zantema
  prove NON-termination, and a bounded certificate is fine there precisely because you are
  exhibiting an infinite path, not ruling one out — which is why it transferred so cleanly to C1(a)
  and why I over-generalised from that success. Proving termination with automata is match-bounds:
  well-foundedness comes from a height annotation being bounded over the reachable set. Different
  mechanism, much bigger build. One tool solved C1(a) in an afternoon and I assumed its neighbour
  would solve the rungs.
- Lean caught something I want to record. I wrote `not_on_cycle_of_strict_step` with a hypothesis
  `B.step b b'`, and the unused-variable warning showed the proof never touched it — the fact needs
  only the measure drop. That is the "trivial witness" test from Stage 42 arriving as a compiler
  warning instead of as self-review. I renamed it and dropped the hypothesis. Two of my last three
  overclaims would have been caught by simply reading the warnings I was filtering out of the build
  output; I should stop grepping them away.
- **Where this leaves the rungs.** Both remain open, and now with a proved account of why: no single
  measure can work, no bounded invariant can finish, and the two open routes are a genuine
  match-bounds implementation or an unbounded well-founded measure nobody has found. That is a
  better-characterised open problem than yesterday and I am not going to pretend it is closer.
- Ranking, against the spec: (1) **Goal 2's `Simulation` gap** — the spec calls the taxonomy "the
  intellectual center", the gap is documented on purpose in `Calibration.lean` (the positive side
  certifies SK realising λ-style bodies, not SK hosting a known-universal MACHINE), and the
  adequacy machinery for it already exists (`RS.bwd_of_abstraction_rel`, `Simulation.ofAbstraction`,
  `universalReach_extend`). It is bounded work on the spec's declared centre, which is more than can
  be said for a match-bounds framework. (2) rungs 2/3 via match-bounds, as a deliberate multi-stage
  project rather than a hoped-for corollary. (3) C6, declined a thirty-second time.

## 2026-07-25 — Stage 45: the untried route was the cheap one

- Ranking against the spec sent me to Goal 2, the declared "intellectual center", where the blocker
  has been adequacy since Stage 8. Reading my own probe files properly was most of the work: Stage 10
  found drift, Stage 11 half-fixed it, Stage 13 refuted the fix and named three routes, two dead. The
  third — "read only the live spine, ignore subterms destined for a K-discard" — had sat untouched
  for thirty-two stages with no one noticing it was a one-line idea.
- It is one line. Contract the K-redexes before reading. A doomed copy collapses regardless of what
  it drifted into, so drift stops being a problem to solve and becomes a thing you cannot see. Stage
  10 tried to PREVENT drift and Stage 13 showed you cannot; route 1 tried to TOLERATE it and it went
  too coarse. Making it invisible is a third relation to the problem and it did not occur to me for
  thirty-two stages.
- What I did right, and it is the habit that has paid every time this week: I tested before building.
  Fifteen minutes of `#eval` established that the abstraction fixes the probe's own failure case,
  still inverts the encoder, and satisfies stutter-or-advance over every SK term up to seven leaves.
  Had I gone straight to proofs I would have discovered the same thing three stages later or, worse,
  proved something about a mechanism that did not work.
- I also tested the obligation where it actually lives. `RS.bwd_of_abstraction` quantifies over EVERY
  pair of host terms, not the reachable ones, and it would have been easy to test the reachable
  closure, get a clean result, and report it as though it meant the obligation held. The reachable
  closure of the countdown is 183 terms; the real test space at seven leaves is 16896. Same class of
  error as the size-capped searches in Stage 41 — the finding is about the domain you quantified over.
- What I got wrong: three attempts at certifying the K-normaliser, all lost to the equation lemmas
  that Lean generates for overlapping patterns. I stopped and shipped it as census tooling, which is
  the project's existing convention for unverified code and cost nothing, since the finding is
  empirical anyway. The honest note is that the first attempt was not a proof attempt at all — I
  wrote a `have ... |> fun _ => by` construction that was nonsense, which is what flailing looks like
  when I have not thought about the induction. The second and third were real attempts.
- I ran a negative control on the guards before claiming them, because the build finished in 1.1
  seconds and that felt too fast for a check over 3238 terms. Inserting a guard that must fail made
  the build fail, so they bite. Thirty seconds to convert a suspicion into a fact.
- **Where Goal 2 stands.** The gap is unchanged in shape — no `Simulation` from a universal source
  into SK — but its hardest obligation went from "two dead routes" to "one mechanism that works on
  every case tested". That is the difference between blocked and unfinished.
- Ranking, against the spec: (1) prove stutter-or-advance for `absK` on the countdown, which turns
  the empirical finding into the first `Simulation` into `RS.SK` with a genuinely multi-step encoding.
  The crux is one question — how does an S-step interact with K-normalisation — and it needs
  confluence of K-reduction, which is a small self-contained lemma this tree does not yet have.
  (2) piece (v), the tag-step driver, once the mechanism is certified rather than measured.
  (3) rungs 2/3 via match-bounds. (4) C6, declined a thirty-third time.

## 2026-07-25 — Stage 46: mirroring beat inventing

- The task was the lemma I named yesterday: K-reduction is confluent, so "the K-normal form" denotes
  and Stage 45's abstraction is a function of its argument. I did the thing CLAUDE.md says to do and
  I have not always done — found the existing implementation of the same shape and followed it.
  `Confluence.lean` proves SK confluence by Takahashi: parallel reduction sandwiched between step
  and steps, a complete development, the triangle, then diamond → strip → confluence. Restricting
  that to the K rule is mechanical, and the K-only version is strictly simpler because there is no
  S_red case and `kdev` has one redex arm.
- It built with two small fixes, both mine and both from not following the model closely enough. I
  hand-rolled the `app` congruence case of `KPar.to_ksteps` as a nested type-ascribed `by` block
  instead of factoring out `congL`/`congR` the way the original does, and it did not elaborate. And
  I copied the original's `rw [← ..., ← ...]` ending for `knf_unique` without checking that my
  lemma's equation pointed the same way; `.trans` and `.symm` were clearer anyway. Both were the
  cost of paraphrasing rather than mirroring.
- The result I actually wanted is `IsKNF.of_kstep`: a K-step does not move the K-normal form. That is
  the K-step case of stutter-or-advance, and it falls out of confluence with no reference to the
  encoding at all — no case analysis, no countdown-specific reasoning. Half the crux of Stage 45's
  obligation is now a theorem instead of a measurement.
- I anchored it against vacuity deliberately, including one anchor I nearly skipped: `I` is K-normal.
  It looks like a triviality and it is the property the whole design rests on — if S-redexes were
  K-reducible, the abstraction would advance the machine while pretending to observe it. Worth a
  theorem, not a comment.
- Axiom footprint is `[propext]` or nothing across the file, which is the cleanest section in the
  tree. Nothing here touches arithmetic, and it shows.
- **What is left of the crux.** The S-step case. A K-step is settled; an S-step can create and
  destroy K-redexes, so I still need: if `b ⟶_S b'` and `IsKNF b w`, then `IsKNF b' w'` with `w'`
  either equal to `w` or one countdown step further along. That is where the encoding finally has to
  be reasoned about, and it is the half that is genuinely about the machine rather than about
  rewriting.
- Ranking, unchanged in shape but with the first item now smaller: (1) the S-step case, which
  completes stutter-or-advance and yields the first `Simulation` into `RS.SK` with a genuinely
  multi-step encoding; (2) piece (v), the tag-step driver, once the mechanism is certified rather
  than measured; (3) rungs 2/3 via match-bounds; (4) C6, declined a thirty-fourth time.

## 2026-07-25 — Stage 47: refuting my own next step before taking it

- The plan was the S-step case. I got the surrounding obligations done — `habs`, `hfun`, `fwd`, and
  the exhaustiveness of the K/S split — and then, before starting the commutation proof, I wrote down
  the statement I intended to prove and tested it. It is false. `S K S S` refutes it: when the fired
  redex is `S K g x`, the reduct `(K x)(g x)` is itself a K-redex, so `kdev` collapses it further and
  overshoots what one S-step from `kdev b` can reach.
- That is fifteen minutes that saved a stage, and it is the same habit as Stage 44 (work out what the
  tool buys before building it) and Stage 45 (test the mechanism before proving it). What is new is
  that this time the thing I tested was a PROOF OBLIGATION rather than a search or a measurement. I
  should generalise: write the target statement, look for a small counterexample, and only then start
  the induction. It is cheaper than discovering the same fact three lemmas deep.
- `naive_kdev_commutation_fails` is in the tree as a theorem, not a comment, because a refuted plan is
  exactly the sort of thing that gets forgotten and retried.
- The satisfying part of the stage is `hfun`. That obligation is what killed the joinability
  abstraction back in Stage 29 — `RS.joinable_abs_not_functional` — and it is the one Stage 45's
  mechanism had to pass without becoming coarse. It passes for a clean reason: K-normal forms are
  unique (Stage 46) and `Itower` is injective, so the abstraction is genuinely single-valued while
  still being blind to drift. Being blind to the right things and not the wrong ones is the whole
  trick, and it now has two theorems behind it instead of a hope.
- I also want to record `kNormalForm_I`'s role, because it looked like filler when I proved it
  yesterday. It is the reason the design is coherent: an S-redex must be invisible to K-reduction, or
  the abstraction would advance the machine while claiming to observe it. The abstraction is allowed
  to be blind to doomed subterms and must NOT be blind to progress. Those are the two halves, and
  `kNormalForm_I` is the second one.
- **Where Goal 2 stands.** Two of three obligations discharged, the third split into a done half and
  an open half, and the open half's cheap route eliminated. The countdown is still not a universal
  source, so criterion (a) still wants piece (v) — but the interface it has to satisfy is now mostly
  proved rather than mostly hoped.
- Ranking: (1) the S-step commutation square, now with the wrong statement eliminated and two
  narrowings identified (doomed-position S-steps cannot move the K-normal form; K-reduction never
  duplicates, so a live S-redex has exactly one downstream image). (2) piece (v). (3) rungs 2/3 via
  match-bounds. (4) C6, declined a thirty-fifth time.

## 2026-07-25 — Stage 48: the square, and a forty-stage arc closing

- The commutation square went in essentially as designed. I worked the cases out on paper first —
  disjoint redexes, S-redex inside the kept argument, S-redex inside the discarded argument, K-redex
  inside each of the S-redex's three arguments — checked that each closed, and only then wrote Lean.
  It built after two fixes, both about `cases` rather than about mathematics.
- The two fixes are the same lesson twice. `cases` on an indexed hypothesis will not name a field that
  the indices already determine (the S-redex's third argument is the ambient `u`, so `| S_red f g` not
  `| S_red f g x`), and it WILL generate impossible alternatives that unification cannot kill on its
  own (`SStep Term.K _` has no constructor but Lean still asks for the branch, discharged by `cases`).
  That is the third and fourth appearance of this family in the session. I now know the shape well
  enough that it cost minutes rather than attempts.
- What pleases me about the result is that both weakenings in the square are FORCED, and for
  different reasons that I would not have predicted from the same place. The K-side sometimes needs
  ZERO S-steps, because the S-redex may sit in exactly the argument a `K` throws away. The S-side
  sometimes needs TWO K-steps, because the S-step duplicated its third argument and a K-redex inside
  it got copied. Stage 47's refutation told me the equation was wrong; it did not tell me the shape,
  and the shape has content.
- `sk_local_square` and `sk_square` need no axioms at all — not even `propext`. Pure structural
  induction on two relations.
- **The arc is worth stating because it took forty stages.** Stage 8 identified `bwd` as the piece
  that could fail in kind. Stage 10 found the failure. Stage 11 half-fixed it and Stage 13 refuted the
  fix, leaving two dead routes and a third named in a comment. Thirty-two stages later Stage 45 tried
  the third route, Stage 46 made it well defined, Stage 47 refuted the cheap version of the last step,
  and Stage 48 proved the real one. The thing that unblocked it was not cleverness — it was reading
  my own probe files properly and noticing that the untried route was one line.
- **The limit, which I want on the record next to the result.** The countdown is not universal. This
  discharges the mechanism criterion (a) was blocked on; it does not discharge criterion (a). Piece
  (v), a tag-step driver, is still unwritten, and it is a substantial construction. What changed is
  that its hardest obligation is a solved problem with a worked example rather than a research risk —
  which is a real change, and less than "Goal 2 is done".
- Ranking, against the spec: (1) **piece (v)** — the tag-step driver, now that adequacy has a
  template. This is construction work rather than research: encode words, write the step driver, and
  discharge `fwd`; `bwd` follows the countdown's pattern with `Itower` replaced by the word encoding,
  provided the driver keeps its data K-normal. (2) rungs 2/3 via match-bounds, still a deliberate
  multi-stage project. (3) C6, declined a thirty-sixth time.

## 2026-07-25 — Stage 49: I overclaimed in yesterday's ranking, and the refutation was already in the tree

- Yesterday I closed adequacy and wrote that piece (v) would follow "provided the driver keeps its data
  K-normal". Today's first job was to start the driver. Instead I checked what the abstraction actually
  demands, and the demand is different from what I said: `RS.abstraction_tracks_rel` — a theorem I have
  had since Stage 8 and used in Stage 48 — forces the abstraction to be defined at every reachable host
  term. So the constraint falls on the driver's INTERMEDIATES, not on its data.
- The countdown passes for a reason specific to the countdown: its entire step is one S-step followed by
  K-reduction, so every intermediate K-normalises to the after-state. Measuring it made the property
  vivid — of the 183 terms reachable from `Itower 3`, all 183 K-normalise to one of exactly four terms,
  the encodings of 3, 2, 1, 0. The reachable set collapses completely. That is not a mild side
  condition, it is the whole reason the abstraction works.
- A tag-step driver has to inspect a symbol and dispatch, so it has several S-steps per source step, and
  each intermediate must also K-normalise to an encoding — before-state early, after-state late, flipping
  exactly once. I do not know whether that is arrangeable. It is not obviously impossible, because
  combinator programming has room to hide work inside things a `K` will discard. It is obviously the
  thing to prototype first.
- **The pattern I keep repeating, now with a name.** When I finish a hard piece, my ranking of the next
  piece is written in the glow of the finish and is too optimistic. Stage 38 did it ("no obstruction is
  apparent"), Stage 39 did it (ranked the empty shapes first), Stage 43 did it (one tool for two
  literatures), Stage 48 did it here. The fix is mechanical and I should just apply it: before writing
  the ranking, state the next piece's hardest obligation explicitly and check whether the thing I just
  proved actually discharges it. Twice this week that check took fifteen minutes and saved a stage.
- Worth noting the refutation cost nothing to find: the theorem was already in the tree, I had used it
  the day before, and I had not asked what it implied about the case I was about to attempt. That is a
  different failure from not knowing something.
- Second honest note, added to the file so it is not lost: nothing here says the K-normal-form abstraction
  is the only option. `bwd_of_abstraction_rel` takes an arbitrary relation. What Stage 49 establishes is
  the price of THIS abstraction, and a driver that cannot pay it may still be adequate by another route.
- Ranking, and this time stated as an obligation rather than a plan: (1) **prototype the intermediate
  condition** for a minimal dispatching driver — something that inspects one symbol and branches — and
  measure whether its intermediates K-normalise to encodings. Cheap, decisive, and it determines whether
  piece (v) is construction or research. (2) piece (v) proper, contingent on that. (3) rungs 2/3 via
  match-bounds. (4) C6, declined a thirty-seventh time.

## 2026-07-25 — Stage 50: the part I expected to fight came for free

- I applied yesterday's fix and it worked. Instead of writing a driver I stated the obligation, found a
  cheap diagnostic for it, and measured. The diagnostic is a ratio — reachable terms versus distinct
  K-normal forms — because the abstraction can only tolerate two K-normal forms per source step, so any
  construct that sprawls is disqualified before a line of driver exists.
- The result inverted my expectations in both directions. Dispatch, which I assumed would be the hard
  part, is perfect: `S K a b` produces exactly two K-normal forms, itself and the selected branch,
  because selecting is one S-step whose reduct is immediately a K-redex. It commits, the doomed branch
  vanishes, and the abstraction sees precisely the flip it needs. That behaviour is not something I
  arranged; it falls out of how booleans are encoded in SK.
- Recursion, which Stages 11 and 13 had already warned about in prose, fails on the numbers.
  `omegaSK`'s reachable set is smaller than the countdown's — 107 against 183 — and it has seventeen
  distinct K-normal forms against the countdown's four. Sprawl, not collapse.
- I want to be careful about what that does and does not show, because the temptation is to write
  "recursion is incompatible" and move on. `omegaSK` is not a driver. It has no source machine, so
  there is no notion of how many K-normal forms it is ALLOWED. Seventeen would be fine for a machine
  with seventeen reachable states. What is genuinely evidence is the direction: as the closure grows,
  the countdown's K-normal-form set stays at four while `omegaSK`'s keeps growing. That is a trend, and
  it is the right kind of thing to steer by, and it is not a theorem.
- The stage's real output is a localisation. Piece (v) was "write a tag-step driver and hope adequacy
  follows". It is now "find a recursion scheme that commits each unfolding through a K-discard, or pick
  a different abstraction" — with the dispatching half already known compatible with machinery that is
  proved. That is a much better-shaped problem, and it cost one measurement rather than a construction.
- Meta-note I want on the record after fifty stages: the last four stages have each consisted of
  checking an obligation before attempting it, and three of the four overturned the plan I had written
  the day before. The habit is now clearly worth more than the individual results — it is the reason
  the plans keep getting better rather than the reason they keep being wrong.
- Ranking, stated as obligations: (1) **can a recursion commit through a K-discard?** — the concrete
  question is whether there is a fixpoint idiom whose unfolding is `S K`-shaped, so each recursive step
  behaves like a dispatch rather than like self-application. Cheap to search over small terms, and
  decisive for route one. (2) if not, design a different abstraction for piece (v) — the trajectory
  relation rather than the K-normal form. (3) rungs 2/3 via match-bounds. (4) C6, declined a
  thirty-eighth time.

## 2026-07-25 — Stage 51: I used a detector my own tree had proved unreliable

- Two real results and one instructive failure.
- The results. A committing S-step — one whose reduct is immediately a K-redex, the pattern Stage 50
  measured as ideal — requires its first argument to be literally `K`, and then the whole thing is a
  projection: `S K g x` gives `x` and throws `g` away, with the duplicate it just made sitting inside the
  discarded part. So committing steps cannot compute. Stage 50's route one is impossible as I phrased it,
  and it took two lines of injectivity to see.
- And a conflation I should not have made: I tested `omegaSK` as a proxy for "recursion" when what I
  needed was "self-reproduction". The countdown TERMINATES. Its 183 reachable terms are the orders its
  layers can fire in, not unbounded work. A driver needs the driver term to reappear alongside advanced
  data, with each segment finite — which is a different property from non-termination, and one the
  countdown has.
- **The failure.** To look for self-reproducing terms I filtered by `onCycle?`. That is the
  leftmost-outermost cycle detector, and Stage 21 of this very project proved that an LO hunt is blind to
  cycles that exist in the relation — that was the stage that rescoped all my earlier hunt data. So I
  reached for a tool my own notebook records as unreliable for precisely this question, got zeros, and
  had to notice for myself that `onCycle? omegaSK` returns false while two theorems in Calibration.lean
  put `omegaSK` on a cycle. The probe could not see its own control.
- Stage 41 wrote the lesson down: when a probe has a parameter, the finding is about the parameter. What
  Stage 51 adds is the sharper version — a probe with a KNOWN blind spot must be run against a control
  that exercises the blind spot, not just any control. I did run controls this stage, twice, and caught
  the size-range problem that way. I did not think to control the detector itself.
- I have made both facts guards rather than comments, because the next person to reach for `onCycle?` on
  a question about cycles-in-the-relation should trip over `onCycle? omegaSK = false` immediately.
- What the stage leaves: the question is unsettled and I now believe search cannot settle it. The smallest
  self-reproducing object in SK is fourteen leaves and exhaustive enumeration dies at seven or eight. So
  route one needs a CONSTRUCTION — design a self-reproducing driver and check its segment — rather than a
  sweep. That is a genuine change in method, and it is the honest output of a stage that otherwise
  produced two small theorems and a mistake.
- Ranking, as obligations: (1) **construct** a minimal self-reproducing term by hand — something of the
  shape `X data` reducing to `X data'` — and measure its segment's K-normal forms. Construction rather
  than search, because search cannot reach the size. (2) route two: design the trajectory-relation
  abstraction, which Stage 49 noted is unconstrained by any of this. (3) rungs 2/3 via match-bounds.
  (4) C6, declined a thirty-ninth time.

## 2026-07-25 — Stage 52: the habit that has been winning has a precondition

- I set out to construct the self-reproducing prototype Stage 51 asked for, and found that the tree already
  contains a certified one — `omegaSK`, with `omega_to_M` and `M_to_omega` proving it returns to itself. So
  I measured that instead of building something new, which was the right call for about ten minutes.
- Then the measurement would not interpret. The diagnostic I invented in Stage 50 counts K-normal forms and
  compares against "at most two per source step". `omegaSK` has no source. So seventeen K-normal forms, or
  thirteen along a twenty-step trace, is not too many or few — it is not comparable to anything. Stage 50's
  headline was "dispatch passes, recursion does not", and the second half of that does not follow from what
  I measured. The first half does: dispatch's source really is a two-state selection, so two is exactly
  right.
- I want to be clear that this is my error and not a subtlety. I wrote the diagnostic as "at most two per
  SOURCE step" in Stage 50 and then applied it to a term with no source in the same stage. The words were
  right and I did not read them.
- What the numbers do show is a difference in kind, and I have guarded it as suggestive rather than
  decisive: the countdown's K-normal forms shrink monotonically along its trajectory — 10, 7, 4, 1 — which
  is what a source that only moves forward looks like. `omegaSK`'s oscillate and revisit — 14, 20, 17, 17,
  26, 23, 23, 20, 20, 32 — which would force the source to cycle. Suggestive. Not a refutation, because
  neither term encodes anything.
- **The finding I actually value.** "Prototype the obligation before building the artifact" has driven the
  last six stages and been right every time. This is the first time it fails, and now I know why: the
  diagnostic has to be interpretable WITHOUT the artifact. "How many K-normal forms is too many" is a
  question about the source machine, so it cannot be answered before there is a driver. The prototype was
  supposed to de-risk building the driver and it turns out to require it. That is a precondition on the
  habit, not a failure of it, and it is worth having explicit before the next time I reach for it.
- So route one is not refuted and not testable cheaply, and I am going to stop circling it. Route two has
  been sitting untouched since Stage 49 and has the property route one lacks: `bwd_of_abstraction_rel`
  takes an arbitrary relation, so the trajectory relation — "b lies on the host segment for source state
  w" — can be designed and its obligations checked against the countdown, which I already have, before any
  driver exists.
- Ranking, as obligations: (1) **design the trajectory relation** and check its three obligations against
  the countdown — `habs` and `hfun` are the ones to worry about, since a trajectory relation is naturally
  coarse and `hfun` is exactly what coarseness broke for joinability. If it survives the countdown it is a
  candidate for piece (v); if it fails `hfun` the same way joinability did, that is a third dead route and
  worth knowing. (2) rungs 2/3 via match-bounds. (3) C6, declined a fortieth time.

## 2026-07-25 — Stage 53: the route I should have tried three stages ago

- Route two took one stage and gave up its two hard obligations without a fight. `habs` is immediate and
  `hfun` — the obligation that killed joinability back in Stage 29 and that I flagged as the thing to worry
  about — falls out of the Stage 48 `Simulation`'s own `bwd`. Reusing the result I had just proved to prove
  the next thing is the most satisfying kind of progress and I did not expect it here.
- The design point worth keeping: bare reachability fails `hfun` in BOTH directions, because the countdown's
  encodings are linearly ordered by reachability, so `Itower 2 ⟶* Itower 1` confuses states 2 and 1. The fix
  is the "not yet past `w`" clause, and it is exactly load-bearing — reachability gives `a ≤ a'` and the
  clause gives `a' ≤ a`. Neither half alone is a relation; together they pin the state.
- What remains, `hstep`, unwinds to "no single host step reaches past two source states", i.e. consecutive
  encodings are at least two host steps apart. That is a condition of an entirely different character from
  route one's. Route one wanted every intermediate to K-normalise to an encoding, which is a coincidence one
  hopes for; this is a spacing property one arranges. The countdown satisfies it because `I t` takes two
  steps to become `t`.
- **The real lesson is about the three stages I spent on route one.** Route two was named in Stage 49 as a
  parenthetical, and Stages 50, 51 and 52 all went to route one — each correcting the previous one's error,
  none of them getting anywhere, and Stage 52 concluding route one is not even testable without building
  the driver. Route two was cheaper, more promising, and available the whole time. What kept me on route one
  was that it was the route the countdown happened to use, so it felt like the established path. That is the
  same local-gradient failure Nathan asked me about around Stage 43, in miniature: I kept refining the thing
  I had just built instead of asking which available thing was best.
- The corrective is not "try harder to notice" — it is what I already committed to and applied unevenly:
  when a route stalls, re-read the alternatives that were written down when the routes were enumerated. They
  are in the file. Stage 49 wrote route two down and I read past it three times.
- The cost of route two is real and I have recorded it next to the benefit: the relation is not a
  computation, so it supplies `bwd` but not a decoder. A `Simulation` needs both. The countdown got its
  decoder from `naiveAbs` independently of its abstraction, and a driver must do the same — decode
  syntactically, track relationally. That is two obligations rather than one, and it is worth knowing before
  writing a driver rather than after.
- Ranking, as obligations: (1) **prove `hstep` for the trajectory relation on the countdown** — the spacing
  condition, which would complete a SECOND independent adequacy proof for the same machine and confirm the
  route end to end before it is used on anything harder. (2) piece (v) with route two, decoder and tracker
  as separate obligations. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-first time.

## 2026-07-25 — Stage 54: the obstruction was in my own interface

- I measured `hstep` before proving it, and it failed — 36 of 183. Good thing, because Stage 53 had
  hypothesised the wrong reason for the difficulty (a spacing condition) and I would have spent the stage
  proving something false about something irrelevant.
- The actual reason is one term. `K (Itower 1) (K (Itower 2))` sits on segment three and is itself a
  K-redex whose contraction is `Itower 1`. One host step, two source states, segment two skipped. The
  pending computation was in the discarded argument, so contracting the `K` arrived early. Nothing to do
  with how far apart the encodings are.
- And then the fix was not in the relation but in the INTERFACE I wrote in Stage 8. `hstep` let the
  abstraction advance by at most one source step per host step. Nothing in the tracking proof needs that —
  it composes source paths, and composing with `trans` instead of `tail` is the whole change. Relaxing it
  takes the failures from 36 to 0. So route two was fine and my own adequacy interface was the obstruction,
  for forty-six stages, unnoticed because until now every encoding I tried advanced one step at a time.
- I want to name that failure mode because it is new in this project. I have repeatedly caught myself
  overclaiming, mis-ranking, and using blind probes. This is different: a definition I wrote early, that
  was adequate for every case I met, silently narrower than the theorem it supports. The tell was available
  — `abstraction_tracks_rel`'s proof builds a path and then artificially restricts the input to single
  steps — and reading my own proof would have shown it. I only looked because a measurement forced me to.
- The symmetry is the thing I will remember from this stage. The K rule erases, and erasure is exactly what
  makes the K-normal-form abstraction work (drift in discarded arguments becomes invisible) and exactly
  what makes the trajectory relation fail (discarding pending work skips states). The same mechanism, load
  bearing for one design and fatal to the other. That is a genuinely nice fact about SK and it fell out of
  comparing two failed routes rather than from either one.
- Where this leaves piece (v): two abstractions, both viable, with complementary demands. Route one wants
  intermediates whose K-normal forms are encodings — a shape condition. Route two wants nothing about
  shape, only that segments be well defined, and now tolerates state-skipping. Route two looks better and
  is measured clean; the honest caveat is that "measured clean" means one machine at one size.
- Ranking, as obligations: (1) **prove `OnSegmentHStepPath` for the countdown**, which would give a second
  independent adequacy proof for the same machine and validate the generalised interface on something. The
  proof needs the source-order lemmas from Stage 53 plus a case analysis on whether the step crosses a
  segment boundary. (2) piece (v) with route two. (3) rungs 2/3 via match-bounds. (4) C6, declined a
  forty-second time.

## 2026-07-25 — Stage 55: the proof was four lines and the hypothesis was the whole problem

- I expected `hstep` for the trajectory relation to be a case analysis: does the step cross a segment
  boundary or not. It is not. Take the LEAST source state whose encoding reaches `b'`, and everything
  follows — the advance is a path to that state, and if it happens to be `w` the path is empty, so the
  stutter case never needs mentioning. Four lines.
- Two things fell out that I would not have seen by proving it the hard way. The proof never touches the
  "not yet past `w`" clause of its hypothesis, only the reachability half — so that clause exists purely
  for `hfun`, which is a clean division of labour I had not noticed. And the entire difficulty relocated
  into one hypothesis, `hleast`.
- `hleast` needs decidability, because a least element of a non-empty bounded set of naturals is only
  extractable constructively when membership is decidable, and this tree refuses `Classical.choice`. That
  chases back to: `Itower m`'s reachable set must be finite, i.e. `Itower m` must be strongly normalising.
- **And the tree cannot supply that, for a reason I find genuinely satisfying to have found.** C5 is exactly
  the theorem that turns "has a normal form" into "strongly normalising" — and C5 requires K-freeness.
  `Itower` is built from `I = S K K`. So my own conservation theorem is blocked from reaching my own
  encoding, and the blocker is the `K` rule's erasure: with `K` present, WN does not imply SN at all
  (`K S omegaSK` normalises and also diverges). That is the third stage running in which the K rule's
  erasure is the pivot — it made route one's abstraction work, made route two skip states, and now blocks
  the theorem route two needs.
- I could have reached for `Classical.choice` here and had the whole thing in twenty minutes. I would rather
  report a reduction than break a property the project has held for fifty-five stages, and the reduction is
  more informative anyway: "route two needs SN of `I^m S`" is a sentence someone can act on.
- A correction to my own record: I wrote "both theorems axiom-free" in the commit message before reading the
  audit, and they are `[propext, Quot.sound]`. Amended. I have been running the audit after composing the
  message, which is the wrong order and has now bitten once.
- Ranking, as obligations: (1) **prove `Itower m` is strongly normalising** — plausibly by a measure that
  accounts for the duplication `I t ⟶ (K t)(K t)` honestly, since leaf count grows there; the natural
  attempt is a measure on the number of `I` layers times something, and it is a self-contained termination
  problem. That completes route two's adequacy for the countdown and gives the second independent proof.
  (2) piece (v) with route two. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-third time.

## 2026-07-25 — Stage 56: measure the answer, then prove it

- Stage 55 left route two needing strong normalisation of `Itower m`, which is a real theorem I did not
  want to prove. So I asked what I actually needed — a finite reachable set — and noticed that BOUNDED SIZE
  suffices and is much weaker. Then I measured the bound before trying to prove anything: largest reducts
  of `Itower m` are 1, 4, 10, 22 leaves. That is `3·2^m − 2`, and having the closed form in hand made the
  proof a matter of checking four cases rather than searching for a measure.
- The proof needs the reachable set characterised, because no measure can work for all of SK — `S`
  duplicates, so size growth is unbounded, and any measure that dominated leaf count would have to be
  non-increasing on a rule that doubles its argument. Three layer states do it: intact, half-consumed,
  collapsed.
- **The satisfying part.** The `half` constructor has to let the two copies of a half-consumed layer be
  DIFFERENT tower states, or the family is not closed under reduction. That is exactly the drift Stage 10
  discovered and that every abstraction since has had to cope with — and here, for the first time, it is not
  an obstacle but a constructor. Fifty stages after finding drift I finally gave it a type, and the size
  bound falls out because a drifted pair is still two things of bounded size. The `half` case is also where
  the bound is tight.
- What remains is smaller than it was and of a different kind. Decidable reachability needs a certified
  enumeration of bounded-size SK terms, and this tree's `smallTerms` is K-free because `enumAt` is — Goal 3's
  whole decidability layer was built for pure S and inherits that restriction. So the gap is now
  infrastructure: build the K-inclusive version of a thing I already have uncertified as `skTerms`. That is
  the first time in about ten stages that the blocker has been engineering rather than mathematics, and I
  should say so plainly rather than dress it up.
- Method note worth keeping, since it is now three for three: measure the answer, then prove it. Stage 54
  measured that hstep fails, Stage 56 measured what the bound is. Knowing `3·2^m − 2` before starting turned
  an open-ended search for a measure into four arithmetic checks. I have been treating measurement as a way
  to decide WHETHER to prove something; it is at least as useful for deciding WHAT to prove.
- Ranking, as obligations: (1) **certify a K-inclusive bounded enumeration** — `skTerms` plus the soundness
  and completeness lemmas `enumAt` has, which would close the chain to route two's `hstep` and, incidentally,
  widen Goal 3's decidability layer beyond pure S. Engineering, but it unblocks a proof. (2) piece (v) with
  route two, once the chain closes. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-fourth time.

## 2026-07-25 — Stage 57: one line, and fifty stages of restriction lifted

- The K-inclusive enumeration was, as predicted, engineering. It is `Completeness.lean` with the leaf case
  changed from `[S]` to `[S, K]` and the `KFree` conjunct deleted from soundness. Both proofs went through
  unchanged otherwise, including the budget-indexing trick and Slice 2's care about explicit witnesses.
- That the diff is one line is the finding. `enumAt`'s K-freeness has been load-bearing since Stage 6 and
  I had come to think of it as intrinsic — Goal 3's decidability, C1(b)'s floor, C5's pigeonhole all run on
  it, and they all genuinely need pure S. But the enumerator itself never needed the restriction; it
  inherited it from what the census happened to want. Fifty stages of treating an accident as a constraint.
- I only found out because route two's chain reached back through decidability to enumeration, which is the
  second time this session a long chain has ended somewhere I assumed was bedrock. The first was Stage 54,
  where the obstruction turned out to be my own Stage 8 interface. Both were early definitions, adequate for
  every case that came up, silently narrower than needed — and in both cases the tell was visible in the
  original file and I had never had a reason to look.
- What that suggests as a habit, and I want to state it as more than an observation: when a chain of
  reductions bottoms out at an old definition, check whether the definition's restriction is load-bearing or
  inherited before treating it as a wall. Twice now the answer was "inherited" and the fix was small.
- Where the chain stands: route two's `hstep` ⟸ `hleast` ⟸ decidable reachability from `Itower m` ⟸
  bounded enumeration (now certified) plus the size bound (Stage 56). Both ingredients exist. What remains is
  to assemble them into the decision procedure and the `hleast` extraction, which is the deficit-style
  argument `boundedClosure_isSome` already does for the K-free case — and which will need the same widening,
  since it too is built on `smallTerms`.
- Ranking, as obligations: (1) **widen the closure-saturation argument to `skSmallTerms`** — `deficit`,
  `deficit_lt` and `boundedClosure_isSome` are the pieces, all of them K-free only for the same inherited
  reason. That yields decidable reachability from `Itower m` and closes route two's chain to `hstep`.
  (2) piece (v) with route two. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-fifth time.

## 2026-07-25 — Stage 58: four inherited restrictions and one real one

- The chain closed. Route two's `hstep` is proved and there is now a second `Simulation` of the countdown
  into SK whose `bwd` shares nothing with the first except the encoding — one through K-normal forms and a
  commutation square, one through trajectory segments and a path-advancing interface. Getting two
  independent proofs of the same adequacy is the kind of confirmation I would not have sought deliberately
  and am glad to have.
- The stage's real content is the audit of five K-freeness restrictions. Four of them — `enumAt`,
  `smallTerms`, `deficit`, `boundedClosure_isSome` — turned out to be inherited from what the census wanted
  rather than structural, and lifting them was mechanical once I looked. The fifth, `mem_of_saturated`, was
  genuinely load-bearing: it bounds an intermediate by leaf-count monotonicity, and with `K` around leaf
  count rises and falls, so an intermediate can exceed both endpoints. That one could not be removed. It
  could be REPLACED, by the hypothesis actually needed — a bound on the whole region, which travels along a
  path because a reduct of a reduct is a reduct.
- I want to hold onto the distinction, because "check whether the restriction is load-bearing or inherited"
  was Stage 57's habit and this is the first time the answer came back "load-bearing". The right response
  was not to give up and not to force it, but to ask what the hypothesis was BUYING and supply that instead.
  Four removals and one substitution is a better outcome than five removals would have been, because the
  substitution is where the mathematics actually was.
- A general fact fell out that is worth more than its role here: bounded-region reachability is decidable
  for full SK. That does not contradict undecidability of SK reachability — it is undecidable precisely
  because the region cannot be bounded in advance — and the countdown supplies its own bound via Stage 56.
- Small note: `Nat.find` is Mathlib's, not core's, so the least-witness extraction is fifteen lines of
  walking up from zero carrying "nothing below has satisfied it yet". Zero-dependency has cost real time
  across this project and almost never cost correctness; this is a typical instance of the tax.
- Stage 55 said this step needed `Classical.choice` and I declined to use it, reporting a reduction instead.
  Three stages later the reduction closed constructively. I do not think that was luck — the reduction named
  what was missing precisely enough that finding it was a search rather than a hope — but it is worth noting
  that "report the reduction rather than reach for the axiom" paid off in the end and not just in principle.
- Ranking, as obligations: (1) **piece (v)** — the tag-step driver, now with two proven adequacy templates
  and a decidability layer that no longer stops at pure S. This is construction work at last. (2) rungs 2/3
  via match-bounds. (3) C6, declined a forty-sixth time.

## 2026-07-25 — Stage 59: the composition was free, and that is the finding and the caveat

- I wanted to know whether the pipeline composes before building a driver, so I looked for the smallest
  genuine `TagSystem` I could push through it. Deletion number one, one symbol, empty rule: the word shrinks
  by one per step and halts when empty. That is the countdown exactly, `List.length` is the isomorphism, and
  `Simulation.comp` did the rest.
- Two things I did not expect. First, `Simulation.comp` has been in the tree since Stage 8 and had never been
  used for anything but a sanity example; it worked on the first try. Second, the tag system inherits BOTH of
  the countdown's adequacy proofs for nothing, because composition takes whatever `bwd` it is handed — so
  there are now two independent `Simulation`s of a `TagSystem` into SK.
- And the composition was free precisely because the system does not compute. A unary tag system with an
  empty rule is a countdown wearing a tag system's clothes. I want that stated as loudly as the result,
  because "a TagSystem is now hosted in SK" is exactly the sort of sentence that could be read as discharging
  criterion (a), and it does not come close: Cocke–Minsky universality needs m = 2 over a finite alphabet, and
  the driver has to inspect a symbol and append its rule. Neither happens anywhere in this file.
- What it does buy is the shape of the remaining construction, and that is not nothing after nine stages of
  circling. Encode the word, do one deletion per source step, reuse the countdown's adequacy template. The
  extra work is symbol dispatch — which Stage 50 measured as compatible with the K-normal-form abstraction,
  and which was the part I had expected to be hardest — and the rule append, which no stage has tested.
- Small Lean note, third time this week: `subst` on `h : w' = rest` eliminates whichever variable it can, and
  which one that is depends on binding order. Twice now I have written the follow-up proof against the wrong
  survivor. The fix is to rewrite with the equation rather than substitute when I care which name remains.
- Ranking, as obligations: (1) **test the rule append** — the one part of a driver no stage has probed.
  Concretely: can a term that appends a fixed list to an encoded word keep its intermediates inside the
  abstraction, the way dispatch does? Cheap to check with the countdown's own machinery, and it is the last
  unmeasured component before the construction. (2) piece (v) proper. (3) rungs 2/3 via match-bounds.
  (4) C6, declined a forty-seventh time.

## 2026-07-25 — Stage 60: the component that turned out not to exist

- Yesterday's ranking said the rule append was the last unmeasured component of a driver. It is not a
  component. With a right-fold encoding, appending at the end is substituting for the fold's nil argument,
  which is a fixed four-abstraction wrapper with no recursion and no dependence on the list. I compiled it
  with the tree's own bracket abstraction and checked it against directly-encoded lists.
- The encoding choice is doing all the work, and it is the natural one for this problem rather than a trick:
  tag systems consume at the front and produce at the back, and a right fold makes both ends cheap. I had
  been carrying an unexamined assumption that the word would be a cons-list, where append is a traversal and
  therefore recursive. That assumption was never stated, which is why it survived several stages.
- I used two different observers for the agreement checks — `(K, S)`, which keeps only the head, and
  `(I, K)`, which keeps the structure. A single observer that collapses would have made any two lists look
  equal. That is the same care as Stage 50's non-vacuity count and I am glad it is becoming automatic.
- And I ran a negative control, because the build finished in 1.3 seconds and normalising a 414-leaf term
  four times with fuel 20000 should not be that fast. A deliberately wrong guard made the build fail, so the
  guards bite. Second time this week that "that felt too fast" was worth thirty seconds.
- **Where piece (v) actually stands, after ten stages of narrowing.** Three ingredients were in question.
  Symbol dispatch was measured compatible in Stage 50 and came for free. Rule append is a constant, shown
  here. Self-reproduction is open and has been open since Stage 50, and every attempt to test it without
  building a driver has failed for the reason Stage 52 identified: the diagnostic is only meaningful relative
  to a source machine.
- So the narrowing is done. There is nothing left to measure, and the remaining question cannot be answered
  by measurement. That is a clean place to have arrived, and it took correcting my own ranking in four of the
  last six stages to get here — which I would rather record as the method working than as four mistakes.
- Ranking: (1) **build the driver**. Not "test something first" — Stage 52 established that the last
  ingredient is not testable in isolation, and Stages 59–60 have fixed the shape and eliminated two of three
  unknowns. The construction is a fold-encoded word, a dispatch on the head symbol, a constant append, and a
  self-reproducing wrapper; the first three are settled. (2) rungs 2/3 via match-bounds. (3) C6, declined a
  forty-eighth time.

## 2026-07-25 — Stage 61: the fixpoint I did not need

- The last open ingredient turned out to be two abstractions. `W = λx.λd. x x (F d)` gives `W W d ⟶* W W (F d)`
  for any `F`: the driver reappears, the data advances, and the self-application is one `S`-redex rather than
  an unfolding. Fifteen leaves plus `F`.
- I had been carrying "self-reproduction means a fixpoint combinator" since Stage 11, and it shaped three
  stages of measurement. Stage 50 measured `omegaSK` as the proxy and found its K-normal forms sprawl; Stages
  51 and 52 tried and failed to make that measurement mean something. The proxy was wrong in a way I can now
  say precisely: `omegaSK` is self-application with NOTHING TO ADVANCE. A driver's self-application carries a
  step function, and the step function is where the discipline lives. Measuring the bare self-application told
  me about a term with no encoding, which is exactly Stage 52's complaint about itself.
- Doing the bracket abstraction by hand instead of calling `bracket` mattered twice. It gave fifteen leaves
  instead of the hundreds the naive algorithm produces — Stage 60's `APPEND` came out at 414 — and it made the
  proof a short explicit reduction chain, which needs no axioms at all, rather than a normalisation of
  something enormous. When the term is small enough to reason about, prove it; when it is not, the tooling
  will only tell you it evaluates.
- So all three ingredients of piece (v) are settled: dispatch free, append constant, self-reproduction proved.
  What is left is assembling the step function for a universal tag system, and that is engineering with
  understood parts rather than an open question. After eleven stages of narrowing that is a real change in
  kind, and I want to be careful not to overstate it: assembling `head`, `tail`, `dispatch` and `append` into
  one certified `fwd` for m = 2 over a two-symbol alphabet is still a substantial build, and the terms will be
  large enough that proving `fwd` will need the same by-hand discipline that made today cheap.
- The pattern worth keeping from today: **an assumption inherited from a plausible analogy survived eleven
  stages because it was never written as a claim.** "Recursion needs a fixpoint" is true for general recursion
  and false for self-reproduction with a fixed step, and I never separated the two. Stage 60 caught the same
  shape — "append needs a traversal" was true for cons-lists and false for folds. Both were unstated
  assumptions about representation, and both dissolved the moment I wrote down what was actually required.
- Ranking: (1) **assemble the step function** for a two-symbol m = 2 tag system — head, double tail, dispatch,
  append — and prove `fwd` for it. By hand where the terms are small enough to reason about. (2) rungs 2/3 via
  match-bounds. (3) C6, declined a forty-ninth time.
