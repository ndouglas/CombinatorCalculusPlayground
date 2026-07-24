# Stage 5 Slice 3: The Invariant Observatory Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Map the divergence frontier — hunt for self-embedding on the C1 candidates, test the plateau-nesting reading of C3, tabulate divergence density (C6) — and consolidate the two hosting refutations into one RS-level theorem (`Simulation.refute_of_acyclic`), registering C5 and the unbounded-trajectory corollary as dependency-annotated queue items.

**Architecture:** This slice is census-heavy by design and EXPECTED to end with better maps, not a resolved conjecture — the ledger must say so. Task 1 adds `isSubterm` and runs the explore-then-record self-embedding hunt on both C1 candidates (either outcome — found or not-found-within-fuel — is an honest, recordable finding). Task 2 is scratch-based census exploration (plateau argmax terms, density table) whose findings land in CONJECTURES with reproducibility snippets, per the established "Runs behind this file" methodology. Task 3 is the slice's one theorem: RS-level acyclicity + the generic refutation, with `RS.PureS` and `RS.Iota` acyclicity instances and subsumption demonstrations of both Stage 4/Slice 2 refutations (originals kept untouched). Task 4 registers C5, the corollary, and the C1 strategy fork.

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0`. Zero dependencies.
- **No `sorry` on main.** 3 documented failed attempts → CONJECTURES registration + removal (spec escape hatch).
- **No `partial def`.** Plain `decide`/`rfl` allowed; `native_decide` banned.
- Every commit must `lake build` clean with zero warnings.
- Epistemic labels exact (kernel vs evaluator vs fuel-bounded-census — the established three-level discipline). Exploratory findings are FUEL-BOUNDED CENSUS DATA unless a theorem or compile-time check backs them; say which, every time.
- **Explore-then-record discipline (this slice's specific burden):** Tasks 1–2 run open-ended explorations whose outcomes are unknown at plan time. The recorded artifact must state what was ACTUALLY found — a probe that finds nothing records "nothing found within fuel F," never a weakened check that passes vacuously. Scratch exploration files are deleted before commit; their exact commands/snippets are documented in CONJECTURES for reproducibility.
- Expectation-setting is part of the deliverable: no artifact may imply C1/C3/C6 were resolved this slice.

## Lean TDD adaptation (house rules)

- Functions: `#guard`s first (RED) → implement (GREEN). Theorems: `:= sorry` (RED, counts stated) → proof (GREEN). NEVER commit with sorry.
- Known friction: `induction`/`cases` on `RS.Steps` at CONCRETE instances needs the `.rec` pattern (RS.lean precedent); at VARIABLE `B : RS` ordinary tactics work. Prefer `simp only` over bare `simp` (choice-leak precedent from Slice 2).

---

### Task 1: `isSubterm` + the self-embedding hunt (explore, then record the truth)

**Files:**
- Modify: `CombinatorCalculusPlayground/Reachability.lean` (append — it has `trace`, `leafCount`, `sTerms` in scope)

**Interfaces:**
- Consumes: `Term`, `trace` (Census/Eval.lean), `leafCount`, `sTerms`.
- Produces: `isSubterm (s t : Term) : Bool`; `c1 c2 : Term` (the C1 candidates as named defs); the recorded hunt outcome as `#guard`s.

- [ ] **Step 1: `isSubterm` with guards (RED: unknown identifier → GREEN)**

```lean
-- ## Slice 3: the self-embedding hunt (C1 reconnaissance)
-- Rewriting theory's standard non-termination witness is the LOOP
-- t →⁺ C[t] — the term reappears as a subterm of its own reduct, and
-- congruence pumps forever. Whether either C1 candidate loops this way
-- has never been checked. Either answer is a finding.

/-- Is s a subterm of t (including t itself)? -/
def isSubterm (s t : Term) : Bool :=
  t == s ||
    match t with
    | .app a b => isSubterm s a || isSubterm s b
    | _ => false

#guard isSubterm S (app S K) = true
#guard isSubterm K (app S K) = true
#guard isSubterm (app S K) (app S K) = true
#guard isSubterm (app K S) (app S K) = false
#guard isSubterm (app S S) (app (app S S) (app K K)) = true
```

- [ ] **Step 2: The C1 candidates as named defs, membership-pinned**

```lean
-- The two 7-leaf non-normalization candidates (CONJECTURES C1), as terms:
--   c1 = S S S (S S) S S      c2 = S (S S) S S S S
def c1 : Term :=
  Term.app (Term.app (Term.app (Term.app (Term.app S S) S) (Term.app S S)) S) S
def c2 : Term :=
  Term.app (Term.app (Term.app (Term.app (Term.app S (Term.app S S)) S) S) S) S

#guard leafCount c1 = 7
#guard leafCount c2 = 7
#guard (sTerms 7).contains c1
#guard (sTerms 7).contains c2
-- Pin the renderings against the ledger's candidate strings:
#guard render c1 = "S S S (S S) S S"
#guard render c2 = "S (S S) S S S S"
```

(If a render guard fails, the DEF is mis-associated — fix the def to match
the ledger string, never the guard; the ledger strings are the source of
truth for which terms C1 names.)

- [ ] **Step 3: EXPLORE — the hunt itself (scratch #eval, then record)**

In a temporary scratch section (deleted before commit), evaluate for each
candidate c ∈ {c1, c2}:

```lean
-- scratch exploration (DELETE before commit):
#eval ((trace 120 c1).drop 1).findIdx? (fun u => isSubterm c1 u)
#eval ((trace 120 c2).drop 1).findIdx? (fun u => isSubterm c2 u)
-- and the cross-embedding directions:
#eval ((trace 120 c1).drop 1).findIdx? (fun u => isSubterm c2 u)
#eval ((trace 120 c2).drop 1).findIdx? (fun u => isSubterm c1 u)
```

If evaluation is slow, reduce fuel stepwise (100, 80, 60) and record the
achieved fuel. THEN record the actual outcome as committed guards, one of:

```lean
-- OUTCOME A (self-embedding FOUND at step k for candidate c):
-- pins the discovery; k is whatever the exploration returned.
#guard isSubterm c1 ((trace k c1).getLast!) = true   -- adjust to the exact index found
```

or

```lean
-- OUTCOME B (no self-embedding within the achieved fuel F):
-- an honest negative: within F leftmost-outermost steps, neither candidate
-- ever contains itself (or the other) as a subterm of a proper reduct.
-- This is FUEL-BOUNDED CENSUS DATA, not a theorem about all steps.
#guard ((trace F c1).drop 1).all (fun u => !(isSubterm c1 u))
#guard ((trace F c2).drop 1).all (fun u => !(isSubterm c2 u))
```

Record BOTH candidate outcomes and both cross-directions (four findings
total, whichever way each lands). If Outcome A occurs for ANY of the four,
flag it prominently in your report — it opens the loop route to C1 and
changes the slice's conclusions (do not attempt the divergence proof here;
it needs C5, see Task 4).

- [ ] **Step 4: Build and commit**

Run: `lake build` — zero warnings; compile time for the guards under ~2 min
(reduce fuel honestly if not).

```bash
git add -A
git commit -m "feat: self-embedding hunt on the C1 candidates (isSubterm + recorded outcome)"
```

---

### Task 2: Plateau-nesting and divergence-density (scratch census, findings to CONJECTURES)

**Files:**
- Modify: `CONJECTURES.md` (C3 addendum; new C6 registration; snippets documented)

**Interfaces:**
- Consumes: `sTerms`, `trace`, `leafCount`, `normalize` (all existing); the census data already recorded in CONJECTURES/LAB_NOTEBOOK (exhausted counts per n).
- Produces: C3 addendum (plateau-nesting finding, whatever it is); C6 registration (divergence density) with the tabulated data.

- [ ] **Step 1: EXPLORE — argmax terms behind the plateau (scratch, delete after)**

In a scratch file (e.g. `/private/tmp` or an untracked `Scratch.lean` —
never committed), for n ∈ {7, 8, 9} (small sizes only; n ≥ 10 is
runtime-prohibitive at compile time and the plateau data for 10–12 stays
fuel-bounded-census from the original runs):

```lean
-- scratch (DELETE): the term achieving max final leafCount at fuel 200
#eval (sTerms 7).foldl (fun (best : Term × Nat) t =>
  let fl := leafCount ((trace 200 t).getLast!)
  if fl > best.2 then (t, fl) else best) (Term.S, 0)
-- repeat for sTerms 8, sTerms 9; render the argmax terms.
```

Questions to answer from the outputs: (a) is argmax(n+1) structurally
related to argmax(n) — e.g. `app argmax(n) S`, `app S argmax(n)`, or
argmax(n) as a subterm (use `isSubterm` from Task 1)? (b) do the final
leaf counts at consecutive n differ by a small constant (the +1 pattern
seen at 10/11/12)?

- [ ] **Step 2: Record the C3 addendum**

Append to C3's section in CONJECTURES.md (adapt entirely to what was
found — the text below is the SHAPE, not the content):

```markdown
**Slice 3 probe (fuel-bounded census data, fuel 200, n = 7..9):** the
max-final-size terms at consecutive sizes [ARE / ARE NOT] structurally
nested: [state the actual relation found, with the rendered argmax terms,
or state plainly that no nesting relation was observed]. [If nested:] This
supports the reading that the n=10..12 plateau (88,163,896 → +1 → +1)
reflects a single extremal trajectory family with rider leaves — still a
conjecture; the 10..12 argmax terms were not recomputed (runtime cost).
Reproduce with: [the exact scratch snippet used].
```

- [ ] **Step 3: Tabulate divergence density and register C6**

From the census data ALREADY in the ledger (n=7: 2/132; n=8: 41/429;
n=11: 6842/16796; n=12: 29337/58786 — pull n=9, n=10 from the recorded
runs in CONJECTURES/LAB_NOTEBOOK; if a value was never recorded, mark it
"not recorded" rather than recomputing), add:

```markdown
## C6: Divergence density grows with size — status: open
Fraction of pure-S terms at exactly n leaves that exhaust fuel 200
(leftmost-outermost; fuel-outs are NOT divergence proofs — this is a
density of *fuel-exhaustion*, a proxy observable):

| n  | exhausted / total | fraction |
|----|-------------------|----------|
| 7  | 2 / 132           | 1.5%     |
| 8  | 41 / 429          | 9.6%     |
| ...                                |

Conjecture: the fraction is monotone non-decreasing in n and → 1.
(Cheap to extend: rerun `lake exe ccp` at higher fuel to test
fuel-sensitivity of the table; not done this slice.)
```

(Compute the actual fractions from the actual numbers; the two rows shown
are from the ledger and must be re-verified against it, not trusted from
this plan.)

- [ ] **Step 4: Build (no code changed — still verify) and commit**

Run: `lake build` — zero warnings.

```bash
git add -A
git commit -m "feat: plateau-nesting probe and divergence-density table (C3 addendum, C6)"
```

---

### Task 3: `Simulation.refute_of_acyclic` — one mechanism, stated once

**Files:**
- Modify: `CombinatorCalculusPlayground/Universality/Taxonomy.lean` (append: `RS.Acyclic`, `RS.Steps.head_of_ne`, the theorem)
- Modify: `CombinatorCalculusPlayground/Universality/Calibration.lean` (append: the two Acyclic instances + subsumption examples; add `import CombinatorCalculusPlayground.Isometric` if not already present — it is, from Slice 2)

**Interfaces:**
- Consumes: `RS`, `RS.Steps` (refl/tail, `.trans`), `Simulation` (+ `fwd_steps`, `enc_injective`); `no_pure_S_cycle` (Isometric.lean); `iota_step_lt`, `iota_steps_le` (Calibration.lean, Stage 4); `RS.PureS_steps_iff`, `RS.SK_steps_iff`; `omegaSK`, `Mcycle`, `omega_to_M`, `M_to_omega`, `omega_ne_M`.
- Produces: `RS.Acyclic (B : RS) : Prop`; `RS.Steps.head_of_ne {B : RS} {b b' : B.Carrier} (h : B.Steps b b') (hne : b ≠ b') : ∃ w, B.step b w ∧ B.Steps w b'`; `Simulation.refute_of_acyclic {A B : RS} (hB : RS.Acyclic B) {a a' : A.Carrier} (h1 : A.Steps a a') (h2 : A.Steps a' a) (hne : a ≠ a') : ¬ Nonempty (Simulation A B)`; `RS.PureS_acyclic : RS.Acyclic RS.PureS`; `RS.Iota_acyclic : RS.Acyclic RS.Iota`.

- [ ] **Step 1: Taxonomy.lean — statements with `sorry` (RED: exactly two sorry warnings; the def lands whole)**

```lean
-- ## One refutation mechanism, stated once
-- Both hosting refutations (iota, Stage 4; pure S, Slice 2) are instances
-- of a single fact: an injective step-faithful simulation cannot carry a
-- two-point reduction cycle into an acyclic host. Strict growth (iota)
-- and τ-termination (pure S) were just two CAUSES of acyclicity. Stating
-- the mechanism generically makes every future refutation a one-liner:
-- prove your host Acyclic, exhibit any source cycle, done.

/-- No state begins a loop: a step out never comes back. -/
def RS.Acyclic (B : RS) : Prop :=
  ∀ {b b' : B.Carrier}, B.step b b' → B.Steps b' b → False

-- Peel a genuine first step off a nonempty path (generic twin of the
-- Term-level `Steps.head_of_ne` in Calibration.lean).
theorem RS.Steps.head_of_ne {B : RS} {b b' : B.Carrier}
    (h : B.Steps b b') (hne : b ≠ b') :
    ∃ w, B.step b w ∧ B.Steps w b' := sorry

theorem Simulation.refute_of_acyclic {A B : RS} (hB : RS.Acyclic B)
    {a a' : A.Carrier} (h1 : A.Steps a a') (h2 : A.Steps a' a)
    (hne : a ≠ a') : ¬ Nonempty (Simulation A B) := sorry
```

- [ ] **Step 2: Prove (GREEN)**

Candidates (both at a VARIABLE `B : RS` — ordinary `cases`/tactics work;
the mkElimApp friction is concrete-instance-only):

```lean
theorem RS.Steps.head_of_ne {B : RS} {b b' : B.Carrier}
    (h : B.Steps b b') (hne : b ≠ b') :
    ∃ w, B.step b w ∧ B.Steps w b' := by
  cases h with
  | refl => exact absurd rfl hne
  | tail s rest => exact ⟨_, s, rest⟩

theorem Simulation.refute_of_acyclic {A B : RS} (hB : RS.Acyclic B)
    {a a' : A.Carrier} (h1 : A.Steps a a') (h2 : A.Steps a' a)
    (hne : a ≠ a') : ¬ Nonempty (Simulation A B) := by
  rintro ⟨Sim⟩
  have e1 : B.Steps (Sim.enc a) (Sim.enc a') := Sim.fwd_steps h1
  have e2 : B.Steps (Sim.enc a') (Sim.enc a) := Sim.fwd_steps h2
  have hne' : Sim.enc a ≠ Sim.enc a' :=
    fun h => hne (Sim.enc_injective h)
  obtain ⟨w, hstep, hrest⟩ := RS.Steps.head_of_ne e1 hne'
  exact hB hstep (RS.Steps.trans hrest e2)
```

- [ ] **Step 3: Calibration.lean — the two Acyclic instances + subsumption (RED: two sorry warnings → GREEN)**

Append to Calibration.lean:

```lean
-- ## The two known acyclic hosts, as instances of RS.Acyclic
theorem RS.PureS_acyclic : RS.Acyclic RS.PureS := sorry

theorem RS.Iota_acyclic : RS.Acyclic RS.Iota := sorry
```

Candidates:

```lean
theorem RS.PureS_acyclic : RS.Acyclic RS.PureS := by
  intro b b' hstep hback
  -- a PureS step is a Term step on K-free values; the return path
  -- converts via the agreement lemma; no_pure_S_cycle finishes.
  exact no_pure_S_cycle b.property
    ⟨b'.val, hstep, RS.PureS_steps_iff.mp hback⟩

theorem RS.Iota_acyclic : RS.Acyclic RS.Iota := by
  intro b b' hstep hback
  -- strict growth forward, monotone return: |b| < |b'| ≤ |b|.
  have hlt := iota_step_lt hstep
  rcases iota_steps_le hback with heq | hlt2
  · exact absurd (heq ▸ hlt) (Nat.lt_irrefl _)
  · exact absurd (Nat.lt_trans hlt hlt2) (Nat.lt_irrefl _)
```

(`iota_steps_le` takes `RS.Iota.Steps` directly ✓ — check its actual
statement in Calibration.lean; the `heq ▸` orientation is the usual
read-the-goal adjustment.)

Then the subsumption demonstrations — the ORIGINAL refutation theorems
stay untouched; these examples prove the generic theorem recovers them:

```lean
-- Subsumption: both Stage 4's and Slice 2's refutations are one-liners
-- under the generic mechanism. The original theorems remain the citable
-- artifacts; these demonstrations pin the consolidation.
example : ¬ Nonempty (Simulation RS.SK RS.PureS) :=
  Simulation.refute_of_acyclic RS.PureS_acyclic
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M

example : ¬ Nonempty (Simulation RS.SK RS.Iota) :=
  Simulation.refute_of_acyclic RS.Iota_acyclic
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M
```

Run: `lake build` — zero warnings. Axiom audit (scratch, delete):
`#print axioms Simulation.refute_of_acyclic`, `RS.PureS_acyclic`,
`RS.Iota_acyclic` — record (expect [propext, Quot.sound] or better for the
instances; the generic theorem plausibly axiom-free).

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: one refutation mechanism — Simulation.refute_of_acyclic with both instances"
```

---

### Task 4: Registrations + ledger + notebook

**Files:**
- Modify: `CONJECTURES.md` (C5 registration; unbounded-trajectory corollary registration; C1 strategy note; Slice 3 section; methodology line)
- Modify: `LAB_NOTEBOOK.md` (dated entry)

**Interfaces:**
- Consumes (grep-verify): `isSubterm`, `c1`, `c2`, `RS.Acyclic`, `RS.Steps.head_of_ne`, `Simulation.refute_of_acyclic`, `RS.PureS_acyclic`, `RS.Iota_acyclic`; Task 1's recorded hunt outcome; Task 2's findings.
- Produces: the honest Slice 3 register. **NO conjecture status changes this slice** (C6 is newly ADDED as open by Task 2; everything else untouched).

- [ ] **Step 1: Register C5 and the corollary**

Add to CONJECTURES.md:

```markdown
## C5: Conservation for pure S (WN ⇒ SN) — status: open
In erasure-free calculi, weak normalization implies strong normalization
(the λI conservation theorem — Church 1941 territory; Barendregt §9.5 has
the modern treatment). Pure S is erasure-free (Stage 2), so conservation
SHOULD hold — but it is not formalized here, and nothing in this tree
depends on it yet. WHY IT MATTERS: it is the missing link of the loop
route to C1 — a self-embedding t →⁺ C[t] yields an infinite reduction;
conservation would upgrade that to "no normal form." Without it, a loop
proves only the existence of one infinite trajectory. Registered as a
future-slice target; classical proof routes exist (external), none
machine-checked here.

**Corollary registered alongside (statement ready, dependency noted):**
every infinite pure-S trajectory has unbounded size — bounded size plus
`no_pure_S_cycle` plus the finiteness of each size class would force a
revisit. Blocked on the same finiteness lemma as the pigeonhole queue
(`sTerms`-completeness chain); registered, not claimed.
```

- [ ] **Step 2: The C1 strategy note + Slice 3 section**

Under C1, add a strategy note reflecting Task 1's ACTUAL outcome:

```markdown
**Slice 3 reconnaissance:** [If no embedding found:] neither candidate
self-embeds (nor cross-embeds) within [F] leftmost-outermost steps
(`isSubterm` guards, `Reachability.lean` — fuel-bounded census data).
The loop route to C1 therefore has no cheap witness in the explored
prefix; the two live routes are (a) a leftmost-outermost reduction
invariant (decidable predicate preserved by `stepOnce`, implying
reducibility — none known yet; candidate features should be mined from
trajectory data), and (b) a loop witness deeper in the trajectory or
under a different strategy, combined with C5.
[If embedding found: state the step index and term, note the route now
runs through C5, and that the divergence proof was deliberately NOT
attempted this slice.]
```

Add the Slice 3 section (calibrated to actual outcomes):

```markdown
### Stage 5, Slice 3: the invariant observatory

Reconnaissance slice — by design it produced maps and one consolidation
theorem, and resolved nothing (as planned):
- Self-embedding hunt on the C1 candidates: [outcome].
- C3 plateau-nesting probe: [outcome].
- C6 registered (divergence density).
- **Consolidation theorem:** `Simulation.refute_of_acyclic`
  (`Universality/Taxonomy.lean`) — an injective step-faithful simulation
  cannot carry a two-point cycle into an acyclic host. `RS.PureS_acyclic`
  and `RS.Iota_acyclic` instantiate it; both existing refutations are
  recovered as one-line demonstrations (originals unchanged). Axioms:
  [record the audit].
- C5 (conservation) and the unbounded-trajectory corollary registered
  with dependencies.
```

Plus one methodology-header sentence.

- [ ] **Step 3: LAB_NOTEBOOK.md entry**

Dated entry (actual date), honest voice: the two ideonomy passes that
produced this slice (notation lens → loop route + required slots; timeline
crossing → the consolidation theorem); the explore-then-record discipline
and what the hunts actually returned; the expectation-setting (maps not
resolutions — and whether that held); axiom audits; next-target ranking as
it now stands (C1 invariant route vs C5 formalization vs diverging-pairs
core vs pigeonhole queue).

- [ ] **Step 4: Build and commit**

Run: `lake build` — zero warnings.

```bash
git add -A
git commit -m "feat: Stage 5 slice 3 ledger — observatory findings, C5/C6 registered"
```

---

## Self-review notes

- Explore-then-record discipline is explicit in Global Constraints and instantiated in Tasks 1–2 with both-outcome templates; no probe can pass vacuously without the artifact saying so.
- Expectation-setting ("maps, not resolutions") appears in the header, the Slice 3 section template, and the notebook instructions — no artifact can imply C1/C3/C6 were resolved.
- Type consistency: `isSubterm (s t : Term) : Bool` argument order consistent between Task 1 guards and Task 2's scratch usage; `c1`/`c2` defined Task 1, referenced Task 2/4; `RS.Acyclic`/`head_of_ne`/`refute_of_acyclic` signatures consistent between Taxonomy statements and Calibration instances/examples; `iota_steps_le` is the Slice 1-era Calibration lemma (grep before use — the plan flags reading its actual statement).
- Sorry counts: T1=0 (function+guards), T2=0 (prose), T3=4 (two in Taxonomy, two in Calibration), T4=0.
- Named risk sites: Task 1's compile-time cost (fuel-reduction instruction with honest recording); Task 1's render-guard authority rule (ledger strings win); Task 3's `heq ▸` orientation and `iota_steps_le` statement-check; Task 2's instruction to pull recorded numbers from the ledger rather than trusting the plan's sample rows.
- Import DAG: no new imports except those already present; Taxonomy gains nothing (RS.Acyclic uses only RS-level names); Calibration already imports Isometric (Slice 2). No cycles.
- C6 is an ADDITION (status open), not a change; the no-status-change rule is stated in Task 4.
