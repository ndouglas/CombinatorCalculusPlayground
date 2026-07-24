# Stage 5 Slice 2: The Isometric Fragment Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove conjecture C2 — pure-S reduction has no cycles, at any size, under any strategy (`no_pure_S_cycle`) — via a head-weight measure that strictly decreases on size-preserving steps, and derive the hosting refutation `no_sim_SK_pureS`: under the pinned Simulation class, the S combinator alone cannot host SK.

**Architecture:** The mathematical claim (derived in prose, UNVERIFIED until Task 1's probes pass): define τ(S) = τ(K) = 1, τ(app a b) = 2·τ(a) + τ(b). On a size-preserving K-free step — which by Stage 2's arithmetic forces the fired S-redex's third argument to be the atom S — τ drops by exactly 6 at the redex, and the positive coefficients carry strictness through congruence. Since any cycle is size-preserving at every step (sizes are monotone and return), τ would strictly decrease around a loop: contradiction, C2. Then SK's explicit Ω ↔ M cycle (already in Calibration.lean) yields the refutation exactly as it did for iota: mutually reachable distinct encodings would form a pure-S cycle. New `Isometric.lean` holds τ and C2; the refutation appends to `Universality/Calibration.lean`; STOP-gate probes append to `Reachability.lean` (which has `succs`/`sTerms` in scope).

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0`. Zero dependencies.
- **No `sorry` on main.** 3 documented failed attempts → statement to `CONJECTURES.md`, code removed (spec escape hatch).
- **No `partial def`.** Plain `decide`/`rfl` allowed; `native_decide` banned.
- Every commit must `lake build` clean with zero warnings.
- Comments state precisely what is machine-checked and at what level (kernel vs evaluator — the Slice 1 discipline).
- **Census-first:** Task 1's τ probes gate the slice. A failed probe = STOP, report the failing case; the arithmetic would be wrong and Tasks 2–4 pointless.
- **Framing discipline (the honesty burden of this slice):** `no_sim_SK_pureS` refutes step-faithful hosting under THIS taxonomy's pinned Simulation class. It does NOT resolve the Wolfram prize question, whose informal notion of universality is broader. Every artifact mention must carry this scope — the quotable form is: "if S alone is universal, its encoding must do non-step-faithful work." Overclaiming here would be the worst failure available to this program.
- Known instance-level friction: `.rec` pattern for inductions on `RS.Steps` at concrete instances (precedent comments in RS.lean); Term-level `Step`/`Steps` inductions are fine.

## Lean TDD adaptation (house rules)

- Functions: `#guard`s first (RED) → implement (GREEN). Theorems: `:= sorry` (RED, count stated) → proof (GREEN, zero warnings). NEVER commit with sorry.
- Candidates are candidates; statements are the contract. Named cases; hypothesis-threading inductions per Stage 2/Slice 1 precedent (`KFree` auto-reverts into motives or use `generalizing`).

---

### Task 1: τ and the CENSUS-FIRST STOP gate

**Files:**
- Create: `CombinatorCalculusPlayground/Isometric.lean`
- Modify: `CombinatorCalculusPlayground/Reachability.lean` (append probes; add `import CombinatorCalculusPlayground.Isometric`)
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Isometric` after SFragment, before RS)

**Interfaces:**
- Consumes: `Term`, `leafCount`, `app2`, `app3` (Term.lean); `KFree` (SFragment.lean, via import); `succs`, `sTerms`, `kFree` (Reachability.lean's scope, for the probes).
- Produces: `tau : Term → Nat` (S ↦ 1, K ↦ 1, app a b ↦ 2·tau a + tau b).

- [ ] **Step 1: Create `Isometric.lean` — τ with its guards**

```lean
--! # The isometric fragment and the head-weight measure
-- THE CLAIM THIS FILE EXISTS TO CHECK AND THEN PROVE: any cycle in
-- pure-S reduction would have to preserve leaf count at every step
-- (Stage 2: sizes are monotone, and around a loop they return), and a
-- size-preserving K-free step is exactly an S-redex whose third argument
-- is the atom S — the ISOMETRIC fragment. The head-weight measure below
-- strictly DECREASES on every isometric step, so no trajectory can loop:
-- conjecture C2 becomes a theorem (`no_pure_S_cycle`).
--
-- τ has a natural reading: each leaf weighs 2^(number of left-edges on
-- its root path) — material in head position weighs exponentially more,
-- and isometric steps push weight rightward. The head burns fuel.
--
-- EPISTEMIC STATUS while this file is under construction: the τ-decrease
-- arithmetic was derived on paper and is probed empirically in
-- Reachability.lean BEFORE the theorems below are attempted. The
-- paper-level idea (polynomial interpretations proving termination) is
-- STANDARD term-rewriting technology; its application to C2 may well be
-- known — the machine-checked resolution is the contribution claimed.
import CombinatorCalculusPlayground.SFragment

open Term

/-- Head weight: leaves in head (left) position count exponentially. -/
def tau : Term → Nat
  | .S => 1
  | .K => 1
  | .app a b => 2 * tau a + tau b

-- Hand-checked values (S S S S is the classic isometric redex):
#guard tau S = 1
#guard tau (app S S) = 3
#guard tau (app (app S S) S) = 7
#guard tau (app3 S S S S) = 15
-- ...and its reduct (S S)(S S) weighs 9: the promised drop of exactly 6.
#guard tau (app (app S S) (app S S)) = 9
```

- [ ] **Step 2: Append the STOP-gate probes to `Reachability.lean`**

Add `import CombinatorCalculusPlayground.Isometric` to Reachability.lean's imports, and append:

```lean
-- ## Slice 2 CENSUS-FIRST PROBES (the STOP gate for Isometric.lean)
-- The τ-decrease claim, checked empirically over every pure-S term with
-- ≤ 6 leaves BEFORE any proof effort. If EITHER probe fails: STOP, do
-- not adjust anything, report the failing term — the slice's arithmetic
-- would be wrong.

-- Probe A: on every SIZE-PRESERVING successor step, τ strictly drops.
#guard (List.range 7).all fun n => (sTerms n).all fun t =>
  (succs t).all fun v =>
    leafCount v != leafCount t || decide (tau v < tau t)

-- Probe B: the drop at a root isometric redex is exactly 6 — spot-check
-- the arithmetic's exactness on every size-4 S-term that IS a root
-- isometric redex (third argument atomic).
#guard (sTerms 4).all fun t =>
  match t with
  | .app (.app (.app .S _) _) .S =>
    (succs t).any fun v => leafCount v == leafCount t && tau t - tau v == 6
  | _ => true
```

Run: `lake build`
Expected: `Build completed successfully`, zero warnings, all guards pass. Probe A is the load-bearing one (`!=` short-circuits non-isometric successors; the `decide` wraps the Prop `<` into the Bool world). If Probe A fails, extract the failing (t, v) with a temporary `#eval` (removed before commit), hand-compute τ on both, and STOP with the numbers.

- [ ] **Step 3: Root import; commit**

```bash
git add -A
git commit -m "feat: head-weight measure tau with census-first isometric probes"
```

---

### Task 2: The core arithmetic — τ strictly decreases on isometric steps

**Files:**
- Modify: `CombinatorCalculusPlayground/Isometric.lean` (append)

**Interfaces:**
- Consumes: `tau`; `KFree` (constructors S, app), `leafCount`, `leafCount_pos` (SFragment.lean); `Step` (K_red, S_red, appL, appR), notation ⟶.
- Produces: `tau_pos : ∀ (t : Term), 1 ≤ tau t`; `KFree.leafCount_eq_one : KFree x → leafCount x = 1 → x = Term.S`; `tau_lt_of_isometric_step : ∀ {t u : Term}, KFree t → (t ⟶ u) → leafCount t = leafCount u → tau u < tau t`.

- [ ] **Step 1: State all three with `sorry` (RED: exactly three warnings)**

```lean
-- ## The decrease lemma
theorem tau_pos : ∀ (t : Term), 1 ≤ tau t := sorry

-- In a K-free term, one leaf means THE atom.
theorem KFree.leafCount_eq_one {x : Term} (hk : KFree x)
    (h : leafCount x = 1) : x = Term.S := sorry

-- The heart of the slice: a size-preserving K-free step strictly drops τ.
-- (Size preservation forces the S-redex's third argument to be atomic —
-- Stage 2's arithmetic — and then the drop at the redex is exactly 6,
-- carried through congruence by τ's positive coefficients.)
theorem tau_lt_of_isometric_step : ∀ {t u : Term}, KFree t → (t ⟶ u) →
    leafCount t = leafCount u → tau u < tau t := sorry
```

Run: `lake build` — exactly three sorry warnings.

- [ ] **Step 2: Prove, in order (GREEN)**

Candidates:

```lean
theorem tau_pos : ∀ (t : Term), 1 ≤ tau t := by
  intro t
  induction t with
  | S => simp [tau]
  | K => simp [tau]
  | app a b iha ihb => simp [tau]; omega

theorem KFree.leafCount_eq_one {x : Term} (hk : KFree x)
    (h : leafCount x = 1) : x = Term.S := by
  cases hk with
  | S => rfl
  | app hl hr =>
    -- an application has ≥ 2 leaves: contradiction
    have h1 := leafCount_pos _   -- left subterm (supply the term)
    have h2 := leafCount_pos _   -- right subterm
    simp [leafCount] at h
    omega
```

(`cases hk` gives exactly the two KFree constructors — K is impossible by
K-freeness, and the case analysis knows it. The `leafCount_pos` argument
placeholders: name the subterms from the `app` pattern, e.g.
`| app (t := l) (u := r) hl hr` or positional — read the constructor's
actual binder names in SFragment.lean.)

```lean
theorem tau_lt_of_isometric_step : ∀ {t u : Term}, KFree t → (t ⟶ u) →
    leafCount t = leafCount u → tau u < tau t := by
  intro t u hk h
  induction h with
  | K_red x y =>
    -- K-free t cannot contain the firing K: the Stage 2 vacuity pattern.
    intro _
    cases hk with | app hl _ =>
    cases hl with | app hK _ =>
    cases hK
  | S_red f g x =>
    intro hsize
    -- Size equality forces leafCount x = 1, hence x = S.
    have hkx : KFree x := by
      cases hk with | app _ hx => exact hx
    have hx1 : leafCount x = 1 := by
      simp [leafCount, app3] at hsize
      omega
    have hxS : x = Term.S := hkx.leafCount_eq_one hx1
    subst hxS
    -- τ(S f g S) = 4τf + 2τg + 9  >  4τf + 2τg + 3 = τ((f S)(g S))
    simp [tau, app3]
    omega
  | appL s ih =>
    intro hsize
    cases hk with | app hl hr =>
    -- whole-size equality gives subterm-size equality by plain arithmetic
    have : leafCount _ = leafCount _ := by
      simp [leafCount] at hsize
      omega
    have := ih hl this
    simp [tau]
    omega
  | appR s ih =>
    intro hsize
    cases hk with | app hl hr =>
    have : leafCount _ = leafCount _ := by
      simp [leafCount] at hsize
      omega
    have := ih hr this
    simp [tau]
    omega
```

CAUTION (the same threading dance as Stage 2 / Slice 1): `induction h`
must leave `hk` and the size hypothesis usable per-case — the candidate
introduces the size hypothesis AFTER the induction (`intro hsize` in each
case) so the IH keeps its slots; if the elaborator fights, `induction h
generalizing` or hoist `hk` explicitly. The two `leafCount _ = leafCount _`
underscore pairs must name the stepping subterm and its reduct (read the
case's goal). The S_red τ-arithmetic (`simp [tau, app3]` then `omega`) is
the exact-6 drop; if `simp` normalizes differently, unfold by `show` and
let `omega` finish — the numbers are fixed.

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: tau strictly decreases on isometric steps"
```

---

### Task 3: C2 — `no_pure_S_cycle` (the program's first conjecture resolution)

**Files:**
- Modify: `CombinatorCalculusPlayground/Isometric.lean` (append)

**Interfaces:**
- Consumes: `tau_lt_of_isometric_step`; `KFree.of_step`, `leafCount_le_of_step`, `leafCount_le_of_steps` (SFragment.lean); `Steps` (refl/tail), `Steps.trans`.
- Produces: `tau_lt_of_steps_size_eq : ∀ {t u : Term}, KFree t → (t ⟶* u) → leafCount t = leafCount u → t = u ∨ tau u < tau t`; `no_pure_S_cycle : ∀ {t : Term}, KFree t → ¬ ∃ v, (t ⟶ v) ∧ (v ⟶* t)`.

**Escape hatch (spec):** 3 documented attempts per theorem, then CONJECTURES registration + removal — but note: if THESE fail, the slice's headline dies; escalate loudly, not quietly.

- [ ] **Step 1: State both with `sorry` (RED: exactly two warnings)**

```lean
-- ## Around a size-plateau, τ can only fall
theorem tau_lt_of_steps_size_eq : ∀ {t u : Term}, KFree t → (t ⟶* u) →
    leafCount t = leafCount u → t = u ∨ tau u < tau t := sorry

-- ## C2, resolved: pure-S reduction never cycles — any size, any strategy.
-- (The census conjectured this for leftmost-outermost up to 12 leaves;
-- the theorem is strictly stronger on both axes.)
theorem no_pure_S_cycle : ∀ {t : Term}, KFree t →
    ¬ ∃ v, (t ⟶ v) ∧ (v ⟶* t) := sorry
```

Run: `lake build` — exactly two sorry warnings.

- [ ] **Step 2: Prove (GREEN)**

Candidates:

```lean
theorem tau_lt_of_steps_size_eq : ∀ {t u : Term}, KFree t → (t ⟶* u) →
    leafCount t = leafCount u → t = u ∨ tau u < tau t := by
  intro t u hk h
  induction h with
  | refl => intro _; exact Or.inl rfl
  | tail s rest ih =>
    intro hsize
    -- t ⟶ w ⟶* u on a size plateau: both legs are size-equal by the
    -- monotonicity squeeze (|t| ≤ |w| ≤ |u| = |t|).
    have hk1 : KFree _ := hk.of_step s
    have hw_le := leafCount_le_of_step hk s
    have hu_le := leafCount_le_of_steps hk1 rest
    have hw_eq : leafCount _ = leafCount _ := by omega   -- |t| = |w|
    have hwu_eq : leafCount _ = leafCount _ := by omega  -- |w| = |u|
    have hdrop := tau_lt_of_isometric_step hk s hw_eq
    rcases ih hk1 hwu_eq with heq | hlt
    · exact Or.inr (heq ▸ hdrop)
    · exact Or.inr (Nat.lt_trans hlt hdrop)
  -- (as before: if the IH arrives without slots, restructure with
  --  `generalizing` — Stage 2 / Slice 1 precedent.)

theorem no_pure_S_cycle : ∀ {t : Term}, KFree t →
    ¬ ∃ v, (t ⟶ v) ∧ (v ⟶* t) := by
  rintro t hk ⟨v, hstep, hback⟩
  have hkv : KFree v := hk.of_step hstep
  -- the squeeze: |t| ≤ |v| (one step) and |v| ≤ |t| (the return) — equal.
  have h1 := leafCount_le_of_step hk hstep
  have h2 := leafCount_le_of_steps hkv hback
  have hsize_tv : leafCount t = leafCount v := by omega
  have hsize_vt : leafCount v = leafCount t := by omega
  -- τ drops on the step...
  have hdrop := tau_lt_of_isometric_step hk hstep hsize_tv
  -- ...and can only fall (or stall via equality) on the return.
  rcases tau_lt_of_steps_size_eq hkv hback hsize_vt with heq | hlt
  · -- v = t: then the step was t ⟶ t with τ t < τ t.
    rw [heq] at hdrop
    exact absurd hdrop (Nat.lt_irrefl _)
  · -- τ t < τ v < τ t.
    exact absurd (Nat.lt_trans hlt hdrop) (Nat.lt_irrefl _)
```

Careful with the `heq ▸ hdrop` / `rw` orientations — `tau_lt_of_steps_size_eq`'s
equality is `t = u` (source = target of the multi-step); in `no_pure_S_cycle`
it instantiates as `v = t`. Read the actual goal and orient. The disjunct
bookkeeping is small; the mathematics is fixed.

Run: `lake build` — zero warnings. Then the axiom audit (scratch, delete):
`#print axioms no_pure_S_cycle`, `tau_lt_of_isometric_step` — record.

- [ ] **Step 3: Cross-check against the Slice 1 machinery**

Append — the theorem and the evaluator sweep should agree, and now the
theorem SUBSUMES the sweep; record the relationship precisely:

```lean
-- Cross-check: the Slice 1 evaluator sweep (`onCycle?` over ≤ 6 leaves)
-- and the kernel theorems `ssss_not_on_cycle`/`sssss_not_on_cycle` are
-- now special cases of `no_pure_S_cycle`. They remain in the tree as
-- independent evidence paths (evaluator, per-instance kernel, and now
-- general kernel) — three levels that agree.
example : ¬ ∃ v, ((app3 S S S S) ⟶ v) ∧ (v ⟶* (app3 S S S S)) :=
  no_pure_S_cycle (by repeat constructor)
```

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: C2 resolved — pure-S reduction has no cycles (no_pure_S_cycle)"
```

---

### Task 4: The hosting refutation — `no_sim_SK_pureS`

**Files:**
- Modify: `CombinatorCalculusPlayground/Universality/Calibration.lean` (append; add `import CombinatorCalculusPlayground.Isometric`)

**Interfaces:**
- Consumes: `no_pure_S_cycle` (Task 3); `Simulation` (+ `fwd_steps`, `enc_injective`), `UniversalReach`, `UniversalNorm`, `UniversalConv` (Universality/Defs.lean); `RS.PureS`, `RS.PureS_steps_iff` (RS.lean); `Wdup`, `omegaSK`, `Mcycle`, `omega_to_M`, `M_to_omega`, `omega_ne_M` (this file, Stage 4); `RS.SK_steps_iff`; `Steps.trans`.
- Produces: `Steps.head_of_ne : ∀ {t u : Term}, (t ⟶* u) → t ≠ u → ∃ w, (t ⟶ w) ∧ (w ⟶* u)`; `no_sim_SK_pureS : ¬ Nonempty (Simulation RS.SK RS.PureS)`; `pureS_not_universalReach_for_SK : ¬ UniversalReach RS.SK RS.PureS`; `pureS_not_universalNorm_for_SK : ¬ UniversalNorm RS.SK RS.PureS`; `pureS_not_universalConv_for_SK : ¬ UniversalConv RS.SK RS.PureS`.

- [ ] **Step 1: State all five with `sorry` (RED: exactly five warnings)**

```lean
-- ## The prize-adjacent refutation
-- SCOPE, stated before the theorem so nobody quotes it without this:
-- what follows refutes STEP-FAITHFUL hosting of SK inside pure S, under
-- this taxonomy's pinned Simulation class — the same class the iota
-- refutation used. It does NOT resolve the Wolfram prize question, whose
-- informal notion of universality admits broader encodings. What it
-- establishes precisely: if S alone is universal, its encoding must do
-- non-step-faithful work. The mechanism is the same as iota's, with
-- acyclicity (no_pure_S_cycle) playing the role strict growth played
-- there: SK's explicit Ω ↔ M cycle cannot be carried by an injective
-- encoding into a cycle-free system.
theorem Steps.head_of_ne : ∀ {t u : Term}, (t ⟶* u) → t ≠ u →
    ∃ w, (t ⟶ w) ∧ (w ⟶* u) := sorry

theorem no_sim_SK_pureS : ¬ Nonempty (Simulation RS.SK RS.PureS) := sorry

theorem pureS_not_universalReach_for_SK : ¬ UniversalReach RS.SK RS.PureS := sorry

theorem pureS_not_universalNorm_for_SK : ¬ UniversalNorm RS.SK RS.PureS := sorry

theorem pureS_not_universalConv_for_SK : ¬ UniversalConv RS.SK RS.PureS := sorry
```

Run: `lake build` — exactly five sorry warnings.

- [ ] **Step 2: Prove (GREEN)**

Candidates:

```lean
theorem Steps.head_of_ne : ∀ {t u : Term}, (t ⟶* u) → t ≠ u →
    ∃ w, (t ⟶ w) ∧ (w ⟶* u) := by
  intro t u h hne
  cases h with
  | refl => exact absurd rfl hne
  | tail s rest => exact ⟨_, s, rest⟩

theorem no_sim_SK_pureS : ¬ Nonempty (Simulation RS.SK RS.PureS) := by
  rintro ⟨Sim⟩
  -- carry the SK cycle across: enc Ω and enc M are mutually reachable
  -- subtype elements of the K-free carrier.
  have h1 : RS.PureS.Steps (Sim.enc omegaSK) (Sim.enc Mcycle) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr omega_to_M)
  have h2 : RS.PureS.Steps (Sim.enc Mcycle) (Sim.enc omegaSK) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr M_to_omega)
  -- translate to Term-level Steps on the underlying (K-free!) values
  have hv1 : (Sim.enc omegaSK).val ⟶* (Sim.enc Mcycle).val :=
    RS.PureS_steps_iff.mp h1
  have hv2 : (Sim.enc Mcycle).val ⟶* (Sim.enc omegaSK).val :=
    RS.PureS_steps_iff.mp h2
  -- distinct encodings (enc is injective; Ω ≠ M), hence distinct values
  have hne : (Sim.enc omegaSK).val ≠ (Sim.enc Mcycle).val := by
    intro hval
    exact omega_ne_M (Sim.enc_injective (Subtype.ext hval))
  -- a genuine first step exists, and the rest closes the loop: a cycle.
  obtain ⟨w, hstep, hrest⟩ := Steps.head_of_ne hv1 hne
  exact no_pure_S_cycle (Sim.enc omegaSK).property
    ⟨w, hstep, Steps.trans hrest hv2⟩

theorem pureS_not_universalReach_for_SK : ¬ UniversalReach RS.SK RS.PureS :=
  no_sim_SK_pureS

theorem pureS_not_universalNorm_for_SK : ¬ UniversalNorm RS.SK RS.PureS :=
  fun ⟨S, _⟩ => no_sim_SK_pureS ⟨S⟩

theorem pureS_not_universalConv_for_SK : ¬ UniversalConv RS.SK RS.PureS :=
  fun ⟨S, _⟩ => no_sim_SK_pureS ⟨S⟩
```

(`Subtype.ext` direction: from value equality to subtype equality — check
the core name (`Subtype.ext` takes val-equality; if the elaborator wants
`Subtype.val_injective` or an `ext`-lemma spelled differently, adapt).
`(Sim.enc omegaSK).property : KFree (Sim.enc omegaSK).val` is the carrier's
certificate — that the host's OWN TYPE hands us K-freeness is the whole
point of the subtype design. If `UniversalNorm`'s ∃-destructuring needs
`obtain` instead of the anonymous-constructor `fun`, adapt.)

Run: `lake build` — zero warnings. Axiom audit (scratch, delete):
`#print axioms no_sim_SK_pureS` and the three corollaries — record.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: pure S cannot host SK — acyclicity meets the Omega cycle"
```

---

### Task 5: Ledger + notebook — the first resolved conjecture

**Files:**
- Modify: `CONJECTURES.md`
- Modify: `LAB_NOTEBOOK.md`

**Interfaces:**
- Consumes (grep-verify every name): `tau`, `tau_lt_of_isometric_step`, `tau_lt_of_steps_size_eq`, `no_pure_S_cycle`, `Steps.head_of_ne`, `no_sim_SK_pureS`, `pureS_not_universalReach_for_SK`, `pureS_not_universalNorm_for_SK`, `pureS_not_universalConv_for_SK`.
- Produces: the updated register. **C2's status line changes to `proved` — the program's first conjecture resolution. This is the ONLY status change permitted.**

- [ ] **Step 1: Update C2 in `CONJECTURES.md`**

Change C2's heading status to `proved` and add at the top of its body
(keep the historical census text below it, prefixed as history):

```markdown
## C2: No proper cycles in pure-S reduction — status: PROVED
**Resolved (Stage 5, Slice 2):** `no_pure_S_cycle` (`Isometric.lean`) —
for every K-free t there is no v with t ⟶ v and v ⟶* t. The theorem is
STRONGER than the census conjecture on both axes: any strategy (not just
leftmost-outermost) and any size (not just ≤ 12 leaves). Mechanism: any
cycle must preserve leaf count at every step (Stage 2 monotonicity
squeezed around the loop); a size-preserving K-free step is an S-redex
with atomic third argument; the head-weight measure τ (τ(app a b) =
2·τ(a) + τ(b)) strictly drops by 6 at every such redex
(`tau_lt_of_isometric_step`) and cannot return. Axioms: [record the
audit]. The τ technique is standard term-rewriting technology
(polynomial interpretation); its application here may be folklore — the
machine-checked resolution is the contribution claimed. The Slice 1
evaluator sweep and kernel instances remain in the tree as independent
evidence paths that now agree with the general theorem.
```

- [ ] **Step 2: Add the hosting-refutation section + update the ledger table**

New section (adapt names only after grep-verification):

```markdown
### Stage 5, Slice 2: the isometric fragment

- **C2 is the program's first resolved conjecture** (see C2 above).
- **Prize-adjacent refutation, precisely scoped:** `no_sim_SK_pureS`
  (`Universality/Calibration.lean`) — under this taxonomy's pinned
  Simulation class, pure S cannot host SK: SK's explicit Ω ↔ M reduction
  cycle cannot be carried by an injective encoding into a system that
  `no_pure_S_cycle` proves cycle-free. All three observation modes fall
  together as named theorems (`pureS_not_universalReach_for_SK`,
  `pureS_not_universalNorm_for_SK`, `pureS_not_universalConv_for_SK`),
  since all three quantify over `Simulation`. SCOPE — read before
  quoting: this does NOT resolve the Wolfram prize question, whose
  informal universality admits broader encodings than step-faithful
  simulation. What is now machine-checked: **if S alone is universal,
  its encoding must do non-step-faithful work.** The taxonomy has
  located the prize question in the gap between the pinned class and
  the informal one — which is exactly the definitional territory the
  program was built to map.
- **The refutation mechanism, unified:** iota fell to strict growth
  (Stage 4); pure S falls to acyclicity (this slice). Both are instances
  of one pattern — a system whose reduction order admits no return trips
  cannot host a cyclic source under injective step-faithful encoding.
  C4's strictly-size-increasing class is one cause of no-return; τ-style
  termination of the isometric fragment is another. (C4's statement is
  unchanged; this remark widens the observed pattern, not the
  conjecture.)
```

Update the ledger table's PureS row: Reach/Norm/Conv vs reference SK →
REFUTED (named theorems); vs reference Tag → still open, with a footnote
that the same mechanism would refute Tag→PureS for any tag system with a
reduction cycle (not formalized). Update the methodology header with one
Slice 2 sentence.

- [ ] **Step 3: `LAB_NOTEBOOK.md` entry**

Dated entry (actual execution date), honest voice: the ideonomy pass that
produced τ (cross-domain: termination-by-polynomial-interpretation applied
to the cycle question); the census gate outcome; which candidates survived;
the axiom audits; the framing-discipline work on the refutation; and the
milestone sentence: the program's first conjecture RESOLUTION, and the
second time the Ω cycle has served as the refuting witness. Note for the
future: C1 divergence proofs are the natural next target and need
NON-termination tools (the other polarity of the same toolbox).

- [ ] **Step 4: Build and commit**

Run: `lake build` — zero warnings.

```bash
git add -A
git commit -m "feat: Stage 5 slice 2 ledger — C2 proved, pure S cannot host SK"
```

---

## Self-review notes

- Conservatism honored: STOP-gate probes precede all proofs (Task 1, load-bearing Probe A); the refutation's scope paragraph is written INTO the code above the theorem (Task 4) so it cannot be quoted without its frame; the folklore caveat appears in both the module docstring and C2's ledger text; the ONLY status change is C2 → proved.
- Type consistency: `tau : Term → Nat` consistent across all tasks; `tau_lt_of_isometric_step`'s hypothesis order (KFree, Step, size-eq) matches its uses in Tasks 3; `tau_lt_of_steps_size_eq`'s disjunction (`t = u ∨ tau u < tau t`) matches `no_pure_S_cycle`'s case analysis; `Steps.head_of_ne` produced and consumed in Task 4; `omegaSK`/`Mcycle`/`omega_to_M`/`M_to_omega`/`omega_ne_M` are the Stage 4 names (grep-verified in Calibration.lean); the corollaries' ∃-shapes match Stage 3's pinned `UniversalNorm`/`UniversalConv` (∃ S : Simulation …).
- Sorry counts for RED gates: T1=0, T2=3, T3=2, T4=5, T5=0.
- Named risk sites: T2's hypothesis-threading induction (precedent cited); T3's equality orientation in the disjunct bookkeeping; T4's `Subtype.ext` spelling; Probe B's match-pattern shape (if no size-4 term matches the root-redex pattern the guard passes vacuously — acceptable, Probe A carries the load).
- Import DAG: Isometric imports SFragment only; Reachability adds Isometric (no cycle — Isometric imports nothing from Reachability); Calibration adds Isometric (Calibration already imports Defs + Iota; no cycle). Root order: … SFragment, Isometric, RS, ….
- Placeholder scan: T2's `leafCount_pos _` and `leafCount _ = leafCount _` underscores are explicitly flagged compiler-driven slots with instructions; no TBDs.
