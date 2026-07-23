# Stage 2: Conservation Laws of the S-Fragment Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize what pure-S reduction preserves — K-freeness is closed under reduction, leaf count never decreases (no erasure), cycles are leaf-count-constant (a proven constraint on census conjecture C2), and K-free normal forms have an exact structural shape — with executable census cross-validation.

**Architecture:** A new `SFragment.lean` (imports Step.lean only) holds the `KFree` predicate, its reduction-closure, the leaf-count monotonicity laws, and the structural normal-form characterization `SNF`. Census cross-validation guards live in `Census/Enumerate.lean` (which gains an SFragment import). The module docstring carries the spec-mandated honest framing: these laws explain why naive erasure-based encodings fail; they are NOT an impossibility argument — the λI-calculus is the standing counterexample.

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0`. Zero dependencies.
- **No `sorry` on main.** A theorem that resists 3 documented attempts gets its statement recorded in `CONJECTURES.md` and is removed from the code (spec escape hatch).
- **No `partial def`** anywhere.
- Every commit must `lake build` clean with zero warnings.
- Pedagogical comment style; comments state precisely what is machine-checked.
- **Honest framing is a spec requirement, verbatim:** "these laws explain why *naive* encodings fail; they are NOT an impossibility argument — λI is the standing counterexample. The module docstring must say so."

## Lean TDD adaptation (same as Stages 0–1)

- Functions: `#guard` tests first (RED: unknown identifier) → implement (GREEN).
- Theorems: statement `:= sorry` (RED: only sorry warnings) → proof (GREEN: zero warnings). NEVER commit with sorry.
- Candidate proofs are candidates; the statements are the contract. House precedent: named cases, no `first |` catch-alls; `fun_induction` for function-shaped goals; qualify `Term.S`/`Term.K` inside namespaces where constructor names shadow.

---

### Task 1: `SFragment.lean` — the `KFree` predicate

**Files:**
- Create: `CombinatorCalculusPlayground/SFragment.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.SFragment` after Confluence, before Census imports)

**Interfaces:**
- Consumes: `Term` (.S/.K/.app), `I` (= `app2 S K K`) from Term.lean; Step.lean via import.
- Produces: `KFree : Term → Prop` (constructors `S : KFree Term.S`, `app : KFree t → KFree u → KFree (Term.app t u)`); `kFree : Term → Bool`; `kFree_iff : ∀ {t : Term}, kFree t = true ↔ KFree t` (and via it, `instance : DecidablePred KFree`).

- [ ] **Step 1: Create the file with docstring, `KFree`, and failing `#guard`s (RED)**

Create `CombinatorCalculusPlayground/SFragment.lean`:

```lean
--! # Conservation laws of the S-fragment
-- Pure-S terms (no K anywhere) are the arena of the prize question. This
-- module proves what S-reduction CONSERVES: K-freeness itself, and leaf
-- count (S cannot erase — its reduct mentions every argument).
--
-- HONEST FRAMING (spec requirement): these laws explain why *naive*
-- encodings into pure S fail — you cannot discard scaffolding, so
-- halting-as-normalization tricks that rely on erasure don't transfer.
-- They are NOT an impossibility argument. The λI-calculus (equivalently
-- the {S,B,C,I} basis) is also erasure-free, and it is computationally
-- complete for total computable functions (Church 1941; Barendregt §9.5). Whatever
-- blocks S alone — if anything does — is not mere non-erasure.
import CombinatorCalculusPlayground.Step

open Term

-- A term is K-free when every leaf is S. The only ways to build one:
inductive KFree : Term → Prop
  | S : KFree Term.S
  | app {t u : Term} : KFree t → KFree u → KFree (Term.app t u)

-- Executable twin, for census guards and decidability.
def kFree : Term → Bool
  | .S => true
  | .K => false
  | .app t u => kFree t && kFree u

#guard kFree S = true
#guard kFree K = false
#guard kFree I = false                         -- I = S K K smuggles two K's
#guard kFree (app (app S S) S) = true
#guard kFree (app S (app S K)) = false
```

Run: `lake build`
Expected: FAIL — `unknown identifier 'kFree'` is impossible here since def precedes guards; instead this step's RED is for the NEXT declaration: proceed to Step 2's statement before building, or build now and expect GREEN for the guards alone. (Guards for a just-written function serve as immediate tests; the theorem below is the RED/GREEN cycle.)

- [ ] **Step 2: State `kFree_iff` with `sorry` (RED), add the import**

Append:

```lean
-- The Bool and the Prop agree — so KFree is decidable, and census guards
-- can speak for the proposition.
theorem kFree_iff : ∀ {t : Term}, kFree t = true ↔ KFree t := sorry

instance : DecidablePred KFree := fun t =>
  decidable_of_iff (kFree t = true) kFree_iff
```

Add `import CombinatorCalculusPlayground.SFragment` to `CombinatorCalculusPlayground.lean` (after Confluence, before Census).

Run: `lake build`
Expected: builds with exactly one `sorry` warning.

- [ ] **Step 3: Prove it (GREEN)**

```lean
theorem kFree_iff : ∀ {t : Term}, kFree t = true ↔ KFree t := by
  intro t
  induction t with
  | S => simp [kFree]; exact KFree.S
  | K => simp [kFree]; intro h; cases h
  | app l r ihl ihr =>
    simp [kFree, Bool.and_eq_true, ihl, ihr]
    constructor
    · exact fun ⟨hl, hr⟩ => KFree.app hl hr
    · intro h; cases h with | app hl hr => exact ⟨hl, hr⟩
```

(Adapt the `simp`/`constructor` bookkeeping freely — e.g. the K case may close by `simp [kFree]` alone once it sees `false = true` implies anything, or need `nofun`. The statement and the instance are the contract.)

Run: `lake build`
Expected: `Build completed successfully`, zero warnings.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: KFree predicate with decidable Bool twin and honest framing"
```

---

### Task 2: K-freeness is closed under reduction

**Files:**
- Modify: `CombinatorCalculusPlayground/SFragment.lean` (append)

**Interfaces:**
- Consumes: `KFree` (Task 1), `Step`, `Steps` (⟶, ⟶*), `app2`, `app3`.
- Produces: `KFree.of_step : KFree t → t ⟶ u → KFree u`; `KFree.of_steps : KFree t → t ⟶* u → KFree u`.

- [ ] **Step 1: State both with `sorry` (RED)**

Append to `SFragment.lean`:

```lean
-- ## Closure under reduction
-- The S-fragment is a world unto itself: reduction can never manufacture
-- a K. (The K-redex case is vacuous — a K-free term cannot contain the
-- K that would fire.)
theorem KFree.of_step {t u : Term} (hk : KFree t) (h : t ⟶ u) : KFree u := sorry

theorem KFree.of_steps {t u : Term} (hk : KFree t) (h : t ⟶* u) : KFree u := sorry
```

Run: `lake build` — expect exactly two sorry warnings.

- [ ] **Step 2: Prove (GREEN)**

Candidates:

```lean
theorem KFree.of_step {t u : Term} (hk : KFree t) (h : t ⟶ u) : KFree u := by
  induction h with
  | K_red x y =>
    -- t = app (app K x) y and KFree t: invert twice to expose KFree K.
    cases hk with | app hl _ =>
    cases hl with | app hK _ =>
    cases hK
  | S_red f g x =>
    -- t = app (app (app S f) g) x: harvest KFree f, g, x, reassemble.
    cases hk with | app hl hx =>
    cases hl with | app hl2 hg =>
    cases hl2 with | app _ hf =>
    exact KFree.app (KFree.app hf hx) (KFree.app hg hx)
  | appL _ ih =>
    cases hk with | app hl hr => exact KFree.app (ih hl) hr
  | appR _ ih =>
    cases hk with | app hl hr => exact KFree.app hl (ih hr)

theorem KFree.of_steps {t u : Term} (hk : KFree t) (h : t ⟶* u) : KFree u := by
  induction h with
  | refl => exact hk
  | tail s _ ih => exact ih (hk.of_step s)
```

Note: `app2 K x y` in `Step.K_red`'s type is definitionally `app (app K x) y`, so `cases hk` sees an `app` — the nested inversions land as written or after a `show`/`simp only [app2, app3] at hk`. Iterate against the compiler.

Run: `lake build` — expect zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: K-freeness is closed under reduction"
```

---

### Task 3: No erasure — leaf-count monotonicity and the cycle constraint

**Files:**
- Modify: `CombinatorCalculusPlayground/SFragment.lean` (append)

**Interfaces:**
- Consumes: `KFree`, `KFree.of_step`, `KFree.of_steps` (Task 2), `leafCount` (Term.lean), `Step`, `Steps`.
- Produces: `leafCount_pos : ∀ (t : Term), 1 ≤ leafCount t`; `leafCount_le_of_step : KFree t → t ⟶ u → leafCount t ≤ leafCount u`; `leafCount_le_of_steps : KFree t → t ⟶* u → leafCount t ≤ leafCount u`; `cycle_leafCount_eq : KFree t → t ⟶* u → u ⟶* t → leafCount t = leafCount u`.

- [ ] **Step 1: State all four with `sorry` (RED)**

Append to `SFragment.lean`:

```lean
-- ## No erasure
-- The heart of the conservation story. An S-step S f g x → (f x)(g x)
-- keeps one copy of f and g and DUPLICATES x; nothing is discarded.
-- Leaf count: |f|+|g|+|x|+1 becomes |f|+|g|+2|x|, a gain of |x|-1 ≥ 0.
-- (K-steps erase — which is exactly why they're excluded by KFree.)

-- Every term has at least one leaf.
theorem leafCount_pos : ∀ (t : Term), 1 ≤ leafCount t := sorry

theorem leafCount_le_of_step {t u : Term} (hk : KFree t) (h : t ⟶ u) :
    leafCount t ≤ leafCount u := sorry

theorem leafCount_le_of_steps {t u : Term} (hk : KFree t) (h : t ⟶* u) :
    leafCount t ≤ leafCount u := sorry

-- A proven constraint on census conjecture C2: if a K-free term sits on
-- a reduction cycle, every term on that cycle has the SAME leaf count.
-- Any hunt for S-cycles can restrict to size-preserving steps.
theorem cycle_leafCount_eq {t u : Term} (hk : KFree t)
    (h1 : t ⟶* u) (h2 : u ⟶* t) : leafCount t = leafCount u := sorry
```

Run: `lake build` — expect exactly four sorry warnings.

- [ ] **Step 2: Prove (GREEN)**

Candidates:

```lean
theorem leafCount_pos : ∀ (t : Term), 1 ≤ leafCount t := by
  intro t
  induction t with
  | S => simp [leafCount]
  | K => simp [leafCount]
  | app l r ihl ihr => simp [leafCount]; omega

theorem leafCount_le_of_step {t u : Term} (hk : KFree t) (h : t ⟶ u) :
    leafCount t ≤ leafCount u := by
  induction h with
  | K_red x y =>
    cases hk with | app hl _ => cases hl with | app hK _ => cases hK
  | S_red f g x =>
    -- |S f g x| = |f|+|g|+|x|+1 ≤ |f|+|x|+(|g|+|x|) = |(f x)(g x)|
    have := leafCount_pos x
    simp [leafCount, app3]
    omega
  | appL _ ih =>
    cases hk with | app hl _ =>
    simp [leafCount]
    exact Nat.add_le_add_right (ih hl) _
  | appR _ ih =>
    cases hk with | app _ hr =>
    simp [leafCount]
    exact Nat.add_le_add_left (ih hr) _

theorem leafCount_le_of_steps {t u : Term} (hk : KFree t) (h : t ⟶* u) :
    leafCount t ≤ leafCount u := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail s rest ih =>
    exact Nat.le_trans (leafCount_le_of_step hk s) (ih (hk.of_step s))
```

Careful in `leafCount_le_of_steps`: the induction hypothesis needs the K-freeness of the INTERMEDIATE term — if `induction h` doesn't generalize `hk` properly, use `induction h generalizing` or restructure as shown (the `tail` case re-derives `KFree` for the next term via `hk.of_step s` before applying `ih`). If the IH arrives without the hypothesis slot, `induction h with` + explicit binders per Stage 1 precedent.

```lean
theorem cycle_leafCount_eq {t u : Term} (hk : KFree t)
    (h1 : t ⟶* u) (h2 : u ⟶* t) : leafCount t = leafCount u :=
  Nat.le_antisymm
    (leafCount_le_of_steps hk h1)
    (leafCount_le_of_steps (hk.of_steps h1) h2)
```

Run: `lake build` — expect zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: no-erasure laws — leaf-count monotonicity and cycle constraint"
```

---

### Task 4: Structural characterization of K-free normal forms

**Files:**
- Modify: `CombinatorCalculusPlayground/SFragment.lean` (append)

**Interfaces:**
- Consumes: `KFree`, `NormalForm` (Step.lean), `Step` constructors, `app2`, `app3`.
- Produces: `SNF : Term → Prop` (constructors `S : SNF Term.S`, `app1 {t} : SNF t → SNF (Term.app Term.S t)`, `app2 {t u} : SNF t → SNF u → SNF (Term.app (Term.app Term.S t) u)`); `SNF.kFree : SNF t → KFree t`; `SNF.normal : SNF t → NormalForm t`; `SNF.of_normal : KFree t → NormalForm t → SNF t`; `SNF_iff : SNF t ↔ KFree t ∧ NormalForm t`. Helper: `NormalForm.of_appL : NormalForm (Term.app t u) → NormalForm t`, `NormalForm.of_appR : NormalForm (Term.app t u) → NormalForm u`.

**Escape hatch (spec):** 3 genuinely different documented attempts per theorem, then record in CONJECTURES.md, remove broken code, commit green, DONE_WITH_CONCERNS.

- [ ] **Step 1: State everything with `sorry` (RED)**

Append to `SFragment.lean`:

```lean
-- ## The shape of a K-free normal form
-- A K-free term is a tree of S's; it is normal exactly when no S has
-- three arguments — i.e. every head spine has length ≤ 2. SNF captures
-- that shape structurally: an S, an S with one normal argument, or an S
-- with two. This is the S-fragment's answer to "what do values look
-- like?", and a stepping stone toward Waldmann-style normalization
-- analysis in later stages.
inductive SNF : Term → Prop
  | S : SNF Term.S
  | app1 {t : Term} : SNF t → SNF (Term.app Term.S t)
  | app2 {t u : Term} : SNF t → SNF u → SNF (Term.app (Term.app Term.S t) u)

-- A step inside either side of an application lifts to the whole —
-- so a normal application has normal sides (contrapositive).
theorem NormalForm.of_appL {t u : Term} (h : NormalForm (Term.app t u)) :
    NormalForm t := sorry

theorem NormalForm.of_appR {t u : Term} (h : NormalForm (Term.app t u)) :
    NormalForm u := sorry

theorem SNF.kFree {t : Term} (h : SNF t) : KFree t := sorry

theorem SNF.normal {t : Term} (h : SNF t) : NormalForm t := sorry

theorem SNF.of_normal {t : Term} (hk : KFree t) (hn : NormalForm t) : SNF t := sorry

-- The characterization, both directions bundled.
theorem SNF_iff {t : Term} : SNF t ↔ KFree t ∧ NormalForm t := sorry
```

Run: `lake build` — expect exactly six sorry warnings.

- [ ] **Step 2: Prove, in this order (GREEN)**

Candidates and strategy:

```lean
theorem NormalForm.of_appL {t u : Term} (h : NormalForm (Term.app t u)) :
    NormalForm t :=
  fun ⟨t', s⟩ => h ⟨Term.app t' u, Step.appL s⟩

theorem NormalForm.of_appR {t u : Term} (h : NormalForm (Term.app t u)) :
    NormalForm u :=
  fun ⟨u', s⟩ => h ⟨Term.app t u', Step.appR s⟩

theorem SNF.kFree {t : Term} (h : SNF t) : KFree t := by
  induction h with
  | S => exact KFree.S
  | app1 _ ih => exact KFree.app KFree.S ih
  | app2 _ _ ih1 ih2 => exact KFree.app (KFree.app KFree.S ih1) ih2
```

`SNF.normal` — induction on SNF; in each case `intro ⟨u, s⟩` and `cases s`. The `S` case: no Step constructor applies to an atom (cases closes it). `app1` (t = app S t'): the step is appL (impossible — no step from S; cases on the inner step) or appR (contradicts the IH `NormalForm t'`... note the IH from `induction` arrives as `NormalForm t'` — use it against the sub-step). K_red/S_red cannot match `app S t'` (wrong depth/head). `app2` (t = app (app S t') u'): appR contradicts IH on u'; appL's inner step on `app S t'` recurses one level (cases again: appL from S impossible, appR contradicts IH on t'); S_red needs head spine 3 (this term has 2 — no match); K_red needs head K. Expect nested `cases`; name every case.

```lean
theorem SNF.of_normal {t : Term} (hk : KFree t) (hn : NormalForm t) : SNF t := by
  induction t with
  | S => exact SNF.S
  | K => cases hk
  | app l r ihl ihr =>
    cases hk with | app hkl hkr =>
    have hl : SNF l := ihl hkl hn.of_appL
    have hr : SNF r := ihr hkr hn.of_appR
    -- Which shape is l? SNF gives exactly three possibilities.
    cases hl with
    | S => exact SNF.app1 hr
    | app1 hl' => exact SNF.app2 hl' hr
    | app2 hl' hr' =>
      -- l = app (app S a) b, so app l r = S a b r — an S-redex, contradicting hn.
      exact absurd ⟨_, Step.S_red ..⟩ hn

theorem SNF_iff {t : Term} : SNF t ↔ KFree t ∧ NormalForm t :=
  ⟨fun h => ⟨h.kFree, h.normal⟩, fun ⟨hk, hn⟩ => SNF.of_normal hk hn⟩
```

(In `SNF.of_normal`'s contradiction leaf, the S-redex is `app3 S a b r` up to unfolding — supply `Step.S_red a b r` with explicit arguments if the anonymous constructor form doesn't elaborate.)

Run: `lake build` — expect zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: K-free normal forms are exactly the SNF shapes"
```

---

### Task 5: Census cross-validation + artifact updates

**Files:**
- Modify: `CombinatorCalculusPlayground/Census/Enumerate.lean` (add import + guards at end)
- Modify: `CONJECTURES.md` (C2 constraint note + Stage 2 methodology line)
- Modify: `LAB_NOTEBOOK.md` (dated entry)

**Interfaces:**
- Consumes: `kFree` (Task 1), `sTerms`, `trace`, `stepOnce`, `leafCount`; `snf` (defined here).
- Produces: `snf : Term → Bool` (executable twin of SNF, in SFragment.lean); census guards; updated artifacts.

- [ ] **Step 1: Add `snf` to `SFragment.lean` with guards (RED then GREEN)**

Append to `SFragment.lean` (guards first, build to see `unknown identifier 'snf'`, then the def above them):

```lean
-- Executable twin of SNF, for census cross-validation. NOTE (epistemics):
-- snf ↔ SNF is NOT proven — the Bool twin is census tooling, validated
-- against the certified reducer by the guards in Census/Enumerate.lean,
-- not by a theorem. (kFree ↔ KFree, by contrast, IS proven: kFree_iff.)
def snf : Term → Bool
  | .S => true
  | .app .S t => snf t
  | .app (.app .S t) u => snf t && snf u
  | _ => false

#guard snf S = true
#guard snf (app S S) = true
#guard snf (app (app S S) S) = true
#guard snf (app (app (app S S) S) S) = false   -- three arguments: a redex
#guard snf K = false
```

- [ ] **Step 2: Census guards in `Census/Enumerate.lean` (RED expectations, GREEN on build)**

Add `import CombinatorCalculusPlayground.SFragment` at the top of `Census/Enumerate.lean` (alongside the existing Eval import), and append at the end:

```lean
-- ## Stage 2 cross-validation
-- The conservation laws, checked empirically against the census machinery
-- at small sizes. These guards tie the PROVEN laws (KFree closure, leaf
-- monotonicity) to the EXECUTABLE census world, and validate the unproven
-- Bool twin snf against the certified reducer.

-- Everything sTerms enumerates is K-free (it never mints a K).
#guard (sTerms 6).all kFree

-- Leaf count never decreases along any leftmost-outermost trajectory of a
-- K-free term (empirical face of leafCount_le_of_steps).
#guard (sTerms 6).all fun t =>
  let tr := trace 50 t
  (tr.zip tr.tail).all fun (a, b) => leafCount a ≤ leafCount b

-- snf agrees with the certified reducer's verdict on normality, for every
-- K-free term up to 6 leaves: snf t = true exactly when stepOnce t = none.
#guard (sTerms 6).all fun t => snf t == (stepOnce t).isNone
```

Run: `lake build`
Expected: `Build completed successfully`, zero warnings. If the third guard fails, one of `snf` or the trace above it is wrong — hand-check the smallest failing term (add a temporary `#eval` to find it, remove before committing) and fix the actual error; do not weaken the guard.

- [ ] **Step 3: Update `CONJECTURES.md`**

Two edits. (a) Under C2's paragraph, add:

```markdown
**Proven constraint (Stage 2):** any K-free reduction cycle is
leaf-count-constant (`cycle_leafCount_eq`, `SFragment.lean`) — a cycle
hunt may restrict to size-preserving steps, i.e. S-redexes whose third
argument is a single leaf. C2 itself remains open.
```

(b) In the methodology header, after the Stage 1 sentence, add:

```markdown
As of Stage 2, the S-fragment's conservation laws are machine-checked
(`SFragment.lean`): K-freeness is closed under reduction
(`KFree.of_step`), leaf count never decreases (`leafCount_le_of_steps` —
no erasure), and K-free normal forms are exactly the spine-≤2 shapes
(`SNF_iff`). Honest framing per the spec: these explain why naive
erasure-based encodings fail; they are NOT an impossibility argument —
the erasure-free λI-calculus is complete (Church 1941; Barendregt §9.5).
```

- [ ] **Step 4: Add the `LAB_NOTEBOOK.md` entry**

Dated entry (actual execution date), covering: which candidate proofs survived verbatim vs needed rework (real friction only), the SNF inversion-depth experience in `SNF.normal`, and the census cross-validation outcome (did the snf/stepOnce agreement guard pass first try?). Keep the honest voice of the prior entries.

- [ ] **Step 5: Build and commit**

Run: `lake build` — expect zero warnings.

```bash
git add -A
git commit -m "feat: census cross-validation of conservation laws; Stage 2 artifacts"
```

---

## Self-review notes

- Spec coverage (Stage 2 section): `KFree` predicate closed under reduction ✓ (Tasks 1–2); leaf count non-decreasing under S-steps ✓ (Task 3); spine-structure lemmas ✓ (Task 4's SNF characterizes head-spine shape — the spec's "spine structure lemmas" made concrete); honest-framing docstring ✓ (Task 1, spec text quoted in Global Constraints); census confirmation at small sizes ✓ (Task 5). Bonus beyond spec but on-mission: `cycle_leafCount_eq` (C2 constraint), flagged as such in CONJECTURES.
- Placeholder scan: clean; every theorem has a candidate script or (SNF.normal) an explicit case-analysis strategy with the statement exact.
- Type consistency: `KFree` constructor names (S, app) consistent across Tasks 1–4; `kFree`/`snf` Bool twins used in Task 5's guards match their Task 1/5 definitions; `NormalForm.of_appL/of_appR` produced in Task 4 and consumed in the same task's `SNF.of_normal`; `cycle_leafCount_eq` signature in Task 3 matches the CONJECTURES text in Task 5.
- Naming: `SNF.app2` constructor shadows nothing (Term's `app2` is a def, not in SNF's namespace); inside SFragment all Term constructors are `Term.`-qualified in inductive declarations per Stage 1's lesson.
- Import discipline: SFragment imports only Step (spec architecture); Census/Enumerate gains SFragment — no cycles (SFragment never imports Census).
