# Stage 0: Census + Module Split Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Split `Basic.lean` into focused modules and build the Stage 0 census: a verified evaluator, an S-term enumerator, a dynamics classifier, a CLI runner, and the two standing artifacts (`CONJECTURES.md`, `LAB_NOTEBOOK.md`).

**Architecture:** Deep-embedded combinatory terms (`Term`) with a relational reduction semantics (`Step`/`Steps`) and an executable leftmost-outermost reducer (`stepOnce`) proven sound against the relation. The census enumerates all pure-S terms by leaf count and classifies each trajectory as terminating (certified by a reached normal form), cyclic (certified by deterministic revisit), or fuel-exhausted (honest "unknown", with growth observables).

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0` (already pinned in `lean-toolchain`). Zero dependencies.
- **No `sorry` on main.** A theorem that resists 3 documented attempts gets its statement recorded in `CONJECTURES.md` and is removed from the code (see spec's escape hatches).
- **Fuel-based totality:** no `partial def` anywhere in this slice.
- Every commit must `lake build` clean.
- Preserve the existing pedagogical comment style (explain *what Lean is doing*, not just the math) when moving code — this repo is also a Lean tutorial for its owner.
- `fuelExhausted` is NOT a divergence proof. Comments and docs must never claim it is.

## Lean TDD adaptation

Lean has no separate test runner in this project; tests are `#guard` commands (compile-time checked, must evaluate to `true`) and theorems.

- For **functions**: write the `#guard` tests FIRST in the file, `lake build` to see the failure (unknown identifier — that's "red"), then add the definition above them, build again ("green").
- For **theorems**: first state with `:= sorry` and build to confirm the *statement* elaborates (red — build succeeds but warns `declaration uses 'sorry'`), then replace `sorry` with the proof (green — no warnings). NEVER commit while a `sorry` remains.
- Verification command is always: `cd /Users/nathan/Projects/CombinatorCalculusPlayground && lake build` (expect `Build completed successfully`, no warnings).

Proof scripts below are best-effort candidates: if a script fails, iterate against the compiler (the goal state tells you what's missing); the acceptance criterion is the exact theorem statement compiling sorry-free, not the exact tactic text.

---

### Task 1: Module split — `Term.lean` and `Step.lean` replace `Basic.lean`

**Files:**
- Create: `CombinatorCalculusPlayground/Term.lean`
- Create: `CombinatorCalculusPlayground/Step.lean`
- Modify: `CombinatorCalculusPlayground.lean` (root import file)
- Delete: `CombinatorCalculusPlayground/Basic.lean`

**Interfaces:**
- Consumes: nothing (foundation task).
- Produces: `Term` (constructors `.S`, `.K`, `.app`), `app2 : Term → Term → Term → Term`, `app3 : Term → Term → Term → Term → Term`, `I : Term`, `leafCount : Term → Nat`, `spineLength : Term → Nat`, `render : Term → String`; `Step` (notation `t ⟶ u`), `Steps` (notation `t ⟶* u`), `Steps.single : t ⟶ u → t ⟶* u`, `Steps.trans : t ⟶* u → u ⟶* v → t ⟶* v`, `I_reduces : ∀ x, app I x ⟶* x`.

- [ ] **Step 1: Create `Term.lean`**

Move the `Term`-related content from `Basic.lean` (keeping its comments) and add the three new measures with their tests:

```lean
--! # Terms of combinatory logic
-- We define the S and K combinators and function application. This is the
-- raw syntax; how terms *reduce* lives in Step.lean.

-- `inductive` means "here are ALL the ways to build this thing, and nothing
-- else." A Term is like a LEGO set with exactly three kinds of brick.
--
-- `deriving Repr, DecidableEq` asks Lean to auto-generate the ability to print
-- Terms (`Repr`, used by `#eval`) and compare them for equality (`DecidableEq`).
inductive Term : Type
  | S : Term                   -- The S (substitution) combinator: S f g x = f x (g x)
  | K : Term                   -- The K (constant) combinator: K x y = x
  | app : Term → Term → Term   -- Sticks two terms together (function application)
deriving Repr, DecidableEq

-- `open` lets us write `S` instead of `Term.S`, etc. Just a convenience.
open Term

-- `def` defines a function or constant. `app` only takes two arguments, so
-- `app2` and `app3` are shortcuts to avoid deeply nested parentheses.
def app2 (f a b : Term) : Term :=
  app (app f a) b

def app3 (f a b c : Term) : Term :=
  app (app (app f a) b) c

-- The identity combinator: I x = x. Built from S and K because S K K x
-- reduces to K x (K x), which reduces to x. Proven in Step.lean (`I_reduces`).
def I : Term :=
  app2 S K K

-- ## Measures
-- Terms are binary trees; a tree with n leaves always has n - 1 internal
-- `app` nodes, so leaf count is the only size measure we need.

-- Number of combinator leaves (S's and K's) in a term.
def leafCount : Term → Nat
  | .S => 1
  | .K => 1
  | .app t u => leafCount t + leafCount u

-- Length of the left spine: how many arguments the head combinator has
-- been applied to. `S a b c` has spine length 3.
def spineLength : Term → Nat
  | .app t _ => spineLength t + 1
  | _ => 0

-- Standard combinator notation: application is left-associative and
-- implicit, so only right-nested applications need parentheses.
def render : Term → String
  | .S => "S"
  | .K => "K"
  | .app t u =>
    match u with
    | .app _ _ => render t ++ " (" ++ render u ++ ")"
    | _ => render t ++ " " ++ render u

-- `#guard` is a compile-time test: the build fails unless the expression
-- evaluates to `true`.
#guard leafCount I = 3
#guard spineLength I = 2
#guard spineLength S = 0
#guard render I = "S K K"
#guard render (app S (app K K)) = "S (K K)"
```

- [ ] **Step 2: Create `Step.lean`**

Move the reduction content from `Basic.lean` (keeping its comments) and add the two helper lemmas:

```lean
--! # Reduction: single steps and multi-step paths
import CombinatorCalculusPlayground.Term

open Term

-- `Step a b` is a Prop meaning "term `a` reduces to term `b` in exactly one
-- step." The four constructors are the only four ways a step can happen:
inductive Step : Term → Term → Prop
  | K_red (x y : Term) :
      Step (app2 K x y) x
      -- K grabs two args and returns the first: K x y → x
  | S_red (f g x : Term) :
      Step (app3 S f g x) (app (app f x) (app g x))
      -- S distributes the third arg to the first two: S f g x → (f x) (g x)
  | appL {t t' u : Term} :
      Step t t' → Step (app t u) (app t' u)
      -- If the left side of an application can step, so can the whole thing
  | appR {t u u' : Term} :
      Step u u' → Step (app t u) (app t u')
      -- Same idea, but for the right side

open Step

infix:50 " ⟶ " => Step

-- `Steps` is zero or more reduction steps — the "can eventually become"
-- relation.
inductive Steps : Term → Term → Prop
  | refl (t : Term) :
      Steps t t
  | tail {t u v : Term} :
      Step t u → Steps u v → Steps t v

open Steps

infix:50 " ⟶* " => Steps

-- A single step is also a many-step path (of length one).
theorem Steps.single {t u : Term} (h : t ⟶ u) : t ⟶* u :=
  tail h (refl u)

-- Paths compose: t ⟶* u and u ⟶* v gives t ⟶* v.
-- Proof by induction on the first path: if it's zero steps, the second path
-- already is the answer; otherwise peel one step off and recurse.
theorem Steps.trans {t u v : Term} (h1 : t ⟶* u) (h2 : u ⟶* v) : t ⟶* v := by
  induction h1 with
  | refl => exact h2
  | tail s _ ih => exact tail s (ih h2)

theorem I_reduces (x : Term) : app I x ⟶* x :=
  tail (S_red K K x) (tail (K_red x (app K x)) (refl x))
  -- S K K x → K x (K x) → x
```

- [ ] **Step 3: Update the root file and delete `Basic.lean`**

Replace the contents of `CombinatorCalculusPlayground.lean` with:

```lean
import CombinatorCalculusPlayground.Term
import CombinatorCalculusPlayground.Step
```

Then: `rm CombinatorCalculusPlayground/Basic.lean`

- [ ] **Step 4: Build**

Run: `lake build`
Expected: `Build completed successfully.` No warnings. (The `#guard`s in Term.lean are the tests for this task; if a measure is wrong the build fails.)

- [ ] **Step 5: Commit**

```bash
git add -A
git commit -m "refactor: split Basic.lean into Term.lean and Step.lean

Adds measures (leafCount, spineLength), a renderer, and Steps
helpers (single, trans) needed by the Stage 0 census."
```

---

### Task 2: `stepOnce` — the executable reducer

**Files:**
- Create: `CombinatorCalculusPlayground/Census/Eval.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add import)

**Interfaces:**
- Consumes: `Term`, `app2`, `app3`, `I` from Task 1.
- Produces: `stepOnce : Term → Option Term` (leftmost-outermost; `none` means no redex found).

- [ ] **Step 1: Write the failing tests**

Create `CombinatorCalculusPlayground/Census/Eval.lean`:

```lean
--! # Executable reduction
-- `Step` (in Step.lean) says which reductions are *legal* — a relation, not
-- a program. Here we pick a deterministic strategy (leftmost-outermost: always
-- fire the leftmost, outermost redex) and implement it as a function we can
-- actually run. Leftmost-outermost is the *normalizing* strategy: if any
-- strategy reaches a normal form, this one does — which is exactly what a
-- census needs.
import CombinatorCalculusPlayground.Step

open Term

-- Tests first (TDD): these lines make the build fail until stepOnce exists
-- and is correct.
#guard stepOnce (app2 K S K) = some S                    -- K-redex fires
#guard stepOnce (app3 S K K S) = some (app (app K S) (app K S))  -- S-redex fires
#guard stepOnce S = none                                 -- bare combinator: no redex
#guard stepOnce (app S K) = none                         -- underapplied: no redex
#guard stepOnce (app2 S K K) = none                      -- still underapplied (I is normal!)
-- Outermost wins: the whole term is a K-redex even though its first argument
-- (I = S K K applied to nothing... but here app I S) contains its own redex.
#guard stepOnce (app2 K (app I S) S) = some (app I S)
-- Leftmost wins: both sides of this app contain a redex; the left one fires.
-- (Left side K S K → S is a one-step K-redex; right side app I K also has a
-- redex but must wait.)
#guard stepOnce (app (app2 K S K) (app I K)) = some (app S (app I K))
```

- [ ] **Step 2: Run to verify failure**

Run: `lake build`
Expected: FAIL with `unknown identifier 'stepOnce'`.

- [ ] **Step 3: Implement**

Insert between the imports/comments and the `#guard` block:

```lean
-- One leftmost-outermost step, or `none` if the term is in normal form.
-- Match arms are tried in order, so the two redex patterns take priority
-- over the structural descent, and left descent takes priority over right.
def stepOnce : Term → Option Term
  | .app (.app .K x) _ => some x
  | .app (.app (.app .S f) g) x => some (.app (.app f x) (.app g x))
  | .app t u =>
    match stepOnce t with
    | some t' => some (.app t' u)
    | none =>
      match stepOnce u with
      | some u' => some (.app t u')
      | none => none
  | _ => none
```

- [ ] **Step 4: Run to verify pass**

Run: `lake build`
Expected: `Build completed successfully.`

Then add `import CombinatorCalculusPlayground.Census.Eval` to `CombinatorCalculusPlayground.lean` and build again to confirm it's part of the library target.

- [ ] **Step 5: Commit**

```bash
git add -A
git commit -m "feat: executable leftmost-outermost reducer stepOnce"
```

---

### Task 3: Soundness — `stepOnce` only takes legal steps

**Files:**
- Modify: `CombinatorCalculusPlayground/Census/Eval.lean`

**Interfaces:**
- Consumes: `stepOnce` (Task 2), `Step` and constructors (Task 1).
- Produces: `stepOnce_sound : stepOnce t = some u → t ⟶ u`.

- [ ] **Step 1: State the theorem with `sorry` (red)**

Append to `Eval.lean`:

```lean
-- ## Soundness
-- Everything stepOnce does is a legal Step. This is what lets the census
-- make *claims*: when the evaluator says "t reduced to u", that's a theorem,
-- not just program output.
theorem stepOnce_sound : ∀ {t u : Term}, stepOnce t = some u → t ⟶ u := sorry
```

Run: `lake build`
Expected: builds with warning `declaration uses 'sorry'` (statement elaborates).

- [ ] **Step 2: Prove it (green)**

Replace `sorry` with a proof. Recommended script — `fun_induction` gives one case per match arm of `stepOnce`, including the nested matches:

```lean
theorem stepOnce_sound : ∀ {t u : Term}, stepOnce t = some u → t ⟶ u := by
  intro t
  fun_induction stepOnce t with
  | case1 x y =>            -- K-redex arm
    intro u h
    cases h
    exact Step.K_red ..
  | case2 f g x =>          -- S-redex arm
    intro u h
    cases h
    exact Step.S_red ..
  | _ =>                    -- descent arms and the no-redex arms
    intro u h
    -- In descent arms the hypotheses from the nested matches plus the
    -- induction hypotheses close the goal; in no-redex arms `h` is
    -- `none = some u`, absurd.
    first
      | (cases h; solve
          | exact Step.appL (by assumption)
          | exact Step.appR (by assumption))
      | simp_all
      | (injection h with h'; subst h'
         solve
           | exact Step.appL (by simp_all)
           | exact Step.appR (by simp_all))
```

Fallback if `fun_induction` case names/shape differ: run `fun_induction stepOnce t` bare, inspect the goals with the compiler, and write one explicit case per goal — each is closed by `Step.K_red`, `Step.S_red`, `Step.appL ih`, `Step.appR ih`, or contradiction on `none = some u`. Iterate freely; the statement is the contract.

- [ ] **Step 3: Verify**

Run: `lake build`
Expected: `Build completed successfully.`, zero warnings (no `sorry`).

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: prove stepOnce sound against the Step relation"
```

---

### Task 4: Completeness — `none` really means normal form

**Files:**
- Modify: `CombinatorCalculusPlayground/Census/Eval.lean`

**Interfaces:**
- Consumes: `stepOnce`, `Step`.
- Produces: `NormalForm : Term → Prop`, `stepOnce_none_normal : stepOnce t = none → NormalForm t`.

**Escape hatch (from spec):** if this resists 3 documented attempts, record the statement in `CONJECTURES.md` (Task 9 creates it; leave a note in the task 9 handoff), delete the broken proof, and commit green without it.

- [ ] **Step 1: State with `sorry` (red)**

Append to `Eval.lean`:

```lean
-- ## Completeness
-- When stepOnce gives up, there really is no legal step: `none` certifies a
-- normal form. Together with soundness this makes the census classifier's
-- "terminating" verdict a machine-checked fact.
def NormalForm (t : Term) : Prop := ¬ ∃ u, t ⟶ u

theorem stepOnce_none_normal : ∀ {t : Term}, stepOnce t = none → NormalForm t := sorry
```

Run: `lake build` — expect the `sorry` warning only.

- [ ] **Step 2: Prove the contrapositive helper, then the theorem**

The clean route is: any legal step implies `stepOnce` finds *something* (not necessarily the same step — leftmost-outermost may pick a different redex).

```lean
-- If any step is possible, stepOnce finds one (maybe a different one:
-- leftmost-outermost picks its own redex, but it never misses).
theorem stepOnce_isSome_of_step : ∀ {t u : Term}, t ⟶ u → (stepOnce t).isSome := by
  intro t u h
  induction h with
  | K_red x y => simp [stepOnce]
  | S_red f g x => simp [stepOnce]
  | appL s ih =>
    -- Goal: (stepOnce (app t u)).isSome given (stepOnce t).isSome.
    -- Split on the match arms of stepOnce (app t u): redex arms are
    -- trivially some; the descent arm consults stepOnce t, which is some.
    simp only [stepOnce]
    split <;> simp_all [Option.isSome]
    -- Remaining goals (if any) are descent arms: unfold the inner match
    -- using `ih` via `Option.isSome_iff_exists` and `split` again.
  | appR s ih =>
    simp only [stepOnce]
    split <;> simp_all [Option.isSome]

theorem stepOnce_none_normal : ∀ {t : Term}, stepOnce t = none → NormalForm t := by
  intro t hnone ⟨u, hstep⟩
  have := stepOnce_isSome_of_step hstep
  simp [hnone] at this
```

The `appL`/`appR` cases are the fiddly part: the outer term may itself be a K/S-redex (in which case `stepOnce` returns `some` immediately regardless of the sub-step), or fall to the descent arm (where `ih` supplies the inner `some`). Expect to iterate: `split` on the match, use `Option.isSome_iff_exists` / `obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ih`, and `simp [hw]`. Three documented attempts, then the escape hatch.

- [ ] **Step 3: Verify**

Run: `lake build`
Expected: `Build completed successfully.`, zero warnings.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: prove stepOnce completeness — none certifies a normal form"
```

---

### Task 5: Fuel-based normalization with a soundness certificate

**Files:**
- Modify: `CombinatorCalculusPlayground/Census/Eval.lean`

**Interfaces:**
- Consumes: `stepOnce`, `stepOnce_sound`, `Steps`, `Steps.trans`, `Steps.single`.
- Produces: `normalize : Nat → Term → Option (Term × Nat)` (normal form + step count, or `none` if fuel ran out), `trace : Nat → Term → List Term` (the trajectory, first element is the input), `normalize_sound : normalize fuel t = some (u, k) → t ⟶* u`.

- [ ] **Step 1: Failing tests**

Append to `Eval.lean`:

```lean
-- I S → K S (K S) → S : two steps to normal form.
#guard normalize 10 (app I S) = some (S, 2)
-- Already normal: zero steps.
#guard normalize 10 (app S K) = some (app S K, 0)
-- Fuel 0 can still succeed on an already-normal term...
#guard normalize 0 S = some (S, 0)
-- ...but a term needing steps runs out.
#guard normalize 1 (app I S) = none
-- Ω = (S I I)(S I I) loops forever (an SK-term; I = S K K). Fuel exhausts.
#guard normalize 100 (app (app2 S I I) (app2 S I I)) = none
-- trace records the trajectory including the start.
#guard (trace 10 (app I S)).length = 3
#guard (trace 10 (app I S)).head? = some (app I S)
```

Run: `lake build` — expect FAIL, `unknown identifier 'normalize'`.

- [ ] **Step 2: Implement**

Insert above the new `#guard`s:

```lean
-- ## Fuel-based normalization
-- Lean requires all functions to terminate, but reduction might not! The
-- standard trick: a `fuel` counter that strictly decreases. `none` means
-- "didn't finish within fuel" — it does NOT mean the term diverges.
def normalize (fuel : Nat) (t : Term) : Option (Term × Nat) :=
  match stepOnce t with
  | none => some (t, 0)
  | some t' =>
    match fuel with
    | 0 => none
    | f + 1 =>
      match normalize f t' with
      | some (nf, k) => some (nf, k + 1)
      | none => none

-- The trajectory: t, then everything it steps through, until normal form
-- or fuel exhaustion. Always non-empty (starts with t).
def trace (fuel : Nat) (t : Term) : List Term :=
  match stepOnce t, fuel with
  | none, _ => [t]
  | some _, 0 => [t]
  | some t', f + 1 => t :: trace f t'
```

- [ ] **Step 3: Verify tests pass**

Run: `lake build`
Expected: `Build completed successfully.`

- [ ] **Step 4: State and prove the certificate (red, then green)**

Append (state with `sorry`, build, then prove):

```lean
-- ## The certificate
-- A successful normalize run IS a reduction sequence: census "terminating"
-- verdicts are theorems. (With stepOnce_none_normal, the result is moreover
-- a normal form — the classifier relies on both.)
theorem normalize_sound :
    ∀ (fuel : Nat) {t u : Term} {k : Nat},
      normalize fuel t = some (u, k) → t ⟶* u := by
  intro fuel
  induction fuel with
  | zero =>
    intro t u k h
    -- fuel 0 succeeds only when t is already normal: u = t.
    unfold normalize at h
    split at h
    · injection h with h'; injection h' with h1 _; subst h1; exact Steps.refl t
    · simp at h
  | succ f ih =>
    intro t u k h
    unfold normalize at h
    split at h
    next hnone =>
      injection h with h'; injection h' with h1 _; subst h1; exact Steps.refl t
    next t' hsome =>
      -- one certified step, then the induction hypothesis on the rest
      split at h
      next nf k' hrec =>
        injection h with h'; injection h' with h1 _; subst h1
        exact Steps.tail (stepOnce_sound hsome) (ih hrec)
      next => simp at h
    
```

(As before: iterate against the compiler if the `split`/`injection` bookkeeping differs; the match structure of `normalize` drives the case split. Note the `fuel` match in `normalize` sits *inside* the `some` branch — mirror that order when splitting.)

- [ ] **Step 5: Verify**

Run: `lake build` — expect success, zero warnings.

- [ ] **Step 6: Commit**

```bash
git add -A
git commit -m "feat: fuel-based normalize/trace with soundness certificate"
```

---

### Task 6: Enumerating all pure-S terms by size

**Files:**
- Create: `CombinatorCalculusPlayground/Census/Enumerate.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add import)

**Interfaces:**
- Consumes: `Term`, `leafCount`.
- Produces: `sTerms : Nat → List Term` — ALL pure-S terms with exactly n leaves (Catalan(n−1) of them).

- [ ] **Step 1: Failing tests**

Create `CombinatorCalculusPlayground/Census/Enumerate.lean`:

```lean
--! # The census: enumerate and classify pure-S terms
import CombinatorCalculusPlayground.Census.Eval

open Term

-- Binary trees with n leaves are counted by the Catalan numbers:
-- 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, ...
#guard (sTerms 0).length = 0
#guard (sTerms 1).length = 1
#guard (sTerms 2).length = 1
#guard (sTerms 3).length = 2
#guard (sTerms 4).length = 5
#guard (sTerms 5).length = 14
#guard (sTerms 6).length = 42
-- Every enumerated term has exactly the requested number of leaves.
#guard (sTerms 5).all (fun t => leafCount t = 5)
-- No duplicates (checked at a small size).
#guard (sTerms 5).eraseDups.length = 14
```

Run: `lake build` — expect FAIL, `unknown identifier 'sTerms'`.

- [ ] **Step 2: Implement (dynamic programming, no well-founded recursion)**

Insert above the `#guard`s:

```lean
-- All pure-S terms with exactly n leaves. Built bottom-up with a table
-- (index m holds all terms with m leaves) — this sidesteps the termination
-- proof a naive two-sided recursion would need, and shares work.
def sTermsTable (n : Nat) : Array (List Term) := Id.run do
  let mut table : Array (List Term) := #[[], [Term.S]]
  for m in [2:n+1] do
    let mut terms : List Term := []
    for k in [1:m] do
      for l in table[k]! do
        for r in table[m - k]! do
          terms := Term.app l r :: terms
    table := table.push terms
  return table

def sTerms (n : Nat) : List Term :=
  (sTermsTable n)[n]!
```

Note: `[k]!` panics on out-of-range, but the loop structure guarantees index `m` is pushed exactly at iteration `m`; the `#guard`s exercise this. (A proof-carrying index is deliberate YAGNI here — this is census tooling, not proof-bearing code.)

- [ ] **Step 3: Verify**

Run: `lake build`
Expected: `Build completed successfully.`

Then add `import CombinatorCalculusPlayground.Census.Enumerate` to the root file; build again.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: enumerate all pure-S terms by leaf count (Catalan-checked)"
```

---

### Task 7: The dynamics classifier

**Files:**
- Modify: `CombinatorCalculusPlayground/Census/Enumerate.lean`

**Interfaces:**
- Consumes: `stepOnce`, `leafCount`, `sTerms`.
- Produces: `Dynamics` (constructors `.terminating (steps : Nat) (nf : Term)`, `.cyclic (entry period : Nat)`, `.fuelExhausted (finalLeaves : Nat)`), `classify : Nat → Term → Dynamics`.

- [ ] **Step 1: Failing tests**

Append to `Enumerate.lean`:

```lean
-- S alone is normal.
#guard classify 10 S = .terminating 0 S
-- S S S S → (S S)(S S), which is normal (head S has only 2 args).
#guard classify 10 (app3 S S S S) = .terminating 1 (app (app S S) (app S S))
-- Ω (an SK-term) never terminates and never revisits... within tiny fuel it
-- just exhausts. (Ω actually cycles: (SII)(SII) → I(SII)(I(SII)) → ... —
-- we deliberately test only what the classifier certifies: not-done-yet.)
#guard (match classify 3 (app (app2 S I I) (app2 S I I)) with
        | .fuelExhausted _ => true
        | .cyclic _ _ => true
        | _ => false)
-- A genuinely cyclic SK-term: t = (S I I)(S I I) revisits itself in
-- leftmost-outermost reduction within modest fuel — if it does, classify
-- must say cyclic, never terminating.
#guard (match classify 100 (app (app2 S I I) (app2 S I I)) with
        | .terminating _ _ => false
        | _ => true)
```

Run: `lake build` — expect FAIL, `unknown identifier 'classify'`.

- [ ] **Step 2: Implement**

Insert above the new `#guard`s:

```lean
-- ## Classifying a trajectory
-- Three verdicts, with three different epistemic standings:
--   terminating — CERTIFIED: a normal form was reached (stepOnce = none,
--                 which stepOnce_none_normal proves is really normal).
--   cyclic      — CERTIFIED: stepOnce is deterministic, so revisiting a
--                 term means the trajectory repeats forever.
--   fuelExhausted — HONESTLY UNKNOWN. Not a divergence proof. We record the
--                 final leaf count so growth is observable.
inductive Dynamics : Type
  | terminating (steps : Nat) (nf : Term)
  | cyclic (entry period : Nat)
  | fuelExhausted (finalLeaves : Nat)
deriving Repr, DecidableEq

-- Walk the trajectory keeping every visited term (in order) for cycle
-- detection. `seen` always ends with the current term.
def classify (fuel : Nat) (t : Term) : Dynamics :=
  go fuel [t] t
where
  go : Nat → List Term → Term → Dynamics
  | 0, _, cur => .fuelExhausted (leafCount cur)
  | f + 1, seen, cur =>
    match stepOnce cur with
    | none => .terminating (seen.length - 1) cur
    | some next =>
      match seen.findIdx? (· = next) with
      | some i => .cyclic i (seen.length - i)
      | none => go f (seen ++ [next]) next
```

(If `findIdx?` with `(· = next)` complains about decidability vs `Bool`, use `(· == next)` — `Term` derives `DecidableEq`, which supplies `BEq`.)

- [ ] **Step 3: Verify**

Run: `lake build`
Expected: `Build completed successfully.`

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: trajectory classifier with certified verdicts and honest unknowns"
```

---

### Task 8: The census runner (`Main.lean`)

**Files:**
- Modify: `Main.lean`

**Interfaces:**
- Consumes: `sTerms`, `classify`, `Dynamics`, `render`, `leafCount`.
- Produces: `lake exe ccp [maxLeaves] [fuel]` — per-size census table on stdout; prints every cyclic term found and the smallest fuel-exhausted terms.

- [ ] **Step 1: Implement the runner**

Replace `Main.lean` contents:

```lean
import CombinatorCalculusPlayground

open Term

-- Census over all pure-S terms with n = 1 .. maxLeaves leaves.
-- Usage: lake exe ccp [maxLeaves] [fuel]   (defaults: 8, 200)
def censusLine (fuel n : Nat) : String × List Term × List Term := Id.run do
  let mut term0 := 0  -- terminating
  let mut cyc : List Term := []
  let mut exhausted : List Term := []
  let mut maxSteps := 0
  let mut maxFinal := 0
  for t in sTerms n do
    match classify fuel t with
    | .terminating k _ =>
      term0 := term0 + 1
      if k > maxSteps then maxSteps := k
    | .cyclic _ _ => cyc := t :: cyc
    | .fuelExhausted fl =>
      exhausted := t :: exhausted
      if fl > maxFinal then maxFinal := fl
  let line := s!"n={n}: total={(sTerms n).length} terminating={term0} " ++
              s!"cyclic={cyc.length} exhausted={exhausted.length} " ++
              s!"maxSteps={maxSteps} maxFinalLeaves={maxFinal}"
  return (line, cyc, exhausted)

def main (args : List String) : IO Unit := do
  let maxLeaves := (args[0]?.bind String.toNat?).getD 8
  let fuel := (args[1]?.bind String.toNat?).getD 200
  IO.println s!"Pure-S census up to {maxLeaves} leaves, fuel {fuel}"
  IO.println "==========================================="
  let mut anyCycle := false
  let mut firstExhaustedReported := false
  for n in [1:maxLeaves+1] do
    let (line, cyc, exhausted) := censusLine fuel n
    IO.println line
    for t in cyc do
      anyCycle := true
      IO.println s!"  CYCLE FOUND: {render t}"
    if !exhausted.isEmpty && !firstExhaustedReported then
      firstExhaustedReported := true
      IO.println s!"  smallest fuel-exhausted terms (n={n}):"
      for t in exhausted.take 10 do
        IO.println s!"    {render t}"
  if !anyCycle then
    IO.println "No cycles found at any size (within fuel)."
```

- [ ] **Step 2: Smoke test**

Run: `lake build && lake exe ccp 5 50`
Expected output shape (exact counts are the test):

```
Pure-S census up to 5 leaves, fuel 50
===========================================
n=1: total=1 terminating=1 cyclic=0 exhausted=0 maxSteps=0 maxFinalLeaves=0
n=2: total=1 terminating=1 ...
n=3: total=2 terminating=2 ...
n=4: total=5 terminating=5 ...
n=5: total=14 terminating=14 ...
No cycles found at any size (within fuel).
```

(All S-terms with ≤ 5 leaves should terminate quickly; if not, that is itself a census finding — record it, don't "fix" it.)

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: census CLI runner over pure-S terms"
```

---

### Task 9: Run the real census; create `CONJECTURES.md` and `LAB_NOTEBOOK.md`

**Files:**
- Create: `CONJECTURES.md`
- Create: `LAB_NOTEBOOK.md`

**Interfaces:**
- Consumes: the `ccp` executable (Task 8).
- Produces: the two standing artifacts the spec mandates, populated with real (not placeholder) data.

- [ ] **Step 1: Run the census at increasing depth**

Run, recording output of each:

```bash
lake exe ccp 8 200
lake exe ccp 10 1000
lake exe ccp 12 2000   # skip or reduce if runtime exceeds ~10 minutes
```

Watch for: first size with fuel-exhausted terms (candidate smallest non-normalizing S-terms), any `CYCLE FOUND` lines (answers the S-cycle question at small sizes), max step counts (how deep terminating reductions go).

- [ ] **Step 2: Create `CONJECTURES.md` from the actual results**

Structure (fill every bracketed slot with observed data — the numbers come from Step 1's output, they are not invented):

```markdown
# Conjectures

Census-generated claims, each with a status:
**open** / **proved** (link the theorem) / **refuted** (link the counterexample).
Census methodology: leftmost-outermost reduction (`stepOnce`), which is the
normalizing strategy; "exhausted" verdicts are fuel-outs, NOT divergence proofs.

## C1: Smallest non-normalizing pure-S term — status: open
Census (fuel N=[fuel used]) finds all S-terms with ≤ [k] leaves normalize;
at [k+1] leaves, [count] terms exhaust fuel. Candidates: [list terms].
Conjecture: [the specific smallest candidate] has no normal form.

## C2: No proper cycles in pure-S reduction — status: open
No S-term with ≤ [max n censused] leaves revisits a previous term
(leftmost-outermost, fuel [N]). Conjecture: pure-S leftmost-outermost
trajectories never cycle. (NOTE: cycle-freedom under ALL strategies is a
stronger, separate claim.)

## C3: [any growth-pattern regularity observed] — status: open
[e.g., "all fuel-exhausted terms at size k share head shape S S ..."]
```

If the census output contradicts a slot (e.g., a cycle IS found), the conjecture flips accordingly — record what was actually observed.

- [ ] **Step 3: Create `LAB_NOTEBOOK.md`**

```markdown
# Lab Notebook — the Fable-vs-Lean meta-experiment

One dated entry per work session: what was attempted, what Lean resisted,
what automation could and couldn't do. This file is a first-class deliverable
(spec: if Stage 5 never terminates, the notebook is the result).

## 2026-07-23 — Stage 0
- Module split + census slice implemented ([N] tasks, [M] commits).
- Proof friction encountered: [honest notes — e.g., which of
  stepOnce_sound / stepOnce_none_normal / normalize_sound needed iteration,
  what tactic finally worked, anything that hit the 3-attempt rule].
- Census headline: [first exhausted size, cycle question answer at small n,
  max reduction lengths].
- Next: Stage 1 (confluence) / Stage 2 (conservation) / Stage 3 (taxonomy)
  are all unblocked per the DAG.
```

- [ ] **Step 4: Commit**

```bash
git add CONJECTURES.md LAB_NOTEBOOK.md
git commit -m "feat: first census results; standing artifacts CONJECTURES and LAB_NOTEBOOK"
```

---

## Self-review notes

- Spec coverage: evaluator ✓ (T2–5), enumerator ✓ (T6), classifier ✓ (T7), observables ✓ (leafCount/spineLength in T1, finalLeaves in T7, maxSteps in T8), first questions ✓ (T8 output + T9 conjectures), module split ✓ (T1), standing artifacts ✓ (T9). `RS.lean`/`Confluence.lean`/etc. are later stages, correctly absent.
- Type consistency: `classify : Nat → Term → Dynamics` consumed as such in T8; `Dynamics.terminating (steps) (nf)` pattern-matched with both fields in T8 ✓; `render` defined T1, used T8 ✓; `normalize` returns `Option (Term × Nat)` and T5's guards match ✓.
- Bracketed slots in Task 9 are empirical-data collection instructions, not placeholders — the runner's output supplies them at execution time.
