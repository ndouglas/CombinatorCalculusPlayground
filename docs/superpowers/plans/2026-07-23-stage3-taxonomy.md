# Stage 3: The Universality Taxonomy Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Machine-checked definitions of "computationally universal" stated over an abstract rewriting-system interface, with the provable implication lattice between them, instances for SK / pure-S / a reference tag system, and an explicit status ledger for every (definition, system) pair.

**Architecture:** `RS.lean` defines the abstract interface (carrier + step relation) with generic closures (`Steps`, `Conv`), normal forms, and the three instances — SK, pure-S (subtype carrier, legal by Stage 2's `KFree.of_step`), and a 2-symbol tag system as the designated reference model (its universality is external knowledge, cited and registered, never claimed as machine-checked). `Universality/Defs.lean` defines simulation as an (encoder, decoder) triple plus the three observation-mode universality definitions (reachability / normalization / convertibility). `Universality/Taxonomy.lean` proves the lattice: convertibility-preservation is unconditional, convertibility-reflection needs generic Church–Rosser + image-closure, normalization-preservation needs normal-form correspondence — and connects Stage 1 by instantiating generic Church–Rosser for `RS.SK`.

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0`. Zero dependencies.
- **No `sorry` on main.** 3 documented failed attempts → statement to `CONJECTURES.md`, code removed (spec escape hatch).
- **No `partial def`** anywhere.
- Every commit must `lake build` clean with zero warnings.
- Comments state precisely what is machine-checked. In this stage that constraint has teeth twice: (a) the tag system's universality is EXTERNAL (Cocke–Minsky 1964) — every mention must say so; (b) the encoding-class pinning is partially internal (see Task 4's docstring, a required deliverable).
- Spec success criterion: "the lattice compiles; each definition's status for {S,K} and for pure S is either proven or explicitly registered as open."

## Lean TDD adaptation (same as Stages 0–2)

- Functions/instances: `#guard`/`example` tests first where possible (RED: unknown identifier) → implement (GREEN).
- Theorems: statement `:= sorry` (RED: only sorry warnings) → proof (GREEN: zero warnings). NEVER commit with sorry.
- Candidate proofs are candidates; statements are the contract. House precedent: named cases; no `first |` catch-alls; `fun_induction` for function-shaped goals; `Term.S`/`Term.K` qualified inside namespaces; proof irrelevance makes same-value subtype elements definitionally equal (`rfl` closes `⟨t, h1⟩ = ⟨t, h2⟩` goals — relevant in Task 3).

---

### Task 1: Warm-ups — `snf_iff_SNF` and the spineLength bridge

**Files:**
- Modify: `CombinatorCalculusPlayground/SFragment.lean` (append; also update the `snf` epistemics comment — see Step 3)

**Interfaces:**
- Consumes: `snf`, `SNF` (constructors S, app1, app2), `spineLength` (Term.lean).
- Produces: `snf_iff_SNF : ∀ {t : Term}, snf t = true ↔ SNF t`; `SNF.spineLength_le {t : Term} (h : SNF t) : spineLength t ≤ 2`.

- [ ] **Step 1: State both with `sorry` (RED)**

Append to `SFragment.lean`:

```lean
-- ## Retiring the informal bridges (queued by the Stage 2 final review)
-- The Bool twin and the Prop agree after all — snf may now be used inside
-- proofs, like kFree before it.
theorem snf_iff_SNF : ∀ {t : Term}, snf t = true ↔ SNF t := sorry

-- The spec's "spine structure" reading of SNF, as a lemma: a K-free
-- normal form's head spine carries at most two arguments.
theorem SNF.spineLength_le {t : Term} (h : SNF t) : spineLength t ≤ 2 := sorry
```

Run: `lake build` — expect exactly two sorry warnings.

- [ ] **Step 2: Prove (GREEN)**

Candidates:

```lean
theorem snf_iff_SNF : ∀ {t : Term}, snf t = true ↔ SNF t := by
  intro t
  fun_induction snf t with
  | case1 =>            -- t = S
    simp; exact SNF.S
  | case2 t ih =>       -- t = app S t
    simp [ih]
    exact ⟨fun h => SNF.app1 h, fun h => by cases h with | app1 h' => exact h'⟩
  | case3 t u iht ihu => -- t = app (app S t) u
    simp [iht, ihu, Bool.and_eq_true]
    exact ⟨fun ⟨h1, h2⟩ => SNF.app2 h1 h2,
           fun h => by cases h with | app2 h1 h2 => exact ⟨h1, h2⟩⟩
  | case4 =>            -- catch-all: shapes SNF cannot inhabit
    simp
    intro h
    cases h <;> simp_all
```

The `case4` catch-all may split into several concrete shapes under `fun_induction` (Lean compiles overlapping matches to case trees) and the `cases h` dismissals may need per-shape handling — iterate; the statement is the contract. If `fun_induction` fights the wildcard arms, fall back to structural `induction t` with nested `cases` on the left component.

```lean
theorem SNF.spineLength_le {t : Term} (h : SNF t) : spineLength t ≤ 2 := by
  cases h with
  | S => simp [spineLength]
  | app1 _ => simp [spineLength]
  | app2 _ _ => simp [spineLength]
```

(`spineLength S = 0`, `spineLength (app S t) = 1`, `spineLength (app (app S t) u) = 2` — each closes by unfolding; `decide`-style closers also fine.)

Run: `lake build` — zero warnings.

- [ ] **Step 3: Update the `snf` epistemics comment**

The NOTE above `def snf` currently says snf ↔ SNF is NOT proven. That is now false. Replace that sentence with: "`snf_iff_SNF` (below) proves the Bool twin agrees with `SNF`, so snf may be used inside proofs — the census guards in Census/Enumerate.lean now double as checks of the certified reducer, not of snf itself." Keep the contrast with `kFree_iff` if it still reads naturally.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: snf_iff_SNF and SNF spine-length bridge (Stage 2 review queue)"
```

---

### Task 2: `RS.lean` — the abstract rewriting-system interface

**Files:**
- Create: `CombinatorCalculusPlayground/RS.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.RS` after SFragment, before Census)

**Interfaces:**
- Consumes: nothing project-specific (imports SFragment for later tasks' convenience is NOT needed here — import `CombinatorCalculusPlayground.Step` only in Task 3's edit; this task's file starts dependency-free except core).
- Produces: `structure RS where Carrier : Type; step : Carrier → Carrier → Prop`; namespace RS containing: `Steps (A : RS)` (inductive: `refl`, `tail`), `Steps.single`, `Steps.trans`; `NormalForm (A : RS) (a) : Prop := ¬ ∃ b, A.step a b`; `Normalizes (A : RS) (a) : Prop := ∃ b, A.Steps a b ∧ A.NormalForm b`; `Conv (A : RS)` (inductive: `refl`, `fwd`, `bwd`), `Conv.of_steps`, `Conv.trans`, `Conv.snoc_fwd`, `Conv.snoc_bwd`, `Conv.symm`.

- [ ] **Step 1: Create the file with definitions and `sorry`-stubbed lemmas (RED)**

Create `CombinatorCalculusPlayground/RS.lean`:

```lean
--! # Abstract rewriting systems
-- Stage 3's key interface decision (from the spec): universality
-- definitions are stated over an ABSTRACT rewriting system — a carrier
-- type plus a step relation — never over `Term` directly. SK, pure S,
-- tag systems, and any future reference machine are instances. This is
-- what makes the taxonomy comparative rather than bespoke.

/-- A rewriting system: things, and one-step rewrites between them. -/
structure RS where
  Carrier : Type
  step : Carrier → Carrier → Prop

namespace RS

variable {A : RS}

-- Zero or more steps — the generic twin of Term's `Steps`.
inductive Steps (A : RS) : A.Carrier → A.Carrier → Prop
  | refl (a : A.Carrier) : Steps A a a
  | tail {a b c : A.Carrier} : A.step a b → Steps A b c → Steps A a c

theorem Steps.single {a b : A.Carrier} (h : A.step a b) : A.Steps a b := sorry

theorem Steps.trans {a b c : A.Carrier} (h1 : A.Steps a b) (h2 : A.Steps b c) :
    A.Steps a c := sorry

/-- No step applies. -/
def NormalForm (A : RS) (a : A.Carrier) : Prop := ¬ ∃ b, A.step a b

/-- Some reduction path ends at a normal form. -/
def Normalizes (A : RS) (a : A.Carrier) : Prop :=
  ∃ b, A.Steps a b ∧ A.NormalForm b

-- Convertibility: walk step edges in EITHER direction (the zig-zag
-- closure). This is the "equational theory" view of a rewriting system.
inductive Conv (A : RS) : A.Carrier → A.Carrier → Prop
  | refl (a : A.Carrier) : Conv A a a
  | fwd {a b c : A.Carrier} : A.step a b → Conv A b c → Conv A a c
  | bwd {a b c : A.Carrier} : A.step b a → Conv A b c → Conv A a c

theorem Conv.of_steps {a b : A.Carrier} (h : A.Steps a b) : A.Conv a b := sorry

theorem Conv.trans {a b c : A.Carrier} (h1 : A.Conv a b) (h2 : A.Conv b c) :
    A.Conv a c := sorry

-- Append a forward/backward edge at the far end (needed for symm).
theorem Conv.snoc_fwd {a b c : A.Carrier} (h : A.Conv a b) (s : A.step b c) :
    A.Conv a c := sorry

theorem Conv.snoc_bwd {a b c : A.Carrier} (h : A.Conv a b) (s : A.step c b) :
    A.Conv a c := sorry

theorem Conv.symm {a b : A.Carrier} (h : A.Conv a b) : A.Conv b a := sorry

end RS
```

Add the root import. Run: `lake build` — expect exactly six sorry warnings.

- [ ] **Step 2: Prove (GREEN)**

Candidates:

```lean
theorem Steps.single {a b : A.Carrier} (h : A.step a b) : A.Steps a b :=
  Steps.tail h (Steps.refl b)

theorem Steps.trans {a b c : A.Carrier} (h1 : A.Steps a b) (h2 : A.Steps b c) :
    A.Steps a c := by
  induction h1 with
  | refl => exact h2
  | tail s _ ih => exact Steps.tail s (ih h2)

theorem Conv.of_steps {a b : A.Carrier} (h : A.Steps a b) : A.Conv a b := by
  induction h with
  | refl => exact Conv.refl _
  | tail s _ ih => exact Conv.fwd s ih

theorem Conv.trans {a b c : A.Carrier} (h1 : A.Conv a b) (h2 : A.Conv b c) :
    A.Conv a c := by
  induction h1 with
  | refl => exact h2
  | fwd s _ ih => exact Conv.fwd s (ih h2)
  | bwd s _ ih => exact Conv.bwd s (ih h2)

theorem Conv.snoc_fwd {a b c : A.Carrier} (h : A.Conv a b) (s : A.step b c) :
    A.Conv a c :=
  Conv.trans h (Conv.fwd s (Conv.refl c))

theorem Conv.snoc_bwd {a b c : A.Carrier} (h : A.Conv a b) (s : A.step c b) :
    A.Conv a c :=
  Conv.trans h (Conv.bwd s (Conv.refl c))

theorem Conv.symm {a b : A.Carrier} (h : A.Conv a b) : A.Conv b a := by
  induction h with
  | refl => exact Conv.refl _
  | fwd s _ ih => exact Conv.snoc_bwd ih s
  | bwd s _ ih => exact Conv.snoc_fwd ih s
```

- [ ] **Step 3: Add example-based tests**

Append (these are the module's executable-spirit tests — Props, so `example` not `#guard`):

```lean
-- ## Sanity examples: a toy countdown system (n+1 steps to n; 0 is normal)
private def countdown : RS := ⟨Nat, fun a b => a = b + 1⟩

example : countdown.Steps 2 0 :=
  RS.Steps.tail rfl (RS.Steps.tail rfl (RS.Steps.refl 0))

example : countdown.NormalForm 0 := fun ⟨_, h⟩ => by simp at h

example : countdown.Normalizes 2 :=
  ⟨0, RS.Steps.tail rfl (RS.Steps.tail rfl (RS.Steps.refl 0)),
   fun ⟨_, h⟩ => by simp at h⟩

-- 1 and 2 are convertible without either reducing to the other directly:
-- 2 → 1 forward.  And 0 connects everything below any n.
example : countdown.Conv 1 2 := RS.Conv.bwd rfl (RS.Conv.refl _)
```

(Adapt the `simp at h` closers freely — `countdown.step 0 b` unfolds to `0 = b + 1`, absurd by `omega`/`simp`.)

Run: `lake build` — zero warnings.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: abstract rewriting-system interface with generic closures"
```

---

### Task 3: Instances — SK, pure S, and the reference tag system

**Files:**
- Modify: `CombinatorCalculusPlayground/RS.lean` (append; ADD `import CombinatorCalculusPlayground.SFragment` at the top — brings in Step.lean transitively)

**Interfaces:**
- Consumes: `RS`, `RS.Steps`; `Term`, `Step`, `Steps` (⟶*) from Step.lean; `KFree`, `KFree.of_step` from SFragment.lean.
- Produces: `RS.SK : RS`; `RS.SK_steps_iff {t u : Term} : RS.SK.Steps t u ↔ t ⟶* u`; `RS.PureS : RS` (carrier `{t : Term // KFree t}`); `RS.PureS_steps_iff {a b : {t : Term // KFree t}} : RS.PureS.Steps a b ↔ a.val ⟶* b.val`; `structure TagSystem where m : Nat; rule : Bool → List Bool`; `TagSystem.stepRel`; `RS.Tag (T : TagSystem) : RS`.

- [ ] **Step 1: Statements + definitions with `sorry`-stubbed lemmas (RED)**

Append to `RS.lean` (and add the SFragment import at the top):

```lean
-- ## The instances
namespace RS

/-- Full SK reduction as a rewriting system. -/
def SK : RS := ⟨Term, Step⟩

-- The generic closure agrees with Term's own ⟶* (they have the same
-- constructors; this lemma lets Stage 1 theorems flow into RS-land).
theorem SK_steps_iff {t u : Term} : RS.SK.Steps t u ↔ t ⟶* u := sorry

/-- The pure-S fragment: carriers are terms WITH their K-freeness proof.
Legal as a rewriting system precisely because of Stage 2's closure
theorem — a step from a K-free term lands on a K-free term, so the
subtype is closed under the inherited relation. -/
def PureS : RS := ⟨{t : Term // KFree t}, fun a b => Step a.val b.val⟩

theorem PureS_steps_iff {a b : {t : Term // KFree t}} :
    RS.PureS.Steps a b ↔ a.val ⟶* b.val := sorry

end RS

/-- A 2-symbol tag system: read the head symbol, delete `m` symbols from
the front, append `rule head` at the back.

REFERENCE MODEL — EPISTEMIC STATUS: 2-tag systems are computationally
universal by Cocke–Minsky (1964). That fact is EXTERNAL knowledge, cited
here so the universality definitions in Universality/ have a concrete
reference system to be stated against; it is NOT machine-checked in this
repository and nothing here depends on its truth. -/
structure TagSystem where
  m : Nat
  rule : Bool → List Bool

/-- One tag step, as a relation (deterministic in fact, relational in form
to fit RS). -/
def TagSystem.stepRel (T : TagSystem) (w w' : List Bool) : Prop :=
  ∃ a rest, w = a :: rest ∧ T.m ≤ w.length ∧ w' = w.drop T.m ++ T.rule a

/-- A tag system as a rewriting system. -/
def RS.Tag (T : TagSystem) : RS := ⟨List Bool, T.stepRel⟩

-- Sanity example: in the tag system (m := 2, a ↦ [a]), the word
-- [true, false, false] steps to [false, true].
example : (RS.Tag ⟨2, fun a => [a]⟩).step [true, false, false] [false, true] :=
  ⟨true, [false, false], rfl, by simp, rfl⟩

-- A word shorter than m is stuck (normal form).
example : (RS.Tag ⟨2, fun a => [a]⟩).NormalForm [true] := by
  rintro ⟨w', a, rest, hw, hlen, _⟩
  subst hw
  simp at hlen
```

Run: `lake build` — expect exactly two sorry warnings (the two `_iff` lemmas); the `example`s must already elaborate — if one fails, hand-check the arithmetic before touching the definition.

- [ ] **Step 2: Prove the agreement lemmas (GREEN)**

Candidates:

```lean
theorem SK_steps_iff {t u : Term} : RS.SK.Steps t u ↔ t ⟶* u := by
  constructor
  · intro h
    induction h with
    | refl => exact Steps.refl _
    | tail s _ ih => exact Steps.tail s ih
  · intro h
    induction h with
    | refl => exact RS.Steps.refl _
    | tail s _ ih => exact RS.Steps.tail s ih
```

For `PureS_steps_iff`, the forward direction is the same shape; the backward direction needs an auxiliary induction that rebuilds the K-freeness certificates along the path (this is where Stage 2's `KFree.of_step` earns its keep):

```lean
private theorem PureS_steps_of_steps :
    ∀ {t u : Term} (h : t ⟶* u) (ht : KFree t) (hu : KFree u),
      RS.PureS.Steps ⟨t, ht⟩ ⟨u, hu⟩ := by
  intro t u h
  induction h with
  | refl => intro ht hu; exact RS.Steps.refl _
    -- ⟨t, ht⟩ = ⟨t, hu⟩ definitionally: KFree is a Prop, proof irrelevance.
  | tail s _ ih =>
    intro ht hu
    exact RS.Steps.tail (s : Step _ _) (ih (ht.of_step s) hu)

theorem PureS_steps_iff {a b : {t : Term // KFree t}} :
    RS.PureS.Steps a b ↔ a.val ⟶* b.val := by
  constructor
  · intro h
    induction h with
    | refl => exact Steps.refl _
    | tail s _ ih => exact Steps.tail s ih
  · intro h
    obtain ⟨t, ht⟩ := a
    obtain ⟨u, hu⟩ := b
    exact PureS_steps_of_steps h ht hu
```

(In the `refl` case of the auxiliary, if `exact RS.Steps.refl _` doesn't close because the two subtype elements print differently, `exact (Subtype.ext rfl : (⟨t,ht⟩ : {t // KFree t}) = ⟨t,hu⟩) ▸ RS.Steps.refl _` — but proof irrelevance is definitional in Lean 4, so plain `rfl`-driven forms should work. Iterate.)

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: RS instances — SK, pure S via KFree closure, reference tag system"
```

---

### Task 4: `Universality/Defs.lean` — simulation triples and the three definitions

**Files:**
- Create: `CombinatorCalculusPlayground/Universality/Defs.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Universality.Defs` after RS)

**Interfaces:**
- Consumes: `RS`, `RS.Steps`, `RS.Normalizes`, `RS.Conv`.
- Produces: `structure Simulation (A B : RS)` with fields `enc : A.Carrier → B.Carrier`, `dec : B.Carrier → Option A.Carrier`, `dec_enc : ∀ a, dec (enc a) = some a`, `fwd : ∀ {a a' : A.Carrier}, A.step a a' → B.Steps (enc a) (enc a')`, `bwd : ∀ {a a' : A.Carrier}, B.Steps (enc a) (enc a') → A.Steps a a'`; `Simulation.enc_injective`; `Simulation.fwd_steps`; `PreservesNormalizes (A B : RS) (enc : A.Carrier → B.Carrier) : Prop`; `PreservesConv (A B : RS) (enc : A.Carrier → B.Carrier) : Prop`; `UniversalReach (R B : RS) : Prop := Nonempty (Simulation R B)`; `UniversalNorm (R B : RS) : Prop`; `UniversalConv (R B : RS) : Prop`.

- [ ] **Step 1: Create the file (definitions land whole; the two lemmas get the sorry cycle) (RED)**

Create `CombinatorCalculusPlayground/Universality/Defs.lean`:

```lean
--! # What "computationally universal" could mean
-- The prize question's hidden difficulty is DEFINITIONAL: universal under
-- which observations, and which encodings? This module pins the candidate
-- definitions as properties of (system, encoder, decoder) triples over
-- abstract rewriting systems.
--
-- ## The encoding class: what IS and IS NOT pinned here (required honesty)
-- PINNED, formally: the encoder is one fixed total function, uniform in
-- its input (no per-instance cleverness); the decoder inverts it on the
-- image (`dec_enc`), so encodings are faithful and answers can be read
-- back. Simulations must track steps structurally (`fwd`/`bwd`), which
-- blocks the grossest form of the 2007 Wolfram-prize objection (an
-- "encoding" that performs the computation itself and ships the answer).
-- NOT PINNED, and not formalizable in this zero-dependency setting: that
-- `enc`/`dec` are COMPUTABLE. Every Lean `def` is computable by
-- construction, but that is a metatheoretic fact, not a hypothesis these
-- definitions can state or use. A full internal answer needs a
-- computability theory (registered as an explicit limitation in
-- CONJECTURES.md, not papered over).
import CombinatorCalculusPlayground.RS

/-- A simulation of `A` inside `B`: encode, run, decode.
`fwd` says B can follow every A-step (in possibly many steps);
`bwd` says B's behavior between encoded states is not richer than A's —
reachability between image points reflects back. -/
structure Simulation (A B : RS) where
  enc : A.Carrier → B.Carrier
  dec : B.Carrier → Option A.Carrier
  dec_enc : ∀ a, dec (enc a) = some a
  fwd : ∀ {a a' : A.Carrier}, A.step a a' → B.Steps (enc a) (enc a')
  bwd : ∀ {a a' : A.Carrier}, B.Steps (enc a) (enc a') → A.Steps a a'

namespace Simulation

variable {A B : RS}

-- The decoder makes the encoder injective — distinct programs stay
-- distinct inside the host.
theorem enc_injective (S : Simulation A B) {a a' : A.Carrier}
    (h : S.enc a = S.enc a') : a = a' := sorry

-- fwd lifts from single steps to paths.
theorem fwd_steps (S : Simulation A B) {a a' : A.Carrier}
    (h : A.Steps a a') : B.Steps (S.enc a) (S.enc a') := sorry

end Simulation

-- ## The three observation modes
-- Same triple shape, different question asked of the host system.

/-- Normalization-based: the host halts exactly when the source does.
(For pure S this observable is externally known to be degenerate —
Waldmann 2000 shows S-normalization is decidable; see CONJECTURES.md.) -/
def PreservesNormalizes (A B : RS) (enc : A.Carrier → B.Carrier) : Prop :=
  ∀ a, A.Normalizes a ↔ B.Normalizes (enc a)

/-- Convertibility-based: the host's equational theory restricted to the
image is exactly the source's. -/
def PreservesConv (A B : RS) (enc : A.Carrier → B.Carrier) : Prop :=
  ∀ a a', A.Conv a a' ↔ B.Conv (enc a) (enc a')

-- ## Universality, relative to a reference system R
-- Universality claims are ∃-encoding (exhibit one); non-universality
-- claims are ∀-encoding over the pinned class (the quantifier asymmetry
-- from the spec).

/-- Reachability-based universality: B hosts a full step-faithful
simulation of the reference. -/
def UniversalReach (R B : RS) : Prop := Nonempty (Simulation R B)

/-- Normalization-based universality: some encoding makes halting agree. -/
def UniversalNorm (R B : RS) : Prop :=
  ∃ enc : R.Carrier → B.Carrier, PreservesNormalizes R B enc

/-- Convertibility-based universality: some encoding embeds the reference's
equational theory. -/
def UniversalConv (R B : RS) : Prop :=
  ∃ enc : R.Carrier → B.Carrier, PreservesConv R B enc
```

Add the root import. Run: `lake build` — expect exactly two sorry warnings.

- [ ] **Step 2: Prove the two lemmas (GREEN)**

```lean
theorem enc_injective (S : Simulation A B) {a a' : A.Carrier}
    (h : S.enc a = S.enc a') : a = a' := by
  have h1 := S.dec_enc a
  have h2 := S.dec_enc a'
  rw [h] at h1
  rw [h1] at h2
  injection h2

theorem fwd_steps (S : Simulation A B) {a a' : A.Carrier}
    (h : A.Steps a a') : B.Steps (S.enc a) (S.enc a') := by
  induction h with
  | refl => exact RS.Steps.refl _
  | tail s _ ih => exact RS.Steps.trans (S.fwd s) ih
```

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: simulation triples and the three universality definitions"
```

---

### Task 5: `Universality/Taxonomy.lean` — the implication lattice + the Stage 1 bridge

**Files:**
- Create: `CombinatorCalculusPlayground/Universality/Taxonomy.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Universality.Taxonomy` after Defs)

**Interfaces:**
- Consumes: everything from Tasks 2–4; Stage 1's `confluence {t u v : Term} : t ⟶* u → t ⟶* v → ∃ w, (u ⟶* w) ∧ (v ⟶* w)` (Confluence.lean) via `RS.SK_steps_iff`.
- Produces: `RS.Confluent (B : RS) : Prop`; `RS.ChurchRosser (B : RS) : Prop`; `RS.ChurchRosser_of_confluent`; `RS.SK_confluent : RS.Confluent RS.SK`; `RS.SK_churchRosser : RS.ChurchRosser RS.SK`; `Simulation.conv_preserve`; `Simulation.ImageClosed`; `Simulation.conv_reflect`; `Simulation.preservesConv`; `Simulation.normalizes_preserve`; `UniversalReach.toUniversalConv`.

**Escape hatch (spec):** 3 documented attempts per theorem, then CONJECTURES registration + removal.

- [ ] **Step 1: Create the file, all statements `sorry` (RED)**

Create `CombinatorCalculusPlayground/Universality/Taxonomy.lean`:

```lean
--! # The implication lattice
-- Which universality definitions imply which, and at what price. The
-- shape of the answers (proved below):
--
--   reachability (Simulation) ══unconditionally══▶ Conv-preservation (→)
--   reachability + host Church–Rosser + image-closure ══▶ full ConvSim
--   reachability + NF-correspondence ══▶ Norm-preservation (→)
--
-- The reverse implications are NOT theorems here: a Conv- or Norm-
-- preserving encoding need not track steps at all. Each definition's
-- status per system lives in CONJECTURES.md's definitions ledger.
import CombinatorCalculusPlayground.Universality.Defs
import CombinatorCalculusPlayground.Confluence

namespace RS

/-- Diamond for the reflexive-transitive closure. -/
def Confluent (B : RS) : Prop :=
  ∀ {a b c : B.Carrier}, B.Steps a b → B.Steps a c → ∃ d, B.Steps b d ∧ B.Steps c d

/-- Convertible things rejoin. -/
def ChurchRosser (B : RS) : Prop :=
  ∀ {a b : B.Carrier}, B.Conv a b → ∃ c, B.Steps a c ∧ B.Steps b c

theorem ChurchRosser_of_confluent {B : RS} (h : B.Confluent) : B.ChurchRosser := sorry

-- ## The Stage 1 bridge: SK is Church–Rosser in RS-language.
theorem SK_confluent : RS.Confluent RS.SK := sorry

theorem SK_churchRosser : RS.ChurchRosser RS.SK := sorry

end RS

namespace Simulation

variable {A B : RS}

-- ## Lattice edge 1 (unconditional): simulations preserve convertibility.
theorem conv_preserve (S : Simulation A B) {a a' : A.Carrier}
    (h : A.Conv a a') : B.Conv (S.enc a) (S.enc a') := sorry

/-- Everything the host reaches from an encoded state can flow back to an
encoded state. Rules out the host wandering into junk it can never
account for. -/
def ImageClosed (S : Simulation A B) : Prop :=
  ∀ (a : A.Carrier) (b : B.Carrier),
    B.Steps (S.enc a) b → ∃ a', B.Steps b (S.enc a')

-- ## Lattice edge 2: with a Church–Rosser host and image-closure,
-- convertibility also REFLECTS — the encoding adds no equations.
theorem conv_reflect (S : Simulation A B) (hcr : B.ChurchRosser)
    (hic : S.ImageClosed) {a a' : A.Carrier}
    (h : B.Conv (S.enc a) (S.enc a')) : A.Conv a a' := sorry

-- Packaging both directions: a full convertibility-preserving encoding.
theorem preservesConv (S : Simulation A B) (hcr : B.ChurchRosser)
    (hic : S.ImageClosed) : PreservesConv A B S.enc := sorry

-- ## Lattice edge 3: with normal-form correspondence, normalization is
-- preserved (one direction — reflection needs more, see module header).
theorem normalizes_preserve (S : Simulation A B)
    (hnf : ∀ a, A.NormalForm a → B.NormalForm (S.enc a))
    {a : A.Carrier} (h : A.Normalizes a) : B.Normalizes (S.enc a) := sorry

end Simulation

-- ## The lattice at the Universal* level
theorem UniversalReach.toUniversalConv {R B : RS}
    (h : UniversalReach R B) (hcr : B.ChurchRosser)
    (hic : ∀ S : Simulation R B, S.ImageClosed) : UniversalConv R B := sorry
```

Add the root import. Run: `lake build` — expect exactly seven sorry warnings.

- [ ] **Step 2: Prove, in this order (GREEN)**

Candidates:

```lean
theorem ChurchRosser_of_confluent {B : RS} (h : B.Confluent) : B.ChurchRosser := by
  intro a b hconv
  induction hconv with
  | refl => exact ⟨_, RS.Steps.refl _, RS.Steps.refl _⟩
  | fwd s _ ih =>
    -- a → a₁ ~ b, and a₁, b rejoin at d: then a →* d via the extra step.
    obtain ⟨d, h1, h2⟩ := ih
    exact ⟨d, RS.Steps.tail s h1, h2⟩
  | bwd s _ ih =>
    -- a₁ → a and a₁ ~ b rejoining at d: confluence on (a₁ → a) vs (a₁ →* d).
    obtain ⟨d, h1, h2⟩ := ih
    obtain ⟨e, he1, he2⟩ := h (RS.Steps.single s) h1
    exact ⟨e, he1, RS.Steps.trans h2 he2⟩

theorem SK_confluent : RS.Confluent RS.SK := by
  intro a b c h1 h2
  obtain ⟨w, hw1, hw2⟩ := confluence (RS.SK_steps_iff.mp h1) (RS.SK_steps_iff.mp h2)
  exact ⟨w, RS.SK_steps_iff.mpr hw1, RS.SK_steps_iff.mpr hw2⟩

theorem SK_churchRosser : RS.ChurchRosser RS.SK :=
  RS.ChurchRosser_of_confluent RS.SK_confluent
```

```lean
theorem conv_preserve (S : Simulation A B) {a a' : A.Carrier}
    (h : A.Conv a a') : B.Conv (S.enc a) (S.enc a') := by
  induction h with
  | refl => exact RS.Conv.refl _
  | fwd s _ ih => exact RS.Conv.trans (RS.Conv.of_steps (S.fwd s)) ih
  | bwd s _ ih => exact RS.Conv.trans (RS.Conv.of_steps (S.fwd s)).symm ih

theorem conv_reflect (S : Simulation A B) (hcr : B.ChurchRosser)
    (hic : S.ImageClosed) {a a' : A.Carrier}
    (h : B.Conv (S.enc a) (S.enc a')) : A.Conv a a' := by
  obtain ⟨w, hw1, hw2⟩ := hcr h
  obtain ⟨a₁, hback⟩ := hic a w hw1
  have h1 : A.Steps a a₁ := S.bwd (RS.Steps.trans hw1 hback)
  have h2 : A.Steps a' a₁ := S.bwd (RS.Steps.trans hw2 hback)
  exact RS.Conv.trans (RS.Conv.of_steps h1) (RS.Conv.of_steps h2).symm

theorem preservesConv (S : Simulation A B) (hcr : B.ChurchRosser)
    (hic : S.ImageClosed) : PreservesConv A B S.enc :=
  fun _ _ => ⟨S.conv_preserve, S.conv_reflect hcr hic⟩

theorem normalizes_preserve (S : Simulation A B)
    (hnf : ∀ a, A.NormalForm a → B.NormalForm (S.enc a))
    {a : A.Carrier} (h : A.Normalizes a) : B.Normalizes (S.enc a) := by
  obtain ⟨b, hsteps, hnfb⟩ := h
  exact ⟨S.enc b, S.fwd_steps hsteps, hnf b hnfb⟩

theorem UniversalReach.toUniversalConv {R B : RS}
    (h : UniversalReach R B) (hcr : B.ChurchRosser)
    (hic : ∀ S : Simulation R B, S.ImageClosed) : UniversalConv R B := by
  obtain ⟨S⟩ := h
  exact ⟨S.enc, S.preservesConv hcr (hic S)⟩
```

Run: `lake build` — zero warnings.

- [ ] **Step 3: Run the axiom audit and commit**

Run `lake env lean` on a scratch file (delete after) with `#print axioms` for `RS.SK_churchRosser`, `Simulation.preservesConv`, `UniversalReach.toUniversalConv`; record outputs for the report (expect `[propext]`-class trails inherited from Stage 1; no `sorryAx`).

```bash
git add -A
git commit -m "feat: implication lattice with SK Church-Rosser bridge from Stage 1"
```

---

### Task 6: The definitions ledger + artifacts

**Files:**
- Modify: `CONJECTURES.md` (new "Definitions ledger" section + methodology line)
- Modify: `LAB_NOTEBOOK.md` (dated entry)

**Interfaces:**
- Consumes: all Stage 3 names (must cite only theorems that exist: `snf_iff_SNF`, `SNF.spineLength_le`, `RS.SK_churchRosser`, `Simulation.conv_preserve`, `Simulation.conv_reflect`, `Simulation.normalizes_preserve`, `UniversalReach.toUniversalConv`, instances `RS.SK`/`RS.PureS`/`RS.Tag`).
- Produces: the spec's Stage 3 success criterion — every (definition, system) status proven or explicitly open.

- [ ] **Step 1: Add the Definitions ledger to `CONJECTURES.md`**

New section after the conjectures (adapt only if theorem names differ in the tree — verify each against the code before writing):

```markdown
## Definitions ledger (Stage 3)

Universality is relative to a reference system R and an observation mode
(Universality/Defs.lean). Designated reference: 2-symbol tag systems
(`RS.Tag`) — universal by Cocke–Minsky 1964, an EXTERNAL fact cited, not
machine-checked. The encoding class pins uniformity and decoder-inversion
formally; computability of encoders is NOT internally pinned (no
computability theory in a zero-dependency setting) — an explicit,
registered limitation.

Proven lattice edges (Universality/Taxonomy.lean): simulations preserve
convertibility unconditionally (`Simulation.conv_preserve`); they reflect
it when the host is Church–Rosser and image-closed
(`Simulation.conv_reflect`); they preserve normalization under
normal-form correspondence (`Simulation.normalizes_preserve`). SK is
Church–Rosser in RS-language (`RS.SK_churchRosser`, riding Stage 1).

Status of `UniversalReach (RS.Tag T) — / UniversalNorm — / UniversalConv —`
for each host:

| Host        | Reach (Simulation)      | Norm                          | Conv |
|-------------|-------------------------|-------------------------------|------|
| `RS.SK`     | open (Stage 4 target)   | open                          | open |
| `RS.PureS`  | open (prize-adjacent)   | externally expected FALSE for |open |
|             |                         | nontrivial R: Waldmann 2000   |      |
|             |                         | (S-normalization decidable) — |      |
|             |                         | NOT machine-checked here      |      |

No cell of this table is a theorem yet; the table is the register the
spec's Stage 3 success criterion requires ("proven or explicitly open").
```

- [ ] **Step 2: Add the methodology line**

After the Stage 2 methodology paragraph in `CONJECTURES.md`:

```markdown
As of Stage 3, the universality definitions themselves are formal objects
(`Universality/Defs.lean`) over abstract rewriting systems (`RS.lean`),
with a machine-checked implication lattice (`Universality/Taxonomy.lean`)
and instances for SK, pure S, and the tag-system reference. See the
Definitions ledger below.
```

- [ ] **Step 3: `LAB_NOTEBOOK.md` entry**

Dated entry (actual execution date): which candidates survived, real friction (the plan expects the `snf_iff_SNF` catch-all case and the subtype `refl` in `PureS_steps_iff` to be the likeliest fight-sites — report what actually happened), the axiom-audit results from Task 5, and one line on the design decision that computability pinning is registered-not-formalized.

- [ ] **Step 4: Build and commit**

Run: `lake build` — zero warnings.

```bash
git add -A
git commit -m "feat: Stage 3 definitions ledger and lab-notebook entry"
```

---

## Self-review notes

- Spec coverage (Stage 3 section): `RS` interface ✓ (T2); instances SK/pure-S/reference ✓ (T3, tag system with external-status framing); (system, encoder, decoder) triples with pinning ✓ (T4, incl. the honesty docstring the spec's "formal answer to the 2007 dispute" demands — with the computability limitation registered rather than overclaimed); normalization-/reachability-/convertibility-based definitions ✓ (T4); implication lattice ✓ (T5); statuses proven-or-open ✓ (T6 ledger). Calibration-sandwich items (a) certify iota etc. are Stage 4 per the spec — correctly absent. Waldmann kill: registered as external in the ledger, not claimed (consistent with spec's Risks section allowing the citation downgrade).
- Warm-ups from Stage 2 final review ✓ (T1).
- Type consistency: `Simulation` field names (`enc`, `dec`, `dec_enc`, `fwd`, `bwd`) used identically in T4 lemmas and T5 theorems; `RS.Steps`/`RS.Conv` constructor names (refl/tail; refl/fwd/bwd) consistent across T2 proofs, T3 agreement lemmas, T5 inductions; `PreservesConv A B S.enc` argument order consistent between T4 def and T5 `preservesConv`; `UniversalReach`/`UniversalNorm`/`UniversalConv` defined T4, consumed T5/T6.
- Placeholder scan: clean; every proof step has a candidate or an explicit expected-fight note.
- Import discipline: RS.lean imports SFragment (T3 edit; brings Step transitively); Universality/Defs imports RS; Taxonomy imports Defs + Confluence. No cycles. Root file order: … Confluence, SFragment, RS, Universality.Defs, Universality.Taxonomy, Census.*.
- Known risk flagged for implementers: `variable {A : RS}` scoping across `namespace RS` sections, and dot-notation for `A.Steps`/`A.Conv` (defined as `Steps (A : RS) : …` so `A.Steps a b` elaborates) — if dot-notation fights, fall back to `RS.Steps A a b` spellings; statements may be adjusted to the qualified form as long as the propositions are unchanged.
