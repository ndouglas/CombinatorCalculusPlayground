--! # Abstract rewriting systems
-- Stage 3's key interface decision (from the spec): universality
-- definitions are stated over an ABSTRACT rewriting system — a carrier
-- type plus a step relation — never over `Term` directly. SK, pure S,
-- tag systems, and any future reference machine are instances. This is
-- what makes the taxonomy comparative rather than bespoke.
import CombinatorCalculusPlayground.SFragment

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

theorem Steps.single {a b : A.Carrier} (h : A.step a b) : A.Steps a b :=
  Steps.tail h (Steps.refl b)

theorem Steps.trans {a b c : A.Carrier} (h1 : A.Steps a b) (h2 : A.Steps b c) :
    A.Steps a c := by
  induction h1 with
  | refl => exact h2
  | tail s _ ih => exact Steps.tail s (ih h2)

-- Length-indexed paths (Stage 92). `Steps` is Prop-level and lengthless, so statements like "a
-- cycle has finitely many root fires" or "take a minimal cycle" are unstatable against it.
-- `StepsN n` counts steps; the descent engine below turns any strictly-shortening cycle surgery
-- into a no-cycles theorem, by bounded induction — no choice.
inductive StepsN (A : RS) : Nat → A.Carrier → A.Carrier → Prop
  | refl (a : A.Carrier) : StepsN A 0 a a
  | tail {n : Nat} {a b c : A.Carrier} : A.step a b → StepsN A n b c → StepsN A (n + 1) a c

theorem StepsN.toSteps {n : Nat} {a b : A.Carrier} (h : A.StepsN n a b) : A.Steps a b := by
  induction h with
  | refl a => exact Steps.refl a
  | tail s _ ih => exact Steps.tail s ih

theorem Steps.toStepsN {a b : A.Carrier} (h : A.Steps a b) : ∃ n, A.StepsN n a b := by
  induction h with
  | refl a => exact ⟨0, StepsN.refl a⟩
  | tail s _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, StepsN.tail s hn⟩

theorem StepsN.trans {m n : Nat} {a b c : A.Carrier} (h1 : A.StepsN m a b)
    (h2 : A.StepsN n b c) : A.StepsN (m + n) a c := by
  induction h1 with
  | refl a =>
      rw [Nat.zero_add]
      exact h2
  | tail s _ ih =>
      rw [Nat.add_right_comm]
      exact StepsN.tail s (ih h2)

/-- Basepoint shift: a cycle through `a` visiting `b` is a cycle through `b`, same total length. -/
theorem StepsN.rotate {m n : Nat} {a b : A.Carrier} (h1 : A.StepsN m a b) (h2 : A.StepsN n b a) :
    A.StepsN (n + m) b b :=
  StepsN.trans h2 h1

/-- The descent engine: if every nonempty cycle yields a strictly shorter nonempty cycle, there
are no nonempty cycles. Bounded strong induction — no minimum is ever chosen. -/
theorem no_cycle_of_descent
    (h : ∀ n t, 1 ≤ n → A.StepsN n t t → ∃ m u, 1 ≤ m ∧ m < n ∧ A.StepsN m u u) :
    ∀ n t, 1 ≤ n → ¬ A.StepsN n t t := by
  have key : ∀ (bound n : Nat) (t : A.Carrier), n ≤ bound → 1 ≤ n → ¬ A.StepsN n t t := by
    intro bound
    induction bound with
    | zero =>
        intro n t hle h1 _
        omega
    | succ bound ih =>
        intro n t hle h1 hcyc
        obtain ⟨m, u, hm1, hmn, hmc⟩ := h n t h1 hcyc
        exact ih m u (by omega) hm1 hmc
  intro n t h1
  exact key n n t (Nat.le_refl n) h1

/-- No step applies. -/
def NormalForm (A : RS) (a : A.Carrier) : Prop := ¬ ∃ b, A.step a b

/-- A normal form goes nowhere: any path out of it has length zero. (Stage 65 — the generic twin of
Term's `NormalForm.steps_eq`.) -/
theorem NormalForm.steps_eq {a b : A.Carrier} (hn : A.NormalForm a) (h : A.Steps a b) : a = b := by
  cases h with
  | refl => rfl
  | tail s _ => exact absurd ⟨_, s⟩ hn

/-- Some reduction path ends at a normal form. -/
def Normalizes (A : RS) (a : A.Carrier) : Prop :=
  ∃ b, A.Steps a b ∧ A.NormalForm b

-- Convertibility: walk step edges in EITHER direction (the zig-zag
-- closure). This is the "equational theory" view of a rewriting system.
inductive Conv (A : RS) : A.Carrier → A.Carrier → Prop
  | refl (a : A.Carrier) : Conv A a a
  | fwd {a b c : A.Carrier} : A.step a b → Conv A b c → Conv A a c
  | bwd {a b c : A.Carrier} : A.step b a → Conv A b c → Conv A a c

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

-- Append a forward/backward edge at the far end (needed for symm).
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

end RS

-- ## Sanity examples: a toy countdown system (n+1 steps to n; 0 is normal)
@[reducible] private def countdown : RS := ⟨Nat, fun a b => a = b + 1⟩

example : countdown.Steps 2 0 :=
  RS.Steps.tail rfl (RS.Steps.tail rfl (RS.Steps.refl (0 : countdown.Carrier)))

example : countdown.NormalForm 0 := fun ⟨_, h⟩ => by omega

example : countdown.Normalizes 2 :=
  ⟨0, RS.Steps.tail rfl (RS.Steps.tail rfl (RS.Steps.refl (0 : countdown.Carrier))),
   fun ⟨_, h⟩ => by omega⟩

-- 1 does not reduce to 2, yet Conv 1 2 holds — the zig-zag sees the
-- backward edge (2 → 1 is a step, walked in reverse).
example : countdown.Conv 1 2 := RS.Conv.bwd rfl (RS.Conv.refl _)

-- ## The instances
namespace RS

/-- Full SK reduction as a rewriting system. -/
def SK : RS := ⟨Term, Step⟩

-- The generic closure agrees with Term's own ⟶* (they have the same
-- constructors; this lemma lets Stage 1 theorems flow into RS-land).
theorem SK_steps_iff {t u : Term} : RS.SK.Steps t u ↔ t ⟶* u := by
  constructor
  · -- `induction` chokes on `RS.Steps` at a concrete carrier (an
    -- `mkElimApp` motive error — it needs the `RS` to be a variable, as in
    -- `RS.Steps.trans`), so drive the recursor by hand instead.
    intro h
    exact h.rec (fun a => _root_.Steps.refl a) (fun s _ ih => _root_.Steps.tail s ih)
  · intro h
    induction h with
    | refl => exact RS.Steps.refl _
    | tail s _ ih => exact RS.Steps.tail s ih

/-- The pure-S fragment: carriers are terms WITH their K-freeness proof.
Legal as a rewriting system precisely because of Stage 2's closure
theorem — a step from a K-free term lands on a K-free term, so the
subtype is closed under the inherited relation. -/
def PureS : RS := ⟨{t : Term // KFree t}, fun a b => Step a.val b.val⟩

private theorem PureS_steps_of_steps :
    ∀ {t u : Term} (_ : t ⟶* u) (ht : KFree t) (hu : KFree u),
      RS.PureS.Steps ⟨t, ht⟩ ⟨u, hu⟩ := by
  intro t u h
  induction h with
  | refl => intro ht hu; exact RS.Steps.refl _
    -- ⟨t, ht⟩ = ⟨t, hu⟩ definitionally: KFree is a Prop, proof irrelevance.
  | tail s _ ih =>
    intro ht hu
    -- The middle carrier keeps a fresh K-freeness certificate (Stage 2's
    -- `KFree.of_step`); typing the step forces `PureS.step` to unfold to
    -- the underlying `Step`, so the raw `s` fits.
    have hstep : RS.PureS.step ⟨_, ht⟩ ⟨_, ht.of_step s⟩ := s
    exact RS.Steps.tail hstep (ih (ht.of_step s) hu)

theorem PureS_steps_iff {a b : {t : Term // KFree t}} :
    RS.PureS.Steps a b ↔ a.val ⟶* b.val := by
  constructor
  · intro h
    -- Raw recursor for the same reason as SK_steps_iff above: `induction`
    -- fails on RS.Steps at a concrete instance (mkElimApp motive error).
    exact h.rec (fun a => _root_.Steps.refl a.val) (fun s _ ih => _root_.Steps.tail s ih)
  · intro h
    obtain ⟨t, ht⟩ := a
    obtain ⟨u, hu⟩ := b
    exact PureS_steps_of_steps h ht hu

end RS

/-- A tag system over an arbitrary symbol alphabet: read the head symbol,
delete `m` symbols from the front, append `rule head` at the back.

REFERENCE MODEL — EPISTEMIC STATUS: deletion-number-2 tag systems
(`m = 2`) over finite alphabets are computationally universal by
Cocke–Minsky (1964). That fact is EXTERNAL knowledge, cited here so the
universality definitions in Universality/ have a concrete reference class
to be stated against; it is NOT machine-checked in this repository and
nothing here depends on its truth. (`m = 0` instances are degenerate —
they never consume input — and the literature's tag systems have m ≥ 1;
no field constraint is imposed.) -/
structure TagSystem where
  Sym : Type
  m : Nat
  rule : Sym → List Sym

/-- One tag step, as a relation (deterministic in fact, relational in form
to fit RS). -/
def TagSystem.stepRel (T : TagSystem) (w w' : List T.Sym) : Prop :=
  ∃ a rest, w = a :: rest ∧ T.m ≤ w.length ∧ w' = w.drop T.m ++ T.rule a

/-- A tag system as a rewriting system. -/
def RS.Tag (T : TagSystem) : RS := ⟨List T.Sym, T.stepRel⟩

-- Sanity example: in the tag system (Sym := Bool, m := 2, a ↦ [a]), the
-- word [true, false, false] steps to [false, true].
example : (RS.Tag ⟨Bool, 2, fun a => [a]⟩).step [true, false, false] [false, true] :=
  ⟨true, [false, false], rfl, by simp, rfl⟩

-- A word shorter than m is stuck (normal form).
example : (RS.Tag ⟨Bool, 2, fun a => [a]⟩).NormalForm [true] := by
  rintro ⟨w', a, rest, hw, hlen, _⟩
  simp at hlen
