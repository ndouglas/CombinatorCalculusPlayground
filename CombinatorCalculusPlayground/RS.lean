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

theorem Steps.single {a b : A.Carrier} (h : A.step a b) : A.Steps a b :=
  Steps.tail h (Steps.refl b)

theorem Steps.trans {a b c : A.Carrier} (h1 : A.Steps a b) (h2 : A.Steps b c) :
    A.Steps a c := by
  induction h1 with
  | refl => exact h2
  | tail s _ ih => exact Steps.tail s (ih h2)

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

-- 1 and 2 are convertible without either reducing to the other directly:
-- 2 → 1 forward.  And 0 connects everything below any n.
example : countdown.Conv 1 2 := RS.Conv.bwd rfl (RS.Conv.refl _)
