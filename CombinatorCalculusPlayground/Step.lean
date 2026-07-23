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
