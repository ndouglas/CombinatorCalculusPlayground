--! # Executable reduction
-- `Step` (in Step.lean) says which reductions are *legal* — a relation, not
-- a program. Here we pick a deterministic strategy (leftmost-outermost: always
-- fire the leftmost, outermost redex) and implement it as a function we can
-- actually run. Leftmost-outermost is the *normalizing* strategy: if any
-- strategy reaches a normal form, this one does — which is exactly what a
-- census needs.
import CombinatorCalculusPlayground.Step

open Term

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

-- ## Soundness
-- Everything stepOnce does is a legal Step. This is what lets the census
-- make *claims*: when the evaluator says "t reduced to u", that's a theorem,
-- not just program output.
theorem stepOnce_sound : ∀ {t u : Term}, stepOnce t = some u → t ⟶ u := by
  intro t
  fun_induction stepOnce t with
  | case1 x y =>
    intro u h
    cases h
    exact Step.K_red ..
  | case2 f g x =>
    intro u h
    cases h
    exact Step.S_red ..
  | case3 a b _ _ a' hstep ih =>
    intro u h
    injection h with h
    subst h
    exact Step.appL (ih hstep)
  | case4 a b _ _ _ b' hstep _ ih =>
    intro u h
    injection h with h
    subst h
    exact Step.appR (ih hstep)
  | _ =>
    intro u h
    simp_all

-- ## Completeness
-- When stepOnce gives up, there really is no legal step: `none` certifies a
-- normal form. Together with soundness this makes the census classifier's
-- "terminating" verdict a machine-checked fact.
def NormalForm (t : Term) : Prop := ¬ ∃ u, t ⟶ u

-- If any step is possible, stepOnce finds one (maybe a different one:
-- leftmost-outermost picks its own redex, but it never misses).
theorem stepOnce_isSome_of_step : ∀ {t u : Term}, t ⟶ u → (stepOnce t).isSome := by
  intro t u h
  induction h with
  | K_red x y => simp [stepOnce, app2]
  | S_red f g x => simp [stepOnce, app3]
  | @appL t t' u s ih =>
    -- The left side can step, so stepOnce t = some w by the IH. Splitting on
    -- stepOnce's match arms: the two redex arms return some outright, and the
    -- descent arm consults stepOnce t — which hw says is some.
    rcases Option.isSome_iff_exists.mp ih with ⟨w, hw⟩
    rw [stepOnce.eq_def]
    split <;> simp_all
  | @appR t u u' s ih =>
    -- Same shape, but the descent arm tries stepOnce t *first*: if it's some
    -- we're done immediately, and only if it's none does hw's stepOnce u kick
    -- in — hence the extra case split on stepOnce t.
    rcases Option.isSome_iff_exists.mp ih with ⟨w, hw⟩
    rw [stepOnce.eq_def]
    split <;> simp_all
    cases hst : stepOnce t <;> simp_all

-- Contrapositive: if stepOnce found nothing, no step exists — because if one
-- did, stepOnce_isSome_of_step would contradict the `none` we were handed.
theorem stepOnce_none_normal : ∀ {t : Term}, stepOnce t = none → NormalForm t := by
  intro t hnone ⟨u, hstep⟩
  have := stepOnce_isSome_of_step hstep
  simp [hnone] at this
