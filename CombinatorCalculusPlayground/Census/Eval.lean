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
