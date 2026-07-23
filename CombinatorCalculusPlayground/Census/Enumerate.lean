--! # The census: enumerate and classify pure-S terms
import CombinatorCalculusPlayground.Census.Eval

open Term

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

-- ## Classifying a trajectory
-- Three verdicts, with three different epistemic standings. No theorem
-- about classify itself exists — the seen-list/step-counting/cycle-index
-- bookkeeping below is unverified census tooling built on top of the
-- verified stepOnce. What each verdict can actually lean on:
--   terminating — grounded in the verified core: stepOnce_none_normal
--                 proves the halt condition really is a normal form, and
--                 stepOnce_sound proves every step taken to get there is
--                 legal. classify's own bookkeeping (step count) is not
--                 itself verified.
--   cyclic      — rests on stepOnce's determinism (informal: not proven
--                 here) plus the unverified revisit bookkeeping above.
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
      match seen.findIdx? (· == next) with
      | some i => .cyclic i (seen.length - i)
      | none => go f (seen ++ [next]) next

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
