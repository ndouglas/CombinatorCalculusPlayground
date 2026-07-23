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
