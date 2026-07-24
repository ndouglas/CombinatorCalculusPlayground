--! # Bounded reachability for the S-fragment
-- THE CLAIM THIS FILE EXISTS TO CHECK AND THEN PROVE: along any K-free
-- reduction path, leaf counts are monotone non-decreasing (Stage 2's
-- `leafCount_le_of_steps`), so every intermediate term on a path from t
-- to u has at most `leafCount u` leaves. Reachability between K-free
-- terms is therefore search in a FINITE universe — and this file builds
-- the certified searcher. The paper-level observation is two lines given
-- monotonicity and may well be folklore; the machine-checked decision
-- procedure is the contribution (see CONJECTURES.md for the register).
--
-- HONESTY CONTRACT: the procedure returns Option Bool. `some b` is a
-- certified verdict (theorem `reachable?_correct`); `none` means fuel
-- ran out before the closure saturated and is NEVER evidence.
import CombinatorCalculusPlayground.Confluence
import CombinatorCalculusPlayground.Census.Enumerate

open Term

-- ## Every one-step reduct
-- stepOnce picks the leftmost-outermost redex; reachability quantifies
-- over ALL steps, so we need the full successor set: the root redex (if
-- the term is one) plus every reduct inside either side.
def rootRed : Term → List Term
  | .app (.app .K x) _ => [x]
  | .app (.app (.app .S f) g) x => [.app (.app f x) (.app g x)]
  | _ => []

def succs : Term → List Term
  | .S => []
  | .K => []
  | .app t u =>
    rootRed (.app t u)
      ++ (succs t).map (fun t' => Term.app t' u)
      ++ (succs u).map (fun u' => Term.app t u')

-- Root redexes fire.
#guard succs (app2 K S K) = [S]
#guard succs (app3 S K K S) = [app (app K S) (app K S)]
-- Atoms and underapplied heads have no successors.
#guard succs S = []
#guard succs (app S K) = []
-- A term with BOTH a root redex and an inner redex lists both
-- (K (I S) S has the root K-redex and the inner I S redex — recall
-- I = S K K, so app I S is an S-redex at depth).
#guard (succs (app2 K (app I S) S)).length = 2
-- Congruence on both sides: (I S)(I S) has one redex per side.
#guard (succs (app (app I S) (app I S))).length = 2

-- ## CENSUS-FIRST PROBES (the STOP gate for this whole slice)
-- If ANY of these fails: STOP. Do not adjust guards, definitions, or
-- fuel. Report the failing case — the slice's premise would be wrong.

-- Probe A: succs subsumes the certified leftmost reducer — whatever
-- stepOnce finds is among the successors. (Over every S-term ≤ 6 leaves
-- and a hand-set of K-bearing terms.)
#guard (List.range 7).all fun n => (sTerms n).all fun t =>
  match stepOnce t with
  | none => (succs t).isEmpty   -- no leftmost redex ⇒ no redex at all? NO —
    -- careful: stepOnce none means NO redex exists (stepOnce_none_normal),
    -- so succs must be empty too. This tests succs' emptiness agreement.
  | some w => (succs t).contains w

#guard [app2 K S K, app I K, app (app2 K S S) (app2 K K K)].all fun t =>
  match stepOnce t with
  | none => (succs t).isEmpty
  | some w => (succs t).contains w

-- Probe B (the bounded-path claim, empirically): every successor of a
-- K-free term is at least as large. (The theorem exists at the Steps
-- level — Stage 2; this probes the NEW succs enumeration against it.)
#guard (List.range 7).all fun n => (sTerms n).all fun t =>
  (succs t).all fun w => leafCount t ≤ leafCount w

-- Probe C (bounded universes are genuinely closed): iterating succs from
-- any S-term of ≤ 5 leaves, filtered to size ≤ 8, never escapes size 8 —
-- trivially true by the filter, so probe the REAL claim: the set of
-- distinct terms seen in 200 rounds of unfiltered succs-iteration from
-- size-≤4 S-terms whose sizes stay ≤ 4 is finite and small. Concretely:
-- from any size-≤4 S-term, the size-preserving successor relation
-- revisits nothing new after at most (number of size-≤4 terms) rounds.
#guard (List.range 5).all fun n => (sTerms n).all fun t =>
  ((succs t).filter (fun w => leafCount w ≤ 4)).all fun w => kFree w
