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

-- Probe C (one-step K-freeness closure at the succs level): the
-- size-bounded successors of small S-terms are themselves K-free. This
-- checks ONE step only — the multi-step closure claim is what Task 3's
-- boundedClosure + Stage 2's KFree.of_step deliver as theorems; this
-- probe just confirms the new succs enumeration cooperates with them.
#guard (List.range 5).all fun n => (sTerms n).all fun t =>
  ((succs t).filter (fun w => leafCount w ≤ 4)).all fun w => kFree w

-- ## succs is exactly the step relation
theorem rootRed_sound : ∀ {t w : Term}, w ∈ rootRed t → t ⟶ w := by
  intro t w h
  unfold rootRed at h
  split at h
  · simp at h; subst h; exact Step.K_red ..
  · simp at h; subst h; exact Step.S_red ..
  · simp at h

theorem succs_sound : ∀ {t w : Term}, w ∈ succs t → t ⟶ w := by
  intro t
  induction t with
  | S => intro w h; simp [succs] at h
  | K => intro w h; simp [succs] at h
  | app a b iha ihb =>
    intro w h
    simp [succs] at h
    rcases h with hroot | ⟨t', ht', rfl⟩ | ⟨u', hu', rfl⟩
    · exact rootRed_sound (by simpa using hroot)
    · exact Step.appL (iha ht')
    · exact Step.appR (ihb hu')

theorem succs_complete : ∀ {t w : Term}, t ⟶ w → w ∈ succs t := by
  intro t w h
  induction h with
  | K_red x y =>
    simp [succs, rootRed, app2]
  | S_red f g x =>
    simp [succs, rootRed, app3]
  | @appL t t' u s ih =>
    simp only [succs]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨t', ih, rfl⟩))))
  | @appR t u u' s ih =>
    simp only [succs]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨u', ih, rfl⟩))

-- ## The saturating bounded closure
-- Grow the reachable set one frontier at a time, keeping only terms
-- within the size bound. `some acc` means the frontier came back empty —
-- the set is SATURATED (closed under bounded steps); `none` means fuel
-- ran out first, which verdicts NOTHING.
def closureStep (bound : Nat) (acc : List Term) : List Term :=
  (acc.flatMap succs).filter (fun w => leafCount w ≤ bound && !acc.contains w)

def boundedClosure (bound : Nat) : Nat → List Term → Option (List Term)
  | 0, acc => if (closureStep bound acc).isEmpty then some acc else none
  | f + 1, acc =>
    let next := closureStep bound acc
    if next.isEmpty then some acc
    else boundedClosure bound f (acc ++ next.eraseDups)

/-- Certified-when-`some` reachability check: is u reachable from t?
`none` = fuel exhausted (no verdict). Sound and complete for K-free t
via `reachable?_correct`. -/
def reachable? (t u : Term) (fuel : Nat) : Option Bool :=
  (boundedClosure (leafCount u) fuel [t]).map (fun acc => acc.contains u)

-- S S S S → (S S)(S S): reachable, and the closure saturates fast.
#guard reachable? (app3 S S S S) (app (app S S) (app S S)) 50 = some true
-- Not reachable the other way (sizes equal, but no backward step).
#guard reachable? (app (app S S) (app S S)) (app3 S S S S) 50 = some false
-- Self-reachability (zero steps).
#guard reachable? (app S S) (app S S) 10 = some true
-- Size forbids: a 4-leaf term cannot reach a 3-leaf one; the closure over
-- bound 3 saturates instantly and answers false.
#guard reachable? (app3 S S S S) (app S (app S S)) 10 = some false
-- Fuel 0 on a non-saturated instance is an honest none: S S S S has a
-- bounded successor ((S S)(S S)), so the frontier is non-empty and fuel
-- 0 cannot saturate — the very same instance verdicts `some true` once it
-- is given a single round of fuel (the first guard above).
#guard reachable? (app3 S S S S) (app (app S S) (app S S)) 0 = none

-- Membership in a closure step: it came from somewhere in acc.
theorem mem_closureStep {bound : Nat} {acc : List Term} {w : Term}
    (h : w ∈ closureStep bound acc) :
    (∃ v ∈ acc, w ∈ succs v) ∧ leafCount w ≤ bound ∧ w ∉ acc := by
  simp only [closureStep, List.mem_filter, List.mem_flatMap, Bool.and_eq_true,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

-- `eraseDups` only drops duplicates, so membership in it implies membership
-- in the original. (Core 4.28 has no `mem_eraseDups`; length recursion supplies
-- it — `eraseDups_cons` peels one head, filtering the tail, which shrinks.)
theorem mem_of_mem_eraseDups :
    ∀ {l : List Term} {a : Term}, a ∈ l.eraseDups → a ∈ l
  | [], a, h => by simp at h
  | x :: xs, a, h => by
    rw [List.eraseDups_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _
        ((List.mem_filter.mp (mem_of_mem_eraseDups h)).1)
  termination_by l => l.length
  decreasing_by
    simp_wf
    calc (xs.filter _).length ≤ xs.length := List.length_filter_le _ _
      _ < (x :: xs).length := by simp

-- Everything the closure collects is genuinely reachable from something
-- in the start set.
theorem boundedClosure_sound {bound fuel : Nat} {start acc : List Term} {t : Term}
    (hstart : ∀ w ∈ start, t ⟶* w)
    (h : boundedClosure bound fuel start = some acc) :
    ∀ w ∈ acc, t ⟶* w := by
  induction fuel generalizing start with
  | zero =>
    unfold boundedClosure at h
    split at h
    · injection h with h; subst h; exact hstart
    · exact absurd h (by simp)
  | succ f ih =>
    unfold boundedClosure at h
    simp only at h
    split at h
    · injection h with h; subst h; exact hstart
    · refine ih (start := start ++ (closureStep bound start).eraseDups) ?_ h
      intro w hw
      rw [List.mem_append] at hw
      rcases hw with hw | hw
      · exact hstart w hw
      · obtain ⟨⟨v, hv, hws⟩, _, _⟩ := mem_closureStep (mem_of_mem_eraseDups hw)
        exact (hstart v hv).trans (Steps.tail (succs_sound hws) (Steps.refl _))

-- The start set survives into the result.
theorem boundedClosure_subset {bound fuel : Nat} {start acc : List Term}
    (h : boundedClosure bound fuel start = some acc) :
    ∀ w ∈ start, w ∈ acc := by
  induction fuel generalizing start with
  | zero =>
    unfold boundedClosure at h
    split at h
    · injection h with h; subst h; exact fun w hw => hw
    · exact absurd h (by simp)
  | succ f ih =>
    unfold boundedClosure at h
    simp only at h
    split at h
    · injection h with h; subst h; exact fun w hw => hw
    · intro w hw
      exact ih h w (List.mem_append.mpr (Or.inl hw))

-- `some` really means saturated: bounded successors of members are members.
theorem boundedClosure_saturated {bound fuel : Nat} {start acc : List Term}
    (h : boundedClosure bound fuel start = some acc) :
    ∀ w ∈ acc, ∀ v ∈ succs w, leafCount v ≤ bound → v ∈ acc := by
  induction fuel generalizing start with
  | zero =>
    unfold boundedClosure at h
    split at h
    · rename_i hemp
      injection h with h; subst h
      intro w hw v hv hle
      by_cases hvin : v ∈ start
      · exact hvin
      · exfalso
        have : v ∈ closureStep bound start := by
          simp only [closureStep, List.mem_filter, List.mem_flatMap, Bool.and_eq_true,
            Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
            decide_eq_true_eq]
          exact ⟨⟨w, hw, hv⟩, hle, hvin⟩
        rw [List.isEmpty_iff] at hemp
        rw [hemp] at this
        exact List.not_mem_nil this
    · exact absurd h (by simp)
  | succ f ih =>
    unfold boundedClosure at h
    simp only at h
    split at h
    · rename_i hemp
      injection h with h; subst h
      intro w hw v hv hle
      by_cases hvin : v ∈ start
      · exact hvin
      · exfalso
        have : v ∈ closureStep bound start := by
          simp only [closureStep, List.mem_filter, List.mem_flatMap, Bool.and_eq_true,
            Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
            decide_eq_true_eq]
          exact ⟨⟨w, hw, hv⟩, hle, hvin⟩
        rw [List.isEmpty_iff] at hemp
        rw [hemp] at this
        exact List.not_mem_nil this
    · exact ih h
