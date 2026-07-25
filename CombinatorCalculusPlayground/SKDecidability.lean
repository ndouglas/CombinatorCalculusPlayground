--! # Closure saturation without K-freeness
-- `Decidability.lean` proves that a size-bounded closure always saturates, by a deficit argument against
-- the finite universe `smallTerms`. Every one of its K-freeness hypotheses exists for a single purpose:
-- to place a frontier element in `smallTerms` via `mem_smallTerms`, which demands it.
--
-- Stage 57 built `skSmallTerms`, whose membership lemma demands only a size bound. So the hypotheses have
-- nothing left to do, and they disappear — not weakened, not worked around, gone. What is left is the same
-- pigeonhole with a bigger universe.
import CombinatorCalculusPlayground.Decidability
import CombinatorCalculusPlayground.Census.SKComplete

open Term

/-- How much of the bounded SK universe the closure has not yet collected. -/
def skDeficit (bound : Nat) (acc : List Term) : Nat :=
  ((skSmallTerms bound).filter (fun w => !acc.contains w)).length

/-- The pigeonhole step, with no side condition on `acc`: a non-empty frontier strictly reduces the
deficit. A frontier element is within bound (the filter enforces it) and absent from `acc` (same filter),
and that is now the whole requirement. -/
theorem skDeficit_lt {bound : Nat} {acc : List Term}
    (hne : closureStep bound acc ≠ []) :
    skDeficit bound (acc ++ (closureStep bound acc).eraseDups) < skDeficit bound acc := by
  obtain ⟨x, hxd⟩ : ∃ x, x ∈ (closureStep bound acc).eraseDups := by
    cases hcs : closureStep bound acc with
    | nil => exact absurd hcs hne
    | cons a _ =>
      refine ⟨a, ?_⟩
      rw [List.eraseDups_cons]
      exact List.mem_cons_self
  have hx : x ∈ closureStep bound acc := mem_of_mem_eraseDups hxd
  obtain ⟨⟨v, hv, hvx⟩, hle, hnotin⟩ := mem_closureStep hx
  refine length_filter_lt_of_witness (l := skSmallTerms bound) ?_
    (mem_skSmallTerms hle) (by simpa using hnotin) ?_
  · intro a _ ha
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.mem_append] at ha ⊢
    exact fun hmem => ha (Or.inl hmem)
  · simp only [List.contains_eq_mem, Bool.not_eq_false', decide_eq_true_eq,
      List.mem_append]
    exact Or.inr hxd

theorem skBoundedClosure_isSome_of_deficit_le {bound : Nat} :
    ∀ (fuel : Nat) (acc : List Term),
      skDeficit bound acc ≤ fuel → (boundedClosure bound fuel acc).isSome := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc hdef
    have hempty : closureStep bound acc = [] := by
      cases hcs : closureStep bound acc with
      | nil => rfl
      | cons a rest =>
        exfalso
        have hx : a ∈ closureStep bound acc := by rw [hcs]; exact List.mem_cons_self
        obtain ⟨⟨v, hv, hva⟩, hle, hnotin⟩ := mem_closureStep hx
        have : a ∈ (skSmallTerms bound).filter (fun w => !acc.contains w) :=
          List.mem_filter.mpr ⟨mem_skSmallTerms hle, by simpa using hnotin⟩
        have := List.length_pos_of_mem this
        unfold skDeficit at hdef
        omega
    unfold boundedClosure
    rw [hempty]
    simp
  | succ f ih =>
    intro acc hdef
    unfold boundedClosure
    by_cases hcs : (closureStep bound acc).isEmpty = true
    · simp [hcs]
    · have hne : closureStep bound acc ≠ [] := by
        intro h; rw [h] at hcs; simp at hcs
      simp only [hcs, if_false, Bool.false_eq_true]
      refine ih _ ?_
      have := skDeficit_lt (bound := bound) (acc := acc) hne
      omega

/-- **A size-bounded closure always saturates, for ANY start set.** The K-free version
(`boundedClosure_isSome`) is the special case. -/
theorem skBoundedClosure_isSome {bound : Nat} {acc : List Term} :
    (boundedClosure bound (skDeficit bound acc) acc).isSome :=
  skBoundedClosure_isSome_of_deficit_le _ acc (Nat.le_refl _)

-- ## Decidable reachability inside a size-bounded region
-- Saturation plus the two existing correctness lemmas give a decision procedure whenever the start term's
-- reducts are known to stay within the bound. `boundedClosure_sound` says members are reachable;
-- `mem_of_saturated` says a saturated closure has everything reachable that stays in bound.

/-- Reachability, decided within an explicit size bound. -/
def reachableWithin (bound : Nat) (t u : Term) : Bool :=
  match boundedClosure bound (skDeficit bound [t]) [t] with
  | none => false
  | some acc => acc.contains u

/-- `mem_of_saturated` without K-freeness. Its K-freeness hypothesis is genuinely load-bearing — it bounds
an INTERMEDIATE by `leafCount_le_of_steps`, and with `K` in play leaf count can rise and fall, so an
intermediate may exceed both endpoints. The fix is not to remove the hypothesis but to replace it with what
is actually needed: a bound on the whole REGION, which travels along the path because a reduct of a reduct
is a reduct. -/
theorem mem_of_saturated_region {acc : List Term} {bound : Nat}
    (hsat : ∀ w ∈ acc, ∀ v ∈ succs w, leafCount v ≤ bound → v ∈ acc) :
    ∀ {t u : Term}, (t ⟶* u) → (∀ v, (t ⟶* v) → leafCount v ≤ bound) → t ∈ acc → u ∈ acc := by
  intro t u h
  induction h with
  | refl => exact fun _ ht => ht
  | @tail t t1 u s _ ih =>
      intro hreg ht
      have ht1 : t1 ∈ acc := hsat _ ht _ (succs_complete s) (hreg t1 (Steps.single s))
      exact ih (fun v hv => hreg v ((Steps.single s).trans hv)) ht1

/-- **Bounded-region reachability is decidable for full SK.** No K-freeness anywhere: the only hypothesis is
that every reduct of `t` stays within the bound, which is what makes the region finite in the first place. -/
theorem reachableWithin_correct {bound : Nat} {t u : Term}
    (hreg : ∀ v, (t ⟶* v) → leafCount v ≤ bound) :
    reachableWithin bound t u = true ↔ (t ⟶* u) := by
  unfold reachableWithin
  cases hbc : boundedClosure bound (skDeficit bound [t]) [t] with
  | none =>
      exact absurd (hbc ▸ (skBoundedClosure_isSome (bound := bound) (acc := [t]))) (by simp)
  | some acc =>
      have hstart : ∀ w ∈ [t], t ⟶* w := by
        intro w hw; simp at hw; subst hw; exact Steps.refl _
      constructor
      · intro hc
        exact boundedClosure_sound hstart hbc u (by simpa using hc)
      · intro hsteps
        have ht : t ∈ acc := boundedClosure_subset hbc t (by simp)
        have := mem_of_saturated_region (boundedClosure_saturated hbc) hsteps hreg ht
        simpa using this

/-- Decidability as a `Decidable` value, so it can be used as one. -/
def stepsDecidableWithin {bound : Nat} {t u : Term}
    (hreg : ∀ v, (t ⟶* v) → leafCount v ≤ bound) : Decidable (t ⟶* u) := by
  cases h : reachableWithin bound t u with
  | true => exact isTrue ((reachableWithin_correct hreg).mp h)
  | false =>
      refine isFalse (fun hs => ?_)
      have := (reachableWithin_correct (u := u) hreg).mpr hs
      rw [h] at this
      simp at this

-- ## Least witness, without `Nat.find`
-- `Nat.find` is Mathlib's, not core's, so the extraction is done by hand: walk up from zero carrying the
-- invariant that nothing below has satisfied the predicate yet. Decidability is what lets the walk branch.

theorem exists_least_from {p : Nat → Prop} [DecidablePred p] :
    ∀ (fuel start : Nat), (∀ k, k < start → ¬ p k) → p (start + fuel) →
      ∃ m, m ≤ start + fuel ∧ p m ∧ ∀ k, k < m → ¬ p k := by
  intro fuel
  induction fuel with
  | zero => intro start hlow hp; exact ⟨start, by omega, by simpa using hp, hlow⟩
  | succ f ih =>
      intro start hlow hp
      by_cases hs : p start
      · exact ⟨start, by omega, hs, hlow⟩
      · have hlow' : ∀ k, k < start + 1 → ¬ p k := by
          intro k hk
          rcases Nat.lt_or_ge k start with h1 | h1
          · exact hlow k h1
          · have hks : k = start := by omega
            exact hks ▸ hs
        have hp' : p (start + 1 + f) := by
          have he : start + 1 + f = start + (f + 1) := by omega
          rw [he]; exact hp
        obtain ⟨m, hm1, hm2, hm3⟩ := ih (start + 1) hlow' hp'
        exact ⟨m, by omega, hm2, hm3⟩

/-- The least witness at or below a known one, for any decidable predicate on `Nat`. -/
theorem exists_least {p : Nat → Prop} [DecidablePred p] {w : Nat} (h : p w) :
    ∃ m, m ≤ w ∧ p m ∧ ∀ k, k < m → ¬ p k := by
  have hres := exists_least_from (p := p) w 0
    (fun k hk => absurd hk (Nat.not_lt_zero k)) (by simpa using h)
  simpa using hres

-- ## What this widens
-- Goal 3's decidability layer was pure-S-only in four places: `enumAt`, `smallTerms`, `deficit` and
-- `boundedClosure_isSome`. Stage 57 widened the first two and this file widens the other two. None of the
-- four restrictions was structural; all were inherited from the census, which needed pure S for good
-- reasons that never applied to the enumeration machinery itself.
--
-- The immediate consumer is route two's chain, which needs reachability from `Itower m` to be decidable and
-- has the size bound (`itower_reduct_bound`) to supply the region. The general statement is worth having on
-- its own: **bounded-region reachability is decidable for full SK**, which is not in tension with anything —
-- SK reachability is undecidable only because the region cannot be bounded in advance.
