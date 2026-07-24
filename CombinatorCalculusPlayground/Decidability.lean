--! # Goal 3: reachability between pure S-terms is decidable
-- The design spec's north star (Goal 3) is: is `t ⟶* u` between pure
-- S-terms decidable? Slice 1 answered it PER INSTANCE — `reachable?` with
-- `reachable?_correct` gives a theorem-backed verdict whenever it returns
-- `some` — and left one gap: nothing proved that enough fuel always makes
-- the closure saturate, so `none` remained possible for every fuel and the
-- abstract statement stayed out of reach.
--
-- That gap needed exactly one ingredient: the finiteness of the bounded
-- term universe. Slice 5's `enum_complete` supplies it. The argument is a
-- pigeonhole with an explicit measure: every term the closure adds is
-- K-free (Stage 2's `KFree.of_step`) with leaf count under the bound, so it
-- lives in the finite list `smallTerms bound`; the count of `smallTerms`
-- members NOT yet collected strictly drops each round; a Nat cannot drop
-- forever.
--
-- HONEST FRAMING, and it belongs at the top: on paper this is
-- folklore-adjacent. "Monotone size implies bounded search" is two lines
-- given Stage 2 monotonicity, and the rewriting literature may well have
-- it. What is claimed here is the machine-checked version — the decision
-- procedure, its certificates, and the saturation bound that makes the
-- abstract statement true rather than fuel-dependent.
import CombinatorCalculusPlayground.Reachability

open Term

-- ## Two generic list lemmas
-- Neither is in core 4.28 in the form needed, and both are about filtering
-- ONE list by two comparable predicates.

/-- Weakening the predicate cannot shrink a filter. -/
theorem length_filter_le_of_imp {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ a ∈ l, q a = true → p a = true) :
    (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun b hb => hpq b (List.mem_cons_of_mem _ hb))
    by_cases hq : q a = true
    · have hp : p a = true := hpq a List.mem_cons_self hq
      rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hp]
      simpa using ih'
    · rw [List.filter_cons_of_neg (by simpa using hq)]
      by_cases hp : p a = true
      · rw [List.filter_cons_of_pos hp]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg (by simpa using hp)]
        exact ih'

/-- ...and if one element is kept by `p` but dropped by `q`, the filter
strictly shrinks. This is the pigeonhole step. -/
theorem length_filter_lt_of_witness {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ a ∈ l, q a = true → p a = true)
    {x : α} (hx : x ∈ l) (hpx : p x = true) (hqx : q x = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    have hpq' : ∀ b ∈ t, q b = true → p b = true :=
      fun b hb => hpq b (List.mem_cons_of_mem _ hb)
    by_cases hq : q a = true
    · -- a is kept by both; the witness must be in the tail (q x = false)
      have hp : p a = true := hpq a List.mem_cons_self hq
      have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with rfl | h
        · rw [hqx] at hq; exact absurd hq (by simp)
        · exact h
      rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos hp]
      simp only [List.length_cons]
      have := ih hpq' hxt
      omega
    · rw [List.filter_cons_of_neg (by simpa using hq)]
      by_cases hp : p a = true
      · -- a is dropped by q, kept by p: one slot gained outright
        rw [List.filter_cons_of_pos hp]
        simp only [List.length_cons]
        have := length_filter_le_of_imp hpq'
        omega
      · -- both drop a; witness is in the tail (p x = true, p a = false)
        have hxt : x ∈ t := by
          rcases List.mem_cons.mp hx with rfl | h
          · exact absurd hpx (by simpa using hp)
          · exact h
        rw [List.filter_cons_of_neg (by simpa using hp)]
        exact ih hpq' hxt

-- ## The finite universe
-- Every K-free term inside the size bound, as one explicit list. This is
-- what `enum_complete` buys: the census's enumeration is now known to MISS
-- NOTHING, so a list can stand in for the whole (infinite) type.

def smallTerms (bound : Nat) : List Term :=
  (List.range (bound + 1)).flatMap enumAt

theorem mem_smallTerms {t : Term} {bound : Nat}
    (hk : KFree t) (h : leafCount t ≤ bound) : t ∈ smallTerms bound :=
  List.mem_flatMap.mpr
    ⟨leafCount t, List.mem_range.mpr (by omega), mem_enumAt_iff.mpr ⟨hk, rfl⟩⟩

#guard (smallTerms 4).length = 1 + 1 + 2 + 5
#guard (smallTerms 6).contains (app3 S S S S)

-- ## The measure
-- How much of the bounded universe the closure has NOT yet collected.

def deficit (bound : Nat) (acc : List Term) : Nat :=
  ((smallTerms bound).filter (fun w => !acc.contains w)).length

/-- The pigeonhole step: a non-empty frontier strictly reduces the deficit.
Every frontier element is K-free (its source is, and `KFree.of_step`
closes), within bound (the filter enforces it), and absent from `acc` (same
filter) — so it is a `smallTerms` member that was uncollected and now is
collected. -/
theorem deficit_lt {bound : Nat} {acc : List Term}
    (hkacc : ∀ v ∈ acc, KFree v)
    (hne : closureStep bound acc ≠ []) :
    deficit bound (acc ++ (closureStep bound acc).eraseDups)
      < deficit bound acc := by
  -- Pick the witness from the DEDUPED frontier, so that landing it in the
  -- extended accumulator is immediate. Core 4.28 has only one direction of
  -- eraseDups membership (`mem_of_mem_eraseDups`, Reachability.lean); taking
  -- the head via `eraseDups_cons` avoids needing the other.
  obtain ⟨x, hxd⟩ : ∃ x, x ∈ (closureStep bound acc).eraseDups := by
    cases hcs : closureStep bound acc with
    | nil => exact absurd hcs hne
    | cons a _ =>
      refine ⟨a, ?_⟩
      rw [List.eraseDups_cons]
      exact List.mem_cons_self
  have hx : x ∈ closureStep bound acc := mem_of_mem_eraseDups hxd
  obtain ⟨⟨v, hv, hvx⟩, hle, hnotin⟩ := mem_closureStep hx
  have hkx : KFree x := (hkacc v hv).of_step (succs_sound hvx)
  refine length_filter_lt_of_witness (l := smallTerms bound) ?_
    (mem_smallTerms hkx hle) (by simpa using hnotin) ?_
  · -- absent from the LONGER accumulator implies absent from `acc`
    intro a _ ha
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.mem_append] at ha ⊢
    exact fun hmem => ha (Or.inl hmem)
  · -- x IS in the longer accumulator, via the deduped frontier
    simp only [List.contains_eq_mem, Bool.not_eq_false', decide_eq_true_eq,
      List.mem_append]
    exact Or.inr hxd

-- ## Saturation always happens
theorem boundedClosure_isSome_of_deficit_le {bound : Nat} :
    ∀ (fuel : Nat) (acc : List Term), (∀ v ∈ acc, KFree v) →
      deficit bound acc ≤ fuel → (boundedClosure bound fuel acc).isSome := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc hkacc hdef
    -- deficit 0 forces an empty frontier: a frontier element would be an
    -- uncollected `smallTerms` member, contributing at least 1.
    have hempty : closureStep bound acc = [] := by
      cases hcs : closureStep bound acc with
      | nil => rfl
      | cons a rest =>
        exfalso
        have hx : a ∈ closureStep bound acc := by rw [hcs]; exact List.mem_cons_self
        obtain ⟨⟨v, hv, hva⟩, hle, hnotin⟩ := mem_closureStep hx
        have hka : KFree a := (hkacc v hv).of_step (succs_sound hva)
        have : a ∈ (smallTerms bound).filter (fun w => !acc.contains w) :=
          List.mem_filter.mpr ⟨mem_smallTerms hka hle, by simpa using hnotin⟩
        have := List.length_pos_of_mem this
        unfold deficit at hdef
        omega
    unfold boundedClosure
    rw [hempty]
    simp
  | succ f ih =>
    intro acc hkacc hdef
    unfold boundedClosure
    by_cases hcs : (closureStep bound acc).isEmpty = true
    · simp [hcs]
    · have hne : closureStep bound acc ≠ [] := by
        intro h; rw [h] at hcs; simp at hcs
      simp only [hcs, if_false, Bool.false_eq_true]
      refine ih _ ?_ ?_
      · -- K-freeness is preserved by the extension
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hkacc w hw
        · obtain ⟨⟨v, hv, hvw⟩, _, _⟩ := mem_closureStep (mem_of_mem_eraseDups hw)
          exact (hkacc v hv).of_step (succs_sound hvw)
      · have := deficit_lt hkacc hne
        omega

/-- Enough fuel always exists: the deficit of the start set is enough. -/
theorem boundedClosure_isSome {bound : Nat} {acc : List Term}
    (hkacc : ∀ v ∈ acc, KFree v) :
    (boundedClosure bound (deficit bound acc) acc).isSome :=
  boundedClosure_isSome_of_deficit_le _ acc hkacc (Nat.le_refl _)

-- ## Goal 3, answered
-- `reachable?` at the computed fuel never returns `none`, so its verdict is
-- always available — and `reachable?_correct` says the verdict is right.

/-- The fuel that provably suffices for `t ⟶* u`. -/
def reachFuel (t u : Term) : Nat := deficit (leafCount u) [t]

theorem reachable?_isSome {t u : Term} (hk : KFree t) :
    (reachable? t u (reachFuel t u)).isSome := by
  unfold reachable? reachFuel
  cases h : boundedClosure (leafCount u) (deficit (leafCount u) [t]) [t] with
  | some _ => simp
  | none =>
    exfalso
    have := boundedClosure_isSome (bound := leafCount u) (acc := [t])
      (fun v hv => by simp at hv; subst hv; exact hk)
    rw [h] at this
    simp at this

/-- **Spec Goal 3 — reachability between pure S-terms is DECIDABLE.**
For K-free `t`, the certified procedure always produces a verdict, and the
verdict is correct. Stated as a `Decidable` value so it can be used as one. -/
def stepsDecidable {t u : Term} (hk : KFree t) : Decidable (t ⟶* u) := by
  have hsome := reachable?_isSome (u := u) hk
  cases h : reachable? t u (reachFuel t u) with
  | none => rw [h] at hsome; simp at hsome
  | some b =>
    cases b with
    | true => exact isTrue ((reachable?_correct hk h).mp rfl)
    | false =>
      refine isFalse (fun hsteps => ?_)
      have := (reachable?_correct hk h).mpr hsteps
      simp at this

/-- The same fact in plain propositional form, for citation. -/
theorem steps_decidable_of_kFree {t u : Term} (hk : KFree t) :
    (t ⟶* u) ∨ ¬ (t ⟶* u) :=
  match stepsDecidable (u := u) hk with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

-- ## The computed bound is not vacuous
-- Every example Slice 1 checked by hand-picked fuel also verdicts at the
-- PROVED fuel, so the bound is usable and not merely finite.
#guard (reachable? (app3 S S S S) (app (app S S) (app S S))
  (reachFuel (app3 S S S S) (app (app S S) (app S S)))) = some true
#guard (reachable? (app (app S S) (app S S)) (app3 S S S S)
  (reachFuel (app (app S S) (app S S)) (app3 S S S S))) = some false
#guard (reachable? (app S S) (app S S) (reachFuel (app S S) (app S S)))
  = some true
#guard (reachable? (app3 S S S S) (app S (app S S))
  (reachFuel (app3 S S S S) (app S (app S S)))) = some false
