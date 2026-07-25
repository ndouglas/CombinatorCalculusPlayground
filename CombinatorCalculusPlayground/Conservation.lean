--! # C5: conservation for pure S — WN ⇒ SN, PROVED HERE
-- C5 has been labelled **external** since Stage 5 Slice 3, on the grounds that it is the
-- λI conservation theorem (Church 1941; Barendregt §9.5) and that formalizing it means
-- importing classical λI machinery. Stage 31 finding: **that is wrong.** For pure S the
-- tree can prove it directly, from results it already has, and the argument is short:
--
--   Suppose `t` reaches a normal form `n`, and also admits an infinite reduction
--   `t → t₁ → t₂ → …`.
--     * CONFLUENCE (Stage 1) makes every `tᵢ` reach `n`, since `n` is normal.
--     * MONOTONICITY (Stage 2) then bounds `leafCount tᵢ ≤ leafCount n`.
--     * ENUMERATION COMPLETENESS (Stage 6, `enum_complete`) puts every `tᵢ` in ONE
--       FINITE list.
--     * PIGEONHOLE forces `tᵢ = tⱼ` for some `i < j`.
--     * ACYCLICITY (C2, `no_pure_S_cycle`) forbids that.
--
-- Every ingredient was already here; only the pigeonhole was missing. So C5 is a
-- THEOREM of this development rather than an import — which also means the loop route to
-- C1(a) no longer waits on external work.
import CombinatorCalculusPlayground.Decidability
import CombinatorCalculusPlayground.Isometric

open Term

-- ## The pigeonhole, in the constructive form the proof needs
-- Core 4.28 has `List.erase` lemmas that would do this directly — but they require
-- `LawfulBEq`, and synthesising that from `DecidableEq` drags in `Classical.choice`
-- (measured: both `List.length_erase_of_mem` and `List.mem_erase_of_ne` report it). Same
-- instance-layer trap as Stage 9. Rebuilt on `List.filter` with `decide`, which avoids
-- `BEq` entirely, plus one length lemma of our own.

/-- Filtering out a witness strictly shortens the list. -/
theorem length_filter_lt {α : Type} {q : α → Bool} :
    ∀ {L : List α} {x : α}, x ∈ L → q x = false → (L.filter q).length < L.length
  | [], x, hx, _ => by simp at hx
  | a :: t, x, hx, hqx => by
    by_cases hqa : q a = true
    · rw [List.filter_cons_of_pos hqa]
      have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with rfl | h
        · rw [hqx] at hqa; exact absurd hqa (by simp)
        · exact h
      have := length_filter_lt hxt hqx
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_neg (by simpa using hqa)]
      have := List.length_filter_le q t
      simp only [List.length_cons]
      omega

/-- A map into `L` that is injective on `0..n` forces `n < L.length`. -/
theorem lt_length_of_inj_on {α : Type} [DecidableEq α] (f : Nat → α) :
    ∀ (n : Nat) (L : List α), (∀ i, i ≤ n → f i ∈ L) →
      (∀ i j, i ≤ n → j ≤ n → f i = f j → i = j) → n < L.length
  | 0, L, hf, _ => List.length_pos_of_mem (hf 0 (Nat.le_refl _))
  | n + 1, L, hf, hinj => by
    -- filter out the value at n+1; every earlier value survives, and the list shortens
    have hmem : f (n + 1) ∈ L := hf (n + 1) (Nat.le_refl _)
    have hqbad : (fun x => decide (x ≠ f (n + 1))) (f (n + 1)) = false := by simp
    have hf' : ∀ i, i ≤ n → f i ∈ L.filter (fun x => decide (x ≠ f (n + 1))) := by
      intro i hi
      have hne : f i ≠ f (n + 1) := by
        intro heq
        have := hinj i (n + 1) (by omega) (Nat.le_refl _) heq
        omega
      exact List.mem_filter.mpr ⟨hf i (by omega), by simpa using hne⟩
    have hinj' : ∀ i j, i ≤ n → j ≤ n → f i = f j → i = j :=
      fun i j hi hj => hinj i j (by omega) (by omega)
    have hrec := lt_length_of_inj_on f n
      (L.filter (fun x => decide (x ≠ f (n + 1)))) hf' hinj'
    have := length_filter_lt (q := fun x => decide (x ≠ f (n + 1))) hmem hqbad
    omega

/-- **Pigeonhole.** A map from `Nat` into a finite list cannot be injective. Stated
negatively, which is the constructive form and exactly what the conservation proof
consumes — no classical step is needed to turn it into an existential. -/
theorem not_injective_into_list {α : Type} [DecidableEq α] (L : List α) (f : Nat → α)
    (hf : ∀ i, f i ∈ L) : ¬ (∀ i j, i < j → f i ≠ f j) := by
  intro hinj
  have hinj' : ∀ i j, i ≤ L.length → j ≤ L.length → f i = f j → i = j := by
    intro i j _ _ heq
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd heq (hinj i j h)
    · exact h
    · exact absurd heq.symm (hinj j i h)
  have := lt_length_of_inj_on f L.length L (fun i _ => hf i) hinj'
  omega

-- ## Infinite reductions

/-- An infinite reduction sequence out of `t`. -/
def InfiniteRed (t : Term) : Prop :=
  ∃ f : Nat → Term, f 0 = t ∧ ∀ i, f i ⟶ f (i + 1)

/-- Every element of such a sequence is reachable from the one before it, hence from any
earlier one. -/
theorem infRed_steps {f : Nat → Term} (hf : ∀ i, f i ⟶ f (i + 1)) :
    ∀ i j, i ≤ j → f i ⟶* f j := by
  intro i j hij
  induction j with
  | zero => have : i = 0 := by omega
            exact this ▸ Steps.refl _
  | succ k ih =>
    by_cases h : i ≤ k
    · exact Steps.trans (ih h) (Steps.single (hf k))
    · have : i = k + 1 := by omega
      exact this ▸ Steps.refl _

-- ## C5

/-- **C5 — conservation for pure S, PROVED.** A K-free term that reaches a normal form
admits no infinite reduction. Equivalently, on the pure-S fragment weak normalization
implies strong normalization.

The five ingredients are Stage 1 confluence, Stage 2 monotonicity, Stage 6 enumeration
completeness, the pigeonhole above, and C2's acyclicity. -/
theorem conservation {t : Term} (hk : KFree t)
    (hwn : ∃ n, (t ⟶* n) ∧ NormalForm n) : ¬ InfiniteRed t := by
  rintro ⟨f, hf0, hf⟩
  obtain ⟨n, hn, hnf⟩ := hwn
  -- every element of the sequence is reachable from t
  have hreach : ∀ i, t ⟶* f i := by
    intro i
    rw [← hf0]
    exact infRed_steps hf 0 i (Nat.zero_le _)
  -- ...hence K-free, and — by confluence with a NORMAL target — reaches n
  have hkf : ∀ i, KFree (f i) := fun i => hk.of_steps (hreach i)
  have hton : ∀ i, f i ⟶* n := by
    intro i
    obtain ⟨w, hw1, hw2⟩ := confluence (hreach i) hn
    exact (hnf.steps_eq hw2) ▸ hw1
  -- ...so all of them live in one finite list
  have hsmall : ∀ i, f i ∈ smallTerms (leafCount n) := by
    intro i
    exact mem_smallTerms (hkf i) (leafCount_le_of_steps (hkf i) (hton i))
  -- a repeat would be a cycle, which C2 forbids
  have hnorep : ∀ i j, i < j → f i ≠ f j := by
    intro i j hij heq
    refine no_pure_S_cycle (hkf i) ⟨f (i + 1), hf i, ?_⟩
    exact heq ▸ infRed_steps hf (i + 1) j (by omega)
  exact not_injective_into_list _ f hsmall hnorep

/-- The contrapositive, in the shape the C1(a) loop route wants: a term with an infinite
reduction has NO normal form. So exhibiting an infinite reduction sequence is now enough
to prove non-normalization for pure S. -/
theorem no_normalForm_of_infiniteRed {t : Term} (hk : KFree t) (h : InfiniteRed t) :
    ¬ ∃ n, (t ⟶* n) ∧ NormalForm n :=
  fun hwn => conservation hk hwn h

/-- And the self-embedding form. If `t` reduces to a term properly containing a copy of
`t`... this is the shape a divergence witness would take; the missing piece is turning a
self-embedding into an infinite sequence, which needs the context to be reduction-stable.
Recorded as the interface, not yet inhabited. -/
theorem conservation_apply {t : Term} (hk : KFree t) (h : InfiniteRed t) :
    ∀ n, NormalForm n → ¬ (t ⟶* n) :=
  fun n hnf hsteps => no_normalForm_of_infiniteRed hk h ⟨n, hsteps, hnf⟩
