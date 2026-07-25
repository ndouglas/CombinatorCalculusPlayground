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

-- ## Stage 32: what C1(a) still needs, reduced to spine arithmetic
-- C5 removed C1(a)'s external DEPENDENCY: `no_normalForm_of_infiniteRed` means an
-- infinite reduction sequence now suffices for non-normalization. What remains is purely
-- a REDUCIBILITY INVARIANT — a predicate `P` with `P c1` and `P t → ∃ u, t ⟶ u ∧ P u`,
-- from which the sequence is built by recursion. This section proves the two facts any
-- such invariant must be built from, and states precisely where they fall short.

/-- **For a K-free term, head spine ≥ 3 is enough to be reducible.** The only leaf is `S`,
so the head of any application chain is `S`, and three arguments fire it. This is the
reducibility half of what an invariant needs. -/
theorem reducible_of_head_spine : ∀ (t : Term), KFree t → 3 ≤ spineLength t → ∃ u, t ⟶ u := by
  intro t
  induction t with
  | S => intro _ h; simp [spineLength] at h
  | K => intro hk _; cases hk
  | app a b iha _ =>
    intro hk h
    cases hk with
    | app hka hkb =>
      simp only [spineLength] at h
      by_cases h3 : 3 ≤ spineLength a
      · obtain ⟨u, hu⟩ := iha hka h3
        exact ⟨_, Step.appL hu⟩
      · have ha2 : spineLength a = 2 := by omega
        cases a with
        | S => simp [spineLength] at ha2
        | K => cases hka
        | app a1 z =>
          simp only [spineLength] at ha2
          cases a1 with
          | S => simp [spineLength] at ha2
          | K => cases hka with | app h1 _ => cases h1
          | app w y =>
            simp only [spineLength] at ha2
            cases w with
            | S => exact ⟨_, Step.S_red y z b⟩
            | K =>
              cases hka with
              | app h1 _ => cases h1 with | app h2 _ => cases h2
            | app p q => simp [spineLength] at ha2

/-- **The spine arithmetic of an S-reduction.** Firing `S f g x` leaves a term of head
spine `spineLength f + 2`. So the reduct is again a head redex exactly when
`spineLength f ≥ 1` — and this is the preservation half of what an invariant needs. -/
theorem spineLength_S_red (f g x : Term) :
    spineLength (Term.app (.app f x) (.app g x)) = spineLength f + 2 := by
  simp [spineLength]

/-- The same redex fired one application deeper: head spine `spineLength f + 3`. In
general, `k` extra applications give `spineLength f + 2 + k`, so for a redex nested under
at least one extra argument the reduct always has spine ≥ 3. -/
theorem spineLength_S_red_appL (f g x y : Term) :
    spineLength (Term.app (.app (.app f x) (.app g x)) y) = spineLength f + 3 := by
  simp [spineLength]

-- ## Where this stops, stated precisely
-- Put together: for a K-free term, spine ≥ 3 gives reducibility, and firing a head redex
-- with `k` trailing arguments yields spine `spineLength f + 2 + k`. So:
--
--   * if `k ≥ 1` — the redex is nested under at least one further argument — the reduct
--     has spine ≥ 3 and is reducible again, unconditionally;
--   * if `k = 0` — the redex is the whole head — the reduct has spine
--     `spineLength f + 2`, which is ≥ 3 only when `spineLength f ≥ 1`.
--
-- So a reducibility invariant needs a lower bound on the FIRST ARGUMENT's spine in the
-- `k = 0` case, and nothing in this development bounds that below. Measured on `c1`: the
-- payload's spine along the frozen part of the trajectory runs
-- 3,4,4,3,3,4,4,3,5,6,6,5,5,8,8,7,9,10,10,9 — never below 3, so the invariant HOLDS
-- empirically, but the `k = 0`, `spineLength f = 0` case does occur and is exactly the
-- unproved step.
--
-- Two further negatives, both extending earlier hunts:
--   * `c1` does not reappear as a subterm of any reduct within 120 steps (Slice 3), and
--     no frozen reduct recurs within 20 starting points (Slice 4);
--   * the classic 14-leaf literature candidate `S A A (S A A)` with `A = S S S` does not
--     self-embed within 40 steps either, and its sizes grow steadily
--     (14, 20, 26, 35, 44, 53, 65, ...). So the self-embedding route has no witness at
--     the literature's own term, not just at ours.
--
-- C1(a) therefore stands as: dependency discharged (C5), reducibility criterion proved
-- (spine ≥ 3), preservation arithmetic proved, and ONE arithmetic gap remaining — a lower
-- bound on the first argument's spine when the redex sits at the head.

-- ## Stage 33: the size criterion — a better-matched target than an invariant
-- Stage 32 framed C1(a)'s remaining gap as "bound the first argument's spine in the k = 0
-- case". Checking that before attacking it shows the framing was wrong, and instructively:
-- `reducible_of_head_spine` is SUFFICIENT for reducibility but not NECESSARY. A term of
-- head spine 2 such as `(S x)(g x)` can still reduce inside. So demanding head spine ≥ 3
-- as an INVARIANT asks for more than reducibility needs, and the `k = 0` gap was an
-- artefact of that over-strong demand rather than a real obstacle.
--
-- The criterion below replaces it, needs no invariant at all, and matches what the census
-- actually measured.

/-- **Reducts of a normalizing term are size-bounded.** If `t` reaches a normal form `n`,
confluence sends every reduct of `t` to `n` as well, and monotonicity then caps its size.
(This is the step C5's proof used internally; extracted because it is the useful criterion
on its own.) -/
theorem leafCount_le_of_normalizes {t n u : Term} (hk : KFree t)
    (hn : t ⟶* n) (hnf : NormalForm n) (hu : t ⟶* u) : leafCount u ≤ leafCount n := by
  obtain ⟨w, hw1, hw2⟩ := confluence hu hn
  have hwn : w = n := hnf.steps_eq hw2
  subst hwn
  exact leafCount_le_of_steps (hk.of_steps hu) hw1

/-- **The size criterion for non-normalization.** A K-free term with reducts of unbounded
size has no normal form. No reducibility invariant is required — only arbitrarily large
reducts.

This is the criterion the census evidence actually fits: `c1` reaches 120112 leaves by step
200 and 25740409924 by fuel 1000 (CONJECTURES.md, C1). Unbounded growth is precisely what
was measured, whereas an invariant was never observed at all. -/
theorem no_normalForm_of_unbounded {t : Term} (hk : KFree t)
    (hub : ∀ N, ∃ u, (t ⟶* u) ∧ N < leafCount u) :
    ¬ ∃ n, (t ⟶* n) ∧ NormalForm n := by
  rintro ⟨n, hn, hnf⟩
  obtain ⟨u, hu, hlt⟩ := hub (leafCount n)
  have := leafCount_le_of_normalizes hk hn hnf hu
  omega

/-- Contrapositive, for reading the census the other way: a normalizing K-free term has a
size bound on its whole reduction graph. So the census's exploding sizes are not merely
suggestive — any bound on them would have been a normalization proof. -/
theorem bounded_of_normalizes {t : Term} (hk : KFree t)
    (h : ∃ n, (t ⟶* n) ∧ NormalForm n) :
    ∃ N, ∀ u, (t ⟶* u) → leafCount u ≤ N := by
  obtain ⟨n, hn, hnf⟩ := h
  exact ⟨leafCount n, fun u hu => leafCount_le_of_normalizes hk hn hnf hu⟩

-- ## C1(a)'s remaining gap, restated
-- With `no_normalForm_of_unbounded`, C1(a) needs exactly one thing: a K-free term whose
-- reducts have unbounded size. Three things are now true of that target that were not true
-- of the invariant target:
--
--   * it needs no preserved predicate — only a family of reducts, one above each bound;
--   * it is what the census measured, so the evidence and the goal finally agree;
--   * it is monotone in the evidence: every larger reduct found is progress toward it,
--     whereas invariant hunting produced nothing cumulative across Slices 3, 4 and 32.
--
-- What is still missing is a PROOF of unboundedness, which needs a growth step —
-- from any reduct, reach a strictly larger one — and that remains open. But the shape of
-- the missing lemma is now "reducts keep growing" rather than "some predicate is
-- preserved", and the former is the one the trajectory data speaks to.

-- ## Stage 34: growth is forced — the size criterion's other half
-- Stage 33 proved unbounded reducts imply non-normalization. The converse direction needs
-- the fact that a pure-S term which never grows must terminate, and that is exactly what
-- τ already gives: on a size plateau τ strictly drops (`tau_lt_of_isometric_step`), and a
-- Nat cannot drop forever.
--
-- Note the recursion is on `stepOnce`, not on a classical case split over `NormalForm`.
-- That keeps the proof constructive: `stepOnce` is computable and certified on both ends
-- (`stepOnce_sound`, `stepOnce_none_normal`), so "normal or reducible" is decided rather
-- than assumed.

/-- **A K-free term whose reducts never grow must normalize.** Strong induction on τ: each
step on a size plateau strictly drops τ, so the recursion is well-founded. -/
theorem normalizes_of_no_growth : ∀ (t : Term), KFree t →
    (∀ u, (t ⟶* u) → leafCount u = leafCount t) → ∃ n, (t ⟶* n) ∧ NormalForm n
  | t, hk, hng => by
    match hs : stepOnce t with
    | none => exact ⟨t, Steps.refl _, stepOnce_none_normal hs⟩
    | some u =>
      have hstep : t ⟶ u := stepOnce_sound hs
      have heq : leafCount t = leafCount u := (hng u (Steps.single hstep)).symm
      have hdrop : tau u < tau t := tau_lt_of_isometric_step hk hstep heq
      have hngu : ∀ v, (u ⟶* v) → leafCount v = leafCount u := by
        intro v hv
        rw [← heq]
        exact hng v (Steps.trans (Steps.single hstep) hv)
      obtain ⟨n, hn, hnf⟩ :=
        normalizes_of_no_growth u (hk.of_step hstep) hngu
      exact ⟨n, Steps.trans (Steps.single hstep) hn, hnf⟩
  termination_by t => tau t

-- ## The other direction: available classically, NOT shipped
-- The converse — "no normal form implies unbounded reducts" — completes the equivalence,
-- and it is three short proofs away. But getting it from a NEGATIVE hypothesis
-- (`¬ ∃ normal form`) to a POSITIVE conclusion (`∃ arbitrarily large reduct`) needs
-- `¬∀ → ∃`, which is not constructive: written the obvious way with `by_cases` on
-- `∃ u, t ⟶* u ∧ leafCount t < leafCount u`, all three theorems report
-- `Classical.choice`. Measured, then removed rather than shipped — this tree has advertised
-- "no Classical.choice" since Stage 0 and the equivalence is a nice-to-have, while the
-- direction that is actually a TOOL (`no_normalForm_of_unbounded`) is already choice-free.
--
-- THE CONSTRUCTIVE ROUTE, worked out and recorded for whoever wants it. Replace the
-- negative hypothesis by the positive one `∀ u, t ⟶* u → ∃ v, u ⟶ v` (every reduct is
-- reducible), which is what non-normalization is used for anyway. Then:
--
--   1. `stepOnce` is total on reducts (by `stepOnce_isSome_of_step`), so the trajectory
--      `f k := iterate stepOnce k t` is definable with `f k ⟶ f (k+1)` — no choice, since
--      `stepOnce` is computable.
--   2. Prove `leafCount (f k) = leafCount t → tau (f k) + k ≤ tau t` by induction on `k`.
--      Each step is on a size plateau (monotonicity squeezes the intermediates), so
--      `tau_lt_of_isometric_step` gives one unit of drop per step.
--   3. Instantiate at `k = tau t + 1`. Since `1 ≤ tau`, the bound is contradictory, so
--      `leafCount (f (tau t + 1)) ≠ leafCount t` — and that is a DECIDABLE proposition
--      being refuted, so monotonicity upgrades it to `>` with no classical step.
--
-- So the equivalence is constructively true; only this development does not yet contain it.
-- What IS contained is the half that matters for C1(a), plus `normalizes_of_no_growth`
-- above, which already says the essential thing: **growth is necessary for
-- non-termination in pure S.**
