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

-- ## Stage 35: the equivalence, constructively
-- Stage 34 recorded the constructive route and declined to build it. Building it turned up
-- one thing that route had not noticed: the negative-to-positive step Stage 34 called
-- intrinsic is avoidable, because per-reduct reducibility is DECIDABLE. Stage 34's
-- `by_cases` was on `∃ u, t ⟶* u ∧ leafCount t < leafCount u` — a statement about ALL
-- reducts, genuinely undecidable. But `∃ v, u ⟶ v` for a FIXED `u` is decided by
-- `stepOnce`. Routing through "every reduct is reducible" therefore needs no classical step
-- anywhere, and the full equivalence is constructive.

/-- The leftmost-outermost trajectory as a total function: stalls at a normal form. -/
def iter (t : Term) : Nat → Term
  | 0 => t
  | k + 1 => match stepOnce (iter t k) with
    | some u => u
    | none => iter t k

/-- **The constructive bridge.** No normal form gives reducibility of every reduct — by
casing on the computable `stepOnce`, not on the proposition. -/
theorem all_reducible_of_no_normalForm {t : Term}
    (h : ¬ ∃ n, (t ⟶* n) ∧ NormalForm n) : ∀ u, (t ⟶* u) → ∃ v, u ⟶ v := by
  intro u hu
  match hs : stepOnce u with
  | none => exact absurd ⟨u, hu, stepOnce_none_normal hs⟩ h
  | some v => exact ⟨v, stepOnce_sound hs⟩

theorem iter_reduct {t : Term} (hall : ∀ u, (t ⟶* u) → ∃ v, u ⟶ v) :
    ∀ k, t ⟶* iter t k
  | 0 => Steps.refl _
  | k + 1 => by
    have hprev := iter_reduct hall k
    obtain ⟨v, hv⟩ := hall _ hprev
    have hsome : (stepOnce (iter t k)).isSome := stepOnce_isSome_of_step hv
    match hs : stepOnce (iter t k) with
    | none => rw [hs] at hsome; simp at hsome
    | some w =>
      have : iter t (k + 1) = w := by simp only [iter, hs]
      rw [this]
      exact Steps.trans hprev (Steps.single (stepOnce_sound hs))

theorem iter_step {t : Term} (hall : ∀ u, (t ⟶* u) → ∃ v, u ⟶ v) :
    ∀ k, iter t k ⟶ iter t (k + 1) := by
  intro k
  obtain ⟨v, hv⟩ := hall _ (iter_reduct hall k)
  have hsome : (stepOnce (iter t k)).isSome := stepOnce_isSome_of_step hv
  match hs : stepOnce (iter t k) with
  | none => rw [hs] at hsome; simp at hsome
  | some w =>
    have he : iter t (k + 1) = w := by simp only [iter, hs]
    rw [he]
    exact stepOnce_sound hs

/-- **The τ budget.** If the trajectory has not grown by step `k`, then τ has paid `k` units
— because every step on a size plateau strictly drops τ. -/
theorem tau_budget {t : Term} (hk : KFree t) (hall : ∀ u, (t ⟶* u) → ∃ v, u ⟶ v) :
    ∀ k, leafCount (iter t k) = leafCount t → tau (iter t k) + k ≤ tau t
  | 0 => fun _ => by simp [iter]
  | k + 1 => by
    intro heq
    -- monotonicity squeezes the intermediate size, so this step is on the plateau
    have hmid := leafCount_le_of_steps hk (iter_reduct hall k)
    have hlast := leafCount_le_of_steps hk (iter_reduct hall (k + 1))
    have hstep := iter_step hall k
    have hgrow := leafCount_le_of_step (hk.of_steps (iter_reduct hall k)) hstep
    have hmk : leafCount (iter t k) = leafCount t := by omega
    have hdrop : tau (iter t (k + 1)) < tau (iter t k) :=
      tau_lt_of_isometric_step (hk.of_steps (iter_reduct hall k)) hstep (by omega)
    have := tau_budget hk hall k hmk
    omega

/-- **The growth step, constructively.** A K-free term all of whose reducts are reducible
has a strictly larger reduct — found at trajectory index `tau t + 1`, where the τ budget is
exhausted. -/
theorem exists_larger_of_all_reducible {t : Term} (hk : KFree t)
    (hall : ∀ u, (t ⟶* u) → ∃ v, u ⟶ v) :
    ∃ u, (t ⟶* u) ∧ leafCount t < leafCount u := by
  refine ⟨iter t (tau t + 1), iter_reduct hall _, ?_⟩
  have hle := leafCount_le_of_steps hk (iter_reduct hall (tau t + 1))
  have hne : leafCount (iter t (tau t + 1)) ≠ leafCount t := by
    intro heq
    have hb := tau_budget hk hall (tau t + 1) heq
    have := tau_pos (iter t (tau t + 1))
    omega
  omega

/-- Iterated: unbounded reducts. -/
theorem unbounded_of_all_reducible {t : Term} (hk : KFree t)
    (hall : ∀ u, (t ⟶* u) → ∃ v, u ⟶ v) :
    ∀ N, ∃ u, (t ⟶* u) ∧ N < leafCount u := by
  intro N
  induction N with
  | zero =>
    obtain ⟨u, hu, hlt⟩ := exists_larger_of_all_reducible hk hall
    have := leafCount_pos t
    exact ⟨u, hu, by omega⟩
  | succ k ih =>
    obtain ⟨u, hu, hgt⟩ := ih
    have hallu : ∀ v, (u ⟶* v) → ∃ w, v ⟶ w :=
      fun v hv => hall v (Steps.trans hu hv)
    obtain ⟨w, hw, hlt⟩ := exists_larger_of_all_reducible (hk.of_steps hu) hallu
    exact ⟨w, Steps.trans hu hw, by omega⟩

/-- **The equivalence, fully constructive.** For a K-free term, having no normal form is the
same thing as having reducts of unbounded size.

This settles the framing question Stages 32–34 circled: the census measured sizes, the
conjecture asked about normalization, and for pure S **they are the same question** — with no
classical step anywhere, because `stepOnce` decides reducibility pointwise. -/
theorem no_normalForm_iff_unbounded {t : Term} (hk : KFree t) :
    (¬ ∃ n, (t ⟶* n) ∧ NormalForm n) ↔ (∀ N, ∃ u, (t ⟶* u) ∧ N < leafCount u) := by
  constructor
  · intro h
    exact unbounded_of_all_reducible hk (all_reducible_of_no_normalForm h)
  · exact no_normalForm_of_unbounded hk

-- ## Stage 36: the reformulations are all the same problem
-- Stage 35's ranking claimed "every reduct is reducible" was a better target for C1(a) than
-- the invariant (Stage 32) or the raw size claim (Stage 33). Checking that before attacking
-- it shows the claim was wrong: all three are EQUIVALENT, and so is the invariant form,
-- because `fun u => t ⟶* u` is itself an invariant whenever every reduct is reducible.
--
-- So Stages 32, 33 and 35 each replaced C1(a)'s statement with a provably equivalent one and
-- I read each replacement as progress. It was not. The theorem below makes that a fact rather
-- than a suspicion, so the cycle cannot repeat: **any further reformulation of C1(a) along
-- these lines is a restatement, and closing it requires new mathematics about pure S, not a
-- better phrasing.**

/-- Iterating a chosen successor function. -/
def iterFn (next : Term → Term) (t : Term) : Nat → Term
  | 0 => t
  | k + 1 => next (iterFn next t k)

/-- **The four formulations of C1(a), proved equivalent.**

1. `t` has no normal form — the conjecture as stated;
2. every reduct of `t` is reducible — the positive phrasing (Stage 35's "better target");
3. there is a reducibility invariant with an explicit successor function — the invariant
   route hunted in Slices 3, 4 and Stage 32;
4. `t`'s reducts have unbounded size — the size criterion (Stage 33).

Constructive throughout: (1)→(2) decides reducibility with `stepOnce`, (2)→(3) takes the
invariant to be "is a reduct of `t`" with `stepOnce` as the successor, (3)→(1) builds an
infinite reduction and applies C5, and (1)↔(4) is Stage 35. -/
theorem c1a_formulations {t : Term} (hk : KFree t) :
    ((¬ ∃ n, (t ⟶* n) ∧ NormalForm n) ↔ (∀ u, (t ⟶* u) → ∃ v, u ⟶ v))
  ∧ ((∀ u, (t ⟶* u) → ∃ v, u ⟶ v) ↔
      (∃ (P : Term → Prop) (next : Term → Term),
         P t ∧ ∀ u, P u → (u ⟶ next u) ∧ P (next u)))
  ∧ ((¬ ∃ n, (t ⟶* n) ∧ NormalForm n) ↔ (∀ N, ∃ u, (t ⟶* u) ∧ N < leafCount u)) := by
  refine ⟨⟨all_reducible_of_no_normalForm, ?_⟩, ⟨?_, ?_⟩, no_normalForm_iff_unbounded hk⟩
  · -- (2) → (1): a normal form would be an irreducible reduct
    intro hall ⟨n, hn, hnf⟩
    exact hnf (hall n hn)
  · -- (2) → (3): "is a reduct of t" is the invariant, with stepOnce as the successor
    intro hall
    refine ⟨fun u => t ⟶* u, fun u => (stepOnce u).getD u, Steps.refl _, ?_⟩
    intro u hu
    obtain ⟨v, hv⟩ := hall u hu
    have hsome : (stepOnce u).isSome := stepOnce_isSome_of_step hv
    match hs : stepOnce u with
    | none => rw [hs] at hsome; simp at hsome
    | some w =>
      have he : (stepOnce u).getD u = w := by rw [hs]; rfl
      show (u ⟶ (stepOnce u).getD u) ∧ (t ⟶* (stepOnce u).getD u)
      rw [he]
      exact ⟨stepOnce_sound hs, Steps.trans hu (Steps.single (stepOnce_sound hs))⟩
  · -- (3) → (2): iterate `next` to get an infinite reduction, then C5
    rintro ⟨P, next, hPt, hstep⟩ u hu
    -- the invariant gives an infinite reduction from t, so t has no normal form...
    have hPall : ∀ k, P (iterFn next t k) := by
      intro k
      induction k with
      | zero => exact hPt
      | succ j ih => exact (hstep _ ih).2
    have hinf : InfiniteRed t :=
      ⟨iterFn next t, rfl, fun k => (hstep _ (hPall k)).1⟩
    -- ...and then every reduct is reducible, by the decidable route
    exact all_reducible_of_no_normalForm (no_normalForm_of_infiniteRed hk hinf) u hu

-- ## What C1(a) actually needs
-- Not another phrasing. Every route above is the same statement, so closing C1(a) requires a
-- genuinely new fact about pure-S reduction — something that produces, for one concrete
-- term, either an infinite reduction, an unbounded family of reducts, or a preserved
-- reducibility predicate. The tree now supplies every *bridge* between those, and none of
-- the sources.
--
-- What the program HAS contributed to C1(a), stated so the negative result above is not
-- mistaken for the whole story:
--   * C1(b) PROVED — no pure-S term below 7 leaves diverges (Slice 5);
--   * C5 PROVED — conservation, so an infinite reduction suffices (Stage 31);
--   * the frozen head PROVED — c1's trajectory is `S A B` with `A` a fixed normal form,
--     reducing the question to the payload (Slice 4);
--   * the four-way equivalence above, so the target is unambiguous;
--   * honest negatives: no self-embedding for `c1` within 120 steps, none for the
--     literature's 14-leaf term within 40, and no I-like combinator in {S,B} to transport
--     rung one's cycle.

-- ## Stage 37: construct-don't-search, attempted — the design space is empty at small size
-- Stage 36 named the one remaining route with new content: build a self-embedding
-- `t ⟶⁺ C[t]` by design rather than searching for one. Such a `t` would give an infinite
-- reduction directly — `C[t] ⟶⁺ C[C[t]]` by congruence — and hence, via C5, no normal form,
-- proving C1(a).
--
-- Note first that C2 forces any such `C` to be NON-TRIVIAL: `t ⟶⁺ t` is a cycle and pure S
-- has none. So the target is strict self-embedding, and sizes must grow along it.
--
-- Attempting the construction meant first searching the design space systematically, which
-- Slices 3 and 4 never did — they checked `c1` and `c2` only. Result: **nothing.**
--
--   leftmost-outermost, 60 steps, size cap 3000, every pure-S term up to 8 leaves:  0
--   leftmost-outermost, 200 steps, size cap 20000, every term up to 8 leaves:       0
--   ALL STRATEGIES (bounded closure, cap 40, fuel 200), every term up to 6 leaves:  0
--
-- The all-strategies row matters because of Stage 21: a leftmost-outermost hunt provably
-- misses cycles that exist in the relation (rung one's `omegaSI` is the witness), so an
-- LO-only negative would have been weak evidence. The closure search is strategy-independent.

/-- Does `t` reappear as a subterm of one of its own leftmost-outermost reducts? Size-capped,
so explosive terms are abandoned rather than pursued. Unverified census tooling. -/
def selfEmbeds (cap steps : Nat) (t : Term) : Bool :=
  let rec go : Nat → Term → Bool
    | 0, _ => false
    | f + 1, cur =>
      match stepOnce cur with
      | none => false
      | some nxt =>
        if cap < leafCount nxt then false
        else if isSubterm t nxt then true
        else go f nxt
  go steps t

-- Guarded at a size the build can afford; the deeper runs above are recorded, not guarded.
#guard (List.range 7).all (fun n => (sTerms n).all (fun t => !(selfEmbeds 3000 60 t)))

-- The two C1 candidates specifically, extending Slice 3's 120-step result to the size cap:
#guard !(selfEmbeds 20000 200 c1)
#guard !(selfEmbeds 20000 200 c2)

-- ## What that leaves
-- "Construct-don't-search" is now ATTEMPTED rather than merely registered, and the honest
-- outcome is that the design space contains no self-embedding at any size the search reaches
-- — under every strategy up to 6 leaves, and under leftmost-outermost up to 8.
--
-- That is a stronger negative than the ledger previously held (two terms, one strategy, 120
-- steps), and it changes the standing of the route: not unexplored, but searched and empty
-- where searchable. What is NOT known is whether a self-embedding is impossible in pure S. No
-- obstruction is proved here, and none is apparent — C2 rules out the trivial context only.
-- Establishing impossibility would be a genuine theorem and would close the loop route for
-- good; finding a witness at larger size would prove C1(a). Both are open, and the search
-- cannot decide between them.

-- ## Stage 38: the one-step obstruction, PROVED
-- Stage 37 left the loop route "searched and empty where searchable" and said plainly that no
-- obstruction was proved and none was apparent. One is apparent after all, at depth one, and it
-- is not a measure argument — measures cannot work here, since a measure that fell on every
-- pure-S step would prove strong normalization and hence REFUTE C1(a). It is structural:
--
--   the reduct of a redex never contains that redex.
--
-- `S f g x ⟶ f x (g x)`, and the reduct's subterms are exactly `f x`, `g x`, the reduct itself,
-- and the subterms of `f`, `g`, `x`. The last group is too small to hold `S f g x`. Of the first
-- three, each forces an equation a term cannot satisfy — `x = g x`, or `f = S f g` — because a
-- term is never a proper subterm of itself. Congruence then lifts this to a redex anywhere, and
-- the lifting is where transitivity of the subterm relation does the work: if `app f u` sits
-- inside `f'`, then so does `f`, which is the induction hypothesis.
--
-- This needs a Prop-level subterm relation. `isSubterm` (Reachability, Slice 3) is Bool-valued
-- census tooling with no lemmas; `Subterm` is the relation the kernel can reason about, and the two
-- are bridged below so the Stage 37 guards inherit the kernel's meaning.

/-- `Subterm s t` — `s` occurs as a subterm of `t`, reflexively. -/
inductive Subterm : Term → Term → Prop
  | refl (t : Term) : Subterm t t
  | left {s a b : Term} : Subterm s a → Subterm s (Term.app a b)
  | right {s a b : Term} : Subterm s b → Subterm s (Term.app a b)

-- The three ways to be a subterm of an application — packaged as an inversion principle so the
-- proofs below never have to `cases` on an indexed hypothesis with a compound index.
theorem Subterm.app_cases {s a b : Term} (h : Subterm s (Term.app a b)) :
    s = Term.app a b ∨ Subterm s a ∨ Subterm s b := by
  cases h with
  | refl => exact Or.inl rfl
  | left h => exact Or.inr (Or.inl h)
  | right h => exact Or.inr (Or.inr h)

theorem Subterm.trans {s t u : Term} (h1 : Subterm s t) (h2 : Subterm t u) : Subterm s u := by
  induction h2 with
  | refl => exact h1
  | left _ ih => exact Subterm.left ih
  | right _ ih => exact Subterm.right ih

-- Immediate but used constantly: a term is a subterm of anything it is applied to or against.
theorem Subterm.appL (a b : Term) : Subterm a (Term.app a b) := Subterm.left (Subterm.refl a)
theorem Subterm.appR (a b : Term) : Subterm b (Term.app a b) := Subterm.right (Subterm.refl b)

-- Arithmetic of the leaf measure on the shapes the step relation produces. All `rfl`: `leafCount`
-- matches on constructors and `1 + f + g + x` associates the same way the nesting does.
theorem leafCount_app (a b : Term) : leafCount (Term.app a b) = leafCount a + leafCount b := rfl
theorem leafCount_app2_K (x y : Term) :
    leafCount (app2 Term.K x y) = 1 + leafCount x + leafCount y := rfl
theorem leafCount_app3_S (f g x : Term) :
    leafCount (app3 Term.S f g x) = 1 + leafCount f + leafCount g + leafCount x := rfl

theorem Subterm.leafCount_le {s t : Term} (h : Subterm s t) : leafCount s ≤ leafCount t := by
  induction h with
  | refl => exact Nat.le_refl _
  | @left a b _ ih =>
      have hb := leafCount_pos b
      show leafCount s ≤ leafCount a + leafCount b
      omega
  | @right a b _ ih =>
      have ha := leafCount_pos a
      show leafCount s ≤ leafCount a + leafCount b
      omega

/-- Antisymmetry, in the form the proofs want it: a subterm that is not smaller is the whole
term. This is what makes "no cycle" (C2) forbid a size-preserving self-embedding. -/
theorem Subterm.eq_of_leafCount_le {s t : Term} (h : Subterm s t) (hle : leafCount t ≤ leafCount s) :
    s = t := by
  induction h with
  | refl => rfl
  | @left a b hsub _ =>
      have hb := leafCount_pos b
      have := hsub.leafCount_le
      exact absurd hle (by show ¬ (leafCount a + leafCount b ≤ leafCount s); omega)
  | @right a b hsub _ =>
      have ha := leafCount_pos a
      have := hsub.leafCount_le
      exact absurd hle (by show ¬ (leafCount a + leafCount b ≤ leafCount s); omega)

/-- **No term reappears inside its own one-step reduct.** Every term, no size bound, and full SK
rather than just pure S — the K case is settled by size alone, since `K x y` discards `y` and
outweighs `x`. -/
theorem Step.not_sub_self : ∀ {t u : Term}, (t ⟶ u) → ¬ Subterm t u := by
  intro t u h
  induction h with
  | K_red x y =>
      intro hs
      have hle := hs.leafCount_le
      rw [leafCount_app2_K] at hle
      have hy := leafCount_pos y
      omega
  | S_red f g x =>
      intro hs
      -- Abbreviate: the redex outweighs f, g and x, which kills every "too small" branch.
      have hT := leafCount_app3_S f g x
      have hf := leafCount_pos f
      have hg := leafCount_pos g
      have hx := leafCount_pos x
      have small : ∀ {s : Term}, Subterm (app3 Term.S f g x) s →
          leafCount s < leafCount (app3 Term.S f g x) → False := fun hsub hlt =>
        absurd hsub.leafCount_le (by omega)
      rcases hs.app_cases with heq | hl | hr
      · -- the reduct IS the redex. Size alone does not settle this branch: the leaf counts
        -- agree when x is a single leaf. Injectivity is what closes it — the equation's right
        -- components give x = g x, and THAT is impossible by size.
        rw [app3, Term.app.injEq] at heq
        have := congrArg leafCount heq.2
        rw [leafCount_app] at this
        omega
      · rcases hl.app_cases with heq | hl' | hl'
        · -- redex = f x: forces f = S f g, impossible by size
          have := congrArg leafCount heq
          rw [hT, leafCount_app] at this
          omega
        · exact small hl' (by omega)
        · exact small hl' (by omega)
      · rcases hr.app_cases with heq | hr' | hr'
        · -- redex = g x: forces g = S f g, impossible by size
          have := congrArg leafCount heq
          rw [hT, leafCount_app] at this
          omega
        · exact small hr' (by omega)
        · exact small hr' (by omega)
  | @appL t t' u hstep ih =>
      intro hs
      rcases hs.app_cases with heq | hl | hr
      · -- app t u = app t' u forces t = t', so the step is a one-step cycle on t
        rw [Term.app.injEq] at heq
        exact ih (heq.1 ▸ Subterm.refl t)
      · -- app t u sits inside t', hence so does t — exactly the induction hypothesis
        exact ih ((Subterm.appL t u).trans hl)
      · -- app t u sits inside u: impossible, it is strictly bigger
        have hle := hr.leafCount_le
        rw [leafCount_app] at hle
        have := leafCount_pos t
        omega
  | @appR t u u' hstep ih =>
      intro hs
      rcases hs.app_cases with heq | hl | hr
      · rw [Term.app.injEq] at heq
        exact ih (heq.2 ▸ Subterm.refl u)
      · have hle := hl.leafCount_le
        rw [leafCount_app] at hle
        have := leafCount_pos u
        omega
      · exact ih ((Subterm.appR t u).trans hr)

-- The Bool-valued census predicate and the kernel relation agree, so Stage 37's guards — and
-- Slice 3's before them — are statements about `Subterm` and not merely about a search routine.
theorem isSubterm_iff_Subterm : ∀ {s t : Term}, isSubterm s t = true ↔ Subterm s t := by
  intro s t
  induction t with
  | S =>
      constructor
      · intro h
        simp [isSubterm] at h
        exact h ▸ Subterm.refl _
      · intro h
        cases h with
        | refl => simp [isSubterm]
  | K =>
      constructor
      · intro h
        simp [isSubterm] at h
        exact h ▸ Subterm.refl _
      · intro h
        cases h with
        | refl => simp [isSubterm]
  | app a b iha ihb =>
      constructor
      · intro h
        rw [isSubterm] at h
        rcases Bool.or_eq_true _ _ |>.mp h with heq | hrest
        · exact (of_decide_eq_true (by simpa using heq) : Term.app a b = s) ▸ Subterm.refl _
        · rcases Bool.or_eq_true _ _ |>.mp hrest with hl | hr
          · exact Subterm.left (iha.mp hl)
          · exact Subterm.right (ihb.mp hr)
      · intro h
        rw [isSubterm]
        rcases h.app_cases with heq | hl | hr
        · simp [heq]
        · simp [iha.mpr hl]
        · simp [ihb.mpr hr]

/-- **Any self-embedding must strictly grow.** If `t` reappears inside a reduct of itself, the
reduct is strictly bigger — because equal leaf counts would force `t` to BE that reduct, i.e. a
cycle, and pure S has none (C2, `no_pure_S_cycle`). This is the kernel form of what Stage 37
argued in prose: the context `C` in `t ⟶⁺ C[t]` cannot be trivial. -/
theorem selfEmbed_leafCount_lt {t u : Term} (hk : KFree t)
    (h : ∃ v, (t ⟶ v) ∧ (v ⟶* u)) (hs : Subterm t u) : leafCount t < leafCount u := by
  rcases Nat.lt_or_ge (leafCount t) (leafCount u) with hlt | hge
  · exact hlt
  · have heq : t = u := hs.eq_of_leafCount_le hge
    subst heq
    exact absurd h (no_pure_S_cycle hk)

/-- **Any self-embedding needs at least two steps.** The one-step case is impossible, so the
first step cannot already be the whole path. -/
theorem selfEmbed_needs_two_steps {t u : Term} (hs : Subterm t u)
    (h : ∃ v, (t ⟶ v) ∧ (v ⟶* u)) : ∃ v w, (t ⟶ v) ∧ (v ⟶ w) ∧ (w ⟶* u) := by
  rcases h with ⟨v, hstep, hback⟩
  cases hback with
  | refl => exact absurd hs hstep.not_sub_self
  | tail h2 hrest => exact ⟨v, _, hstep, h2, hrest⟩

-- ## What lifts and what does not
-- The one-step theorem holds for every SK term with no size bound, which is a different KIND of
-- statement from Stage 37's search: not "no witness below 8 leaves" but "no witness, ever, at
-- depth one". Together with `selfEmbed_leafCount_lt` the loop route now carries two proved
-- constraints — a self-embedding needs at least two steps and must strictly grow.
--
-- It does NOT lift to multi-step reduction, and the reason is worth recording precisely rather
-- than left as "the induction fails". The natural argument inducts on path length: given a
-- shortest self-embedding `t ⟶⁺ w` with last step `v ⟶ w`, split the occurrence of `t` in `w`
-- by its position relative to the redex. Off the redex, `t` is a subterm of `v`, so `t ⟶⁺ v` is
-- a SHORTER self-embedding and minimality closes the case. The residual cases are the ones where
-- the occurrence meets the redex `S f g x`, and there `t` is one of:
--
--   * a term containing the reduct `f x (g x)`,   * `f x`,   * `g x`.
--
-- None of the three is contradictory on its face. Size does not kill them — a self-embedding is
-- allowed to grow, which is exactly what `selfEmbed_leafCount_lt` says — and neither does
-- acyclicity, since these `t` need not recur. So the depth-one proof is a genuine base case with
-- no inductive step, and closing the loop route needs a new idea about those three shapes, not
-- more of this argument.
--
-- One thing the failure does settle: the missing ingredient is not a measure. A measure falling
-- on every pure-S step would prove strong normalization for pure S and so REFUTE C1(a), which
-- the census evidence says is true. Whatever closes this is structural, as the base case is.

-- ## Stage 39: the skeleton, and whether its residue is inhabited
-- Stage 38 described the multi-step induction and its three residual shapes in prose. Prose is
-- where claims go to hide, so the skeleton is a theorem here and the shapes are its conclusion.
-- The organising fact is that a step rewrites ONE position, so a subterm of the result is
-- classified by its position relative to that one: disjoint from it (then it survived from the
-- source), above it (then it contains the reduct), or below it (then it sits inside the reduct).

/-- `RootRedex r r'` — `r` rewrites to `r'` by firing a redex at `r`'s own root. This is `Step`
minus the two congruence rules, and it is what a step's *witness* is: every step fires exactly
one root redex, somewhere. -/
inductive RootRedex : Term → Term → Prop
  | kRed (x y : Term) : RootRedex (app2 Term.K x y) x
  | sRed (f g x : Term) : RootRedex (app3 Term.S f g x) (app (app f x) (app g x))

theorem RootRedex.step {r r' : Term} (h : RootRedex r r') : r ⟶ r' := by
  cases h
  · exact Step.K_red _ _
  · exact Step.S_red _ _ _

-- `cases` on an indexed hypothesis whose index IS one of the constructor's fields (as `r' = x` is
-- for `kRed`) refuses to name that field, so downstream proofs get the shape as an equation pair
-- instead. Same local idiom as the `mkElimApp` workaround elsewhere in the tree: when `cases`
-- fights the indices, extract what you need as a plain disjunction of equations first.
theorem RootRedex.shape {r r' : Term} (h : RootRedex r r') :
    (∃ p q, r = app2 Term.K p q ∧ r' = p) ∨
    (∃ f g x, r = app3 Term.S f g x ∧ r' = app (app f x) (app g x)) := by
  cases h
  · exact Or.inl ⟨_, _, rfl, rfl⟩
  · exact Or.inr ⟨_, _, _, rfl, rfl⟩

theorem KFree.of_subterm {s t : Term} (h : Subterm s t) : KFree t → KFree s := by
  induction h with
  | refl => exact id
  | @left a b _ ih => intro hk; cases hk with | app hl _ => exact ih hl
  | @right a b _ ih => intro hk; cases hk with | app _ hr => exact ih hr

-- The three arguments of an S-redex are subterms of it. Needed to push "t occurs in f" back to
-- "t occurs in v", which is what collapses the easy branches.
theorem Subterm.app3_S_arg1 (f g x : Term) : Subterm f (app3 Term.S f g x) :=
  Subterm.left (Subterm.left (Subterm.right (Subterm.refl f)))
theorem Subterm.app3_S_arg2 (f g x : Term) : Subterm g (app3 Term.S f g x) :=
  Subterm.left (Subterm.right (Subterm.refl g))
theorem Subterm.app3_S_arg3 (f g x : Term) : Subterm x (app3 Term.S f g x) :=
  Subterm.right (Subterm.refl x)

/-- **The positional trichotomy.** A step `v ⟶ w` fires one root redex `r ⟶ r'` sitting inside
`v`, and every subterm of `w` either already occurred in `v`, or contains the reduct, or is
contained in it. The three disjuncts are the three positions available relative to a single
rewritten site: disjoint, above, below. -/
theorem Step.subterm_split : ∀ {v w : Term}, (v ⟶ w) →
    ∃ r r', RootRedex r r' ∧ Subterm r v ∧ Subterm r' w ∧
      ∀ s, Subterm s w → Subterm s v ∨ Subterm r' s ∨ Subterm s r' := by
  intro v w h
  induction h with
  | K_red x y =>
      exact ⟨app2 Term.K x y, x, RootRedex.kRed x y, Subterm.refl _, Subterm.refl _,
        fun _ hs => Or.inr (Or.inr hs)⟩
  | S_red f g x =>
      exact ⟨app3 Term.S f g x, app (app f x) (app g x), RootRedex.sRed f g x,
        Subterm.refl _, Subterm.refl _, fun _ hs => Or.inr (Or.inr hs)⟩
  | @appL t t' u _ ih =>
      obtain ⟨r, r', hred, hrv, hrw, hall⟩ := ih
      refine ⟨r, r', hred, hrv.trans (Subterm.appL t u), hrw.trans (Subterm.appL t' u), ?_⟩
      intro s hs
      rcases hs.app_cases with heq | hl | hr
      · exact Or.inr (Or.inl (heq ▸ hrw.trans (Subterm.appL t' u)))
      · rcases hall s hl with h1 | h2 | h3
        · exact Or.inl (h1.trans (Subterm.appL t u))
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)
      · exact Or.inl (hr.trans (Subterm.appR t u))
  | @appR t u u' _ ih =>
      obtain ⟨r, r', hred, hrv, hrw, hall⟩ := ih
      refine ⟨r, r', hred, hrv.trans (Subterm.appR t u), hrw.trans (Subterm.appR t u'), ?_⟩
      intro s hs
      rcases hs.app_cases with heq | hl | hr
      · exact Or.inr (Or.inl (heq ▸ hrw.trans (Subterm.appR t u')))
      · exact Or.inl (hl.trans (Subterm.appL t u))
      · rcases hall s hr with h1 | h2 | h3
        · exact Or.inl (h1.trans (Subterm.appR t u))
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)

/-- What sits inside an S-reduct: the reduct itself, its two halves, or something already inside
one of the redex's three arguments. -/
theorem subterm_S_reduct_cases {f g x s : Term} (h : Subterm s (app (app f x) (app g x))) :
    s = app (app f x) (app g x) ∨ s = app f x ∨ s = app g x
      ∨ Subterm s f ∨ Subterm s g ∨ Subterm s x := by
  rcases h.app_cases with heq | hl | hr
  · exact Or.inl heq
  · rcases hl.app_cases with heq | h1 | h2
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))
  · rcases hr.app_cases with heq | h1 | h2
    · exact Or.inr (Or.inr (Or.inl heq))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))

/-- **The residue, exactly.** Suppose `t` occurs in `w` but not in `v`, where `v ⟶ w` and `v` is
pure S. Then the step's redex is some `S f g x` inside `v`, and `t` is one of exactly three
shapes: it contains the reduct, or it IS `f x`, or it IS `g x`.

This is the whole obstruction to lifting Stage 38 to multi-step reduction. In a shortest
self-embedding `t ⟶⁺ w` with last step `v ⟶ w`, the hypothesis `¬ Subterm t v` is free —
`Subterm t v` would give a shorter self-embedding — so these three shapes are all that stand
between the depth-one theorem and the general one. -/
theorem selfEmbed_residual_shapes {t v w : Term} (hk : KFree v) (h : v ⟶ w)
    (hs : Subterm t w) (hnv : ¬ Subterm t v) :
    ∃ f g x, Subterm (app3 Term.S f g x) v ∧
      (Subterm (app (app f x) (app g x)) t ∨ t = app f x ∨ t = app g x) := by
  obtain ⟨r, r', hred, hrv, _, hall⟩ := h.subterm_split
  rcases hred.shape with ⟨p, q, hr, _⟩ | ⟨f, g, x, hr, hr'⟩
  · -- a K-redex inside a K-free term: invert KFree twice to expose `KFree Term.K`, which has no
    -- constructor
    subst hr
    have hkr : KFree (app2 Term.K p q) := KFree.of_subterm hrv hk
    cases hkr with
    | app hl _ => cases hl with | app hkk _ => cases hkk
  · subst hr
    subst hr'
    refine ⟨f, g, x, hrv, ?_⟩
    rcases hall t hs with h1 | h2 | h3
    · exact absurd h1 hnv
    · exact Or.inl h2
    · rcases subterm_S_reduct_cases h3 with e | e | e | e | e | e
      · exact Or.inl (e ▸ Subterm.refl _)
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
      · exact absurd (e.trans ((Subterm.app3_S_arg1 f g x).trans hrv)) hnv
      · exact absurd (e.trans ((Subterm.app3_S_arg2 f g x).trans hrv)) hnv
      · exact absurd (e.trans ((Subterm.app3_S_arg3 f g x).trans hrv)) hnv

-- ## Is the residue inhabited? — measuring before attacking
-- Stage 38 ranked "attack shapes B and C (`t = f x`, `t = g x`) — the constrained ones" first, on
-- the reasoning that demanding the whole self-embedding term be a ONE-APPLICATION combination of
-- pieces of the last redex is a strong structural constraint. That reasoning was right about the
-- constraint and wrong about what to do with it, and the cheap measurement below says so.
--
-- The relevant question is not whether the full residual configuration occurs — it cannot, since
-- it is a case analysis OF the self-embedding hypothesis, so an instance would BE a
-- self-embedding and Stage 37 found none. The question is whether each shape's own structural
-- demand is satisfiable at all among the reducts of a term. That is checkable, and the three
-- shapes answer differently.

/-- Shapes B and C: does some S-redex `S f g x` inside `v` have `t` as one of its reduct halves,
`f x` or `g x`? Unverified census tooling. -/
def hasHalfRedex (t : Term) : Term → Bool
  | .app a b =>
      (match t, a with
       | .app tl tr, .app (.app .S f) g => (b == tr) && ((f == tl) || (g == tl))
       | _, _ => false)
      || hasHalfRedex t a || hasHalfRedex t b
  | _ => false

/-- Shape A: every subterm of `t` shaped like an S-reduct `f x (g x)`, mapped back to the redex
`S f g x` it would have to come from. Shape A asks whether any of these occurs in `v`. -/
def reductShapes : Term → List Term
  | .app a b =>
      (match a, b with
       | .app f x, .app g x' => if x == x' then [app3 Term.S f g x] else []
       | _, _ => [])
      ++ reductShapes a ++ reductShapes b
  | _ => []

def halfShapeHit (bound fuel : Nat) (t : Term) : Bool :=
  match boundedClosure bound fuel [t] with
  | none => true   -- a fuel-exhausted closure counts as a hit, so no guard passes vacuously
  | some cl => cl.any (fun v => hasHalfRedex t v)

def reductShapeHit (bound fuel : Nat) (t : Term) : Bool :=
  match boundedClosure bound fuel [t] with
  | none => true
  | some cl => cl.any (fun v => (reductShapes t).any (fun r => isSubterm r v))

def closureUndecided (bound fuel : Nat) (t : Term) : Bool :=
  (boundedClosure bound fuel [t]).isNone

-- Every verdict below is a real saturated closure, not an exhausted one.
#guard (List.range 8).all (fun n => (sTerms n).all (fun t => !(closureUndecided 24 120 t)))

-- **Shapes B and C are empty.** No reduct of any pure-S term up to 7 leaves contains an S-redex
-- one of whose reduct halves is the term itself. (Measured clean to 8 leaves as well; guarded at
-- 7 for build cost.) The `t ⋬ v` side condition is not doing this work — the shapes are empty
-- without it.
#guard (List.range 8).all (fun n => (sTerms n).all (fun t => !(halfShapeHit 24 120 t)))

-- **Shape A is not empty, and it grows.** Terms whose reducts host the redex of a reduct-shaped
-- subterm: 1 at six leaves, 4 at seven, 19 at eight.
#guard ((sTerms 6).filter (fun t => reductShapeHit 24 120 t)).length = 1
#guard ((sTerms 7).filter (fun t => reductShapeHit 24 120 t)).length = 4

-- ## What the measurement changes
-- Stage 38's ranking is INVERTED. Shapes B and C are constrained past the point of usefulness:
-- they are empty, so proving them impossible would narrow the residue from three shapes to one
-- and would not touch the obstruction, because shape A is where the difficulty lives and shape A
-- is growing. Attacking B and C first would have been careful work on the part of the problem
-- that was already not the problem.
--
-- The honest standing of the loop route is therefore:
--   * depth one: closed, for every SK term (`Step.not_sub_self`);
--   * any depth: reduced to ONE shape by the trichotomy — a self-embedding's last step must put
--     `t` strictly above the reduct it fires — with the other two shapes empty by measurement;
--   * that one shape: open, inhabited, and growing with term size.
-- Which is a genuinely better-characterised open problem than Stage 37 left, and still open.

-- ## Stage 40: shape A, closed
-- Stage 39 measured shape A as the inhabited, growing residue and ranked it first with no
-- argument in hand. There is one, and it comes from noticing what the trichotomy THREW AWAY.
--
-- `Step.subterm_split` records that a subterm of `w` lying above the redex "contains the reduct".
-- That is weaker than the truth. If `t` sits at a position above the redex, then the subterm of
-- `v` at that SAME position — call it `u` — satisfies `u ⟶ t`, by firing the very same redex.
-- So shape A does not merely say `t` contains something; it says
--
--   t is a one-step reduct of a subterm of v.
--
-- And that is fatal, because `u ⊴ v` and `u ⟶ t ⟶⁺ v` make `u` a self-embedding term in its own
-- right, one step EARLIER than `t`. Walking backwards like this cannot go on forever: a pure-S
-- step never adds leaves, and a leaf-preserving step strictly lowers τ (`tau_lt_of_isometric_step`
-- — the engine of C2), so each backward step drops a rank built from the finite universe
-- `smallTerms`. The descent bottoms out, and shape A is gone.

/-- The strengthened trichotomy. Same three positions as `Step.subterm_split`, but the "above the
redex" case is recorded as what it actually is — `s` is a one-step reduct of a subterm of `v` —
rather than the weaker "s contains the reduct". -/
theorem Step.subterm_split' : ∀ {v w : Term}, (v ⟶ w) → ∀ {s : Term}, Subterm s w →
    Subterm s v ∨ (∃ u, Subterm u v ∧ (u ⟶ s)) ∨
      (∃ f g x, Subterm (app3 Term.S f g x) v ∧ (s = app f x ∨ s = app g x)) := by
  intro v w h
  induction h with
  | K_red x y =>
      intro s hs
      exact Or.inl (hs.trans (Subterm.left (Subterm.right (Subterm.refl x))))
  | S_red f g x =>
      intro s hs
      rcases hs.app_cases with heq | hl | hr
      · exact Or.inr (Or.inl ⟨app3 Term.S f g x, Subterm.refl _,
          by rw [heq]; exact Step.S_red f g x⟩)
      · rcases hl.app_cases with heq | h1 | h2
        · exact Or.inr (Or.inr ⟨f, g, x, Subterm.refl _, Or.inl heq⟩)
        · exact Or.inl (h1.trans (Subterm.app3_S_arg1 f g x))
        · exact Or.inl (h2.trans (Subterm.app3_S_arg3 f g x))
      · rcases hr.app_cases with heq | h1 | h2
        · exact Or.inr (Or.inr ⟨f, g, x, Subterm.refl _, Or.inr heq⟩)
        · exact Or.inl (h1.trans (Subterm.app3_S_arg2 f g x))
        · exact Or.inl (h2.trans (Subterm.app3_S_arg3 f g x))
  | @appL t t' u hstep ih =>
      intro s hs
      rcases hs.app_cases with heq | hl | hr
      · exact Or.inr (Or.inl ⟨app t u, Subterm.refl _, by rw [heq]; exact Step.appL hstep⟩)
      · rcases ih hl with h1 | ⟨u0, hu0, hstep0⟩ | ⟨f, g, x, hfgx, hshape⟩
        · exact Or.inl (h1.trans (Subterm.appL t u))
        · exact Or.inr (Or.inl ⟨u0, hu0.trans (Subterm.appL t u), hstep0⟩)
        · exact Or.inr (Or.inr ⟨f, g, x, hfgx.trans (Subterm.appL t u), hshape⟩)
      · exact Or.inl (hr.trans (Subterm.appR t u))
  | @appR t u u' hstep ih =>
      intro s hs
      rcases hs.app_cases with heq | hl | hr
      · exact Or.inr (Or.inl ⟨app t u, Subterm.refl _, by rw [heq]; exact Step.appR hstep⟩)
      · exact Or.inl (hl.trans (Subterm.appL t u))
      · rcases ih hr with h1 | ⟨u0, hu0, hstep0⟩ | ⟨f, g, x, hfgx, hshape⟩
        · exact Or.inl (h1.trans (Subterm.appR t u))
        · exact Or.inr (Or.inl ⟨u0, hu0.trans (Subterm.appR t u), hstep0⟩)
        · exact Or.inr (Or.inr ⟨f, g, x, hfgx.trans (Subterm.appR t u), hshape⟩)

theorem Steps.plus_of_ne : ∀ {t v : Term}, (t ⟶* v) → t ≠ v → ∃ u, (t ⟶ u) ∧ (u ⟶* v) := by
  intro t v h hne
  cases h with
  | refl => exact absurd rfl hne
  | tail h1 h2 => exact ⟨_, h1, h2⟩

theorem Steps.cases_last : ∀ {t w : Term}, (t ⟶* w) → t = w ∨ ∃ v, (t ⟶* v) ∧ (v ⟶ w) := by
  intro t w h
  induction h with
  | refl => exact Or.inl rfl
  | @tail t u w hstep _ ih =>
      rcases ih with heq | ⟨v, h1, h2⟩
      · exact Or.inr ⟨t, Steps.refl t, heq ▸ hstep⟩
      · exact Or.inr ⟨v, Steps.tail hstep h1, h2⟩

/-- Residual shapes B and C, as a predicate on one term: `t` is one half of the reduct of an
S-redex that occurs in one of `t`'s own reducts. Stage 39 measured this EMPTY for every pure-S
term up to eight leaves; it is unproved in general, and after Stage 40 it is the only remaining
route to a self-embedding. -/
def HalfShape (t : Term) : Prop :=
  ∃ f g x v, (t = app f x ∨ t = app g x) ∧ (t ⟶* v) ∧ Subterm (app3 Term.S f g x) v

-- The descent rank: how much of the bounded universe lies strictly below `t` in the order "fewer
-- leaves, or equally many and larger τ". Both clauses are needed because a pure-S step can
-- preserve leaf count, and that is exactly the case τ was built for.
private def belowPred (t s : Term) : Bool :=
  decide (leafCount s < leafCount t) ||
    (decide (leafCount s = leafCount t) && decide (tau t < tau s))

def nuBelow (N : Nat) (t : Term) : Nat := ((smallTerms N).filter (belowPred t)).length

/-- Walking BACKWARDS along a step lowers the rank. This is what makes the shape-A descent
terminate, and it is the same squeeze that proves C2: leaf count cannot rise, and when it stays
put, τ falls. -/
theorem nuBelow_lt_of_step {N : Nat} {v w : Term} (hk : KFree v) (h : v ⟶ w)
    (hN : leafCount v ≤ N) : nuBelow N v < nuBelow N w := by
  have hsize := leafCount_le_of_step hk h
  refine length_filter_lt_of_witness ?_ (mem_smallTerms hk hN) ?_ ?_
  · -- The disjunctions are split by hand rather than handed to `omega`: `omega` case-splitting a
    -- DISJUNCTIVE HYPOTHESIS pulls in `Classical.choice`, while a disjunctive goal does not.
    -- Seventh Classical encounter in this tree, and the first from omega's hypothesis handling.
    rcases Nat.lt_or_ge (leafCount v) (leafCount w) with hlt | hge
    · intro a _ ha
      simp only [belowPred, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
      rcases ha with h1 | ⟨h1, _⟩
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    · have heq : leafCount v = leafCount w := Nat.le_antisymm hsize hge
      have htau := tau_lt_of_isometric_step hk h heq
      intro a _ ha
      simp only [belowPred, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
      rcases ha with h1 | ⟨h1, h2⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩
  · -- and here even a disjunctive GOAL costs the axiom once a conjunction is nested inside it, so
    -- the witnesses are supplied as terms
    rcases Nat.lt_or_ge (leafCount v) (leafCount w) with hlt | hge
    · simp only [belowPred, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl hlt
    · have heq : leafCount v = leafCount w := Nat.le_antisymm hsize hge
      simp only [belowPred, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨heq, tau_lt_of_isometric_step hk h heq⟩
  · simp [belowPred]

-- The descent itself. Read the induction as: given a self-embedding whose target is `w`, either
-- it already reduces to a `HalfShape` term, or there is another self-embedding whose target is a
-- PREDECESSOR of `w` — and predecessors have strictly smaller rank, so this cannot recur.
private theorem selfEmbed_imp_halfShape_aux (N : Nat) : ∀ (k : Nat) (t w : Term),
    nuBelow N w < k → KFree t → leafCount w ≤ N →
    (∃ v, (t ⟶ v) ∧ (v ⟶* w)) → Subterm t w → ∃ s, HalfShape s := by
  intro k
  induction k with
  | zero => intro _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ k ih =>
    intro t w hnu hkt hN hpath hsub
    obtain ⟨v0, hstep0, hrest0⟩ := hpath
    rcases (Steps.tail hstep0 hrest0).cases_last with heq | ⟨v, hto, hstep⟩
    · -- the path returns to its own start: a cycle, which C2 forbids
      exact absurd ⟨v0, hstep0, heq ▸ hrest0⟩ (no_pure_S_cycle hkt)
    · have hkv : KFree v := hkt.of_steps hto
      have hNv : leafCount v ≤ N := Nat.le_trans (leafCount_le_of_step hkv hstep) hN
      have hrank : nuBelow N v < k :=
        Nat.lt_of_lt_of_le (nuBelow_lt_of_step hkv hstep hNv) (Nat.lt_succ_iff.mp hnu)
      rcases hstep.subterm_split' hsub with hin | ⟨u, huv, hut⟩ | ⟨f, g, x, hfgx, hshape⟩
      · -- `t` already occurred in `v`: same source, a strictly earlier target
        by_cases hne : t = v
        · -- t = v and v ⟶ w with t ⊴ w: a one-step self-embedding, killed by Stage 38
          exact absurd hsub (hne ▸ hstep).not_sub_self
        · exact ih t v hrank hkt hNv (hto.plus_of_ne hne) hin
      · -- shape A: `t` is a one-step reduct of `u ⊴ v`, so `u` self-embeds one step earlier
        exact ih u v hrank (KFree.of_subterm huv hkv) hNv ⟨t, hut, hto⟩ huv
      · exact ⟨t, f, g, x, v, hshape, hto, hfgx⟩

/-- **Shape A is closed.** If any pure-S term self-embeds, then some pure-S term has `HalfShape`
— it is one half of the reduct of an S-redex occurring in one of its own reducts.

So the loop route to C1(a) no longer has three residual shapes but one, and it is the one Stage 39
measured EMPTY for every pure-S term up to eight leaves. The shape that was inhabited and growing
is the shape that is now impossible. -/
theorem selfEmbed_imp_halfShape {t w : Term} (hk : KFree t)
    (h : ∃ v, (t ⟶ v) ∧ (v ⟶* w)) (hs : Subterm t w) : ∃ s, HalfShape s :=
  selfEmbed_imp_halfShape_aux (leafCount w) (nuBelow (leafCount w) w + 1) t w
    (Nat.lt_succ_self _) hk (Nat.le_refl _) h hs

/-- Contrapositive, as the loop route now reads: no term is one half of the reduct of an S-redex
in its own reduct ⟹ no pure-S term self-embeds ⟹ the loop route to C1(a) is dead. -/
theorem no_selfEmbed_of_no_halfShape (hbc : ∀ s : Term, ¬ HalfShape s) {t w : Term}
    (hk : KFree t) (h : ∃ v, (t ⟶ v) ∧ (v ⟶* w)) : ¬ Subterm t w :=
  fun hs => let ⟨s, hss⟩ := selfEmbed_imp_halfShape hk h hs; hbc s hss

/-- `HalfShape` cannot be satisfied by standing still: the redex `S f g x` outweighs both halves
of its reduct, so the `v` it occurs in must be a STRICT reduct of `t`. Worth stating because it is
the first thing to check about a hypothesis the headline theorem reduces everything to — a
predicate satisfiable at `v = t` would make the reduction empty. -/
theorem halfShape_target_ne {t f g x : Term} (hsh : t = app f x ∨ t = app g x)
    (h : Subterm (app3 Term.S f g x) t) : False := by
  have hle := h.leafCount_le
  rw [leafCount_app3_S] at hle
  have hf := leafCount_pos f
  have hg := leafCount_pos g
  have hx := leafCount_pos x
  rcases hsh with heq | heq
  · rw [heq, leafCount_app] at hle; omega
  · rw [heq, leafCount_app] at hle; omega

-- Stage 39's census probe measured exactly `HalfShape`: `hasHalfRedex t v` asks whether some
-- S-redex in `v` has `t` as a reduct half, scanned over `t`'s bounded reduction closure. The
-- guards above record it empty for every pure-S term up to 7 leaves (8 measured). After Stage 40
-- that is no longer one of three routes to a self-embedding — it is the only one.

-- ## Stage 41: how much the `HalfShape` measurement was worth, and what forces what
-- First a correction to how Stage 39's guards read. `closureStep` keeps only reducts with
-- `leafCount ≤ bound`, so a size-capped closure SATURATES having silently dropped everything
-- larger. "No `HalfShape` witness in the closure at cap 24" therefore means "none among reducts
-- reachable THROUGH terms of at most 24 leaves" — not "none at all". Since a witness needs
-- `1 + |g|` more leaves than `t` has, a low ceiling is exactly where a witness would hide, and I
-- reported that measurement as stronger than it was.
--
-- Raising the ceiling does not produce one.

-- Strategy-independent, ceiling raised from 24 to 40, and out to eight leaves.
#guard (List.range 9).all (fun n => (sTerms n).all (fun t =>
  match boundedClosure 40 300 [t] with
  | none => false          -- an undecided closure fails the guard rather than passing it
  | some cl => !(cl.any (fun v => hasHalfRedex t v))))

-- Ceiling 60, to seven leaves.
#guard (List.range 8).all (fun n => (sTerms n).all (fun t =>
  match boundedClosure 60 500 [t] with
  | none => false
  | some cl => !(cl.any (fun v => hasHalfRedex t v))))

/-- The complementary probe: follow one trajectory as FAR as it goes rather than every trajectory
a short way. Leftmost-outermost, checking each reduct for a `HalfShape` witness. -/
def halfAlongLO (cap steps : Nat) (t : Term) : Bool :=
  let rec go : Nat → Term → Bool
    | 0, _ => false
    | k + 1, cur =>
      if hasHalfRedex t cur then true
      else match stepOnce cur with
        | none => false
        | some nxt => if cap < leafCount nxt then false else go k nxt
  go steps t

-- 300 steps under a 4000-leaf ceiling, every pure-S term up to eight leaves. These trajectories
-- really do run away — the largest reduct visited carries 3994 leaves — so this covers a size
-- range the closure search cannot, along one strategy instead of all.
#guard (List.range 9).all (fun n => (sTerms n).all (fun t => !(halfAlongLO 4000 300 t)))

-- ## What forces what
-- The route to a proof is backward induction along the path: if `S f g x` occurs in `v` and
-- `v' ⟶ v`, ask where it came from. `Step.subterm_split'` gives three answers, and two of them are
-- pinned down completely by the shape of `S f g x`.

/-- If `S f g x` is one HALF of the reduct of a bigger S-redex, the bigger redex is forced: its
third argument is `x` itself, and `(S f) g` is one of its first two arguments. -/
theorem app3_S_reduct_half_forces {f g x f' g' x' : Term}
    (h : app3 Term.S f g x = app f' x' ∨ app3 Term.S f g x = app g' x') :
    x' = x ∧ (f' = app (app Term.S f) g ∨ g' = app (app Term.S f) g) := by
  rcases h with heq | heq <;> simp only [app3, Term.app.injEq] at heq
  · exact ⟨heq.2.symm, Or.inl heq.1.symm⟩
  · exact ⟨heq.2.symm, Or.inr heq.1.symm⟩

theorem leafCount_app2_S (f g : Term) :
    leafCount (app (app Term.S f) g) = 1 + leafCount f + leafCount g := rfl

/-- ...and so it carries at least two more leaves. Going backwards through this case makes the
requirement strictly BIGGER, which is why it cannot be the whole story of a self-embedding. -/
theorem app3_S_reduct_half_grows {f g x f' g' x' : Term}
    (h : app3 Term.S f g x = app f' x' ∨ app3 Term.S f g x = app g' x') :
    leafCount (app3 Term.S f g x) + 2 ≤ leafCount (app3 Term.S f' g' x') := by
  obtain ⟨hx, hfg⟩ := app3_S_reduct_half_forces h
  subst hx
  rw [leafCount_app3_S, leafCount_app3_S]
  have hf := leafCount_pos f
  have hg := leafCount_pos g
  have hf' := leafCount_pos f'
  have hg' := leafCount_pos g'
  rcases hfg with heq | heq <;> subst heq <;> rw [leafCount_app2_S] <;> omega

/-- If `S f g x` is what a ROOT redex produces, the redex is forced to be `S (S f) b g` — and the
third argument `x` must DECOMPOSE as `b g`. So this case cannot recur indefinitely either: it
replaces the third argument by a strictly smaller one. -/
theorem app3_S_as_root_reduct {a b c f g x : Term}
    (h : app (app a c) (app b c) = app3 Term.S f g x) :
    a = app Term.S f ∧ c = g ∧ x = app b g := by
  simp only [app3, Term.app.injEq] at h
  obtain ⟨⟨ha, hc⟩, hx⟩ := h
  exact ⟨ha, hc, by rw [← hx, hc]⟩

/-- The three places `S f g x` can come from, with the second and third refined by the two lemmas
above. This is the case list a proof of `¬ HalfShape` has to discharge. -/
theorem app3_S_subterm_step_cases {v' v f g x : Term} (h : v' ⟶ v)
    (hs : Subterm (app3 Term.S f g x) v) :
    Subterm (app3 Term.S f g x) v'
      ∨ (∃ u, Subterm u v' ∧ (u ⟶ app3 Term.S f g x))
      ∨ (∃ f' g', Subterm (app3 Term.S f' g' x) v'
          ∧ (f' = app (app Term.S f) g ∨ g' = app (app Term.S f) g)) := by
  rcases h.subterm_split' hs with h1 | h2 | ⟨f', g', x', hsub, hshape⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨hx, hfg⟩ := app3_S_reduct_half_forces hshape
    exact Or.inr (Or.inr ⟨f', g', hx ▸ hsub, hfg⟩)

-- ## The state of the proof attempt, honestly
-- Backward induction along the path is the right frame: every case of the trichotomy steps back
-- exactly one reduction, the path is finite, and at its start the requirement must be a subterm of
-- `t` itself — which size forbids, since `S f g x` outweighs `t = f x` by `1 + |g|`. So the
-- argument needs an invariant on the requirement that survives all three cases and contradicts
-- "subterm of t". The natural one is `|requirement| > |t|`, and it survives three of four
-- sub-cases:
--
--   * inherited — same requirement, invariant unchanged;
--   * one half of a bigger redex — `app3_S_reduct_half_grows`, requirement grows by ≥ 2;
--   * produced by a ROOT redex — `app3_S_as_root_reduct` forces the redex to `S (S f) b g` with
--     `x = b g`, and `|S (S f) b g| = |t| + 2` exactly, so the invariant holds and the third
--     argument strictly shrinks;
--   * produced by a step INSIDE it — `u = p x` with `p ⟶ (S f) g`, or `u = ((S f) g) q` with
--     `q ⟶ x`. HERE THE INVARIANT CAN FAIL: pure-S reduction grows, so `p` may be far lighter
--     than `(S f) g`, and nothing yet stops `|u|` from dropping to `|t|` or below.
--
-- That last sub-case is the whole remaining gap, and it is a smaller gap than "prove `HalfShape`
-- uninhabited" was: it asks only whether a term at or below `t`'s size can reduce, at its own
-- root position, into `S f g x`'s left spine. I do not have that argument, and I am not going to
-- claim the three controlled cases as most of a proof — the uncontrolled one is where reduction's
-- growth lives, which is where every hard case in this development has lived.
