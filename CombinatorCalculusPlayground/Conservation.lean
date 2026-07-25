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
