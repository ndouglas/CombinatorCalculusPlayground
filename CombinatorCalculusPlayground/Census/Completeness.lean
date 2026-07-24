--! # A verified enumerator, and C1's minimality half
-- Since Slice 1 the program has carried a blocked chain: `sTerms`-
-- completeness (`∀ t, KFree t → t ∈ sTerms (leafCount t)`) does not exist,
-- because `sTermsTable`'s `Id.run do`/`Array`/range-loop definition is not
-- `rfl`/`decide`/`simp`-transparent — even `sTerms 1 = [S]` fails to close
-- by plain `rfl`. Three prior attempts died there.
--
-- This module takes the OTHER route the blocked-chain note suggested:
-- rather than making the imperative enumerator transparent, add a
-- structurally-recursive one and prove both directions about IT
-- (`enum_sound`, `enum_complete`). The imperative `sTerms` stays exactly
-- as it is, for census performance, and the two are tied together by
-- `#guard` so the verified enumerator is not a parallel universe.
--
-- What that buys, and it is more than a lemma: C1 as written bundles two
-- independent claims — EXISTENCE (some pure-S term diverges) and
-- MINIMALITY (none with ≤ 6 leaves does, so 7 is the floor). Completeness
-- closes the minimality half outright (`no_small_divergence`), because
-- minimality is a FINITE claim: 65 terms, each normalizing in ≤ 4 steps.
-- Existence remains open and untouched.
import CombinatorCalculusPlayground.Census.Enumerate

open Term

-- ## The enumerator
-- `enum d n` lists the K-free terms with exactly `n` leaves, provided the
-- depth budget `d` is at least `n`. The budget exists only to make the
-- recursion structural: splitting `n+2` into `k + (n+2-k)` calls back at
-- two smaller sizes, and Lean cannot see from `List.range` alone that both
-- are smaller — but it can see that `d` decreases.

def enum : Nat → Nat → List Term
  | _, 0 => []
  | _, 1 => [Term.S]
  | 0, _ => []
  | d + 1, n + 2 =>
    (List.range (n + 1)).flatMap fun i =>
      (enum d (i + 1)).flatMap fun l =>
        (enum d (n + 1 - i)).map fun r => Term.app l r

-- Unfold lemmas. The first two hold for EVERY budget, which is what lets
-- the completeness proof handle the leaf case without casing on `d`.
@[simp] theorem enum_zero (d : Nat) : enum d 0 = [] := by
  cases d <;> rfl

@[simp] theorem enum_one (d : Nat) : enum d 1 = [Term.S] := by
  cases d <;> rfl

theorem enum_succ (d n : Nat) :
    enum (d + 1) (n + 2) =
      (List.range (n + 1)).flatMap fun i =>
        (enum d (i + 1)).flatMap fun l =>
          (enum d (n + 1 - i)).map fun r => Term.app l r := rfl

-- ## Soundness: nothing spurious is enumerated
theorem enum_sound : ∀ (d n : Nat) {t : Term},
    t ∈ enum d n → KFree t ∧ leafCount t = n := by
  intro d
  induction d with
  | zero =>
    intro n t ht
    match n, ht with
    | 1, ht =>
      have : t = Term.S := by simpa using ht
      exact ⟨this ▸ KFree.S, by simp [this, leafCount]⟩
  | succ d ih =>
    intro n t ht
    match n with
    | 0 => simp at ht
    | 1 =>
      have : t = Term.S := by simpa using ht
      exact ⟨this ▸ KFree.S, by simp [this, leafCount]⟩
    | m + 2 =>
      rw [enum_succ] at ht
      obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨l, hl, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨r, hr, hEq⟩ := List.mem_map.mp ht
      obtain ⟨hkl, hcl⟩ := ih (i + 1) hl
      obtain ⟨hkr, hcr⟩ := ih (m + 1 - i) hr
      have hilt : i < m + 1 := List.mem_range.mp hi
      subst hEq
      refine ⟨KFree.app hkl hkr, ?_⟩
      show leafCount l + leafCount r = m + 2
      omega

-- ## Completeness: THE lemma the chain was blocked on
-- Every K-free term appears in the enumeration at its own leaf count, as
-- soon as the budget is large enough to reach it.
theorem enum_complete : ∀ {t : Term}, KFree t →
    ∀ d, leafCount t ≤ d → t ∈ enum d (leafCount t) := by
  intro t
  induction t with
  | S => intro _ d _; simp [leafCount]
  | K => intro hk; cases hk
  | app l r ihl ihr =>
    intro hk d hd
    cases hk with
    | app hkl hkr =>
      have hl1 := leafCount_pos l
      have hr1 := leafCount_pos r
      have hsum : leafCount (Term.app l r) = leafCount l + leafCount r := rfl
      -- The budget is at least 2, so it has a predecessor. Written with an
      -- explicit witness rather than `cases d <;> omega`: letting `omega`
      -- discharge a NON-arithmetic goal (this existential) from
      -- contradictory hypotheses pulls in `Classical.choice`, which would
      -- be the tree's first use of it. Same care as Slice 2's choice-free
      -- τ decrease.
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 :=
        ⟨d - 1, (Nat.succ_pred_eq_of_pos (by rw [hsum] at hd; omega)).symm⟩
      -- and the size is at least 2, so it has the shape m+2
      obtain ⟨m, hm⟩ : ∃ m, leafCount l + leafCount r = m + 2 :=
        ⟨leafCount l + leafCount r - 2, by omega⟩
      rw [hsum, hm, enum_succ]
      -- split at i = |l| - 1
      refine List.mem_flatMap.mpr ⟨leafCount l - 1, List.mem_range.mpr ?_, ?_⟩
      · rw [hsum] at hd; omega
      refine List.mem_flatMap.mpr ⟨l, ?_, ?_⟩
      · have : leafCount l - 1 + 1 = leafCount l := by omega
        rw [this]
        exact ihl hkl d' (by rw [hsum] at hd; omega)
      refine List.mem_map.mpr ⟨r, ?_, rfl⟩
      · have : m + 1 - (leafCount l - 1) = leafCount r := by omega
        rw [this]
        exact ihr hkr d' (by rw [hsum] at hd; omega)

/-- The canonical call: budget equal to the size. -/
def enumAt (n : Nat) : List Term := enum n n

theorem mem_enumAt_iff {t : Term} {n : Nat} :
    t ∈ enumAt n ↔ (KFree t ∧ leafCount t = n) := by
  constructor
  · exact enum_sound n n
  · rintro ⟨hk, rfl⟩
    exact enum_complete hk _ (Nat.le_refl _)

-- ## Tied to the census tooling
-- The verified enumerator is not a parallel universe: it agrees with the
-- `sTerms` the census actually ran, at every size the census reported.
#guard (List.range 8).all (fun n => (enumAt n).length = (sTerms n).length)
#guard (List.range 8).all (fun n =>
  (enumAt n).all (fun t => (sTerms n).contains t))
#guard (List.range 8).all (fun n =>
  (sTerms n).all (fun t => (enumAt n).contains t))
#guard (enumAt 6).length = 42
#guard (enumAt 7).length = 132

-- ## C1's minimality half
-- The census observed that every pure-S term with ≤ 6 leaves normalizes.
-- With completeness that observation becomes a theorem, because the claim
-- is finite: 65 terms (1+1+2+5+14+42), each reaching a normal form in at
-- most 4 leftmost-outermost steps, so fuel 10 is ample.

/-- Decidable finite content of the minimality claim: everything the
enumerator produces at sizes 0..6 normalizes within fuel 10. -/
def smallAllNormalize : Bool :=
  (List.range 7).all (fun n => (enumAt n).all (fun t => (normalize 10 t).isSome))

theorem smallAllNormalize_true : smallAllNormalize = true := by decide

/-- **C1(b), MINIMALITY — PROVED.** No K-free term with at most 6 leaves
diverges: every one of them reaches a genuine normal form. So IF a
non-normalizing pure-S term exists, its leaf count is at least 7 — which is
exactly the floor the census observed and could not prove.

SCOPE, stated at the theorem: this is minimality ONLY. It does not show
that any pure-S term diverges; C1's existence half (`c1` and its
trajectory) is untouched and remains open. -/
theorem no_small_divergence {t : Term} (hk : KFree t) (h : leafCount t ≤ 6) :
    ∃ u, (t ⟶* u) ∧ NormalForm u := by
  -- completeness places t in the enumeration at its own size
  have hmem : t ∈ enumAt (leafCount t) := mem_enumAt_iff.mpr ⟨hk, rfl⟩
  -- the decided check applies to that size
  have hn : leafCount t ∈ List.range 7 := List.mem_range.mpr (by omega)
  have hall := (List.all_eq_true.mp smallAllNormalize_true) _ hn
  have := (List.all_eq_true.mp hall) t hmem
  -- turn a normalize success into a certified normal form
  match hres : normalize 10 t with
  | some (u, k) =>
    exact ⟨u, normalize_sound 10 hres, normalize_normal 10 hres⟩
  | none => rw [hres] at this; simp at this

-- Nontriviality: the theorem has real content at a real term. `S S S S`
-- is K-free with 4 leaves, so it lands in scope and comes back with a
-- normal form — the same reduction Stage 2 uses as its worked example.
example : ∃ u, (app3 S S S S ⟶* u) ∧ NormalForm u :=
  no_small_divergence
    (KFree.app (KFree.app (KFree.app KFree.S KFree.S) KFree.S) KFree.S)
    (by decide)

-- (The bound is not idly chosen: the C1 candidate sits exactly one leaf
-- above it. That tie-in is guarded in Reachability.lean, where `c1` is
-- defined — Census must not depend upward on it.)

/-- Contrapositive, in the shape C1(a) will need: a diverging pure-S term
must have at least 7 leaves. -/
theorem seven_is_the_floor {t : Term} (hk : KFree t)
    (hdiv : ¬ ∃ u, (t ⟶* u) ∧ NormalForm u) : 7 ≤ leafCount t := by
  -- `by_contra` is a Mathlib tactic; core's Nat trichotomy does the job.
  match Nat.lt_or_ge (leafCount t) 7 with
  | .inl hlt => exact absurd (no_small_divergence hk (by omega)) hdiv
  | .inr hge => exact hge
