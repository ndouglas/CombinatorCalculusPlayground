--! # A certified finite universe of SK terms
-- `Census/Completeness.lean` builds `enumAt`/`smallTerms`, the finite universe that Goal 3's
-- decidability layer runs on. It enumerates K-FREE terms only, because it was built for pure S and pure S
-- is where the north star lives.
--
-- Stage 56 left route two's adequacy chain needing the same thing for full SK: the reachable set of the
-- countdown's encoding is now known finite (`itower_reduct_bound`, `3·2^m − 2`), but "finite" only becomes
-- "decidable" against a certified enumeration of the bounded universe, and `Itower` is built from
-- `I = S K K`.
--
-- So this file is `Completeness.lean`'s enumerator with one line changed — the leaf case lists `K` as well
-- as `S` — and the K-freeness clause dropped from soundness. Everything else is the same argument, which
-- is the point: the restriction was never structural, only inherited from what the census needed.
import CombinatorCalculusPlayground.Census.Completeness

open Term

/-- `skEnum d n` lists the SK terms with exactly `n` leaves, provided the depth budget `d` is at least
`n`. The budget exists only to make the recursion structural, exactly as in `enum`. -/
def skEnum : Nat → Nat → List Term
  | _, 0 => []
  | _, 1 => [Term.S, Term.K]
  | 0, _ => []
  | d + 1, n + 2 =>
    (List.range (n + 1)).flatMap fun i =>
      (skEnum d (i + 1)).flatMap fun l =>
        (skEnum d (n + 1 - i)).map fun r => Term.app l r

@[simp] theorem skEnum_zero (d : Nat) : skEnum d 0 = [] := by cases d <;> rfl

@[simp] theorem skEnum_one (d : Nat) : skEnum d 1 = [Term.S, Term.K] := by cases d <;> rfl

theorem skEnum_succ (d n : Nat) :
    skEnum (d + 1) (n + 2) =
      (List.range (n + 1)).flatMap fun i =>
        (skEnum d (i + 1)).flatMap fun l =>
          (skEnum d (n + 1 - i)).map fun r => Term.app l r := rfl

theorem skEnum_sound : ∀ (d n : Nat) {t : Term}, t ∈ skEnum d n → leafCount t = n := by
  intro d
  induction d with
  | zero =>
    intro n t ht
    match n, ht with
    | 1, ht =>
      have h : t = Term.S ∨ t = Term.K := by simpa using ht
      rcases h with rfl | rfl <;> rfl
  | succ d ih =>
    intro n t ht
    match n with
    | 0 => simp at ht
    | 1 =>
      have h : t = Term.S ∨ t = Term.K := by simpa using ht
      rcases h with rfl | rfl <;> rfl
    | m + 2 =>
      rw [skEnum_succ] at ht
      obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨l, hl, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨r, hr, hEq⟩ := List.mem_map.mp ht
      have hcl := ih (i + 1) hl
      have hcr := ih (m + 1 - i) hr
      have hilt : i < m + 1 := List.mem_range.mp hi
      subst hEq
      show leafCount l + leafCount r = m + 2
      omega

/-- Every SK term appears at its own leaf count, once the budget reaches it. No `KFree` hypothesis —
which is the whole difference from `enum_complete`. -/
theorem skEnum_complete : ∀ (t : Term) (d : Nat), leafCount t ≤ d → t ∈ skEnum d (leafCount t) := by
  intro t
  induction t with
  | S => intro d _; simp [leafCount]
  | K => intro d _; simp [leafCount]
  | app l r ihl ihr =>
    intro d hd
    have hl1 := leafCount_pos l
    have hr1 := leafCount_pos r
    have hsum : leafCount (Term.app l r) = leafCount l + leafCount r := rfl
    -- explicit witnesses rather than `cases d <;> omega`: letting `omega` discharge a non-arithmetic
    -- existential from contradictory hypotheses costs `Classical.choice`, as Slice 2 found
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 :=
      ⟨d - 1, (Nat.succ_pred_eq_of_pos (by rw [hsum] at hd; omega)).symm⟩
    obtain ⟨m, hm⟩ : ∃ m, leafCount l + leafCount r = m + 2 :=
      ⟨leafCount l + leafCount r - 2, by omega⟩
    rw [hsum, hm, skEnum_succ]
    refine List.mem_flatMap.mpr ⟨leafCount l - 1, List.mem_range.mpr ?_, ?_⟩
    · rw [hsum] at hd; omega
    refine List.mem_flatMap.mpr ⟨l, ?_, ?_⟩
    · have h : leafCount l - 1 + 1 = leafCount l := by omega
      rw [h]
      exact ihl d' (by rw [hsum] at hd; omega)
    refine List.mem_map.mpr ⟨r, ?_, rfl⟩
    · have h : m + 1 - (leafCount l - 1) = leafCount r := by omega
      rw [h]
      exact ihr d' (by rw [hsum] at hd; omega)

/-- The canonical call: budget equal to the size. -/
def skEnumAt (n : Nat) : List Term := skEnum n n

theorem mem_skEnumAt_iff {t : Term} {n : Nat} : t ∈ skEnumAt n ↔ leafCount t = n := by
  constructor
  · exact skEnum_sound n n
  · rintro rfl
    exact skEnum_complete t _ (Nat.le_refl _)

/-- **The finite universe of SK terms up to a size bound** — the K-inclusive twin of `smallTerms`. -/
def skSmallTerms (bound : Nat) : List Term :=
  (List.range (bound + 1)).flatMap skEnumAt

theorem mem_skSmallTerms {t : Term} {bound : Nat} (h : leafCount t ≤ bound) :
    t ∈ skSmallTerms bound :=
  List.mem_flatMap.mpr
    ⟨leafCount t, List.mem_range.mpr (by omega), mem_skEnumAt_iff.mpr rfl⟩

theorem skSmallTerms_sound {t : Term} {bound : Nat} (h : t ∈ skSmallTerms bound) :
    leafCount t ≤ bound := by
  obtain ⟨n, hn, ht⟩ := List.mem_flatMap.mp h
  have := mem_skEnumAt_iff.mp ht
  have := List.mem_range.mp hn
  omega

-- Counts: binary trees with n leaves are Catalan(n−1), and each of the n leaves is independently S or K,
-- so `skEnumAt n` has `Catalan(n−1) · 2^n` entries — 2, 4, 16, 80, 448, 2688.
#guard (List.range 7).map (fun n => (skEnumAt n).length) = [0, 2, 4, 16, 80, 448, 2688]
#guard (skEnumAt 4).all (fun t => leafCount t = 4)
#guard (skEnumAt 4).eraseDups.length = 80
#guard (skSmallTerms 4).length = 2 + 4 + 16 + 80
-- and it really does contain terms the K-free universe misses: `I = S K K` has three leaves and is in
-- `skEnumAt 3` but not in `enumAt 3`, which is the entire reason this file exists.
#guard leafCount I = 3
#guard (skEnumAt 3).contains I
#guard !((enumAt 3).contains I)
