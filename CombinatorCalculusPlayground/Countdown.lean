--! # The countdown machine, and how much of its adequacy is now certified
-- Stage 45 found the mechanism for `bwd`: abstract a host term by reading its K-NORMAL FORM, so
-- that doomed subterms — and any drift inside them — are invisible. Stage 46 made "the K-normal
-- form" denote (`knf_unique`) and settled the K-step case (`IsKNF.of_kstep`).
--
-- This file assembles what that gives for the probe's own test machine, the countdown
-- `Itower n = I (I (… S))`, and states exactly what is left.
--
-- The abstraction is relational — `absKNF b n` says the K-normal form of `b` is `Itower n` — because
-- `RS.bwd_of_abstraction_rel` takes a relation and because "the K-normal form of" is a relation this
-- development can reason about, while the fuel-based `kNorm` census tooling is not certified.
import CombinatorCalculusPlayground.KConfluence
import CombinatorCalculusPlayground.AdequacyProbe

open Term

/-- The countdown: `n+1` steps to `n`, and `0` is normal. Known-universal it is not — it is the
smallest source that is a genuine MULTI-STEP machine rather than an inclusion, which is what the
probe needed. -/
def RS.Countdown : RS := ⟨Nat, fun a b => a = b + 1⟩

theorem leafCount_Itower : ∀ n, leafCount (Itower n) = 3 * n + 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show leafCount I + leafCount (Itower n) = 3 * (n + 1) + 1
      rw [ih]
      show 3 + (3 * n + 1) = 3 * (n + 1) + 1
      omega

theorem Itower_injective {m n : Nat} (h : Itower m = Itower n) : m = n := by
  have h1 := leafCount_Itower m
  have h2 := leafCount_Itower n
  rw [h] at h1
  omega

/-- **The encoding is K-normal.** So the abstraction reads it unchanged, which is `habs`. It matters
that `I` itself is K-normal (`kNormalForm_I`): if the abstraction could K-reduce an `I` layer it
would advance the machine while claiming to observe it. -/
theorem kNormalForm_Itower : ∀ n, KNormalForm (Itower n) := by
  intro n
  induction n with
  | zero => exact kNormalForm_S
  | succ n ih =>
      show KNormalForm (Term.app I (Itower n))
      rintro ⟨u, hu⟩
      cases hu with
      | appL h => exact kNormalForm_I ⟨_, h⟩
      | appR h => exact ih ⟨_, h⟩

/-- The abstraction: `b` stands for countdown state `n` when `b`'s K-normal form is `Itower n`. -/
def absKNF (b : Term) (n : Nat) : Prop := IsKNF b (Itower n)

/-- `habs` — the abstraction relates every encoded state to itself. -/
theorem absKNF_enc (n : Nat) : absKNF (Itower n) n := isKNF_self (kNormalForm_Itower n)

/-- `hfun` — and to nothing else. This is the obligation that killed the joinability abstraction
(`RS.joinable_abs_not_functional`); reading the K-normal form passes it, because K-normal forms are
unique and `Itower` is injective. -/
theorem absKNF_functional {m n : Nat} (h : absKNF (Itower m) n) : m = n :=
  Itower_injective ((absKNF_enc m).unique h)

/-- `fwd` — one countdown step is two host steps: `I t ⟶ (K t)(K t) ⟶ t`. -/
theorem itower_fwd (n : Nat) : Itower (n + 1) ⟶* Itower n :=
  Steps.tail (Step.S_red K K (Itower n))
    (Steps.tail (Step.K_red (Itower n) (Term.app K (Itower n))) (Steps.refl _))

-- ## Where adequacy stands
-- `RS.bwd_of_abstraction_rel` needs `habs`, `hfun` and `hstep`. The first two are above. `hstep`
-- splits by `Step.kOrS`:
--
--   * K-step — DONE, and with nothing encoding-specific in it: `IsKNF.of_kstep` says a K-step does
--     not move the K-normal form, so the abstraction stutters. That is the case Stage 45's whole
--     mechanism existed to handle, and it is now a theorem rather than 20386 measurements.
--   * S-step — OPEN. This is the half that is genuinely about the machine.
--
-- The S-step obligation, stated exactly:
--
--     SStep b b' → IsKNF b (Itower n) →
--       IsKNF b' (Itower n) ∨ ∃ m, n = m + 1 ∧ IsKNF b' (Itower m)
--
-- and `naive_kdev_commutation_fails` (KConfluence.lean) already rules out the cheap route to it.
-- The true shape is a commutation square — an S-step followed by K-reduction, not an S-step between
-- K-normal forms — because an S-reduct can itself be a K-redex and collapse further.
--
-- Two things make the remaining case narrower than it looks, and both are worth recording:
--   * `Itower n` is K-normal AND its only redexes are the `I` layers' S-redexes, so the right-hand
--     side of the square is highly constrained.
--   * An S-step inside a doomed subterm cannot change the K-normal form at all, which is the
--     stuttering half; only S-steps in LIVE position can advance, and K-reduction never duplicates,
--     so a live S-redex corresponds to exactly one S-redex downstream.
-- Neither is proved here. What is proved is that the obligation has been reduced to one case, that
-- the case is about S-steps only, and that the encoding satisfies everything else the interface asks
-- for.

-- Anchors: the encoding is injective and its states really are distinct host terms.
#guard Itower 0 = S
#guard Itower 3 = Term.app I (Term.app I (Term.app I S))
#guard (List.range 6).map (fun n => leafCount (Itower n)) = [1, 4, 7, 10, 13, 16]
#guard Itower 2 != Itower 3
