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
@[reducible] def RS.Countdown : RS := ⟨Nat, fun a b => a = b + 1⟩

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

-- ## Where adequacy stands — SETTLED (Stage 48)
-- `RS.bwd_of_abstraction_rel` needs `habs`, `hfun` and `hstep`. The first two are above. `hstep`
-- splits by `Step.kOrS` into two cases and both are now closed:
--
--   * K-step — `IsKNF.of_kstep`: a K-step does not move the K-normal form, so the abstraction
--     stutters. Nothing encoding-specific in it. This is the case Stage 45's whole mechanism existed
--     to handle, and it is a theorem rather than 20386 measurements.
--   * S-step — `sk_square` plus `itower_sStep`: the square's S-side lands on `Itower n` itself
--     (stutter) or one S-step past it, and an S-step out of `Itower n` can only fire an `I` layer,
--     whose reduct K-collapses to `Itower (n-1)` (advance).
--
-- Stage 47's `naive_kdev_commutation_fails` was right that the cheap route is unavailable; the square
-- is what replaced it, and both of its weakenings turned out to be forced — zero S-steps on the K-side
-- when the S-redex sits in a discarded argument, two K-steps on the S-side when the S-step duplicated
-- a K-redex.

-- Anchors: the encoding is injective and its states really are distinct host terms.
#guard Itower 0 = S
#guard Itower 3 = Term.app I (Term.app I (Term.app I S))
#guard (List.range 6).map (fun n => leafCount (Itower n)) = [1, 4, 7, 10, 13, 16]
#guard Itower 2 != Itower 3

-- ## Stage 48: the S-step case, and the Simulation
-- The commutation square (`sk_square`) supplies the missing half. Its S-side output is `Itower n`
-- itself or one S-step past it, and an S-step out of `Itower n` is completely determined: it can only
-- fire an `I` layer, whose reduct K-collapses to `Itower (n-1)`.

/-- **An S-step out of the encoding advances it by exactly one.** `Itower n`'s only redexes are its
`I` layers, and firing one leaves `(K u)(K u)`, which K-reduces to `u`. -/
theorem itower_sStep : ∀ {n : Nat} {c : Term}, SStep (Itower n) c →
    ∃ m, n = m + 1 ∧ KSteps c (Itower m) := by
  intro n
  induction n with
  | zero => intro c h; cases h
  | succ n ih =>
      intro c h
      cases h with
      | S_red => exact ⟨n, rfl, KSteps.single (KStep.K_red _ _)⟩
      | appL hl => exact absurd ⟨_, hl⟩ sNormalForm_I
      | appR hr =>
          obtain ⟨m, hm, hk⟩ := ih hr
          exact ⟨m + 1, by omega, KSteps.congR hk⟩

/-- `dec_enc`: the syntactic I-layer count inverts the encoder. -/
theorem naiveAbs_Itower : ∀ n, naiveAbs (Itower n) = some n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show (naiveAbs (Itower n)).map (· + 1) = some (n + 1)
      rw [ih]
      rfl

/-- **`hstep`, complete.** Split by `Step.kOrS`: a K-step cannot move the K-normal form, and an
S-step either dies in a doomed subterm (stutter) or advances the count by one. -/
theorem countdown_hstep {b b' : Term} {n : Nat} (hs : b ⟶ b') (habs : absKNF b n) :
    absKNF b' n ∨ ∃ m, RS.Countdown.step n m ∧ absKNF b' m := by
  rcases hs.kOrS with hk | hsS
  · exact Or.inl (habs.of_kstep hk)
  · obtain ⟨c', hc1, hc2⟩ := sk_square habs.1 hsS
    rcases hc2 with hadv | heq
    · obtain ⟨m, hm, hk⟩ := itower_sStep hadv
      exact Or.inr ⟨m, hm, ⟨KSteps.trans hc1 hk, kNormalForm_Itower m⟩⟩
    · subst heq
      exact Or.inl ⟨hc1, kNormalForm_Itower n⟩

/-- **A `Simulation` of a genuine multi-step machine inside SK.** Every piece is now a theorem:
`fwd` is two host steps per source step, and `bwd` comes from the relational adequacy machinery with
the abstraction that reads a term's K-normal form — blind to doomed subterms, and provably not blind
to progress.

This is what Stage 8 flagged as piece (vi), the one that could fail in kind rather than in volume. It
took Stage 10 to find the failure, Stage 13 to refute the first two fixes, Stage 45 to find the third,
Stage 46 to make it well defined, and Stages 47–48 to prove it. -/
def countdownInSK : Simulation RS.Countdown RS.SK where
  enc := Itower
  dec := naiveAbs
  dec_enc := naiveAbs_Itower
  fwd := by
    intro a a' h
    subst h
    exact RS.SK_steps_iff.mpr (itower_fwd a')
  bwd := by
    intro a a' h
    exact RS.bwd_of_abstraction_rel (A := RS.Countdown) (B := RS.SK)
      Itower absKNF absKNF_enc absKNF_functional countdown_hstep h

-- Non-triviality, so this is not the diagonal instance the Stage 8 negative controls rule out: the
-- carriers differ, the encoder is not an inclusion, and one source step really is several host steps.
#guard naiveAbs (Itower 4) = some 4
example : RS.Countdown.step (4 : Nat) (3 : Nat) := rfl
example : Itower 4 ⟶* Itower 3 := itower_fwd 3
#guard leafCount (Itower 4) = 13

/-- The taxonomy therefore certifies a genuine multi-step machine inside SK. Stated for the record,
and with its limit stated too: the COUNTDOWN is not universal, so this does not discharge criterion
(a) — it discharges the mechanism criterion (a) was blocked on. -/
theorem universalReach_countdown_SK : UniversalReach RS.Countdown RS.SK :=
  ⟨countdownInSK⟩

-- The encoder is injective as a consequence of `dec_enc`, which is what stops this from being the
-- degenerate instance the Stage 8 negative controls exclude.
example {m n : Nat} (h : Itower m = Itower n) : m = n := countdownInSK.enc_injective h

-- ## Stage 49: what the K-normal-form abstraction demands of a driver
-- Stage 48's ranking said piece (v) could follow the countdown's pattern "provided the driver keeps
-- its data K-normal". That is too optimistic, and the tree already contained the theorem that says
-- so. `RS.abstraction_tracks_rel` forces the abstraction to be defined at EVERY reachable host term,
-- not just at encodings — so the constraint is not on the driver's data, it is on its INTERMEDIATES.

/-- **The design constraint on any driver, forced.** If the K-normal-form abstraction discharges
`hstep`, then every host term reachable from an encoded state has a K-normal form that is itself an
encoding — of a source state reachable from the original. A driver whose intermediate states
K-normalise to anything else cannot use this abstraction, however normal its data is. -/
theorem knf_abstraction_forces_encodings {A : RS} (enc : A.Carrier → Term)
    (hstep : ∀ {b b' : Term} {a : A.Carrier}, (b ⟶ b') → IsKNF b (enc a) →
      IsKNF b' (enc a) ∨ ∃ a', A.step a a' ∧ IsKNF b' (enc a'))
    (hnorm : ∀ a, KNormalForm (enc a))
    {a : A.Carrier} {b : Term} (h : enc a ⟶* b) :
    ∃ a₂, A.Steps a a₂ ∧ IsKNF b (enc a₂) :=
  RS.abstraction_tracks_rel (A := A) (B := RS.SK) (fun b a => IsKNF b (enc a)) hstep
    (RS.SK_steps_iff.mpr h) a (isKNF_self (hnorm a))

-- The countdown satisfies it, and the measurement shows how STRONG the property is: the whole
-- reachable set collapses onto the handful of encodings. (Unverified census tooling — `kNorm`.)
def isItower (t : Term) : Bool := (List.range 10).any (fun m => t == Itower m)

def knfAllEncodings (bound fuel : Nat) (t : Term) : Bool :=
  match boundedClosure bound fuel [t] with
  | none => false
  | some cl => cl.all (fun b => isItower (kNorm (leafCount b) b))

-- 183 reachable terms from `Itower 3`, and every one of them K-normalises to an encoding.
#guard ((boundedClosure 30 120 [Itower 3]).getD []).length = 183
#guard (List.range 4).all (fun n => knfAllEncodings 30 120 (Itower n))
-- ...and to nothing but the four states reachable from 3: leaf counts 10, 7, 4, 1 = 3n+1.
#guard (((boundedClosure 30 120 [Itower 3]).getD []).map
  (fun b => leafCount (kNorm (leafCount b) b))).eraseDups = [10, 7, 4, 1]

-- ## What piece (v) therefore needs, and what it does not
-- The correction matters because it changes the shape of the remaining work. The countdown's driver
-- does its whole step in ONE S-step followed by K-reduction, which is why every intermediate
-- K-normalises to the after-state. A tag-step driver has to inspect a symbol and dispatch, and each
-- of those S-steps produces an intermediate that must ALSO K-normalise to an encoding — before-state
-- for the early ones, after-state for the later ones, flipping exactly once.
--
-- That is a real constraint and it is not obviously satisfiable; it is also not obviously
-- unsatisfiable, since combinator programming has enough freedom to hide work inside K-discards.
-- What is now clear is that it is the thing to PROTOTYPE before writing a driver — the same lesson
-- Stage 8 learned about piece (vi), arriving one piece later.
--
-- Two honest consequences:
--   * "adequacy has a template" (Stage 48) is right about the MACHINERY and wrong if read as "the
--     remaining work is construction". The template comes with a side condition that the countdown
--     satisfies for a reason the countdown alone explains.
--   * a driver could instead use a DIFFERENT abstraction. Nothing here says the K-normal-form one is
--     the only option; it says what that one costs. `RS.bwd_of_abstraction_rel` takes any relation.
