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
import CombinatorCalculusPlayground.Universality.Calibration
import CombinatorCalculusPlayground.SKDecidability

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

-- ## Stage 50: prototyping the intermediate condition — dispatch passes, recursion does not
-- Stage 49 established that the K-normal-form abstraction demands every reachable intermediate
-- K-normalise to an encoding, and said to prototype that before writing a driver. Here is the
-- prototype. The diagnostic is a RATIO: along one source step's trajectory the abstraction can
-- tolerate at most TWO distinct K-normal forms — the before-state and the after-state — so a
-- construct whose reachable set produces more than that per step cannot be tracked.

/-- The K-normal form, via the unverified normaliser; and the set of them over a reachable set.
Census tooling. -/
def knfOf (t : Term) : Term := kNorm (leafCount t) t

def knfCount (bound fuel : Nat) (t : Term) : Nat × Nat :=
  match boundedClosure bound fuel [t] with
  | none => (0, 0)
  | some cl => (cl.length, (cl.map knfOf).eraseDups.length)

-- Booleans, the usual way: `K` selects the first branch, `S K` the second.
def tru : Term := K
def fls : Term := app S K

-- **Dispatch passes, and passes exactly.** `S K a b` has three reachable terms and precisely TWO
-- K-normal forms: itself (the before-state) and `b` (the selected branch). The intermediate
-- `(K b)(a b)` collapses onto `b`, and the doomed branch `a b` vanishes with it. That is the
-- flip-once behaviour the abstraction wants, arising natively from the dispatch idiom.
#guard knfCount 30 100 (app2 tru (app S S) (app K K)) = (2, 1)
#guard knfCount 30 100 (app2 fls (app S S) (app K K)) = (3, 2)

-- The countdown, for scale: 183 reachable terms collapse onto 4 K-normal forms — its 4 encodings.
#guard knfCount 30 120 (Itower 3) = (183, 4)

-- **Self-application does not.** `omegaSK = (S I I)(S I I)` is the tree's minimal recursive object.
-- Its reachable set is SMALLER than the countdown's and its K-normal forms are four times as many,
-- sprawling into nested `S K K (…)` shapes rather than collapsing.
#guard knfCount 40 60 omegaSK = (107, 17)

-- ## What the prototype settles
-- The blocker for piece (v) is RECURSION, not dispatch — which corroborates with numbers what
-- Stages 11 and 13 flagged in prose about the pending recursive call. Dispatch was the part I would
-- have expected to fight, and it comes for free: selecting a branch is one S-step whose reduct is a
-- K-redex, so it commits immediately and shows the abstraction exactly two states.
--
-- The honest limit of this measurement: `omegaSK` is not a driver and has no source machine, so
-- seventeen K-normal forms is not a refutation. A real driver's seventeen could in principle all be
-- encodings of reachable source states — the abstraction is allowed to stutter across many host terms.
-- What the ratio shows is a TREND in the wrong direction: the countdown's set collapses as the closure
-- grows, `omegaSK`'s does not.
--
-- So piece (v) has two routes and this stage says which is which:
--   * keep the K-normal-form abstraction and find a recursion scheme whose intermediates collapse —
--     the driver would have to commit each recursive unfolding through a K-discard, which is a real
--     design constraint and not obviously achievable;
--   * or use a different abstraction. Stage 49 already noted `RS.bwd_of_abstraction_rel` takes an
--     arbitrary relation; the countdown's success does not oblige piece (v) to reuse its choice.
-- Neither is attempted here. What is established is that the difficulty is localised to recursion,
-- and that the dispatching half of a driver is compatible with the machinery already proved.

-- ## Stage 51: committing steps cannot compute, and a conflation corrected
-- Stage 50 ranked "find a recursion scheme that commits each unfolding through a K-discard" first.
-- That phrasing is impossible, and the reason is two lines of injectivity.

/-- An S-step **commits** when its reduct is itself a K-redex — the pattern that shows the abstraction
exactly one flip (Stage 50 measured `S K a b` doing precisely that). It happens only when the first
argument is literally `K`. -/
theorem committing_S_red_iff {f g x a b : Term}
    (h : Term.app (Term.app f x) (Term.app g x) = app2 Term.K a b) :
    f = Term.K ∧ a = x ∧ b = Term.app g x := by
  simp only [app2, Term.app.injEq] at h
  exact ⟨h.1.1, h.1.2.symm, h.2.symm⟩

/-- **...and then the pair of steps is a projection.** `S K g x` reduces to `x`, discarding `g` — and
the duplicate the S-step made sits inside that discarded argument, so it does no work either.

So committing steps cannot compute, and no driver can be built from them alone. Stage 50's route one
is impossible AS PHRASED. What survives is the weaker demand: non-committing S-steps whose
intermediates K-normalise to encodings by some other route. -/
theorem committing_S_red_projects (g x : Term) :
    (app3 Term.S Term.K g x ⟶ app2 Term.K x (Term.app g x))
      ∧ KStep (app2 Term.K x (Term.app g x)) x :=
  ⟨Step.S_red Term.K g x, KStep.K_red x (Term.app g x)⟩

-- ## The conflation, corrected
-- Stage 50 treated "recursion" and "non-termination" as the same thing and tested `omegaSK`. They are
-- not the same, and the countdown proves it: `Itower n` TERMINATES. Its 183 reachable terms come from
-- the many orders in which its `I` layers may fire, not from unbounded computation.
--
-- What a driver actually needs is SELF-REPRODUCTION — the driver term reappearing alongside advanced
-- data, so the next source step can run — with each segment finite. So the question is not whether a
-- non-terminating term can collapse; it is whether a self-reproducing one can.
--
-- And collapse is NOT rare. Searching self-applications `A A` with `|A| ≤ 5` found four that collapse,
-- the best at 47 reachable terms over 3 K-normal forms:

def bestCollapse : Term := Term.app (app2 S (app S K) (app K S)) (app2 S (app S K) (app K S))

#guard leafCount bestCollapse = 10
#guard knfCount 26 80 bestCollapse = (47, 3)
-- ...and it TERMINATES in four steps, which is the point: collapse coexists with bounded work.
#guard ((trace 30 bestCollapse).map leafCount) = [10, 14, 20, 7, 1]

-- ## Why the searches could not settle it, which is worth more than the searches
-- Neither sweep answered the question, and both failures were about CONTROLS.
--   * The all-terms sweep is affordable to six leaves. Its positive control, `Itower 3`, has TEN. So
--     "no collapsing term up to six leaves" says nothing — and indeed collapsing terms turn up at ten.
--     I caught this one by running the control at the search's own setting before believing the zero.
--   * The self-reproduction sweep used `onCycle?` to find self-reproducing terms. `onCycle?` is
--     leftmost-outermost, and Stage 21 PROVED that an LO hunt is blind to cycles that exist in the
--     relation. Sure enough `onCycle? omegaSK 40` returns `false`, even though `omega_to_M` and
--     `M_to_omega` (Calibration.lean) are theorems putting `omegaSK` on a cycle. So the probe was
--     blind to its own control, and the smallest cycle is fourteen leaves — beyond exhaustive reach
--     anyway. Two independent reasons the zero meant nothing.
#guard (onCycle? omegaSK 40) == some false   -- the Stage 21 blind spot, on the one term that matters
#guard leafCount omegaSK = 14

-- The transferable lesson is the one Stage 41 wrote down and I did not apply here: when a probe has a
-- parameter, the finding is about the parameter — and a probe with a KNOWN blind spot must be run
-- against a control that exercises it. I used a detector this tree had already proved unreliable for
-- exactly this purpose.

-- ## Stage 52: the diagnostic needs a source machine — correcting Stage 50
-- Stage 50 concluded "dispatch passes, recursion does not" from K-normal-form counts. Half of that was
-- an unfounded inference, and constructing the self-reproducing prototype Stage 51 called for is what
-- exposed it.
--
-- The diagnostic says: along one SOURCE step the abstraction tolerates at most two K-normal forms. To
-- apply it one must know how many source steps a host trajectory covers — and `omegaSK` encodes nothing,
-- so its seventeen K-normal forms cannot be compared to anything. Seventeen would be perfectly fine for
-- a machine with seventeen reachable states. **Stage 50's recursion verdict does not follow from its
-- measurement.** Its dispatch verdict does: `S K a b` selects between two branches, the source is a
-- two-state selection, and two K-normal forms is exactly right.
--
-- What the numbers do show is a difference in KIND, and it is suggestive rather than decisive.

-- The countdown's K-normal forms shrink monotonically along its trajectory — the signature of a source
-- that only ever moves forward.
#guard ((trace 30 (Itower 3)).map (fun t => leafCount (knfOf t))).eraseDups = [10, 7, 4, 1]

-- `omegaSK`'s oscillate and revisit values, which would force the source to cycle.
#guard ((trace 20 omegaSK).map (fun t => leafCount (knfOf t)))
  = [14, 20, 17, 17, 26, 23, 23, 20, 20, 32, 29, 29, 26, 26, 23, 23, 38, 35, 35, 32, 32]
#guard (((trace 20 omegaSK).map knfOf).eraseDups).length = 13

-- ## The methodological finding, which is this stage's real output
-- "Prototype the obligation before building the artifact" has been the winning habit for six stages.
-- Stage 52 is the first time it does not apply, and the precondition is now explicit: **the diagnostic
-- must be interpretable without the artifact.** Here it is not — "how many K-normal forms is too many"
-- is a question about the source machine, so it cannot be answered before there is one. Route one can
-- only be tested by building a driver, which is the work the prototype was meant to de-risk.
--
-- That leaves route two, and Stage 49 already noted it is untouched by any of this:
-- `RS.bwd_of_abstraction_rel` takes an ARBITRARY relation, and nothing obliges piece (v) to reuse the
-- countdown's choice of one. The trajectory relation — "b lies on the host segment for source state w" —
-- is the obvious candidate and has not been examined. It is also the honest next step, because unlike
-- route one it can be designed and checked without first building the driver.

-- ## Stage 53: route two — the trajectory relation
-- Stage 49 noted that `RS.bwd_of_abstraction_rel` takes an ARBITRARY relation, so nothing obliges a
-- driver to reuse the countdown's K-normal-form abstraction. The obvious alternative is the trajectory
-- relation: `b` stands for `w` when `b` lies on the host segment belonging to `w`. Unlike route one it
-- can be designed and checked before any driver exists — which is why Stage 52 pivoted here.
--
-- The definition has to say "not yet past `w`", or it degenerates. Plain reachability in either
-- direction fails `hfun` immediately, and for the same reason joinability did: the countdown's
-- encodings are linearly ordered by reachability, so any bare reachability relation confuses them.

/-- `b` is reachable from `enc w`, and not yet reachable from the encoding of any successor of `w`. -/
def OnSegment {A : RS} (enc : A.Carrier → Term) (b : Term) (w : A.Carrier) : Prop :=
  (enc w ⟶* b) ∧ ∀ w', A.step w w' → ¬ (enc w' ⟶* b)

/-- The countdown's instance, named because `A` is not inferable from `Nat` alone. -/
def onSeg (b : Term) (w : Nat) : Prop := OnSegment (A := RS.Countdown) Itower b w

theorem countdown_steps_le : ∀ {a a' : Nat}, RS.Countdown.Steps a a' → a' ≤ a := by
  intro a a' h
  exact h.rec (fun _ => Nat.le_refl _) (fun {x y _} hs _ ih => by
    have : x = y + 1 := hs
    omega)

/-- Reachability between encodings recovers the source order — via the Stage 48 `Simulation`, whose
`bwd` is exactly this statement transported. -/
theorem itower_steps_le {w w' : Nat} (h : Itower w ⟶* Itower w') : w' ≤ w :=
  countdown_steps_le (countdownInSK.bwd (RS.SK_steps_iff.mpr h))

/-- `habs` for the trajectory relation. It needs the encoding not to run backwards, which for the
countdown is `itower_steps_le`. -/
theorem onSegment_enc (w : Nat) : onSeg (Itower w) w := by
  refine ⟨Steps.refl _, ?_⟩
  intro w' hs hreach
  have : w = w' + 1 := hs
  have := itower_steps_le hreach
  omega

/-- `fwd` iterated: the encoding reaches every lower state. -/
theorem itower_steps_of_le : ∀ {a k : Nat}, a ≤ k → (Itower k ⟶* Itower a) := by
  intro a k
  induction k with
  | zero =>
      intro h
      have ha : a = 0 := by omega
      subst ha
      exact Steps.refl _
  | succ j ih =>
      intro h
      rcases Nat.lt_or_ge a (j + 1) with hlt | hge
      · exact Steps.trans (itower_fwd j) (ih (by omega))
      · have ha : a = j + 1 := by omega
        subst ha
        exact Steps.refl _

/-- **`hfun` for the trajectory relation — the obligation that killed joinability.** It survives, and
the "not yet past `w`" clause is exactly what makes it survive: reachability alone gives `a ≤ a\'`, and
the clause supplies `a\' ≤ a`. -/
theorem onSegment_functional {a a' : Nat} (h : onSeg (Itower a) a') : a = a' := by
  obtain ⟨hreach, hnot⟩ := h
  have hle : a ≤ a' := itower_steps_le hreach
  cases a' with
  | zero => omega
  | succ k =>
      have hno := hnot k rfl
      have hnk : ¬ (a ≤ k) := fun hak => hno (itower_steps_of_le hak)
      omega

-- ## What route two costs and what it demands
-- `habs` and `hfun` are above, and `hfun` is the one that mattered: it is what killed joinability
-- (`RS.joinable_abs_not_functional`) and what any coarse relation has to survive. The trajectory
-- relation survives it, and the "not yet past `w`" clause is precisely the thing that makes it — bare
-- reachability supplies `a ≤ a'`, the clause supplies `a' ≤ a`.
--
-- `hstep` remains, and unwinding it gives a condition of a completely different character from route
-- one's. If a host step lands on a term reachable from the successor's encoding, tracking it requires
--
--     no single host step reaches past TWO source states,
--
-- i.e. consecutive encodings are at least two host steps apart. For the countdown that is exactly true —
-- `Itower (n+1) ⟶ (K ·)(K ·) ⟶ Itower n` is two steps — and for a driver it is a design property one can
-- arrange and check, not a structural coincidence one has to hope for.
--
-- **The reason this is the promising route.** The trajectory relation says nothing whatever about the
-- SHAPE of intermediates — only about reachability. So Stage 49's constraint, that every intermediate
-- K-normalise to an encoding, simply does not apply to it. That constraint was what made route one look
-- hard and Stage 50–52 unable to test it; route two does not incur it at all.
--
-- The cost, stated so it is not discovered later: the relation quantifies over reachability, so it is not
-- a computation. That is fine for `bwd` — `RS.bwd_of_abstraction_rel` takes an arbitrary relation — but a
-- `Simulation` also needs a decoder FUNCTION, and the trajectory relation does not supply one. The
-- countdown got its decoder from `naiveAbs` independently of the abstraction, and a driver would have to
-- do the same: decode syntactically, track relationally. Those are two separate obligations and route two
-- only discharges the second.

-- Anchors.
example : onSeg (Itower 4) 4 := onSegment_enc 4
example {a : Nat} (h : onSeg (Itower a) 3) : a = 3 := onSegment_functional h
#guard leafCount (Itower 4) = 13

-- ## Stage 54: route two's `hstep` fails for one step and passes for a path
-- Measured before attempting the proof, which was the right order: over the 183 terms reachable from
-- `Itower 3`, single-step `hstep` fails on **36** of them. Stable at closure bounds 26, 30 and 36 with
-- identical saturated closures, so it is not a bound artefact.
--
-- The diagnosis is one example. `K (S K K S) (K (S K K (S K K S)))` sits on segment 3, and it is itself
-- a K-redex whose contraction is `S K K S = I S = Itower 1`. One host step, two source states — segment
-- 2 skipped entirely. Nothing to do with the spacing I hypothesised in Stage 53; the cause is that a
-- K-step can DISCARD a pending computation and arrive early.
--
-- Relaxing `hstep` to advance by a source PATH takes the failures from 36 to **0**. So the trajectory
-- relation was never the problem — `RS.bwd_of_abstraction_rel`'s single-step restriction was, and
-- `RS.bwd_of_abstraction_path` (Defs.lean) removes it. The tracking proof never needed it.
--
-- Note the symmetry with route one, which is the interesting part. The K rule's erasure is what makes
-- the K-normal-form abstraction well behaved — drift inside discarded arguments becomes invisible — and
-- it is the very same erasure that makes the trajectory relation skip states. One mechanism, helping one
-- abstraction and hurting the other.

/-- Route two's remaining obligation, in the form the generalised interface asks for. Measured clean over
the closure of `Itower 3`; not proved, and the measurement is one machine at one size. -/
def OnSegmentHStepPath (A : RS) (enc : A.Carrier → Term) : Prop :=
  ∀ {b b' : Term} {w : A.Carrier}, (b ⟶ b') → OnSegment enc b w →
    OnSegment enc b' w ∨ ∃ w', A.Steps w w' ∧ OnSegment enc b' w'

-- The witness that made the single-step form fail, kept as a guard so the next attempt does not
-- rediscover it: a K-redex on segment three whose contraction is the encoding of state one.
def skipWitness : Term := app2 K (Itower 1) (Term.app K (Itower 2))

#guard leafCount skipWitness = 13
#guard stepOnce skipWitness = some (Itower 1)
#guard Itower 1 = Term.app I S

-- ## Stage 55: the obligation reduces to one fact, and that fact needs strong normalisation
-- Attempting `OnSegmentHStepPath` turns out not to need a case analysis on the step at all. The whole
-- thing follows from the existence of a LEAST segment index, and the stutter case is subsumed rather
-- than handled: if the least index happens to be `w`, the "advance" is the empty path.

theorem countdown_steps_of_le : ∀ {m w : Nat}, m ≤ w → RS.Countdown.Steps w m := by
  intro m w
  induction w with
  | zero =>
      intro h
      have hm : m = 0 := by omega
      subst hm
      exact RS.Steps.refl _
  | succ j ih =>
      intro h
      rcases Nat.lt_or_ge m (j + 1) with hlt | hge
      · exact RS.Steps.tail (show j + 1 = j + 1 from rfl) (ih (by omega))
      · have hm : m = j + 1 := by omega
        subst hm
        exact RS.Steps.refl _

/-- **Route two's obligation, reduced to least-index existence.** Every host term reachable from an
encoding must have a least segment index; given that, `hstep` is four lines and needs neither the
"not yet past `w`" clause of the hypothesis nor any analysis of the step. -/
theorem onSegmentHStepPath_of_least
    (hleast : ∀ (b : Term) (w : Nat), (Itower w ⟶* b) →
      ∃ m, m ≤ w ∧ (Itower m ⟶* b) ∧ ∀ k, m = k + 1 → ¬(Itower k ⟶* b)) :
    OnSegmentHStepPath RS.Countdown Itower := by
  intro b b' w hs hseg
  obtain ⟨hb, _⟩ := hseg
  obtain ⟨m, hmle, hmreach, hmmin⟩ := hleast b' w (hb.trans (Steps.single hs))
  exact Or.inr ⟨m, countdown_steps_of_le hmle, hmreach, hmmin⟩

-- ## What `hleast` needs, and why it is not free
-- Extracting a least element of `{m | Itower m ⟶* b}` needs that predicate to be DECIDABLE — the set is
-- non-empty (it contains `w`) and bounded, so decidability is the only missing ingredient, and this
-- development refuses `Classical.choice`.
--
-- Reachability from `Itower m` is decidable if `Itower m`'s reachable set is FINITE, which follows from
-- strong normalisation: finitely branching plus terminating gives a finite reachable set. So route two's
-- remaining obligation is
--
--     `Itower m` is strongly normalising.
--
-- That is not available from anything here, and the reason is worth stating. C5 (`conservation`) gives
-- WN ⇒ SN — but only for K-FREE terms, and `Itower` is built from `I = S K K`. With `K` in play the
-- implication is false in general: `K S omegaSK` has a normal form and an infinite reduction. So the one
-- theorem in this tree that would supply SN cannot reach the countdown's own encoding.
--
-- Which is a sharper statement of where piece (v) stands than "route two looks promising": route two is
-- reduced to a single, classical, entirely standard fact about a specific family of terms — and this
-- development's own conservation theorem is blocked from proving it by exactly the erasure that Stage 54
-- showed cuts both ways.

-- ## Stage 56: the reachable set of `Itower m` has bounded size
-- Route two needs decidability of `Itower m ⟶* b`, which needs the reachable set to be finite. Full
-- strong normalisation would give that, and C5 cannot supply it (Stage 55). But FINITE SIZE is weaker and
-- enough, and it is provable directly. Measurement first: the largest reduct of `Itower m` has
-- 1, 4, 10, 22 leaves for m = 0,1,2,3 — which is 3·2^m − 2, tight.
--
-- The proof needs a characterisation of the reachable set, because no measure works for all of SK: `S`
-- duplicates, so size growth is unbounded in general. Three layer states suffice — intact, half-consumed,
-- and collapsed — with the two copies of a half-consumed layer allowed to DRIFT independently, which is
-- the phenomenon Stage 10 found and every later abstraction had to cope with.

-- (`I` is already known to be a full-SK normal form: `normalForm_I`, Bracket.lean — it is `S`
-- underapplied. That is what makes an intact layer's only step its own root redex.)

/-- `Tower m t`: `t` is a state of an `m`-layer countdown tower. `half` lets the two copies differ, which
is what makes this closed under reduction; `drop` records that a collapsed layer leaves a shorter tower
where a longer one stood. -/
inductive Tower : Nat → Term → Prop
  | zero : Tower 0 Term.S
  | intact {m : Nat} {t : Term} : Tower m t → Tower (m + 1) (Term.app I t)
  | half {m : Nat} {t u : Term} : Tower m t → Tower m u →
      Tower (m + 1) (Term.app (Term.app Term.K t) (Term.app Term.K u))
  | drop {m : Nat} {t : Term} : Tower m t → Tower (m + 1) t

theorem tower_Itower : ∀ m, Tower m (Itower m) := by
  intro m
  induction m with
  | zero => exact Tower.zero
  | succ n ih => exact Tower.intact ih

/-- **Closed under reduction.** The intact layer's only step is its own S-redex, which produces the
half-consumed shape; the half-consumed layer's root step is the `K`, which drops a layer; everything else
is congruence into a sub-tower. -/
theorem Tower.of_step : ∀ {m : Nat} {t : Term}, Tower m t → ∀ {u : Term}, (t ⟶ u) → Tower m u := by
  intro m t h
  induction h with
  | zero => intro u hu; cases hu
  | @intact m t ht ih =>
      intro u hu
      cases hu with
      | S_red f g x => exact Tower.half ht ht
      | appL hl =>
          -- a step inside `I = S K K`, which is a normal form
          exact absurd ⟨_, hl⟩ normalForm_I
      | appR hr => exact Tower.intact (ih hr)
  | @half m t v ht hv iht ihv =>
      intro u hu
      cases hu with
      | K_red a b => exact Tower.drop ht
      | appL hl =>
          cases hl with
          | appL h => cases h
          | appR hr => exact Tower.half (iht hr) hv
      | appR hr =>
          cases hr with
          | appL h => cases h
          | appR hr' => exact Tower.half ht (ihv hr')
  | @drop m t ht ih => intro u hu; exact Tower.drop (ih hu)

/-- **The size bound**, tight: `3·2^m − 2`, stated without truncated subtraction. -/
theorem Tower.leafCount_bound : ∀ {m : Nat} {t : Term}, Tower m t → leafCount t + 2 ≤ 3 * 2 ^ m := by
  intro m t h
  induction h with
  | zero => decide
  | @intact m t _ ih =>
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      have hp : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
      show leafCount I + leafCount t + 2 ≤ 3 * 2 ^ (m + 1)
      rw [hp]
      show 3 + leafCount t + 2 ≤ 3 * (2 ^ m * 2)
      omega
  | @half m t v _ _ iht ihv =>
      have hp : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
      show (leafCount Term.K + leafCount t) + (leafCount Term.K + leafCount v) + 2
        ≤ 3 * 2 ^ (m + 1)
      rw [hp]
      show (1 + leafCount t) + (1 + leafCount v) + 2 ≤ 3 * (2 ^ m * 2)
      omega
  | @drop m t _ ih =>
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      have hp : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
      rw [hp]
      omega

/-- **Every reduct of the encoding is small.** So the reachable set of `Itower m` is finite: it lives
inside the finitely many SK terms with at most `3·2^m − 2` leaves. -/
theorem Tower.of_steps : ∀ {m : Nat} {t u : Term}, (t ⟶* u) → Tower m t → Tower m u := by
  intro m t u h
  induction h with
  | refl => exact id
  | tail s _ ih => exact fun ht => ih (Tower.of_step ht s)

theorem itower_reduct_bound {m : Nat} {u : Term} (h : Itower m ⟶* u) :
    leafCount u + 2 ≤ 3 * 2 ^ m :=
  (Tower.of_steps h (tower_Itower m)).leafCount_bound

-- The bound is tight, and matches the measurement that suggested it: 1, 4, 10, 22 leaves.
#guard (List.range 4).map (fun m => 3 * 2 ^ m - 2) = [1, 4, 10, 22]
#guard (List.range 4).map (fun m => leafCount (Itower m)) = [1, 4, 7, 10]

-- ## What this gives route two, and what it still does not
-- `itower_reduct_bound` makes the reachable set of `Itower m` FINITE: it sits inside the SK terms of at
-- most `3·2^m − 2` leaves. That is the ingredient Stage 55 said was missing, obtained without strong
-- normalisation and therefore without needing C5 to reach past its K-freeness restriction.
--
-- What it does not yet give is `hleast`, because turning "finite reachable set" into "decidable
-- reachability" needs a CERTIFIED finite universe of SK terms of bounded size — and this tree's universe,
-- `smallTerms`, is built from `enumAt`, which enumerates K-FREE terms only. Goal 3's decidability machinery
-- is K-free by construction, for the good reason that it was built for pure S.
--
-- So the chain now reads: route two's `hstep` ⟸ `hleast` ⟸ decidable reachability from `Itower m` ⟸ a
-- K-inclusive bounded enumeration + the size bound above. The last item is the only gap, it is
-- infrastructure rather than research, and `skTerms` (AdequacyProbe.lean) is already the uncertified
-- version of exactly it.

-- ## Stage 58: the chain closes
-- Stage 56 bounded the region, Stage 57 certified the universe, and `SKDecidability.lean` removed the
-- K-freeness from saturation. That is everything `hleast` was waiting on.

/-- Reachability from the encoding is decidable: the region is bounded by `3·2^m − 2`, so
`stepsDecidableWithin` applies with no K-freeness anywhere. -/
instance itowerStepsDecidable (m : Nat) (b : Term) : Decidable (Itower m ⟶* b) :=
  stepsDecidableWithin (bound := 3 * 2 ^ m - 2)
    (fun v hv => by have := itower_reduct_bound hv; omega)

/-- **`hleast`.** With the predicate decidable, `Nat.find` supplies the least segment index directly —
this is the step that needed `Classical.choice` in Stage 55 and now does not. -/
theorem hleast_itower (b : Term) (w : Nat) (h : Itower w ⟶* b) :
    ∃ m, m ≤ w ∧ (Itower m ⟶* b) ∧ ∀ k, m = k + 1 → ¬(Itower k ⟶* b) := by
  obtain ⟨m, hle, hp, hmin⟩ := exists_least (p := fun m => Itower m ⟶* b) h
  exact ⟨m, hle, hp, fun k hk => hmin k (by omega)⟩

/-- **Route two's `hstep`, proved.** -/
theorem onSegmentHStepPath_countdown : OnSegmentHStepPath RS.Countdown Itower :=
  onSegmentHStepPath_of_least hleast_itower

/-- **A second, independent adequacy proof for the countdown.** `bwd` again — but via the trajectory
relation and the path-advancing interface, sharing nothing with Stage 48's K-normal-form argument except
the encoding itself. Two abstractions, two proofs, one theorem. -/
theorem countdown_bwd_via_trajectory {a a' : Nat}
    (h : RS.SK.Steps (Itower a) (Itower a')) : RS.Countdown.Steps a a' :=
  RS.bwd_of_abstraction_path (A := RS.Countdown) (B := RS.SK)
    Itower onSeg onSegment_enc onSegment_functional onSegmentHStepPath_countdown h

/-- ...and the `Simulation` assembled from it, distinct from `countdownInSK` in its `bwd` field. -/
def countdownInSK' : Simulation RS.Countdown RS.SK where
  enc := Itower
  dec := naiveAbs
  dec_enc := naiveAbs_Itower
  fwd := by
    intro a a' h
    subst h
    exact RS.SK_steps_iff.mpr (itower_fwd a')
  bwd := by
    intro a a' h
    exact countdown_bwd_via_trajectory h
