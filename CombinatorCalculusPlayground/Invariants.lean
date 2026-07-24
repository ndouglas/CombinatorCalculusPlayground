--! # Invariants of the C1 trajectory: measures other than size
-- Term.lean's measures section says "leaf count is the only size measure
-- we need." True for *size*; that is exactly why every C1 attempt so far
-- has been a size argument, and why all of them stalled. This module
-- negates that assumption: it mines the c1 trajectory under four other
-- measures (spine length, depth, redex count, isometric-redex count) and
-- reports what is invariant.
--
-- The probe found one structural regularity strong enough to prove
-- outright, and it is NOT a divergence proof: from step 8 onward the
-- trajectory has a FROZEN HEAD — every reduct is `S A B` for one fixed
-- 9-leaf normal form A, with all remaining activity inside B. The frozen
-- head is preserved by EVERY step (not merely by `stepOnce`), so the
-- shell is inert forever, and C1 becomes exactly a question about the
-- B-trajectory (`frozen_normalizes_iff`). That is a reduction of the
-- problem, not a solution to it: C1 REMAINS OPEN. |B| = 15 > 7 = |c1|,
-- so this buys structure, not a smaller search space.
--
-- Epistemic register, as everywhere in this tree: the theorems below are
-- kernel-checked and hold for ALL terms; the `#guard`s are
-- evaluator-checked observations about ONE trajectory over a 120-step
-- prefix (build-enforced, so they cannot silently rot, but still
-- fuel-bounded census data and NOT divergence evidence).
import CombinatorCalculusPlayground.Reachability

open Term

-- ## The other measures
-- leafCount and spineLength already live in Term.lean.

/-- Tree height. Unlike leaf count this ignores width entirely. -/
def depth : Term → Nat
  | .S => 0
  | .K => 0
  | .app t u => 1 + max (depth t) (depth u)

/-- How many redexes the term contains, anywhere. `redexCount t = 0` is
equivalent to "t is a normal form" — which is why a preserved lower bound
on it would settle C1. -/
def redexCount : Term → Nat
  | .S => 0
  | .K => 0
  | .app t u =>
    let here := match t with
      | .app (.app .S _) _ => 1
      | .app .K _ => 1
      | _ => 0
    here + redexCount t + redexCount u

/-- Redexes whose firing does NOT change leaf count: S-redexes with an
atomic third argument. This is precisely the fragment τ governs
(`Isometric.lean`), so its value along a trajectory says how much of the
τ-machinery is even applicable. -/
def isoRedexCount : Term → Nat
  | .S => 0
  | .K => 0
  | .app t u =>
    let here := match t, u with
      | .app (.app .S _) _, .S => 1
      | .app (.app .S _) _, .K => 1
      | _, _ => 0
    here + isoRedexCount t + isoRedexCount u

#guard depth S = 0
#guard depth (app S S) = 1
#guard redexCount (app3 S S S S) = 1
#guard redexCount (app S S) = 0
#guard isoRedexCount (app3 S S S S) = 1
-- third argument is compound, so the redex is NOT size-preserving:
#guard isoRedexCount (app3 S S S (app S S)) = 0

-- ## The frozen head, proved for all terms
-- `S A B` with A normal admits exactly one kind of step: a step inside B.
-- Neither head rule can fire (spine length 2 < 3, and the head is S not
-- K), and the left component `S A` is itself stuck.

/-- With A normal, `S A` is stuck: no step at all. -/
theorem noStep_app_S_of_normal {A : Term} (hA : NormalForm A) :
    NormalForm (app S A) := by
  rintro ⟨u, h⟩
  cases h with
  | appL hl => cases hl
  | appR hr => exact hA ⟨_, hr⟩

/-- **The frozen-head lemma.** Every step out of `S A B` (A normal) is a
step inside B, and leaves the `S A ·` shell exactly as it was. Holds for
any strategy, not just leftmost-outermost. -/
theorem step_frozen {A B t' : Term} (hA : NormalForm A)
    (h : app (app S A) B ⟶ t') :
    ∃ B', (B ⟶ B') ∧ t' = app (app S A) B' := by
  cases h with
  | appL hl => exact absurd ⟨_, hl⟩ (noStep_app_S_of_normal hA)
  | appR hr => exact ⟨_, hr, rfl⟩

-- The endpoint must be a variable for `induction` on `Steps`, so the
-- frozen shape travels as a hypothesis rather than in the index.
private theorem steps_frozen_aux {A : Term} (hA : NormalForm A)
    {t t' : Term} (h : t ⟶* t') :
    ∀ B, t = app (app S A) B →
      ∃ B', (B ⟶* B') ∧ t' = app (app S A) B' := by
  induction h with
  | refl _ => intro B hB; exact ⟨B, Steps.refl _, hB⟩
  | @tail t u v s _ ih =>
    intro B hB
    subst hB
    obtain ⟨B₁, hB₁, hu⟩ := step_frozen hA s
    obtain ⟨B₂, hB₂, hv⟩ := ih B₁ hu
    exact ⟨B₂, Steps.tail hB₁ hB₂, hv⟩

/-- The shell survives arbitrarily long reductions. -/
theorem steps_frozen {A B t' : Term} (hA : NormalForm A)
    (h : app (app S A) B ⟶* t') :
    ∃ B', (B ⟶* B') ∧ t' = app (app S A) B' :=
  steps_frozen_aux hA h B rfl

/-- A frozen term is normal exactly when its payload is. -/
theorem frozen_normalForm_iff {A B : Term} (hA : NormalForm A) :
    NormalForm (app (app S A) B) ↔ NormalForm B := by
  constructor
  · exact fun h => h.of_appR
  · intro hB
    rintro ⟨u, h⟩
    obtain ⟨B', hB', _⟩ := step_frozen hA h
    exact hB ⟨B', hB'⟩

/-- **C1, relocated.** For A normal, `S A B` has a normal form iff B does.
So a divergence proof for a frozen term is exactly a divergence proof for
its payload — the shell contributes nothing either way. -/
theorem frozen_normalizes_iff {A B : Term} (hA : NormalForm A) :
    (∃ u, (app (app S A) B ⟶* u) ∧ NormalForm u) ↔
    (∃ v, (B ⟶* v) ∧ NormalForm v) := by
  constructor
  · rintro ⟨u, hu, hnf⟩
    obtain ⟨B', hB', rfl⟩ := steps_frozen hA hu
    exact ⟨B', hB', hnf.of_appR⟩
  · rintro ⟨v, hv, hnf⟩
    exact ⟨app (app S A) v, Steps.congR hv,
      (frozen_normalForm_iff hA).mpr hnf⟩

-- ## The trajectory data (evaluator-checked, fuel-bounded, ONE trajectory)

/-- The fixed head argument the c1 trajectory settles into at step 8.
9 leaves, and a normal form — so `step_frozen` applies to it. -/
def frozenArg : Term := app2 S (app S S) (app2 S (app2 S (app S S) S) S)

#guard render frozenArg = "S (S S) (S (S (S S) S) S)"
#guard leafCount frozenArg = 9
-- normal at the evaluator level; the kernel-level fact is below it.
#guard redexCount frozenArg = 0
#guard spineLength frozenArg = 2

/-- Kernel-level: `frozenArg` really is a normal form, via Stage 2's
characterization of K-free normal forms (`SNF.normal`). This is what
licenses feeding it to `step_frozen`. -/
theorem frozenArg_normal : NormalForm frozenArg :=
  SNF.normal
    (SNF.app2 (SNF.app1 SNF.S)
      (SNF.app2 (SNF.app2 (SNF.app1 SNF.S) SNF.S) SNF.S))

/-- Second argument of an application; the payload of a frozen term. -/
def payload : Term → Term
  | .app _ u => u
  | t => t

/-- Head argument of a spine-2 term: the `A` in `S A B`. -/
def headArg : Term → Term
  | .app t _ => payload t
  | t => t

private def c1trace : List Term := trace 120 c1

-- The frozen head appears at step 8 and never leaves, through step 120.
#guard (c1trace.drop 8).all (fun u => headArg u == frozenArg)
-- ...and does NOT hold at any earlier step: step 8 is a genuine onset.
#guard (c1trace.take 8).all (fun u => !(headArg u == frozenArg))

-- The onset payload. `frozen_normalizes_iff` says C1 for c1 is EXACTLY
-- the question "does this 15-leaf term normalize?" — bigger than c1's 7
-- leaves, so the relocation buys structure, not a smaller search. It is
-- itself a redex (spine 3), unlike the frozen term wrapping it (spine 2).
#guard leafCount ((trace 8 c1).getLastD c1) = 25
#guard leafCount (payload ((trace 8 c1).getLastD c1)) = 15
#guard spineLength (payload ((trace 8 c1).getLastD c1)) = 3
#guard render (payload ((trace 8 c1).getLastD c1))
  = "S (S (S S) S) S (S (S S) (S (S (S S) S) S))"
-- and the frozen term at step 8 really is `S frozenArg payload`:
#guard ((trace 8 c1).getLastD c1)
  == app (app S frozenArg) (payload ((trace 8 c1).getLastD c1))

-- Consequence of the frozen head, visible in the data: spine length locks
-- at 2 from step 8 on, having ranged up to 5 before that.
#guard (c1trace.drop 8).all (fun u => spineLength u == 2)
#guard (c1trace.map spineLength).foldl max 0 = 5
#guard spineLength c1 = 5

-- The isometric fragment is ABSENT from the tail: no size-preserving
-- redex survives past step 5. So τ (Isometric.lean), which governs exactly
-- those redexes, has nothing to act on here — a negative result that
-- explains why the C2 machinery does not transfer to C1.
#guard (c1trace.drop 6).all (fun u => isoRedexCount u == 0)
#guard isoRedexCount ((trace 1 c1).getLastD c1) = 1

-- depth is monotone non-decreasing along the prefix, and redexCount never
-- reaches 0 (equivalently: no reduct in the prefix is a normal form).
-- NEITHER is a divergence proof: monotone-so-far is not monotone-forever,
-- and 120 non-normal reducts do not preclude a normal form at step 121.
#guard (c1trace.zip (c1trace.drop 1)).all (fun (u, v) => depth u ≤ depth v)
#guard c1trace.all (fun u => 1 ≤ redexCount u)

-- ## Honest negative: the payload does not recur
-- Slice 3 hunted for `c1` recurring inside its own trajectory. That hunt
-- could not have found a CONTEXT recurrence, since c1 (spine 5) never
-- reappears once the head freezes (spine 2). Re-run at the frozen level:
-- does any frozen reduct recur as a subterm of a later one? Twenty
-- starting points, all negative — so the loop route still has no witness
-- in the explored prefix, now checked at the right granularity.
#guard (List.range 20).all (fun k =>
  let tk := c1trace.getD (8 + k) c1
  !((c1trace.drop (9 + k)).any (fun u => isSubterm tk u)))

-- The frozen ARGUMENT does recur in every later reduct, of course — it is
-- literally a subterm by construction. Recorded so the negative above is
-- not misread as "nothing recurs".
#guard (c1trace.drop 8).all (fun u => isSubterm frozenArg u)
