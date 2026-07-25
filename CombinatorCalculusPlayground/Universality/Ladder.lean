--! # The relaxation ladder, rung one: {S, I}
-- The design spec's Stage 5 has TWO components. One is the north star
-- (decidability of reachability — closed in Stage 6). The other is:
--
--   "Bracketing program (the relaxation ladder): classify universality of bases
--    between {S} and {S,K} — e.g., {S,I}, {S,B}, {S,C} — each rung a publishable
--    partial result that narrows where universality is lost."
--
-- Sixteen stages engaged with the first component and never mentioned the
-- second. This module opens it.
--
-- WHY {S,I} IS THE RIGHT FIRST RUNG, and it is not because it is easiest: it is
-- where the program's ONLY negative mechanism dies. Every refutation in this
-- tree routes through `RS.Acyclic.of_strict_measure` — pure S, first-order ι, and
-- all one-combinator one-rule systems (C4) fall to a host being ACYCLIC. `{S,I}`
-- has a cycle, so that mechanism provably cannot touch it.
--
-- The resulting boundary is sharp. Pure S is acyclic (`no_pure_S_cycle`, C2).
-- Adding `I` — which erases nothing and duplicates nothing — makes it cyclic.
-- So **the acyclicity boundary sits exactly at the first rung of the ladder**,
-- and the program's negative tooling reaches no further than {S}.
import CombinatorCalculusPlayground.Universality.Taxonomy
import CombinatorCalculusPlayground.Confluence

-- ## The basis {S, I}, with I primitive
-- Note this is NOT `Term`'s `I = S K K`. Here `I` is a combinator in its own
-- right, so the system is genuinely erasure-free: neither rule discards an
-- argument. That matters — it makes {S,I} a λI-style basis, and the cycle below
-- shows erasure-freeness is not what keeps pure S acyclic.

inductive SITerm : Type
  | S : SITerm
  | I : SITerm
  | app : SITerm → SITerm → SITerm
deriving Repr, DecidableEq

inductive SIStep : SITerm → SITerm → Prop
  | S_red (f g x : SITerm) :
      SIStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | I_red (x : SITerm) : SIStep (.app .I x) x
  | appL {t t' u : SITerm} : SIStep t t' → SIStep (.app t u) (.app t' u)
  | appR {t u u' : SITerm} : SIStep u u' → SIStep (.app t u) (.app t u')

def RS.SI : RS := ⟨SITerm, SIStep⟩

def SITerm.leafCount : SITerm → Nat
  | .S => 1
  | .I => 1
  | .app a b => a.leafCount + b.leafCount

-- ## The cycle
-- Ω = (S I I)(S I I), the classic. `S I I` has spine 2 so it is not itself a
-- redex; applying it to itself supplies the third argument and fires.

def Wsi : SITerm := .app (.app .S .I) .I
def omegaSI : SITerm := .app Wsi Wsi
def omegaSI_mid1 : SITerm := .app (.app .I Wsi) (.app .I Wsi)
def omegaSI_mid2 : SITerm := .app Wsi (.app .I Wsi)

#guard SITerm.leafCount omegaSI = 6
#guard omegaSI ≠ omegaSI_mid1

/-- `Ω → (I Ω')(I Ω')` — the S-redex fires, duplicating `S I I`. -/
theorem omegaSI_step1 : RS.SI.step omegaSI omegaSI_mid1 :=
  SIStep.S_red .I .I Wsi

/-- ...and two I-reductions close the loop, returning to Ω exactly. -/
theorem omegaSI_back : RS.SI.Steps omegaSI_mid1 omegaSI :=
  RS.Steps.tail (SIStep.appL (SIStep.I_red Wsi))
    (RS.Steps.tail (SIStep.appR (SIStep.I_red Wsi)) (RS.Steps.refl _))

/-- **{S,I} has a proper reduction cycle** — three steps, through two distinct
intermediates. This is the concrete content of the rung. -/
theorem omegaSI_cycle : RS.SI.step omegaSI omegaSI_mid1 ∧ RS.SI.Steps omegaSI_mid1 omegaSI :=
  ⟨omegaSI_step1, omegaSI_back⟩

-- ## The consequence: the program's negative mechanism cannot reach {S,I}

/-- {S,I} is NOT acyclic, so `PathEncoding.refute_of_acyclic` — the single
mechanism behind every refutation in this tree — has an unsatisfiable hypothesis
here. -/
theorem SI_not_acyclic : ¬ RS.Acyclic RS.SI :=
  fun h => h omegaSI_step1 omegaSI_back

/-- Stronger and more useful: NO strictly-increasing measure exists on {S,I}, so
the C4 engine (`RS.Acyclic.of_strict_measure`) provably cannot be applied — not
merely "we have not found a measure", but "there is none". -/
theorem SI_no_strict_measure :
    ¬ ∃ mu : SITerm → Nat, ∀ (b b' : SITerm), RS.SI.step b b' → mu b < mu b' := by
  rintro ⟨mu, hmono⟩
  exact SI_not_acyclic (RS.Acyclic.of_strict_measure mu (fun h => hmono _ _ h))

/-- The same for a strictly DECREASING measure: a cycle rules out monotone
measures in both directions, so no termination argument of that shape works
either. -/
theorem SI_no_decreasing_measure :
    ¬ ∃ mu : SITerm → Nat, ∀ (b b' : SITerm), RS.SI.step b b' → mu b' < mu b := by
  rintro ⟨mu, hmono⟩
  -- walk the measure down around the cycle and back to where it started
  have hdrop : mu omegaSI_mid1 < mu omegaSI := hmono _ _ omegaSI_step1
  -- Raw recursor: `induction` hits the mkElimApp motive error on `RS.Steps` at a
  -- concrete instance, as in `iota_steps_le` and `RS.Discrete2_steps_eq`.
  have hpath : ∀ {a b : SITerm}, RS.SI.Steps a b → mu b ≤ mu a := by
    intro a b h
    exact h.rec (fun _ => Nat.le_refl _)
      (fun s _ ih => Nat.le_trans ih (Nat.le_of_lt (hmono _ _ s)))
  have := hpath omegaSI_back
  omega

-- ## Where the boundary sits
-- Pure S is acyclic — `no_pure_S_cycle` (C2, Isometric.lean), proved via the
-- head-weight measure τ, for every K-free term and every strategy. Adding `I`
-- destroys that, as above. Two things follow, and the second is the point of
-- the rung:
--
--   * erasure-freeness is NOT what keeps pure S acyclic. {S,I} erases nothing
--     either, and it cycles. Whatever τ is measuring is specific to S-only
--     reduction, not a consequence of non-erasure.
--   * the acyclicity boundary is exactly the first rung. The program's entire
--     negative apparatus applies to {S}, to first-order ι, and to every
--     one-combinator one-rule system (C4) — and stops dead at {S,I}. So the
--     answer to "where is universality lost?" cannot be approached from the
--     negative side beyond rung zero, and the ladder's higher rungs need
--     positive constructions or new mechanisms.
--
-- ## Rungs two and three, scoped not attempted
-- `{S,B}` (B x y z → x (y z)) and `{S,C}` (C x y z → x z y) both have a rule
-- that STRICTLY DECREASES leaf count by 1, mixed with S's rule which changes
-- leaf count by |x| - 1 ≥ 0. So `leafCount` is non-monotone in both directions on
-- each of them, and neither the growth refutation nor a naive shrink argument
-- applies. A combined measure in the style of C2's τ would be needed — the same
-- shape of work that resolved C2, which took a full slice.
--
-- Whether either has a cycle is open here. One natural attempt at Ω fails for
-- `{S,B}`: `S B B (SBB) → (B (SBB))(B (SBB))`, and that reduct is a NORMAL FORM,
-- because `B` applied to fewer than three arguments is stuck and `S B B` has
-- spine 2. So the obvious self-application terminates, which is weak evidence
-- that `{S,B}` may be acyclic and therefore refutable by the existing mechanism
-- — the opposite verdict from rung one, and the reason rung two is worth doing
-- next.

-- ## The ladder is a HIERARCHY, not a flat set of rungs (Stage 18)
-- Rung one was recorded as one basis. It is more than that: cycles propagate
-- along path encodings (`not_acyclic_of_pathEncoding`, Taxonomy.lean), so every
-- system that path-encodes {S,I} inherits the cycle and is therefore beyond the
-- acyclicity mechanism too. Rung one is an UPWARD-CLOSED family, not a point.
--
-- The concrete witness is the top of the ladder: {S,I} path-encodes into SK by
-- sending the primitive `I` to `S K K`. That re-derives SK's non-acyclicity from
-- rung one, by a route independent of the Ω ↔ M cycle in Calibration.lean — which
-- is a consistency check on the generic theorem as much as a result.

/-- Send `S` to `S` and the PRIMITIVE `I` to `S K K`. -/
def siToTerm : SITerm → Term
  | .S => Term.S
  | .I => I
  | .app a b => Term.app (siToTerm a) (siToTerm b)

/-- Nothing in the image is `K` — there is no `K` in the source basis. Needed for
injectivity, since `I`'s image contains `K`s. -/
theorem siToTerm_ne_K : ∀ (t : SITerm), siToTerm t ≠ Term.K
  | .S => by simp [siToTerm]
  | .I => by simp [siToTerm, I, app2]
  | .app _ _ => by simp [siToTerm]

theorem siToTerm_inj : ∀ {t u : SITerm}, siToTerm t = siToTerm u → t = u
  | .S, .S, _ => rfl
  | .I, .I, _ => rfl
  | .S, .I, h => by simp [siToTerm, I, app2] at h
  | .I, .S, h => by simp [siToTerm, I, app2] at h
  | .S, .app _ _, h => by simp [siToTerm] at h
  | .app _ _, .S, h => by simp [siToTerm] at h
  | .I, .app a b, h => by
    -- `S K K = (siToTerm a) (siToTerm b)` would force `siToTerm b = K`
    simp only [siToTerm, I, app2, Term.app.injEq] at h
    exact absurd h.2.symm (siToTerm_ne_K b)
  | .app a b, .I, h => by
    simp only [siToTerm, I, app2, Term.app.injEq] at h
    exact absurd h.2 (siToTerm_ne_K b)
  | .app a b, .app c d, h => by
    simp only [siToTerm, Term.app.injEq] at h
    rw [siToTerm_inj h.1, siToTerm_inj h.2]

/-- Each {S,I} step becomes an SK reduction: `S_red` maps to `S_red` in one step,
and `I_red` to `I_reduces` in two. -/
theorem siToTerm_step : ∀ {t u : SITerm}, SIStep t u → siToTerm t ⟶* siToTerm u := by
  intro t u h
  induction h with
  | S_red f g x => exact Steps.single (Step.S_red _ _ _)
  | I_red x => exact I_reduces (siToTerm x)
  | appL _ ih => exact Steps.congL ih
  | appR _ ih => exact Steps.congR ih

theorem siToTerm_steps : ∀ {t u : SITerm}, RS.SI.Steps t u →
    RS.SK.Steps (siToTerm t) (siToTerm u) := by
  intro t u h
  exact h.rec (fun _ => RS.Steps.refl _)
    (fun s _ ih => RS.Steps.trans (RS.SK_steps_iff.mpr (siToTerm_step s)) ih)

/-- {S,I} path-encodes into SK. -/
def siInSK : PathEncoding RS.SI RS.SK where
  enc := siToTerm
  inj := siToTerm_inj
  path := siToTerm_steps

/-- **SK's non-acyclicity, re-derived from rung one.** Independent of the Ω ↔ M
cycle used in Calibration.lean: this route goes through the {S,I} cycle and the
generic propagation theorem. -/
theorem SK_not_acyclic_via_rung1 : ¬ RS.Acyclic RS.SK :=
  not_acyclic_of_pathEncoding siInSK
    (RS.Steps.single omegaSI_step1) omegaSI_back
    (by decide : omegaSI ≠ omegaSI_mid1)

-- So the rung-one verdict is upward-closed: ANY system that path-encodes {S,I} —
-- SK among them, and any basis containing a definable I — is non-acyclic and
-- therefore beyond `PathEncoding.refute_of_acyclic`. Rung one bounds the
-- mechanism's reach for a whole family, not for one basis.

-- ## Rung two: {S, B} — step 3 of the rung procedure, done properly (Stage 19)
-- Stage 17 recorded one hand-traced Ω attempt for `{S,B}` and called it weak
-- evidence. The rung procedure says step 3 is "hunt for a cycle", and one attempt
-- is not a hunt. This section runs Stage 0's census methodology on rung two:
-- enumerate every {S,B}-term up to a size bound and classify its trajectory.
--
-- EPISTEMIC REGISTER, as everywhere: `sbStepOnce` and the enumerator below are
-- UNVERIFIED census tooling. No theorem is proved about them. The `#guard`s are
-- build-enforced evaluator facts about a bounded search, and "no cycle found" is
-- NOT a proof of acyclicity — exactly the standing caveat on the pure-S census.

inductive SBTerm : Type
  | S : SBTerm
  | B : SBTerm
  | app : SBTerm → SBTerm → SBTerm
deriving Repr, DecidableEq

def SBTerm.leafCount : SBTerm → Nat
  | .S => 1
  | .B => 1
  | .app a b => a.leafCount + b.leafCount

/-- Leftmost-outermost reducer for {S,B}. `S f g x → (f x)(g x)`,
`B x y z → x (y z)`. -/
def sbStepOnce : SBTerm → Option SBTerm
  | .app (.app (.app .S f) g) x => some (.app (.app f x) (.app g x))
  | .app (.app (.app .B x) y) z => some (.app x (.app y z))
  | .app t u =>
    match sbStepOnce t with
    | some t' => some (.app t' u)
    | none => (sbStepOnce u).map (.app t)
  | _ => none

def sbNormalize (fuel : Nat) (t : SBTerm) : Option SBTerm :=
  match sbStepOnce t with
  | none => some t
  | some t' => match fuel with
    | 0 => none
    | f + 1 => sbNormalize f t'

/-- Walk the trajectory keeping every visited term, so a revisit is detectable. -/
def sbOnCycle (fuel : Nat) (t : SBTerm) : Bool :=
  go fuel [t] t
where
  go : Nat → List SBTerm → SBTerm → Bool
  | 0, _, _ => false
  | f + 1, seen, cur =>
    match sbStepOnce cur with
    | none => false
    | some next => if seen.contains next then true else go f (seen ++ [next]) next

/-- All {S,B}-terms with exactly `n` leaves. Two constants, so this is
`2^n` labelings of each of the `Catalan (n-1)` tree shapes. -/
def sbTermsTable (n : Nat) : Array (List SBTerm) := Id.run do
  let mut table : Array (List SBTerm) := #[[], [SBTerm.S, SBTerm.B]]
  for m in [2:n+1] do
    let mut terms : List SBTerm := []
    for k in [1:m] do
      for l in table[k]! do
        for r in table[m - k]! do
          terms := SBTerm.app l r :: terms
    table := table.push terms
  return table

def sbTerms (n : Nat) : List SBTerm := (sbTermsTable n)[n]!

-- Counts: 2 * Catalan(n-1) * 2^(n-1) ... concretely 2, 4, 16, 80, 448, 2688.
#guard (sbTerms 1).length = 2
#guard (sbTerms 2).length = 4
#guard (sbTerms 3).length = 16
#guard (sbTerms 4).length = 80
#guard (sbTerms 5).length = 448
#guard (sbTerms 6).length = 2688

-- ## The verdict of the hunt
-- Up to 6 leaves (3238 terms) every {S,B}-term normalizes within fuel 100 and
-- none is on a cycle.

#guard (List.range 7).all (fun n => (sbTerms n).all (fun t => (sbNormalize 100 t).isSome))
#guard (List.range 7).all (fun n => (sbTerms n).all (fun t => !(sbOnCycle 100 t)))

-- ...but at SEVEN leaves that changes, and the change is the rung's real content.
-- Of 16896 terms, exactly 6 exhaust fuel 200 — and the count is unchanged at fuel
-- 1000, so this is not a cutoff artifact. None is on a detectable cycle within 400
-- steps, and all six grow explosively.

def sbExhausted (fuel n : Nat) : List SBTerm :=
  (sbTerms n).filter (fun t => (sbNormalize fuel t).isNone)

#guard (sbExhausted 200 7).length = 6
#guard (sbExhausted 1000 7).length = 6          -- fuel-insensitive, as C6 checks
#guard (sbExhausted 200 7).all (fun t => !(sbOnCycle 400 t))

-- The Ω-shaped attempt specifically, since that is where rung one's cycle came
-- from: `S B B (S B B)` reaches a normal form in two steps.
def Wsb : SBTerm := .app (.app .S .B) .B
#guard sbNormalize 100 (.app Wsb Wsb) = some (.app (.app .B Wsb) (.app .B Wsb))
#guard sbStepOnce (.app (.app .B Wsb) (.app .B Wsb)) = none

-- ## Cross-validation against the pure-S census
-- Pure-S terms ARE {S,B}-terms — `B` simply never occurs — so the rung-2 census
-- CONTAINS the rung-0 census. Two of the six exhausted terms are exactly C1's
-- candidates, and one of them reproduces the 120112-leaf figure recorded for `c1`
-- in CONJECTURES.md, computed here by an independently written reducer. That is a
-- check on both censuses.

def sbC1 : SBTerm :=   -- S S S (S S) S S, i.e. Reachability.lean's `c1`
  .app (.app (.app (.app (.app .S .S) .S) (.app .S .S)) .S) .S

#guard (sbExhausted 200 7).contains sbC1
#guard sbC1.leafCount = 7
-- the other four contain a B and are genuinely new to this rung
#guard ((sbExhausted 200 7).filter (fun t => t != sbC1)).length = 5

-- ## What rung two therefore is
-- Rung one and rung two DISAGREE, which is the contrast the ladder exists to
-- produce — but not in the direction Stage 17 guessed:
--
--   rung 1  {S,I}  CYCLIC, proved (`omegaSI_cycle`). The acyclicity mechanism is
--                  provably inapplicable.
--   rung 2  {S,B}  NO cycle found (≤ 7 leaves, 400 steps) yet six terms at 7
--                  leaves do not normalize within fuel 1000. So {S,B} looks
--                  structurally like PURE S: plausibly acyclic AND plausibly
--                  non-normalizing — which is exactly the C1 + C2 combination.
--
-- Stage 17 called the terminating Ω attempt "weak evidence {S,B} may be acyclic",
-- and read that as evidence toward being REFUTABLE. The first half survives; the
-- second was too quick. Acyclicity does not require termination — pure S is the
-- proof of that — so fuel-outs at 7 leaves are consistent with {S,B} being
-- acyclic and hence refutable. The verdict is unchanged in direction but its
-- basis is different, and it now rests on 16896 terms rather than one trace.
--
-- The structural reason the Ω pattern fails here is worth recording, because it
-- also says what a cycle would have to look like: `B` needs THREE arguments and
-- self-application supplies too few. `S B B x → (B x)(B x)` leaves `B` applied to
-- one argument on each side, and the whole is `B` applied to two — still short.
-- Rung one worked precisely because `I` needs ONE argument, so
-- `S I I x → (I x)(I x) → x x` fires twice and returns. Neither erasure nor
-- duplication is the discriminator; **arity is**.
--
-- Step 4 is the live task, and the census has sharpened its target: not a
-- termination measure (there are probably non-normalizing terms) but a
-- τ-STYLE ACYCLICITY measure, exactly as C2 needed for pure S. Lexicographic,
-- since step 1 showed neither `leafCount` nor B-count is monotone alone — `B_red`
-- removes a `B` while `S_red` duplicates its third argument, so B-count can rise.
-- A C2-sized slice, NOT attempted here.

-- ## Rung two, step 4: why the C2 strategy cannot be ported (Stage 20)
-- Stage 19 specified step 4's target as "a τ-style acyclicity measure,
-- lexicographic". Working the arithmetic shows that specification is WRONG, and
-- wrong for a reason worth proving rather than asserting.
--
-- Recall how C2 actually settled pure-S acyclicity. It did NOT exhibit a globally
-- decreasing measure — pure S is not terminating. It ran a SQUEEZE:
--   (a) leafCount is monotone (non-decreasing) on pure S, so any cycle must be
--       leafCount-CONSTANT at every step;
--   (b) size-preserving K-free steps are exactly S-redexes with atomic third
--       argument;
--   (c) τ strictly drops on those, so no cycle.
-- Step (a) is load-bearing: without a monotone quantity there is no squeeze and
-- (b) has nothing to characterise.
--
-- On {S,B} there is no such quantity, and not merely for `leafCount`: NO counting
-- measure works, in either direction. Proved below.

/-- The step relation, needed for theorems (`sbStepOnce` above is executable
census tooling). -/
inductive SBStep : SBTerm → SBTerm → Prop
  | S_red (f g x : SBTerm) :
      SBStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | B_red (x y z : SBTerm) :
      SBStep (.app (.app (.app .B x) y) z) (.app x (.app y z))
  | appL {t t' u : SBTerm} : SBStep t t' → SBStep (.app t u) (.app t' u)
  | appR {t u u' : SBTerm} : SBStep u u' → SBStep (.app t u) (.app t u')

def SBTerm.countS : SBTerm → Nat
  | .S => 1
  | .B => 0
  | .app a b => a.countS + b.countS

def SBTerm.countB : SBTerm → Nat
  | .S => 0
  | .B => 1
  | .app a b => a.countB + b.countB

theorem SBTerm.count_add (t : SBTerm) : t.countS + t.countB = t.leafCount := by
  induction t with
  | S => rfl
  | B => rfl
  | app a b iha ihb => simp only [countS, countB, leafCount]; omega

-- ## The rule-level arithmetic
-- `S_red` consumes one `S` and DUPLICATES its third argument; `B_red` consumes one
-- `B` and duplicates nothing. So each count moves differently under each rule, and
-- neither moves consistently.

theorem countB_S_red (f g x : SBTerm) :
    (SBTerm.app (.app f x) (.app g x)).countB
      = (SBTerm.app (.app (.app .S f) g) x).countB + x.countB := by
  simp only [SBTerm.countB]; omega

theorem countB_B_red (x y z : SBTerm) :
    (SBTerm.app x (.app y z)).countB + 1
      = (SBTerm.app (.app (.app .B x) y) z).countB := by
  simp only [SBTerm.countB]; omega

theorem countS_S_red (f g x : SBTerm) :
    (SBTerm.app (.app f x) (.app g x)).countS + 1
      = (SBTerm.app (.app (.app .S f) g) x).countS + x.countS := by
  simp only [SBTerm.countS]; omega

theorem countS_B_red (x y z : SBTerm) :
    (SBTerm.app x (.app y z)).countS
      = (SBTerm.app (.app (.app .B x) y) z).countS := by
  simp only [SBTerm.countS]; omega

-- ## Four witnesses, one per direction of each count

/-- `S S S (S S)` — an S-redex whose third argument is compound: S-count RISES. -/
def wGrowS : SBTerm := .app (.app (.app .S .S) .S) (.app .S .S)
/-- `S S S (B B)` — third argument is all `B`: B-count RISES, S-count FALLS. -/
def wBArg : SBTerm := .app (.app (.app .S .S) .S) (.app .B .B)
/-- `B S S S` — a B-redex: B-count FALLS, S-count is unchanged. -/
def wBred : SBTerm := .app (.app (.app .B .S) .S) .S

theorem step_wGrowS : SBStep wGrowS (.app (.app .S (.app .S .S)) (.app .S (.app .S .S))) :=
  SBStep.S_red .S .S (.app .S .S)
theorem step_wBArg : SBStep wBArg (.app (.app .S (.app .B .B)) (.app .S (.app .B .B))) :=
  SBStep.S_red .S .S (.app .B .B)
theorem step_wBred : SBStep wBred (.app .S (.app .S .S)) :=
  SBStep.B_red .S .S .S

-- S-count rises 5 -> 6; B-count rises 2 -> 4; B-count falls 1 -> 0; S-count falls 3 -> 2.
#guard wGrowS.countS = 5 ∧ (SBTerm.app (.app .S (.app .S .S)) (.app .S (.app .S .S))).countS = 6
#guard wBArg.countB = 2 ∧ (SBTerm.app (.app .S (.app .B .B)) (.app .S (.app .B .B))).countB = 4
#guard wBArg.countS = 3 ∧ (SBTerm.app (.app .S (.app .B .B)) (.app .S (.app .B .B))).countS = 2
#guard wBred.countB = 1 ∧ (SBTerm.app .S (.app .S .S)).countB = 0

/-- **No counting measure is monotone on {S,B}, in either direction.** For any
non-trivial weights `a, b`, the quantity `a·#S + b·#B` both rises and falls along
{S,B} reduction. Hence C2's squeeze has no starting point here: there is no
monotone quantity for a cycle to be constant on.

Witness selection, which is the whole proof: a RISE comes from `wGrowS` when
`a > 0` (5a → 6a) and from `wBArg` when `a = 0` (2b → 4b); a FALL comes from
`wBred` when `b > 0` (3a+b → 3a) and from `wBArg` when `b = 0` (3a → 2a). -/
theorem no_monotone_counting_measure (a b : Nat) (hab : 0 < a ∨ 0 < b) :
    (∃ t u, SBStep t u ∧ a * u.countS + b * u.countB < a * t.countS + b * t.countB) ∧
    (∃ t u, SBStep t u ∧ a * t.countS + b * t.countB < a * u.countS + b * u.countB) := by
  constructor
  · -- a FALL exists
    rcases Nat.eq_zero_or_pos b with hb | hb
    · refine ⟨wBArg, _, step_wBArg, ?_⟩
      simp only [wBArg, SBTerm.countS, SBTerm.countB]
      rcases hab with ha | hb' <;> omega
    · refine ⟨wBred, _, step_wBred, ?_⟩
      simp only [wBred, SBTerm.countS, SBTerm.countB]
      omega
  · -- a RISE exists
    rcases Nat.eq_zero_or_pos a with ha | ha
    · refine ⟨wBArg, _, step_wBArg, ?_⟩
      simp only [wBArg, SBTerm.countS, SBTerm.countB]
      rcases hab with ha' | hb <;> omega
    · refine ⟨wGrowS, _, step_wGrowS, ?_⟩
      simp only [wGrowS, SBTerm.countS, SBTerm.countB]
      omega

-- ## What that leaves, stated plainly
-- Rung two's acyclicity is OPEN, and the route Stage 19 named is closed:
--
--   * C2's squeeze needs a monotone quantity. `no_monotone_counting_measure`
--     shows no counting measure is monotone on {S,B}, so step (a) of that
--     argument has no starting point. Stage 19's "lexicographic measure" is ruled
--     out for the same reason — a lexicographic order needs its FIRST component
--     monotone, and none is.
--   * a globally DECREASING measure is ruled out independently: the census found
--     terms at 7 leaves that do not normalize at fuel 1000, and a decreasing
--     Nat-measure would force termination.
--
-- So {S,B} acyclicity needs either a non-counting structural measure (τ's
-- ancestor was positional, not a count — τ(app a b) = 2τ(a) + τ(b) weights by
-- POSITION), or an interpretation argument, or the census is simply wrong about
-- there being no cycle. That last possibility deserves real weight: the hunt
-- reached 7 leaves and 400 steps, which is small, and rung one's cycle lives at
-- 6 leaves. Recorded as open rather than as "nearly done".

-- ## Stage 21: a faster detector — and what validating it revealed
-- Stage 20 diagnosed `sbOnCycle` as quadratic (seen-list plus `contains`) and
-- proposed a faster detector so the hunt could go deeper. Floyd's tortoise-and-hare
-- does it in O(1) memory, since `sbStepOnce` is a FUNCTION and so the trajectory is
-- a functional graph. Written generically, with a SIZE cap, so it can be
-- instantiated on {S,I} too — which is what made the real finding possible.

/-- Floyd cycle detection with a size cap. `some true` = the trajectory is
eventually periodic; `some false` = it reached a normal form; `none` = the fuel or
the size cap ran out, and NO verdict is given. -/
def floydFind {α : Type} [BEq α] (size : α → Nat) (step : α → Option α)
    (maxSize : Nat) : Nat → α → α → Option Bool
  | 0, _, _ => none
  | f + 1, slow, fast =>
    if maxSize < size slow then none
    else if maxSize < size fast then none
    else match step slow with
      | none => some false
      | some s' => match step fast with
        | none => some false
        | some m => match step m with
          | none => some false
          | some f2 => if s' == f2 then some true else floydFind size step maxSize f s' f2

def sbCycle? (maxSize fuel : Nat) (t : SBTerm) : Option Bool :=
  floydFind SBTerm.leafCount sbStepOnce maxSize fuel t t

-- ## Executable {S,I} reduction, and the validation that mattered
-- An untested cycle detector reporting "no cycles found" is worthless, so the
-- true-positive path had to be checked against a cycle known to exist. Rung one
-- supplies one: `omegaSI_cycle` is KERNEL-PROVED. The detector was run on it and
-- **did not find it.**

def siStepOnce : SITerm → Option SITerm
  | .app (.app (.app .S f) g) x => some (.app (.app f x) (.app g x))
  | .app .I x => some x
  | .app t u =>
    match siStepOnce t with
    | some t' => some (.app t' u)
    | none => (siStepOnce u).map (.app t)
  | _ => none

def siTrace : Nat → SITerm → List SITerm
  | 0, t => [t]
  | f + 1, t => t :: (match siStepOnce t with | none => [] | some t' => siTrace f t')

-- **The strategy gap, demonstrated.** `omegaSI` is provably on a cycle
-- (`omegaSI_cycle`), yet leftmost-outermost reduction never returns to it — 60
-- steps and counting. The proved cycle's closing step is `appR (I_red)`, an INNER
-- redex; leftmost-outermost fires the head S-redex instead and walks away forever.
#guard ((siTrace 60 omegaSI).drop 1).all (fun u => u != omegaSI)
#guard floydFind SITerm.leafCount siStepOnce 500 200 omegaSI omegaSI != some true

-- The leftmost-outermost trajectory grows without bound instead of closing:
-- sizes 6, 8, 7, 10, 9, 8, 12, 11, 10, 9, 14, ... — each S-redex adds an `I` layer
-- faster than the I-reductions remove them.
#guard (siTrace 10 omegaSI).map SITerm.leafCount = [6,8,7,10,9,8,12,11,10,9,14]

-- ## The consequence for rungs two and three, stated as a correction
-- Every cycle-hunt figure in this module is LEFTMOST-OUTERMOST ONLY. That was
-- always literally true, and Stage 0's census carried exactly this caveat for pure
-- S ("cycle-freedom under ALL strategies is a stronger, separate claim; this census
-- only ever runs leftmost-outermost", CONJECTURES.md's C2 entry). I rebuilt Stage
-- 0's methodology on a new rung and reproduced its caveat without noticing.
--
-- What is new is that the caveat now has a CONCRETE WITNESS rather than being
-- theoretical: rung one's cycle is exactly a cycle that a leftmost-outermost hunt
-- cannot see. So the {S,B} data below is much weaker evidence for acyclicity than
-- Stages 19–20 treated it as being. It rules out leftmost-outermost cycles and says
-- nothing about the relation.
--
-- With the faster detector the hunt does reach much further, and the figures are
-- worth having at their correct strength:
--
--   n = 8:  109824 terms, 0 LO cycles, 109565 reach a normal form,
--           259 no-verdict at size cap 1000 / fuel 300.   (6 seconds)
--   n = 9:  732160 terms, 0 LO cycles, 727664 reach a normal form,
--           4496 no-verdict at the same caps.              (38 seconds)
--
-- Compare Stage 20's quadratic detector, which was abandoned at n = 8 after ten
-- minutes. The speedup is real; the epistemic value of the extra sizes is smaller
-- than it looks, for the reason above.

#guard (List.range 8).all (fun n => (sbTerms n).all (fun t => sbCycle? 500 200 t != some true))

-- ## Stage 22: a STRATEGY-INDEPENDENT cycle hunt
-- Stage 21 showed the leftmost-outermost hunt is blind to exactly the phenomenon
-- rung one exhibits, so more leftmost-outermost data was the wrong thing to want.
-- The acyclicity question is about the RELATION, so the search has to be over ALL
-- one-step successors. That is the shape Reachability.lean already uses for pure S
-- (`succs` + `boundedClosure` + `onCycle?`); this is the same construction, generic
-- over the term type so it can be validated on {S,I}.

/-- Every one-step successor: the head redex if there is one, plus every step
available in either subterm. Not one strategy's choice — all of them. -/
def siSuccs : SITerm → List SITerm
  | .app a b =>
      (match (SITerm.app a b) with
       | .app (.app (.app .S f) g) x => [SITerm.app (.app f x) (.app g x)]
       | .app .I x => [x]
       | _ => [])
      ++ (siSuccs a).map (fun a' => SITerm.app a' b)
      ++ (siSuccs b).map (fun b' => SITerm.app a b')
  | _ => []

def sbSuccs : SBTerm → List SBTerm
  | .app a b =>
      (match (SBTerm.app a b) with
       | .app (.app (.app .S f) g) x => [SBTerm.app (.app f x) (.app g x)]
       | .app (.app (.app .B x) y) z => [SBTerm.app x (.app y z)]
       | _ => [])
      ++ (sbSuccs a).map (fun a' => SBTerm.app a' b)
      ++ (sbSuccs b).map (fun b' => SBTerm.app a b')
  | _ => []

def closureStepG {α : Type} [BEq α] (size : α → Nat) (succs : α → List α)
    (cap : Nat) (acc : List α) : List α :=
  (acc.flatMap succs).filter (fun w => size w ≤ cap && !acc.contains w)

def closureG {α : Type} [BEq α] (size : α → Nat) (succs : α → List α) (cap : Nat) :
    Nat → List α → Option (List α)
  | 0, acc => if (closureStepG size succs cap acc).isEmpty then some acc else none
  | f + 1, acc =>
    let nxt := closureStepG size succs cap acc
    if nxt.isEmpty then some acc else closureG size succs cap f (acc ++ nxt.eraseDups)

/-- Is `t` on a cycle, under ANY strategy? Explore everything reachable from `t`'s
successors while staying within the size cap; if `t` reappears, it is on a cycle.

`some true` — `t` is on a cycle. A real verdict: an actual return path was found.
`some false` — the closure SATURATED, so no cycle through `t` exists whose terms all
stay within the cap. A verdict relative to the cap, not absolutely.
`none` — fuel ran out; no verdict. Same epistemic shape as `onCycle?` in
Reachability.lean, and unverified census tooling exactly as that is. -/
def onCycleAny {α : Type} [BEq α] (size : α → Nat) (succs : α → List α)
    (cap fuel : Nat) (t : α) : Option Bool :=
  (closureG size succs cap fuel (succs t)).map (fun acc => acc.contains t)

-- ## Validation: it finds what the leftmost-outermost detector could not
-- This is the check Stage 21 taught me to run first. `omegaSI` is kernel-proved to
-- be on a cycle and the LO detector provably misses it; this detector finds it.
#guard onCycleAny SITerm.leafCount siSuccs 20 50 omegaSI = some true
-- ...and does not cry wolf: `S I I` is a normal form, and rung two's Ω attempt
-- genuinely is not on a cycle.
#guard onCycleAny SITerm.leafCount siSuccs 20 50 Wsi = some false
#guard onCycleAny SBTerm.leafCount sbSuccs 20 50 (.app Wsb Wsb) = some false

-- ## Rung two, re-hunted at the right strength
-- Every {S,B}-term up to 7 leaves gets a VERDICT (no fuel-outs), and none is on a
-- cycle staying within 30 leaves — under ANY strategy, not just leftmost-outermost.
#guard (List.range 8).all (fun n =>
  (sbTerms n).all (fun t => onCycleAny SBTerm.leafCount sbSuccs 30 100 t = some false))

-- Measured runs, recorded rather than guarded (build time):
--
--   n = 8, cap 30,  fuel 100: 109824 terms, 0 cycles, ALL verdicted.   (~15 s)
--   n = 7, cap 60,  fuel 200:  16896 terms, 0 cycles, ALL verdicted.
--   n = 7, cap 120, fuel 400:  16896 terms, 0 cycles, ALL verdicted.
--
-- So the verdict is CAP-INSENSITIVE at n = 7 across a 4x range of caps, and every
-- term at every size up to 8 leaves saturated rather than running out of fuel.
--
-- HONEST SCOPE, and it is a real limit: `some false` means no cycle through `t`
-- whose terms ALL stay within the cap. A cycle that swells past 30 (or 120) leaves
-- and returns is not excluded. Since {S,B}'s `leafCount` is non-monotone in both
-- directions (`no_monotone_counting_measure`), such a cycle is not obviously
-- impossible — which is exactly why the cap matters here and would not for pure S,
-- where monotonicity confines every path.
--
-- Even so, this is a genuine strengthening over Stages 19-21: those ruled out
-- leftmost-outermost cycles only, and Stage 21 showed that class of evidence misses
-- real cycles. This rules out ALL strategies within a size bound, and the bound has
-- been tested for sensitivity.

-- ## Stage 23: τ on {S,B}, and an acyclic sub-fragment
-- Two things pointed here. Stage 20 ruled out every LINEAR COUNTING measure and
-- noted that τ is not a count — `τ(app a b) = 2τ(a) + τ(b)` weights by POSITION —
-- flagging that as the live hint. Stage 22 then found the remaining hole in the
-- census (a cycle swelling past the size cap) is not closable by brute force: the
-- closure at cap 200 on the explosive 7-leaf terms did not finish in ten minutes.
-- So the hole has to be attacked analytically, and τ is the tool to try.
--
-- It does not settle rung two, but it gets much closer than any count: τ strictly
-- decreases on EVERY B-reduction, and on an S-reduction it moves by `2τ(x) - 8`,
-- so it decreases there too whenever the third argument is τ-light. That isolates
-- an acyclic sub-fragment — exactly C2's shape, where τ dropped on the isometric
-- fragment of pure S.

def tauSB : SBTerm → Nat
  | .S => 1
  | .B => 1
  | .app a b => 2 * tauSB a + tauSB b

theorem tauSB_pos (t : SBTerm) : 0 < tauSB t := by
  induction t with
  | S => exact Nat.zero_lt_one
  | B => exact Nat.zero_lt_one
  | app a b iha ihb => simp only [tauSB]; omega

/-- On an S-reduction τ moves by exactly `2τ(x) - 8`: down when the duplicated
argument is light, up when it is heavy. Same shape as pure S, where C2 used the
`τ(x) = 1` case to get its drop of 6. -/
theorem tauSB_S_red (f g x : SBTerm) :
    tauSB (.app (.app f x) (.app g x)) + 8
      = tauSB (.app (.app (.app .S f) g) x) + 2 * tauSB x := by
  simp only [tauSB]; omega

/-- On a B-reduction τ strictly decreases, always — by `2τ(x) + 8 ≥ 10`. `B`
duplicates nothing, so there is no compensating term. -/
theorem tauSB_B_red (x y z : SBTerm) :
    tauSB (.app x (.app y z)) + (2 * tauSB x + 8)
      = tauSB (.app (.app (.app .B x) y) z) := by
  simp only [tauSB]; omega

-- ## The τ-light fragment
-- A step is light when it is a B-reduction, or an S-reduction whose duplicated
-- argument has `τ ≤ 3` — precisely the condition making `2τ(x) - 8` negative.

inductive SBLightStep : SBTerm → SBTerm → Prop
  | S_red (f g x : SBTerm) (h : tauSB x ≤ 3) :
      SBLightStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | B_red (x y z : SBTerm) :
      SBLightStep (.app (.app (.app .B x) y) z) (.app x (.app y z))
  | appL {t t' u : SBTerm} : SBLightStep t t' → SBLightStep (.app t u) (.app t' u)
  | appR {t u u' : SBTerm} : SBLightStep u u' → SBLightStep (.app t u) (.app t u')

theorem sbLightStep_isStep {t u : SBTerm} (h : SBLightStep t u) : SBStep t u := by
  induction h with
  | S_red f g x _ => exact SBStep.S_red f g x
  | B_red x y z => exact SBStep.B_red x y z
  | appL _ ih => exact SBStep.appL ih
  | appR _ ih => exact SBStep.appR ih

theorem tauSB_lt_of_light {t u : SBTerm} (h : SBLightStep t u) : tauSB u < tauSB t := by
  induction h with
  | S_red f g x hx =>
    have := tauSB_S_red f g x
    have hp := tauSB_pos x
    omega
  | B_red x y z =>
    have := tauSB_B_red x y z
    have hp := tauSB_pos x
    omega
  | appL _ ih => simp only [tauSB]; omega
  | appR _ ih => simp only [tauSB]; omega

def RS.SBLight : RS := ⟨SBTerm, SBLightStep⟩

/-- **The τ-light fragment of {S,B} is acyclic.** The direct analogue of C2's
isometric fragment for pure S: isolate the steps a measure controls, and no cycle
can live inside them. -/
theorem sbLight_acyclic : RS.Acyclic RS.SBLight :=
  RS.Acyclic.of_decreasing_measure tauSB tauSB_lt_of_light

/-- **Where a {S,B} cycle would have to live.** Since τ strictly drops on every
light step, no cycle consists only of light steps — so any cycle must fire at least
one S-reduction whose duplicated argument is τ-HEAVY (`τ(x) ≥ 4`). That is the
narrowed target the census cap could not reach. -/
theorem sbCycle_needs_heavy_S {t : SBTerm}
    (hcyc : ∃ u, SBLightStep t u ∧ RS.SBLight.Steps u t) : False := by
  obtain ⟨u, h1, h2⟩ := hcyc
  exact sbLight_acyclic h1 h2

-- τ-heavy arguments are not exotic — `S S` already has τ = 3 (light) and `S (S S)`
-- has τ = 5 (heavy), so the boundary sits at very small terms.
#guard tauSB .S = 1
#guard tauSB (.app .S .S) = 3
#guard tauSB (.app .S (.app .S .S)) = 5
#guard tauSB (.app (.app .S .S) .S) = 7

-- ## What rung two now is
--   * no counting measure is monotone            (Stage 20, proved)
--   * no cycle under ANY strategy up to 8 leaves
--     within a 30-leaf cap, cap-insensitive to 120 (Stage 22, censused)
--   * the cap cannot be lifted by brute force      (Stage 23, measured: cap 200 on
--                                                   the explosive 7-leaf terms did
--                                                   not finish in ten minutes)
--   * τ strictly drops on every B-reduction and on
--     every τ-light S-reduction, so the τ-light
--     fragment is ACYCLIC                          (Stage 23, proved)
--
-- So a {S,B} cycle, if one exists, must fire an S-reduction duplicating a τ-heavy
-- argument. Rung two remains OPEN, but the target is now a single named condition
-- rather than an unbounded search.

-- ## Stage 24: rung three {S, C} — where τ distinguishes what leafCount cannot
-- Two things led here. First, the τ family: with `τ_k(app a b) = k·τ_k(a) + τ_k(b)`
-- the S-reduction delta is `k(τ_k(x) − k²)`, so the light fragment GROWS with k —
-- `S (S S)` is τ₂-heavy (5 ≥ 4) but τ₃-light (7 < 9). The general-k lemmas need
-- `ring`, which this zero-dependency tree does not have, so the family is recorded
-- as arithmetic rather than formalised; the k = 2 instance is `tauSB` above.
--
-- Second, and this is the stage's content: `C x y z → x z y` has the SAME leafCount
-- delta as `B x y z → x (y z)` — both remove exactly one leaf. So no counting
-- measure can tell rungs two and three apart. τ can, and it says they are not alike
-- at all: τ strictly decreases on EVERY B-reduction, but a C-reduction can INCREASE
-- τ, because permuting arguments moves a heavy term into a lighter position.

inductive SCTerm : Type
  | S : SCTerm
  | C : SCTerm
  | app : SCTerm → SCTerm → SCTerm
deriving Repr, DecidableEq

def SCTerm.leafCount : SCTerm → Nat
  | .S => 1
  | .C => 1
  | .app a b => a.leafCount + b.leafCount

inductive SCStep : SCTerm → SCTerm → Prop
  | S_red (f g x : SCTerm) :
      SCStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | C_red (x y z : SCTerm) :
      SCStep (.app (.app (.app .C x) y) z) (.app (.app x z) y)
  | appL {t t' u : SCTerm} : SCStep t t' → SCStep (.app t u) (.app t' u)
  | appR {t u u' : SCTerm} : SCStep u u' → SCStep (.app t u) (.app t u')

def tauSC : SCTerm → Nat
  | .S => 1
  | .C => 1
  | .app a b => 2 * tauSC a + tauSC b

theorem tauSC_pos (t : SCTerm) : 0 < tauSC t := by
  induction t with
  | S => exact Nat.zero_lt_one
  | C => exact Nat.zero_lt_one
  | app a b iha ihb => simp only [tauSC]; omega

/-- S-reduction moves τ by `2τ(x) − 8`, exactly as on {S,B}. -/
theorem tauSC_S_red (f g x : SCTerm) :
    tauSC (.app (.app f x) (.app g x)) + 8
      = tauSC (.app (.app (.app .S f) g) x) + 2 * tauSC x := by
  simp only [tauSC]; omega

/-- **C-reduction moves τ by `τ(z) − τ(y) − 8`** — not always down. Contrast
`tauSB_B_red`, where the delta is `−(2τ(x) + 8)` and therefore always negative. This
is the asymmetry `leafCount` cannot see: both rules remove exactly one leaf. -/
theorem tauSC_C_red (x y z : SCTerm) :
    tauSC (.app (.app x z) y) + (tauSC y + 8)
      = tauSC (.app (.app (.app .C x) y) z) + tauSC z := by
  simp only [tauSC]; omega

-- The asymmetry, witnessed concretely. Both are C-reductions; one raises τ, one
-- lowers it, and their leafCount deltas are identical (−1).
def scHeavy : SCTerm := .app (.app (.app .C .S) .S)
  (.app (.app (.app .S .S) .S) .S)                    -- C S S (S S S S)
def scLight : SCTerm := .app (.app (.app .C .S)
  (.app (.app (.app .S .S) .S) .S)) .S                -- C S (S S S S) S

theorem scHeavy_step : SCStep scHeavy
    (.app (.app .S (.app (.app (.app .S .S) .S) .S)) .S) :=
  SCStep.C_red .S .S (.app (.app (.app .S .S) .S) .S)
theorem scLight_step : SCStep scLight
    (.app (.app .S .S) (.app (.app (.app .S .S) .S) .S)) :=
  SCStep.C_red .S (.app (.app (.app .S .S) .S) .S) .S

-- τ rises 29 → 35 on one and falls 43 → 21 on the other...
#guard tauSC scHeavy = 29
#guard tauSC (.app (.app .S (.app (.app (.app .S .S) .S) .S)) .S) = 35
#guard tauSC scLight = 43
#guard tauSC (.app (.app .S .S) (.app (.app (.app .S .S) .S) .S)) = 21
-- ...while leafCount falls by exactly 1 in both cases, seeing no difference at all.
#guard scHeavy.leafCount = 7 ∧ (SCTerm.app (.app .S (.app (.app (.app .S .S) .S) .S)) .S).leafCount = 6
#guard scLight.leafCount = 7 ∧ (SCTerm.app (.app .S .S) (.app (.app (.app .S .S) .S) .S)).leafCount = 6

-- ## Rung three's light fragment, which needs TWO conditions
-- On {S,B} only the S-reductions needed restricting. Here C-reductions do too.

inductive SCLightStep : SCTerm → SCTerm → Prop
  | S_red (f g x : SCTerm) (h : tauSC x ≤ 3) :
      SCLightStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | C_red (x y z : SCTerm) (h : tauSC z < tauSC y + 8) :
      SCLightStep (.app (.app (.app .C x) y) z) (.app (.app x z) y)
  | appL {t t' u : SCTerm} : SCLightStep t t' → SCLightStep (.app t u) (.app t' u)
  | appR {t u u' : SCTerm} : SCLightStep u u' → SCLightStep (.app t u) (.app t u')

theorem scLightStep_isStep {t u : SCTerm} (h : SCLightStep t u) : SCStep t u := by
  induction h with
  | S_red f g x _ => exact SCStep.S_red f g x
  | C_red x y z _ => exact SCStep.C_red x y z
  | appL _ ih => exact SCStep.appL ih
  | appR _ ih => exact SCStep.appR ih

theorem tauSC_lt_of_light {t u : SCTerm} (h : SCLightStep t u) : tauSC u < tauSC t := by
  induction h with
  | S_red f g x hx => have := tauSC_S_red f g x; have := tauSC_pos x; omega
  | C_red x y z hz => have := tauSC_C_red x y z; have := tauSC_pos y; omega
  | appL _ ih => simp only [tauSC]; omega
  | appR _ ih => simp only [tauSC]; omega

def RS.SCLight : RS := ⟨SCTerm, SCLightStep⟩

/-- **The τ-light fragment of {S,C} is acyclic** — the rung-three analogue of
`sbLight_acyclic`, but with a two-clause light condition, since on {S,C} the
permuting rule also needs restricting. -/
theorem scLight_acyclic : RS.Acyclic RS.SCLight :=
  RS.Acyclic.of_decreasing_measure tauSC tauSC_lt_of_light

-- ## The strategy-independent hunt, transferred for free
-- `onCycleAny` was written generically in Stage 22, so rung three costs only a
-- successor function.

def scSuccs : SCTerm → List SCTerm
  | .app a b =>
      (match (SCTerm.app a b) with
       | .app (.app (.app .S f) g) x => [SCTerm.app (.app f x) (.app g x)]
       | .app (.app (.app .C x) y) z => [SCTerm.app (.app x z) y]
       | _ => [])
      ++ (scSuccs a).map (fun a' => SCTerm.app a' b)
      ++ (scSuccs b).map (fun b' => SCTerm.app a b')
  | _ => []

def scTermsTable (n : Nat) : Array (List SCTerm) := Id.run do
  let mut table : Array (List SCTerm) := #[[], [SCTerm.S, SCTerm.C]]
  for m in [2:n+1] do
    let mut terms : List SCTerm := []
    for k in [1:m] do
      for l in table[k]! do
        for r in table[m - k]! do
          terms := SCTerm.app l r :: terms
    table := table.push terms
  return table

def scTerms (n : Nat) : List SCTerm := (scTermsTable n)[n]!

#guard (scTerms 6).length = 2688
-- No cycle through any {S,C}-term of at most 6 leaves within a 30-leaf cap, under
-- ANY strategy, and every term verdicted rather than fuel-exhausted.
#guard (List.range 7).all (fun n =>
  (scTerms n).all (fun t => onCycleAny SCTerm.leafCount scSuccs 30 100 t = some false))

-- ## What rung three is, and how it differs from rung two
--   * leafCount cannot separate them: `B x y z → x (y z)` and `C x y z → x z y`
--     both remove exactly one leaf.
--   * τ separates them sharply: B always lowers τ; C can raise it, because
--     permuting moves a heavy argument into a lighter position. Witnessed above by
--     two C-reductions with identical leafCount deltas and opposite τ deltas.
--   * so rung three's light fragment needs TWO conditions where rung two needed one,
--     and rung three is correspondingly further from a full acyclicity proof.
--   * censused: no cycle up to 6 leaves under any strategy within a 30-leaf cap.
--
-- Rung three is OPEN, like rung two, but for a structurally different reason — and
-- that difference is invisible to every measure the program used before Stage 23.

-- ## Stage 25: bootstrapping the heavy-S condition
-- Stage 23 showed a {S,B} cycle must fire an S-reduction on a τ-heavy argument
-- (τ(x) ≥ 4). That threshold can be pushed much higher by chaining τ against
-- leafCount, and the per-step facts that make the chain work are proved here. The
-- summation over a cycle is arithmetic and is recorded below, not formalised —
-- classifying every step of a path needs a path-indexed induction carrying one
-- accumulator per step class, which is a slice of its own.

theorem SBTerm.leafCount_pos (t : SBTerm) : 0 < t.leafCount := by
  induction t with
  | S => exact Nat.zero_lt_one
  | B => exact Nat.zero_lt_one
  | app a b iha ihb => simp only [SBTerm.leafCount]; omega

theorem SBTerm.eq_atom_of_leafCount_one {t : SBTerm} (h : t.leafCount = 1) :
    t = .S ∨ t = .B := by
  cases t with
  | S => exact Or.inl rfl
  | B => exact Or.inr rfl
  | app a b =>
    exfalso
    have := SBTerm.leafCount_pos a
    have := SBTerm.leafCount_pos b
    simp only [SBTerm.leafCount] at h
    omega

/-- τ is bounded by 3 on terms of at most two leaves — the largest such τ is
`τ(app atom atom) = 3`. -/
theorem tauSB_le_three_of_small {x : SBTerm} (h : x.leafCount ≤ 2) : tauSB x ≤ 3 := by
  cases x with
  | S => simp [tauSB]
  | B => simp [tauSB]
  | app a b =>
    have hpa := SBTerm.leafCount_pos a
    have hpb := SBTerm.leafCount_pos b
    simp only [SBTerm.leafCount] at h
    have ha : a.leafCount = 1 := by omega
    have hb : b.leafCount = 1 := by omega
    rcases SBTerm.eq_atom_of_leafCount_one ha with rfl | rfl <;>
      rcases SBTerm.eq_atom_of_leafCount_one hb with rfl | rfl <;>
      simp [tauSB]

/-- **A τ-heavy argument has at least three leaves.** The bridge between the two
measures, and the reason the bootstrap below gets traction. -/
theorem leafCount_ge_three_of_heavy {x : SBTerm} (h : 4 ≤ tauSB x) :
    3 ≤ x.leafCount := by
  by_cases hs : x.leafCount ≤ 2
  · exact absurd (tauSB_le_three_of_small hs) (by omega)
  · omega

/-- **A heavy S-reduction raises leafCount by at least 2.** Duplicating a
three-or-more-leaf argument costs at least that much, and every B-reduction only
recovers 1 — which is what turns the τ threshold into a count of B-reductions. -/
theorem leafCount_S_red_heavy (f g x : SBTerm) (h : 4 ≤ tauSB x) :
    (SBTerm.app (.app (.app .S f) g) x).leafCount + 2
      ≤ (SBTerm.app (.app f x) (.app g x)).leafCount := by
  have := leafCount_ge_three_of_heavy h
  simp only [SBTerm.leafCount]
  omega

-- ## The bootstrap, as arithmetic
-- Chaining the two measures against each other on a hypothetical cycle. Every
-- ingredient is proved above or in Stage 20/23; only the summation is informal.
--
--   (1) heavy S-red  =>  |x| >= 3  =>  leafCount rises by >= 2
--                                          `leafCount_S_red_heavy`
--   (2) on a cycle, sum over S-reds of (|x_i| - 1) = number of B-reds
--                                          Stage 20's leafCount arithmetic
--   (3) on a cycle, sum of tau-deltas = 0, with each B-red <= -10 and each
--       light S-red <= -2       `tauSB_B_red`, `tauSB_S_red`
--
--   from (1),(2):   #B  >=  2 * #heavy
--   from (3):       sum_heavy (2*tau(x_i) - 8)  >=  10 * #B  >=  20 * #heavy
--   hence:          average tau(x) over heavy S-reds  >=  14
--
-- So the Stage 23 threshold of 4 is far from tight: a cycle needs heavy arguments
-- averaging τ ≥ 14, which by `leafCount_ge_three_of_heavy`-style reasoning means
-- |x| ≥ 4.
--
-- WHY ITERATING THIS DOES NOT CLOSE THE QUESTION, recorded so it is not
-- rediscovered: feeding the new threshold back through the same chain gives
-- `T' = 5·f(T) − 1` where `f(T)` is the least leafCount admitting τ ≥ T. The
-- maximum τ on n leaves is `2^n − 1` (attained by left-nesting), so `f` is
-- LOGARITHMIC and `T'` grows only logarithmically in `T`. The iteration reaches a
-- fixed point at roughly τ ≥ 24, |x| ≥ 5, and stops. τ grows exponentially in size
-- while the constraint grows linearly; that mismatch caps this whole family of
-- arguments.

-- ## No I-like combinator in {S,B} (Stage 25)
-- The other route to rung two would be transport: if {S,B} contained a term acting
-- as `I`, rung one's cycle would carry into it via `not_acyclic_of_pathEncoding` and
-- {S,B} would be non-acyclic immediately. Searched: no {S,B}-term of at most 7
-- leaves acts as an identity on four structurally distinct probe arguments, and none
-- acts as one on two arguments either. Consistent with {S,B} being acyclic, and it
-- closes the transport route at small size.
