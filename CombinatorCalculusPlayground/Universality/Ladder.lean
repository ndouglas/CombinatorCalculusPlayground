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
