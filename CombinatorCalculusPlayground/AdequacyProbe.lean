--! # Probing piece (vi): does a stuttering abstraction survive nondeterminism?
-- Stage 8 reduced `bwd` to supplying an abstraction function with the
-- stutter-or-advance property (`RS.bwd_of_abstraction`) and called the
-- remaining obligation "mechanical". Stage 8 also flagged piece (vi) as the
-- one that could fail IN KIND rather than in volume, and said to prototype it
-- before building the machine it is meant to track. This module is that
-- prototype. It finds a failure, and the failure has a fix that is a DESIGN
-- CONSTRAINT on the encoding — which is exactly the kind of thing a prototype
-- is supposed to surface before piece (v) is written.
--
-- The test system: a countdown. `Itower n` is `I (I (... S))` with n copies of
-- I, and one source step n+1 → n corresponds to two host steps
-- (`I t → (K t)(K t) → t`). It is the smallest encoding that is a genuine
-- multi-step machine rather than an inclusion, and — the point — it has
-- GENUINE NONDETERMINISM: `Itower 3` has three redexes, so reduction can
-- proceed outside-in, inside-out, or interleaved.
import CombinatorCalculusPlayground.Universality.Defs
import CombinatorCalculusPlayground.Bracket
import CombinatorCalculusPlayground.Reachability

open Term

/-- `I (I (... S))`, with n copies of I. One countdown step per I-layer. -/
def Itower : Nat → Term
  | 0 => S
  | n + 1 => Term.app I (Itower n)

#guard Itower 0 = S
#guard Itower 1 = Term.app I S
#guard leafCount (Itower 2) = 7

/-- The naive structural abstraction: count pending I-layers, recognising both
an INTACT layer (`I u`) and a HALF-CONSUMED one (`(K u)(K u)`, which is what
an intact layer becomes after its S-redex fires and before its K-redex does).
This is the obvious first attempt, and the one the Stage 8 write-up implicitly
assumed would work. -/
def naiveAbs : Term → Option Nat
  | .S => some 0
  | .app (.app (.app .S .K) .K) u => (naiveAbs u).map (· + 1)
  | .app (.app .K u) (.app .K u') =>
      if u == u' then (naiveAbs u).map (· + 1) else none
  | _ => none

#guard naiveAbs (Itower 0) = some 0
#guard naiveAbs (Itower 3) = some 3
-- the half-consumed shape is recognised too, at the same count
#guard naiveAbs (Term.app (Term.app K (Itower 2)) (Term.app K (Itower 2)))
  = some 3

-- ## The failure
-- S duplicated the layer's argument, so the two copies can be reduced
-- INDEPENDENTLY. One step inside the left copy desynchronises them, and the
-- abstraction — which recognises the half-consumed shape only when the copies
-- are syntactically equal — falls off a cliff to `none`.

/-- A reducible livePayload: `I S` still has its S-redex. -/
def livePayload : Term := Term.app I S

/-- A half-consumed layer over that livePayload. -/
def desync : Term := Term.app (Term.app K livePayload) (Term.app K livePayload)

/-- ...and the same after one step inside the LEFT copy only. -/
def desync' : Term :=
  Term.app (Term.app K (Term.app (Term.app K S) (Term.app K S)))
    (Term.app K livePayload)

theorem desync_step : desync ⟶ desync' :=
  Step.appL (Step.appR (Step.S_red K K S))

#guard naiveAbs desync = some 2
#guard naiveAbs desync' = none   -- the copies no longer match

/-- **The prototype's finding, machine-checked.** `naiveAbs` does NOT satisfy
the stutter-or-advance hypothesis of `RS.bwd_of_abstraction`: there is a step
out of an abstracted state whose target is not abstracted at all. So piece (vi)
is NOT mechanical in the way Stage 8 assumed — the obligation is not "check
each rule", because the abstraction itself is wrong. -/
theorem naiveAbs_not_stuttering :
    ¬ (∀ {b b' : Term} {n : Nat}, (b ⟶ b') → naiveAbs b = some n →
        naiveAbs b' = some n ∨ ∃ m, n = m + 1 ∧ naiveAbs b' = some m) := by
  intro h
  have hbad : naiveAbs desync' = none := by decide
  rcases h desync_step (by decide : naiveAbs desync = some 2) with h1 | ⟨m, _, h2⟩
  · rw [hbad] at h1; simp at h1
  · rw [hbad] at h2; simp at h2

-- ## What the failure teaches, and the design constraint it yields
-- The cause is precise: `S f g x → (f x)(g x)` DUPLICATES `x`, and the two
-- copies then reduce independently. Any abstraction that reads a duplicated
-- subterm syntactically must therefore cope with the copies drifting apart,
-- and the space of drifted states is combinatorial in the number of live
-- redexes inside the duplicated part.
--
-- Two ways out, and the second is the useful one:
--
--   (1) Define the abstraction UP TO JOINABILITY rather than syntactically —
--       accept `(K u₁)(K u₂)` whenever `u₁` and `u₂` are joinable (Slice 1's
--       `Joinable`, which SK confluence makes well-behaved). Correct, but it
--       makes `abs` non-computable-looking and the stutter-or-advance proof
--       has to carry confluence through every case. This is the expensive
--       route.
--
--   (2) CONSTRAIN THE ENCODING so duplication only ever happens to NORMAL
--       FORMS. If `x` is normal when `S f g x` fires, the two copies cannot
--       drift, because neither can step. Desynchronisation becomes
--       impossible by construction and the syntactic abstraction is fine.
--
-- (2) is a design constraint discoverable only by prototyping, and it is a
-- real restriction on piece (v): the tag-step driver must be written so that
-- every argument it duplicates is already in normal form at the moment of
-- duplication. That is achievable — encoded words and symbols are data, and
-- data can be kept normal — but it is a constraint on the machine's
-- construction, not something that can be patched afterwards.
--
-- Confirming the diagnosis: with a NORMAL livePayload the same shape is stable,
-- because there is no step available inside the copies at all.

/-- The same half-consumed shape over a normal livePayload. -/
def sync : Term := Term.app (Term.app K S) (Term.app K S)

#guard naiveAbs sync = some 1
-- S is a normal form, so the only step from `sync` is the head K-redex, which
-- ADVANCES the count 1 → 0 exactly as stutter-or-advance requires:
theorem sync_step : sync ⟶ S := Step.K_red S (Term.app K S)
#guard naiveAbs S = some 0

-- ## Stage 11: the diagnosis, as a theorem
-- Stage 10 observed that a NORMAL payload cannot desynchronise, and checked it
-- on one instance (`sync_step`). Here it is in general: over a normal payload
-- the half-consumed shape has EXACTLY ONE successor, so there is nothing for
-- an abstraction to lose track of. This is the precise sense in which the
-- design constraint fixes the failure.

theorem step_app_K_pair {X u : Term} (hX : NormalForm X)
    (h : Term.app (Term.app Term.K X) (Term.app Term.K X) ⟶ u) : u = X := by
  cases h with
  | K_red _ _ => rfl
  | appL hl => exact absurd ⟨_, hl⟩ (normalForm_app_K hX)
  | appR hr => exact absurd ⟨_, hr⟩ (normalForm_app_K hX)

-- Where the residual risk now sits, stated because it is NOT covered above.
-- `normalForm_bracket` (Bracket.lean) settles that a machine's CODE is normal,
-- so the self-application inside a fixpoint duplicates a normal term and is
-- safe. What it does not settle: a fixpoint's reduct `f (x x f)` hands `f` a
-- PENDING RECURSIVE CALL, which is not normal. If the step function duplicates
-- that argument, drift is possible again. So piece (v) needs a strict
-- discipline — force the recursive call before any duplication of it — and that
-- is an obligation on the driver's construction, not a consequence of anything
-- proved here.

-- ## Stage 13: the pending-recursive-call risk, and a correction to Stage 10
-- Stage 11 left one specific risk: a fixpoint's reduct `f (x x f)` hands the
-- step function a PENDING RECURSIVE CALL, which is not normal, so if the driver
-- duplicates it, drift returns. Stage 10's route (2) — "constrain the encoding
-- so duplication only hits normal forms" — implicitly assumed duplication is
-- something the driver's AUTHOR controls, e.g. by using the recursive call only
-- once. That assumption is false for this program's abstraction algorithm, and
-- the probe below shows why.
--
-- `bracket` is the NAIVE algorithm (its own comment says so): no occurs-check.
-- So `[x](a b) = S ([x]a) ([x]b)` distributes the argument to BOTH branches
-- even when `x` occurs in only one of them — and `S A B u → (A u)(B u)`
-- duplicates `u` at EVERY application node of the body.

/-- A body with exactly ONE occurrence of the abstracted variable. -/
def body1 : TermV := TermV.app .S (.var 0)

#guard toTerm (TermV.bracket 0 body1)
  = Term.app (Term.app S (Term.app K S)) I

/-- **Naive abstraction duplicates its argument even for a single-occurrence
body.** One S-step and `u` appears twice: once in the live branch `I u`, once in
the doomed branch `(K S) u` that will discard it. -/
theorem naive_bracket_duplicates (u : Term) :
    Term.app (toTerm (TermV.bracket 0 body1)) u ⟶
      Term.app (Term.app (Term.app K S) u) (Term.app I u) :=
  Step.S_red (Term.app K S) I u

/-- ...and the doomed copy drifts independently of the live one. So the two
copies of a non-normal argument differ, which is exactly the Stage 10 failure —
reached here from a body that uses its variable ONCE. -/
theorem naive_bracket_drifts :
    Term.app (Term.app (Term.app K S) livePayload) (Term.app I livePayload) ⟶
      Term.app (Term.app (Term.app K S)
        (Term.app (Term.app K S) (Term.app K S))) (Term.app I livePayload) :=
  Step.appL (Step.appR (Step.S_red K K S))

-- ## What this corrects
-- Stage 10 offered two routes and preferred (2), a design constraint, over
-- (1), an abstraction defined up to `Joinable`. Stage 11 then discharged half
-- of (2) by proving code is normal. The probe above shows (2) is NOT sufficient
-- on its own:
--
--   * Occurrence-counting does not help. `body1` uses its variable once and
--     still duplicates.
--   * The duplicate is DOOMED — `(K S) u` discards `u` — but it exists for at
--     least one step, and reduction can act on it in that window. A syntactic
--     abstraction has to assign a source state to the drifted intermediate, and
--     cannot.
--   * Transient duplicates are not an artefact of naive `bracket` either. In
--     SK every `S`-redex duplicates its third argument, so moving a value past
--     another value costs a transient copy. An occurs-check-optimized
--     abstraction reduces how MANY copies appear; it cannot reduce them to zero.
--
-- So Stage 10's route (1) is back on the table, and probably unavoidable: the
-- abstraction must be insensitive to doomed subterms — either defined up to
-- `Joinable` (Slice 1, with SK confluence doing the work), or defined so it
-- reads only the live spine and ignores subterms destined for a `K`-discard.
-- Either way this is a substantially harder obligation than "check each rule",
-- and it is the real cost of piece (vi).
--
-- Stage 11's `normalForm_bracket` is unaffected and still useful: machine CODE
-- is normal, so the fixpoint's self-application is safe. The problem is
-- specifically the pending recursive call, which is data-shaped and not normal.

-- ## Stage 45: the third route — an abstraction blind to doomed subterms
-- Stage 13 closed with two routes dead and a third named but untried. The syntactic abstraction is
-- too FINE (duplicated copies drift), and joinability is too COARSE
-- (`RS.joinable_abs_not_functional`). The third: *"defined so it reads only the live spine and
-- ignores subterms destined for a `K`-discard."*
--
-- There is a mechanism for that, and it is small. A doomed subterm is doomed because some `K` will
-- discard it, so CONTRACT THE K-REDEXES FIRST and read the result. K-reduction on its own strictly
-- lowers `leafCount`, so it terminates with no fuel guesswork, and a doomed copy `(K a) u`
-- collapses to `a` no matter what `u` drifted into. Drift becomes invisible instead of impossible —
-- which is what route (2) could not achieve, since Stage 13 showed transient duplicates are
-- unavoidable in SK.

/-- One K-contraction, leftmost. `S`-redexes are left alone: contracting them is what advances the
machine, and the abstraction must not do that. -/
def kStepOnce : Term → Option Term
  | .app (.app .K a) _ => some a
  | .app a b => match kStepOnce a with
      | some a' => some (.app a' b)
      | none => (kStepOnce b).map (.app a)
  | _ => none

/-- Contract K-redexes to exhaustion. `leafCount` is enough fuel because each K-contraction
discards both the `K` and an argument, so the term strictly shrinks — but that is an argument, not
a proof: this and `kStepOnce` are UNVERIFIED census tooling. Certifying them (soundness, and the
`leafCount` bound) is listed below as part of the remaining work; three attempts at the two
induction proofs ran into the overlapping-pattern equation lemmas and were abandoned rather than
thrashed on, since the finding below does not depend on them. -/
def kNorm : Nat → Term → Term
  | 0, t => t
  | n + 1, t => match kStepOnce t with
      | none => t
      | some u => kNorm n u

/-- The Stage 13 abstraction, made blind to doomed subterms. -/
def absK (t : Term) : Option Nat := naiveAbs (kNorm (leafCount t) t)

-- Route (1) and route (2) both failed on `desync'`. Route (3) does not.
#guard naiveAbs desync = some 2
#guard naiveAbs desync' = none      -- Stage 10's failure: drift lost the count
#guard absK desync = some 1
#guard absK desync' = some 0        -- ...and K-contraction restores it

-- The abstraction still inverts the encoder, which is `habs` and is what makes it a candidate at
-- all — a coarser abstraction that lost this would be useless.
#guard (List.range 8).all (fun n => absK (Itower n) = some n)

-- ## Stutter-or-advance, tested where the obligation actually lives
-- `RS.bwd_of_abstraction` quantifies `hstep` over EVERY pair of host terms, not just the ones
-- reachable from an encoded state. So the test enumerates all SK terms, K included.
def skUpTo : Nat → List (List Term)
  | 0 => [[]]
  | 1 => [[], [S, K]]
  | n + 1 =>
      let prev := skUpTo n
      prev ++ [(List.range n).flatMap (fun i =>
        (prev.getD (i + 1) []).flatMap (fun a =>
          (prev.getD (n - i) []).map (fun b => Term.app a b)))]

def skTerms (n : Nat) : List Term := (skUpTo n).getD n []

#guard (List.range 8).map (fun n => (skTerms n).length) = [0, 2, 4, 16, 80, 448, 2688, 16896]

/-- The countdown machine's step is `n+1 ↦ n`, so tracking means: every host successor either
keeps the count or drops it by exactly one. -/
def stutterOrAdvance (b : Term) : Bool :=
  match absK b with
  | none => true
  | some a => (succs b).all (fun b' =>
      match absK b' with
      | none => false
      | some a' => a' == a || a == a' + 1)

-- Clean over every SK term up to six leaves; measured clean to seven as well (16896 terms at that
-- size), guarded at six for build cost.
#guard (List.range 7).all (fun n => (skTerms n).all stutterOrAdvance)

-- Non-vacuity: the abstraction is DEFINED on plenty of these, so the check above is not passing
-- because `absK` returns `none` everywhere.
#guard (List.range 8).map (fun n => ((skTerms n).filter (fun b => (absK b).isSome)).length)
  = [0, 1, 0, 2, 5, 28, 142, 813]

-- ## What this settles and what it does not
-- SETTLED: the route Stage 13 named and left untried is the right one, and it is cheap. Drift does
-- not have to be prevented (Stage 10's route 2, which Stage 13 refuted) nor tolerated by coarsening
-- (route 1, refuted by `RS.joinable_abs_not_functional`) — it can be made INVISIBLE, by reading the
-- term only after its doomed subterms have been discarded. On the countdown machine the resulting
-- abstraction satisfies stutter-or-advance over every SK term up to seven leaves, with no failures,
-- while still inverting the encoder.
--
-- NOT SETTLED, and both are real:
--   * The general proof. The crux is how an S-step interacts with K-normalisation: a K-step leaves
--     the K-normal form alone (given confluence of K-reduction, which is not proved here), but an
--     S-step can create and destroy K-redexes, so `absK` tracking it is exactly what needs an
--     argument. Empirical agreement over 20386 terms is evidence, not a theorem.
--   * The source system. The countdown is a genuine multi-step machine, which is what the probe
--     needed, but it is not universal. Criterion (a) wants a known-universal source, so piece (v) —
--     a tag-step driver — is still unwritten. What changes is that its hardest obligation now has a
--     mechanism instead of two dead ends.
