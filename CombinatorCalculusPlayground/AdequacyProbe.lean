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
