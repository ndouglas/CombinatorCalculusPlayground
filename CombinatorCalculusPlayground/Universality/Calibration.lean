--! # Calibration: the definitions have teeth
-- Positive: {S,K} is combinatorially complete (Bracket.lean). Negative —
-- the surprise of this stage: the first-order reading of Barker's ι
-- CANNOT host SK under the pinned Simulation. The argument is a
-- conservation law meeting a cycle: every iota step strictly grows leaf
-- count (+8), while SK reduces (SII)(SII) around a genuine 5-step loop;
-- an injective encoding would need sizes to strictly increase around a
-- circle. Barker's one-combinator universality is thereby LOCATED, not
-- contradicted: it is a λ-calculus (erasing, higher-order) phenomenon,
-- invisible to first-order reachability — exactly the kind of boundary
-- this taxonomy exists to draw.
import CombinatorCalculusPlayground.Universality.Defs
import CombinatorCalculusPlayground.Iota

open Term

-- ## The iota conservation law (compare SFragment: pure S never SHRINKS;
-- first-order iota strictly GROWS — an even stronger conservation).
theorem iota_step_lt {w w' : IotaTerm} (h : IotaTerm.IotaStep w w') :
    IotaTerm.leafCount w < IotaTerm.leafCount w' := by
  induction h with
  | iota_red x =>
    -- 1 + |x|  <  |x| + |Sι| + |Kι|  =  |x| + 9
    simp [IotaTerm.leafCount, IotaTerm.Siota, IotaTerm.Kiota]
    omega
  | appL _ ih => simp [IotaTerm.leafCount]; omega
  | appR _ ih => simp [IotaTerm.leafCount]; omega

theorem iota_steps_le {w w' : IotaTerm} (h : RS.Iota.Steps w w') :
    w = w' ∨ IotaTerm.leafCount w < IotaTerm.leafCount w' := by
  -- Raw recursor: `induction` fails on RS.Steps at a concrete instance
  -- (mkElimApp motive error) — same workaround as RS.SK_steps_iff.
  refine h.rec (fun a => Or.inl rfl) (fun s _ ih => Or.inr ?_)
  -- one strict step s, then either equality (use s's strict bound) or
  -- strictness composing with the tail's bound
  rcases ih with heq | hlt
  · exact heq ▸ iota_step_lt s
  · exact Nat.lt_trans (iota_step_lt s) hlt

-- ## An SK reduction cycle, fully explicit
-- Wdup x would reduce to x x; omegaSK = Wdup Wdup is the classic loop.
def Wdup : Term := app2 S I I
def omegaSK : Term := Term.app Wdup Wdup
def Mcycle : Term := Term.app (Term.app I Wdup) (Term.app I Wdup)

-- omegaSK is definitionally app3 S I I Wdup, so S_red fires directly:
-- (SII)(SII) → (I W)(I W).
theorem omega_to_M : omegaSK ⟶* Mcycle :=
  Steps.tail (Step.S_red I I Wdup) (Steps.refl _)

-- And app I Wdup is definitionally app3 S K K Wdup (I = SKK), so each
-- I-redex takes an S_red then a K_red:
-- (I W)(I W) → ((KW)(KW))(I W) → W (I W) → W ((KW)(KW)) → W W.
theorem M_to_omega : Mcycle ⟶* omegaSK :=
  Steps.tail (Step.appL (Step.S_red K K Wdup))
    (Steps.tail (Step.appL (Step.K_red Wdup (Term.app K Wdup)))
      (Steps.tail (Step.appR (Step.S_red K K Wdup))
        (Steps.tail (Step.appR (Step.K_red Wdup (Term.app K Wdup)))
          (Steps.refl _))))

-- Kernel-checked structural disequality on the derived DecidableEq
-- (plain `decide`; `native_decide` remains banned).
theorem omega_ne_M : omegaSK ≠ Mcycle := by decide

-- ## The refutation
theorem no_sim_SK_iota : ¬ Nonempty (Simulation RS.SK RS.Iota) := by
  rintro ⟨Sim⟩
  have h1 : RS.Iota.Steps (Sim.enc omegaSK) (Sim.enc Mcycle) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr omega_to_M)
  have h2 : RS.Iota.Steps (Sim.enc Mcycle) (Sim.enc omegaSK) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr M_to_omega)
  rcases iota_steps_le h1 with heq1 | hlt1
  · exact omega_ne_M (Sim.enc_injective heq1)
  · rcases iota_steps_le h2 with heq2 | hlt2
    · exact omega_ne_M (Sim.enc_injective heq2.symm)
    · exact absurd (Nat.lt_trans hlt1 hlt2) (Nat.lt_irrefl _)

theorem iota_not_universal_for_SK : ¬ UniversalReach RS.SK RS.Iota :=
  no_sim_SK_iota

-- ## The Simulation class is inhabited (nontrivially)
-- The pure-S fragment sits inside SK by inclusion — enc forgets the
-- K-freeness certificate, dec re-checks it (decidable, Stage 2). This is
-- the class's first machine-checked nontrivial member: it blunts any
-- "Simulation is so strong it's vacuous, making the iota refutation
-- hollow" objection. fwd is a single-step embedding; bwd rides Stage 3's
-- agreement lemmas plus Stage 2's closure.
def pureS_in_SK : Simulation RS.PureS RS.SK where
  enc := fun a => a.val
  dec := fun t => if h : KFree t then some ⟨t, h⟩ else none
  dec_enc := fun a => by
    cases a with
    | mk t ht => simp [ht]
  fwd := fun {a a'} s =>
    -- a PureS step IS an SK step on the carriers
    RS.Steps.tail s (RS.Steps.refl _)
  bwd := fun {a a'} h =>
    RS.PureS_steps_iff.mpr (RS.SK_steps_iff.mp h)

-- The inclusion is NONTRIVIAL because PureS has real dynamics — here is a
-- machine-checked step witness (S S S S → (S S)(S S), both sides K-free):
example : RS.PureS.step
    ⟨app3 S S S S, KFree.app (KFree.app (KFree.app KFree.S KFree.S) KFree.S) KFree.S⟩
    ⟨Term.app (Term.app S S) (Term.app S S),
     KFree.app (KFree.app KFree.S KFree.S) (KFree.app KFree.S KFree.S)⟩ :=
  Step.S_red S S S

-- Sanity: the inclusion composes (here with the identity simulation on SK).
example : Simulation RS.PureS RS.SK := pureS_in_SK.comp (Simulation.id RS.SK)
