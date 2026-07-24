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
import CombinatorCalculusPlayground.Universality.Taxonomy
import CombinatorCalculusPlayground.Iota
import CombinatorCalculusPlayground.Isometric

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

-- ## The adequacy interface, exercised on a real inhabitant
-- `Simulation.ofAbstraction` (Defs.lean) reduces `bwd` to a stuttering
-- abstraction function. Non-vacuity check: rebuild `pureS_in_SK` through it.
-- Here the abstraction is the K-freeness decoder and NO step ever stutters —
-- every SK step out of a K-free term advances the source by exactly one
-- PureS step, by Stage 2's `KFree.of_step`. A real machine encoding will
-- stutter on most steps and advance on few; this checks the interface, not
-- the interesting case.
example : Simulation RS.PureS RS.SK :=
  Simulation.ofAbstraction
    (enc := fun a => a.val)
    (abs := fun t => if h : KFree t then some ⟨t, h⟩ else none)
    (habs := fun a => by cases a with | mk t ht => simp [ht])
    (hstep := by
      intro b b' a hstep habs
      -- `abs b = some a` forces b to be K-free with a = ⟨b, _⟩
      by_cases hkb : KFree b
      · simp only [hkb, dif_pos] at habs
        have ha : a = ⟨b, hkb⟩ := (Option.some.inj habs).symm
        subst ha
        have hkb' : KFree b' := hkb.of_step hstep
        exact Or.inr ⟨⟨b', hkb'⟩, hstep, by simp [hkb']⟩
      · simp [hkb] at habs)
    (fwd := fun {a a'} s => RS.Steps.tail s (RS.Steps.refl _))

-- ## The prize-adjacent refutation
-- SCOPE, stated before the theorem so nobody quotes it without this:
-- what follows refutes STEP-FAITHFUL hosting of SK inside pure S, under
-- this taxonomy's pinned Simulation class — the same class the iota
-- refutation used. It does NOT resolve the Wolfram prize question, whose
-- informal notion of universality admits broader encodings. What it
-- establishes precisely: if S alone is universal, its encoding must do
-- non-step-faithful work. The mechanism is the same as iota's, with
-- acyclicity (no_pure_S_cycle) playing the role strict growth played
-- there: SK's explicit Ω ↔ M cycle cannot be carried by an injective
-- encoding into a cycle-free system.
theorem Steps.head_of_ne : ∀ {t u : Term}, (t ⟶* u) → t ≠ u →
    ∃ w, (t ⟶ w) ∧ (w ⟶* u) := by
  intro t u h hne
  cases h with
  | refl => exact absurd rfl hne
  | tail s rest => exact ⟨_, s, rest⟩

theorem no_sim_SK_pureS : ¬ Nonempty (Simulation RS.SK RS.PureS) := by
  rintro ⟨Sim⟩
  -- carry the SK cycle across: enc Ω and enc M are mutually reachable
  -- subtype elements of the K-free carrier.
  have h1 : RS.PureS.Steps (Sim.enc omegaSK) (Sim.enc Mcycle) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr omega_to_M)
  have h2 : RS.PureS.Steps (Sim.enc Mcycle) (Sim.enc omegaSK) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr M_to_omega)
  -- translate to Term-level Steps on the underlying (K-free!) values
  have hv1 : (Sim.enc omegaSK).val ⟶* (Sim.enc Mcycle).val :=
    RS.PureS_steps_iff.mp h1
  have hv2 : (Sim.enc Mcycle).val ⟶* (Sim.enc omegaSK).val :=
    RS.PureS_steps_iff.mp h2
  -- distinct encodings (enc is injective; Ω ≠ M), hence distinct values
  have hne : (Sim.enc omegaSK).val ≠ (Sim.enc Mcycle).val := by
    intro hval
    exact omega_ne_M (Sim.enc_injective (Subtype.ext hval))
  -- a genuine first step exists, and the rest closes the loop: a cycle.
  obtain ⟨w, hstep, hrest⟩ := Steps.head_of_ne hv1 hne
  exact no_pure_S_cycle (Sim.enc omegaSK).property
    ⟨w, hstep, Steps.trans hrest hv2⟩

theorem pureS_not_universalReach_for_SK : ¬ UniversalReach RS.SK RS.PureS :=
  no_sim_SK_pureS

theorem pureS_not_universalNorm_for_SK : ¬ UniversalNorm RS.SK RS.PureS :=
  fun ⟨Sim, _⟩ => no_sim_SK_pureS ⟨Sim⟩

theorem pureS_not_universalConv_for_SK : ¬ UniversalConv RS.SK RS.PureS :=
  fun ⟨Sim, _⟩ => no_sim_SK_pureS ⟨Sim⟩

-- ## The two known acyclic hosts, as instances of RS.Acyclic
-- Strict growth (iota) and τ-termination (pure S) were just two CAUSES of
-- the same property. Naming it lets the generic mechanism refute both.
theorem RS.PureS_acyclic : RS.Acyclic RS.PureS := by
  intro b b' hstep hback
  -- a PureS step is a Term step on K-free values; the return path
  -- converts via the agreement lemma; no_pure_S_cycle finishes.
  exact no_pure_S_cycle b.property
    ⟨b'.val, hstep, RS.PureS_steps_iff.mp hback⟩

theorem RS.Iota_acyclic : RS.Acyclic RS.Iota := by
  intro b b' hstep hback
  -- strict growth forward, monotone return: |b| < |b'| ≤ |b|.
  have hlt := iota_step_lt hstep
  rcases iota_steps_le hback with heq | hlt2
  · exact absurd (heq ▸ hlt) (Nat.lt_irrefl _)
  · exact absurd (Nat.lt_trans hlt hlt2) (Nat.lt_irrefl _)

-- ## C4's semantic core
-- C4 conjectured that the iota refutation generalizes to every
-- one-combinator, single-rule, first-order system whose rule strictly grows
-- size. The conjecture bundles a SEMANTIC claim with a SYNTACTIC class, and
-- the semantic claim is the whole mathematical content — it holds for ANY
-- host with a strictly step-increasing measure, one-combinator or not, and
-- follows in two lines from `RS.Acyclic.of_strict_measure` plus SK's
-- Ω ↔ M cycle. Same lesson as C1: the bundle was what made it look hard.

/-- **C4, semantic core — PROVED.** No host whose every step strictly
increases some Nat-valued measure can path-encode SK. Stated at
`PathEncoding` strength because this is a NEGATIVE claim, where the weaker
class is the stronger result (see the asymmetry note in Taxonomy.lean). -/
theorem no_pathEncoding_SK_of_strict_measure {B : RS} (mu : B.Carrier → Nat)
    (hmono : ∀ {b b' : B.Carrier}, B.step b b' → mu b < mu b') :
    ¬ Nonempty (PathEncoding RS.SK B) :=
  PathEncoding.refute_of_acyclic (RS.Acyclic.of_strict_measure mu hmono)
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M

/-- ...and the `Simulation`-level corollary, for citation alongside the
original refutations. -/
theorem no_sim_SK_of_strict_measure {B : RS} (mu : B.Carrier → Nat)
    (hmono : ∀ {b b' : B.Carrier}, B.step b b' → mu b < mu b') :
    ¬ Nonempty (Simulation RS.SK B) :=
  -- destructuring Nonempty into a Prop goal needs no choice
  fun ⟨Sim⟩ => no_pathEncoding_SK_of_strict_measure mu hmono
    ⟨Sim.toPathEncoding⟩

-- Confirmation that the generalization is the RIGHT one: iota's acyclicity,
-- and hence Stage 4's refutation, is now an instance rather than a bespoke
-- argument. (`RS.Iota_acyclic` above is kept as the original citable form.)
example : RS.Acyclic RS.Iota :=
  RS.Acyclic.of_strict_measure IotaTerm.leafCount iota_step_lt

example : ¬ Nonempty (PathEncoding RS.SK RS.Iota) :=
  no_pathEncoding_SK_of_strict_measure IotaTerm.leafCount iota_step_lt

-- ## Subsumption: both refutations recovered as one-liners
-- Stage 4's iota refutation and Slice 2's pure-S refutation both fall out
-- of the generic mechanism, feeding it the acyclic-host instance and SK's
-- explicit Ω ↔ M cycle. The original theorems (`no_sim_SK_iota`,
-- `no_sim_SK_pureS`) remain untouched as the citable artifacts; these
-- demonstrations pin the consolidation.
example : ¬ Nonempty (Simulation RS.SK RS.PureS) :=
  Simulation.refute_of_acyclic RS.PureS_acyclic
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M

example : ¬ Nonempty (Simulation RS.SK RS.Iota) :=
  Simulation.refute_of_acyclic RS.Iota_acyclic
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M

-- ## Slice 4: the same refutations at their true strength
-- The mechanism needs only injectivity + path-preservation
-- (`PathEncoding`), never `bwd` and never step-count faithfulness. So the
-- two refutations hold against a class much larger than `Simulation`:
-- ANY injective encoding of SK that maps reduction paths to reduction
-- paths is impossible into either host. These are the widened headline
-- results; the `Simulation`-level theorems above are now corollaries of
-- them (`Simulation.toPathEncoding`).

theorem no_pathEncoding_SK_pureS : ¬ Nonempty (PathEncoding RS.SK RS.PureS) :=
  PathEncoding.refute_of_acyclic RS.PureS_acyclic
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M

theorem no_pathEncoding_SK_iota : ¬ Nonempty (PathEncoding RS.SK RS.Iota) :=
  PathEncoding.refute_of_acyclic RS.Iota_acyclic
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M

-- ## The widening has teeth: PathEncoding is STRICTLY weaker
-- Required check, not decoration. If every `PathEncoding` extended to a
-- `Simulation`, the two theorems above would be a renaming of the old ones
-- and the widened claim would be empty. They do not. Witness: a two-point
-- system with NO rewrites admits an injective path-preserving encoding
-- onto SK's Ω/M cycle — `path` is free because the source has no nontrivial
-- paths to preserve — while no `Simulation` can use that same encoder,
-- since `bwd` would have to reflect the host's genuine Ω ⟶* M path back
-- into a source path, forcing `true = false`. That gap is exactly the
-- `bwd` field the refutation never uses.

/-- Two points, no rewrites. -/
@[reducible] def RS.Discrete2 : RS := ⟨Bool, fun _ _ => False⟩

theorem RS.Discrete2_steps_eq {a b : Bool} (h : RS.Discrete2.Steps a b) :
    a = b :=
  -- Raw recursor: `cases`/`induction` hit the same mkElimApp motive error
  -- on RS.Steps at a concrete instance as `iota_steps_le` above.
  h.rec (fun _ => rfl) (fun s _ _ => s.elim)

/-- Injective, path-preserving, and lands on a genuine host cycle. -/
def omegaM_pathEncoding : PathEncoding RS.Discrete2 RS.SK where
  enc := fun b => match b with | true => omegaSK | false => Mcycle
  inj := by
    intro a a' h
    cases a with
    | true  => cases a' with
      | true  => rfl
      | false => exact absurd h omega_ne_M
    | false => cases a' with
      | true  => exact absurd h.symm omega_ne_M
      | false => rfl
  path := fun h => by
    rw [RS.Discrete2_steps_eq h]
    exact RS.Steps.refl _

theorem pathEncoding_strictly_weaker :
    ¬ ∃ S : Simulation RS.Discrete2 RS.SK,
        S.enc = omegaM_pathEncoding.enc := by
  rintro ⟨S, hS⟩
  have hpath : RS.SK.Steps (S.enc true) (S.enc false) := by
    rw [hS]; exact RS.SK_steps_iff.mpr omega_to_M
  exact absurd (RS.Discrete2_steps_eq (S.bwd hpath)) (by decide)
