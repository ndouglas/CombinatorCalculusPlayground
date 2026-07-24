--! # C4's syntactic residue: one-combinator, single-rule systems
-- Stage 7 proved C4's SEMANTIC core — any host whose steps strictly grow a
-- measure cannot path-encode SK — and registered the residue: C4 as WRITTEN
-- quantifies over "one-combinator, single-rule, first-order systems whose rule
-- is strictly size-increasing on every instance", and nothing in the tree
-- formalized that class. No rule schemas, no matching, no substitution for rule
-- variables. This module builds the class for ARITY ONE and closes C4 there.
--
-- Arity one is not an arbitrary cut: it is exactly ι's arity (`ι x → (x Sι) Kι`,
-- Iota.lean), so this generalizes the very instance C4 was abstracted from —
-- from "ι specifically" to "every arity-1 one-rule system passing a decidable
-- syntactic check". The general-arity case is registered as still open at the
-- bottom of this file, with the precise obstacle.
--
-- The payoff is that C4's informal condition crystallizes into arithmetic. C4
-- said "each rule variable occurs at least once in the reduct AND the reduct is
-- strictly larger even at the minimal instantiation". Here that becomes:
-- `1 ≤ countVar rhs` and `2 ≤ countC rhs` — two decidable counts.
import CombinatorCalculusPlayground.Universality.Calibration

-- ## Terms of a one-combinator system
-- One constant, application, nothing else.

inductive Mono : Type
  | c : Mono
  | app : Mono → Mono → Mono
deriving Repr, DecidableEq

def Mono.leafCount : Mono → Nat
  | .c => 1
  | .app a b => a.leafCount + b.leafCount

theorem Mono.leafCount_pos (t : Mono) : 1 ≤ t.leafCount := by
  induction t with
  | c => exact Nat.le_refl 1
  | app a b iha ihb => simp only [Mono.leafCount]; omega

-- ## Right-hand-side patterns for an arity-1 rule
-- One rule variable, so no variable INDEX is needed — which is what keeps this
-- development free of the occurrence-vector sums the general-arity case needs.

inductive Pat1 : Type
  | var : Pat1
  | c : Pat1
  | app : Pat1 → Pat1 → Pat1
deriving Repr, DecidableEq

/-- Instantiate the rule variable. -/
def Pat1.inst (x : Mono) : Pat1 → Mono
  | .var => x
  | .c => .c
  | .app a b => .app (a.inst x) (b.inst x)

/-- Occurrences of the combinator in the pattern. -/
def Pat1.countC : Pat1 → Nat
  | .var => 0
  | .c => 1
  | .app a b => a.countC + b.countC

/-- Occurrences of the rule variable in the pattern. -/
def Pat1.countVar : Pat1 → Nat
  | .var => 1
  | .c => 0
  | .app a b => a.countVar + b.countVar

/-- **Instantiation is linear in the argument's size.** This is the whole
content of the arity-1 case: the reduct's size is a fixed constant plus the
variable's occurrence count times the argument's size. -/
theorem Pat1.leafCount_inst (x : Mono) (p : Pat1) :
    (p.inst x).leafCount = p.countC + p.countVar * x.leafCount := by
  induction p with
  | var => simp [Pat1.inst, Pat1.countC, Pat1.countVar]
  | c => simp [Pat1.inst, Pat1.countC, Pat1.countVar, Mono.leafCount]
  | app a b iha ihb =>
    -- `omega` cannot distribute a variable product, so `Nat.add_mul` first.
    simp only [Pat1.inst, Pat1.countC, Pat1.countVar, Mono.leafCount, iha, ihb,
      Nat.add_mul]
    omega

-- ## The system, as an RS

inductive MonoStep (rhs : Pat1) : Mono → Mono → Prop
  | red (x : Mono) : MonoStep rhs (.app .c x) (rhs.inst x)
  | appL {t t' u : Mono} : MonoStep rhs t t' → MonoStep rhs (.app t u) (.app t' u)
  | appR {t u u' : Mono} : MonoStep rhs u u' → MonoStep rhs (.app t u) (.app t u')

/-- The arity-1 one-combinator, one-rule system with the given reduct. -/
def RS.Mono1 (rhs : Pat1) : RS := ⟨Mono, MonoStep rhs⟩

-- ## C4's condition, and the growth it buys
-- `1 ≤ countVar` is C4's "each rule variable occurs at least once in the
-- reduct"; `2 ≤ countC` is its "strictly larger even at the minimal
-- instantiation", made arithmetic. Both are decidable by inspection of the
-- reduct pattern.

theorem monoStep_lt {rhs : Pat1} (hv : 1 ≤ rhs.countVar) (hc : 2 ≤ rhs.countC)
    {t u : Mono} (h : MonoStep rhs t u) : t.leafCount < u.leafCount := by
  induction h with
  | red x =>
    -- LHS = 1 + |x|; RHS = countC + countVar * |x| ≥ 2 + |x|
    rw [Pat1.leafCount_inst]
    have hmul : x.leafCount ≤ rhs.countVar * x.leafCount :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [Mono.leafCount]
    omega
  | appL _ ih => simp only [Mono.leafCount]; omega
  | appR _ ih => simp only [Mono.leafCount]; omega

theorem RS.Mono1_acyclic {rhs : Pat1} (hv : 1 ≤ rhs.countVar)
    (hc : 2 ≤ rhs.countC) : RS.Acyclic (RS.Mono1 rhs) :=
  RS.Acyclic.of_strict_measure Mono.leafCount (monoStep_lt hv hc)

/-- **C4, arity-1 case — PROVED.** No one-combinator, single-rule, arity-1
system whose reduct uses the rule variable and contains at least two
combinators can path-encode SK. Stated at `PathEncoding` strength, correct for
a negative claim (Stage 7's asymmetry note). -/
theorem no_pathEncoding_SK_mono1 {rhs : Pat1} (hv : 1 ≤ rhs.countVar)
    (hc : 2 ≤ rhs.countC) : ¬ Nonempty (PathEncoding RS.SK (RS.Mono1 rhs)) :=
  no_pathEncoding_SK_of_strict_measure Mono.leafCount (monoStep_lt hv hc)

theorem no_sim_SK_mono1 {rhs : Pat1} (hv : 1 ≤ rhs.countVar)
    (hc : 2 ≤ rhs.countC) : ¬ Nonempty (Simulation RS.SK (RS.Mono1 rhs)) :=
  fun ⟨Sim⟩ => no_pathEncoding_SK_mono1 hv hc ⟨Sim.toPathEncoding⟩

-- ## Non-vacuity: ι's rule is an instance
-- ι's rule is `ι x → (x Sι) Kι` with Sι = ι Kι and Kι = ι(ι(ι ι)) — arity one,
-- so it lives in exactly this class. Writing it as a `Pat1` and checking the
-- two counts confirms the generalization covers the instance C4 came from.

def KiotaPat : Pat1 := .app .c (.app .c (.app .c .c))
def SiotaPat : Pat1 := .app .c KiotaPat
def iotaRhs : Pat1 := .app (.app .var SiotaPat) KiotaPat

#guard KiotaPat.countC = 4          -- matches IotaTerm.leafCount Kiota
#guard SiotaPat.countC = 5          -- matches IotaTerm.leafCount Siota
#guard iotaRhs.countVar = 1         -- the variable is used: C4's first clause
#guard iotaRhs.countC = 9           -- ≥ 2: C4's second clause
#guard iotaRhs.countC ≥ 2

/-- ι's rule shape falls to the general theorem, with both clauses of C4's
condition discharged by `decide`. -/
example : ¬ Nonempty (PathEncoding RS.SK (RS.Mono1 iotaRhs)) :=
  no_pathEncoding_SK_mono1 (by decide) (by decide)

-- SCOPE, so this is not misread: `RS.Mono1 iotaRhs` is ι's RULE SHAPE over the
-- abstract carrier `Mono`, not the `RS.Iota` instance in Calibration.lean, whose
-- carrier is `IotaTerm`. The two are isomorphic and nothing here re-derives
-- `no_pathEncoding_SK_iota`. What this example shows is that the general
-- theorem's hypotheses are satisfiable by a rule the program already cares
-- about — i.e. that C4's condition is not vacuous.

-- ## What remains of C4: general arity
-- The residue is now precisely delimited. For arity n the reduct's size is
-- still linear in the arguments, but with a COEFFICIENT VECTOR rather than a
-- single coefficient:
--     |inst σ R|  =  countC R + Σ_{i<n} (countVar i R) · |σ i|
-- and the LHS is `1 + Σ_{i<n} |σ i|`. The condition generalizes to
-- "every countVar i R ≥ 1, and countC R ≥ 2" — the same shape, and the same
-- proof idea — but establishing the displayed formula needs sums over `i < n`
-- and their algebra: additivity over `app`, an indicator-sum lemma for the
-- `var j` case, and a partition lemma to split the variable list across an
-- application node. None of those exist in core 4.28 in usable form, and this
-- is a zero-dependency tree (no Mathlib `Finset`/`BigOperators`).
--
-- So: C4 is PROVED for arity 1 and remains open for arity ≥ 2, with the
-- obstacle being list-sum algebra rather than anything about combinators. That
-- is bulk work with no hidden research problem, which is the honest assessment
-- Stage 13 gave the whole residue.
