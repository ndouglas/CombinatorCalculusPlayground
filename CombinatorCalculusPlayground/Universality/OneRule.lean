--! # C4's syntactic residue: one-combinator, single-rule systems
-- Stage 7 proved C4's SEMANTIC core — any host whose steps strictly grow a
-- measure cannot path-encode SK — and registered the residue: C4 as WRITTEN
-- quantifies over "one-combinator, single-rule, first-order systems whose rule
-- is strictly size-increasing on every instance", and nothing in the tree
-- formalized that class. No rule schemas, no matching, no substitution for rule
-- variables. This module builds the class and closes C4 AT EVERY ARITY.
--
-- Read in two passes. The first half does ARITY ONE (`Pat1`, `RS.Mono1`), where
-- a single coefficient replaces the occurrence vector and no sums are needed —
-- ι's arity, so it already generalizes the instance C4 was abstracted from. The
-- second half (Stage 15) does GENERAL ARITY (`Pat`, `RS.Poly`), which Stage 14
-- had registered as blocked on "list-sum algebra". That framing was wrong in one
-- specific way, noted at the section head: taking the assignment as a FUNCTION
-- rather than a list removes the lists entirely.
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

-- ## What remained of C4 after Stage 14 — SUPERSEDED by the general-arity
-- ## section below (Stage 15). Kept as the record of how the gap was framed.
-- The residue was described as follows. For arity n the reduct's size is
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

-- ## General arity (Stage 15)
-- Stage 14 left the general-arity case open, naming the obstacle as "list-sum
-- algebra". That framing was pessimistic in one specific way: it assumed the
-- rule's arguments arrive as a LIST, which forces `getD` bookkeeping and a
-- cons/append mismatch against range-based sums. Taking the assignment as a
-- FUNCTION `σ : Nat → Mono` and recursing on the arity instead removes the
-- lists entirely. What is left is seven small facts about `Σ_{i<n}`.

/-- Sum of `f` over `0 .. n-1`. -/
def sumTo (n : Nat) (f : Nat → Nat) : Nat := ((List.range n).map f).sum

theorem sumTo_succ (n : Nat) (f : Nat → Nat) : sumTo (n + 1) f = sumTo n f + f n := by
  simp [sumTo, List.range_succ]

theorem sumTo_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumTo n f = sumTo n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ, sumTo_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumTo_eq_zero {n : Nat} {f : Nat → Nat} (h : ∀ i, i < n → f i = 0) :
    sumTo n f = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [sumTo_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumTo_add (n : Nat) (f g : Nat → Nat) :
    sumTo n (fun i => f i + g i) = sumTo n f + sumTo n g := by
  induction n with
  | zero => rfl
  | succ k ih => rw [sumTo_succ, sumTo_succ, sumTo_succ, ih]; omega

theorem sumTo_le {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i ≤ g i) :
    sumTo n f ≤ sumTo n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    rw [sumTo_succ, sumTo_succ]
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h k (by omega))

theorem sumTo_indicator {n j : Nat} (hj : j < n) (f : Nat → Nat) :
    sumTo n (fun i => (if i = j then 1 else 0) * f i) = f j := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [sumTo_succ]
    by_cases hjk : j = k
    · subst hjk
      rw [sumTo_eq_zero (fun i hi => by
        rw [if_neg (by omega : ¬ (i = j))]; omega)]
      simp
    · rw [ih (by omega), if_neg (by omega : ¬ (k = j))]
      omega

/-- Distributing a coefficient sum through `sumTo`. Stated as its own lemma
rather than via `sumTo_congr` + `sumTo_add`: the congruence form makes `rw`
unify against the wrong function. -/
theorem sumTo_add_mul (n : Nat) (p q x : Nat → Nat) :
    sumTo n (fun i => (p i + q i) * x i)
      = sumTo n (fun i => p i * x i) + sumTo n (fun i => q i * x i) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [sumTo_succ, sumTo_succ, sumTo_succ, ih, Nat.add_mul]; omega

-- ## Patterns with indexed rule variables

inductive Pat : Type
  | var : Nat → Pat
  | c : Pat
  | app : Pat → Pat → Pat
deriving Repr, DecidableEq

def Pat.inst (σ : Nat → Mono) : Pat → Mono
  | .var i => σ i
  | .c => .c
  | .app a b => .app (a.inst σ) (b.inst σ)

def Pat.countC : Pat → Nat
  | .var _ => 0
  | .c => 1
  | .app a b => a.countC + b.countC

def Pat.countVar (i : Nat) : Pat → Nat
  | .var j => if i = j then 1 else 0
  | .c => 0
  | .app a b => a.countVar i + b.countVar i

/-- **Instantiation is linear in the arguments' sizes** — the general-arity form
of `Pat1.leafCount_inst`, with an occurrence-count coefficient per variable. -/
theorem Pat.leafCount_inst {n : Nat} (σ : Nat → Mono) (p : Pat)
    (hp : ∀ i, p.countVar i ≠ 0 → i < n) :
    (p.inst σ).leafCount
      = p.countC + sumTo n (fun i => p.countVar i * (σ i).leafCount) := by
  induction p with
  | var j =>
    have hj : j < n := hp j (by simp [Pat.countVar])
    simp only [Pat.inst, Pat.countC, Pat.countVar, Nat.zero_add]
    rw [sumTo_indicator hj]
  | c =>
    simp only [Pat.inst, Pat.countC, Pat.countVar, Mono.leafCount]
    rw [sumTo_eq_zero (fun i _ => by omega)]
  | app a b iha ihb =>
    have hpa : ∀ i, a.countVar i ≠ 0 → i < n := by
      intro i hi; exact hp i (by simp only [Pat.countVar]; omega)
    have hpb : ∀ i, b.countVar i ≠ 0 → i < n := by
      intro i hi; exact hp i (by simp only [Pat.countVar]; omega)
    simp only [Pat.inst, Pat.countC, Pat.countVar, Mono.leafCount,
      iha hpa, ihb hpb]
    rw [sumTo_add_mul]
    omega

-- ## The left-hand side: the combinator applied to n arguments

def applyVars (hd : Mono) (σ : Nat → Mono) : Nat → Mono
  | 0 => hd
  | n + 1 => .app (applyVars hd σ n) (σ n)

theorem leafCount_applyVars (hd : Mono) (σ : Nat → Mono) (n : Nat) :
    (applyVars hd σ n).leafCount
      = hd.leafCount + sumTo n (fun i => (σ i).leafCount) := by
  induction n with
  | zero => simp [applyVars, sumTo]
  | succ k ih => simp only [applyVars, Mono.leafCount, ih, sumTo_succ]; omega

-- ## The arity-n system, and C4 in full

inductive PatStep (n : Nat) (rhs : Pat) : Mono → Mono → Prop
  | red (σ : Nat → Mono) : PatStep n rhs (applyVars .c σ n) (rhs.inst σ)
  | appL {t t' u : Mono} : PatStep n rhs t t' → PatStep n rhs (.app t u) (.app t' u)
  | appR {t u u' : Mono} : PatStep n rhs u u' → PatStep n rhs (.app t u) (.app t u')

/-- The arity-`n` one-combinator, one-rule system with the given reduct. -/
def RS.Poly (n : Nat) (rhs : Pat) : RS := ⟨Mono, PatStep n rhs⟩

/-- C4's condition at general arity: every rule variable occurs in the reduct,
and the reduct holds at least two combinators. Both decidable per variable. -/
theorem patStep_lt {n : Nat} {rhs : Pat}
    (hwf : ∀ i, rhs.countVar i ≠ 0 → i < n)
    (hv : ∀ i, i < n → 1 ≤ rhs.countVar i) (hc : 2 ≤ rhs.countC)
    {t u : Mono} (h : PatStep n rhs t u) : t.leafCount < u.leafCount := by
  induction h with
  | red σ =>
    rw [leafCount_applyVars, Pat.leafCount_inst σ rhs hwf]
    have hle : sumTo n (fun i => (σ i).leafCount)
        ≤ sumTo n (fun i => rhs.countVar i * (σ i).leafCount) :=
      sumTo_le (fun i hi => Nat.le_mul_of_pos_left _ (by have := hv i hi; omega))
    simp only [Mono.leafCount]
    omega
  | appL _ ih => simp only [Mono.leafCount]; omega
  | appR _ ih => simp only [Mono.leafCount]; omega

theorem RS.Poly_acyclic {n : Nat} {rhs : Pat}
    (hwf : ∀ i, rhs.countVar i ≠ 0 → i < n)
    (hv : ∀ i, i < n → 1 ≤ rhs.countVar i) (hc : 2 ≤ rhs.countC) :
    RS.Acyclic (RS.Poly n rhs) :=
  RS.Acyclic.of_strict_measure Mono.leafCount (patStep_lt hwf hv hc)

/-- **C4 — PROVED, at every arity.** No one-combinator, single-rule,
first-order system whose reduct uses every rule variable and contains at least
two combinators can path-encode SK. This is C4 as written, with its informal
size condition replaced by two decidable counts on the reduct pattern. -/
theorem no_pathEncoding_SK_poly {n : Nat} {rhs : Pat}
    (hwf : ∀ i, rhs.countVar i ≠ 0 → i < n)
    (hv : ∀ i, i < n → 1 ≤ rhs.countVar i) (hc : 2 ≤ rhs.countC) :
    ¬ Nonempty (PathEncoding RS.SK (RS.Poly n rhs)) :=
  no_pathEncoding_SK_of_strict_measure Mono.leafCount (patStep_lt hwf hv hc)

theorem no_sim_SK_poly {n : Nat} {rhs : Pat}
    (hwf : ∀ i, rhs.countVar i ≠ 0 → i < n)
    (hv : ∀ i, i < n → 1 ≤ rhs.countVar i) (hc : 2 ≤ rhs.countC) :
    ¬ Nonempty (Simulation RS.SK (RS.Poly n rhs)) :=
  fun ⟨Sim⟩ => no_pathEncoding_SK_poly hwf hv hc ⟨Sim.toPathEncoding⟩

-- Non-vacuity at general arity: ι's rule again, now at arity 1 within the
-- arity-n class, and a genuine arity-3 example (`c x y z → x (y z) c c`).
def iotaRhsN : Pat := .app (.app (.var 0) (.app .c (.app .c (.app .c (.app .c .c)))))
  (.app .c (.app .c (.app .c .c)))

#guard iotaRhsN.countVar 0 = 1
#guard iotaRhsN.countC = 9

def arity3Rhs : Pat :=
  .app (.app (.app (.var 0) (.app (.var 1) (.var 2))) .c) .c

#guard arity3Rhs.countVar 0 = 1
#guard arity3Rhs.countVar 1 = 1
#guard arity3Rhs.countVar 2 = 1
#guard arity3Rhs.countVar 3 = 0
#guard arity3Rhs.countC = 2

example : ¬ Nonempty (PathEncoding RS.SK (RS.Poly 3 arity3Rhs)) :=
  no_pathEncoding_SK_poly
    (by
      intro i hi
      rcases i with _ | _ | _ | k
      · omega
      · omega
      · omega
      · simp [arity3Rhs, Pat.countVar] at hi)
    (by
      intro i hi
      rcases i with _ | _ | _ | k
      · decide
      · decide
      · decide
      · omega)
    (by decide)
