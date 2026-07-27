--! # A tag system inside SK, end to end
-- Piece (v) is a tag-step driver. Before building one for a universal tag system — the hard construction —
-- this file runs the whole pipeline on the simplest genuine one, to find out whether the plumbing composes.
--
-- The choice of system is the trick. A tag system with deletion number `m = 1` over a one-symbol alphabet,
-- whose rule appends nothing, deletes one symbol per step and appends none: its words are determined by
-- their length, and it halts exactly when empty. That is `RS.Countdown` with `List.length` as the
-- isomorphism — so `Simulation.comp` with Stage 48's `countdownInSK` gives a `Simulation` from an actual
-- `TagSystem` into SK, with no new SK-side work at all.
--
-- What that is worth, stated up front: the pipeline composes, and a `TagSystem` is now hosted in SK by a
-- machine-checked `Simulation`. What it is NOT worth: a unary tag system is not universal, so criterion (a)
-- still wants a genuinely universal `T`, and that still needs a real driver.
import CombinatorCalculusPlayground.Countdown

open Term

/-- Deletion number one, one symbol, empty rule: delete a symbol per step and append nothing. -/
def unaryTag : TagSystem where
  Sym := Unit
  m := 1
  rule := fun _ => []

/-- A list of units is its own length. -/
theorem listUnit_eq : ∀ (w : List Unit), w = List.replicate w.length () := by
  intro w
  induction w with
  | nil => rfl
  | cons a t ih =>
      show a :: t = List.replicate (t.length + 1) ()
      rw [List.replicate_succ, ← ih]

/-- One tag step: drop the head. -/
theorem unaryTag_step (rest : List Unit) :
    (RS.Tag unaryTag).step (() :: rest) rest :=
  ⟨(), rest, rfl, by simp [unaryTag], by simp [unaryTag]⟩

theorem unaryTag_steps_of_le : ∀ (k n : Nat),
    (RS.Tag unaryTag).Steps (List.replicate (n + k) ()) (List.replicate n ()) := by
  intro k
  induction k with
  | zero => intro n; exact RS.Steps.refl _
  | succ j ih =>
      intro n
      have hr : List.replicate (n + (j + 1)) () = () :: List.replicate (n + j) () := by
        rw [show n + (j + 1) = (n + j) + 1 from by omega, List.replicate_succ]
      rw [hr]
      exact RS.Steps.tail (unaryTag_step _) (ih n)

/-- **The unary tag system is the countdown.** `List.length` is the isomorphism: one tag step deletes one
symbol, and a word is stuck exactly when it is empty. -/
def unaryTagInCountdown : Simulation (RS.Tag unaryTag) RS.Countdown where
  enc := List.length
  dec := fun n => some (List.replicate n ())
  dec_enc := by
    intro w
    show some (List.replicate w.length ()) = some w
    rw [← listUnit_eq]
  fwd := by
    intro w w' h
    obtain ⟨a, rest, hw, _, hw'⟩ := h
    subst hw
    simp [unaryTag] at hw'
    have hlen : (a :: rest).length = w'.length + 1 := by rw [hw']; simp
    exact RS.Steps.tail hlen (RS.Steps.refl _)
  bwd := by
    intro w w' h
    have hle : w'.length ≤ w.length := countdown_steps_le h
    have hk : w.length = w'.length + (w.length - w'.length) := by omega
    have hres := unaryTag_steps_of_le (w.length - w'.length) w'.length
    rw [← hk] at hres
    rw [listUnit_eq w, listUnit_eq w']
    exact hres

/-- **A `TagSystem` hosted in SK, machine-checked, end to end.** Composition of the isomorphism above with
Stage 48's `countdownInSK` — no new SK-side work; the pipeline simply composes. -/
def unaryTagInSK : Simulation (RS.Tag unaryTag) RS.SK :=
  Simulation.comp unaryTagInCountdown countdownInSK

theorem universalReach_unaryTag_SK : UniversalReach (RS.Tag unaryTag) RS.SK :=
  ⟨unaryTagInSK⟩

/-- The same, through the trajectory-relation `Simulation` instead — so the tag system inherits both of the
countdown's independent adequacy proofs. -/
def unaryTagInSK' : Simulation (RS.Tag unaryTag) RS.SK :=
  Simulation.comp unaryTagInCountdown countdownInSK'

-- Anchors: the encoding is what it says, and the system really does step.
example : (RS.Tag unaryTag).step [(), (), ()] [(), ()] := unaryTag_step _
example : (RS.Tag unaryTag).NormalForm [] := by
  rintro ⟨w', a, rest, hw, hlen, _⟩
  simp at hw
example : unaryTagInSK.enc [(), (), ()] = Itower 3 := rfl
#guard leafCount (Itower 3) = 10

-- ## What this settles, and what it does not
-- SETTLED: the pipeline composes. `Simulation.comp` was written in Stage 8 and never used on anything but
-- toys; it now carries a `TagSystem` into SK through two layers, and the tag system inherits BOTH of the
-- countdown's adequacy proofs for free, because composition does not care which `bwd` it is handed.
--
-- NOT SETTLED, and it is the whole of criterion (a): `unaryTag` is not universal. Deletion number one with
-- an empty rule cannot compute — it is a countdown wearing a tag system's clothes, which is exactly why the
-- composition was free. A universal tag system (Cocke–Minsky: m = 2 over a finite alphabet) needs the
-- driver to INSPECT a symbol and APPEND its rule, and neither happens here.
--
-- What this file does buy for that construction: it fixes the shape. Encode the word, simulate one deletion
-- per source step, and reuse the countdown's adequacy template — with the driver's extra work being the
-- symbol dispatch, which Stage 50 already measured as compatible with the K-normal-form abstraction, and
-- the rule append, which is untested.

-- ## Stage 60: the rule append is not a component
-- Stage 59 ranked "test the rule append" first, calling it the last unmeasured piece of a driver. The
-- measurement says it is not a piece at all — in the right encoding it is a CONSTANT.
--
-- Encode a word as its right fold: `[x₁…xₙ]` is `λc.λn. c x₁ (c x₂ (… (c xₙ n)))`. Then appending at the
-- END is substituting for `n`, which is a fixed wrapper:
--
--     APPEND = λL.λy.λc.λn. L c (c y n)
--
-- No recursion, no traversal, no dependence on the list. Deletion at the FRONT is equally cheap for a fold,
-- which is why this encoding suits tag systems: they consume at one end and produce at the other.

/-- `APPEND = λL.λy.λc.λn. L c (c y n)`, compiled by bracket abstraction. -/
def bodyAppend : TermV :=
  TermV.app2 (.var 3) (.var 1) (TermV.app2 (.var 1) (.var 2) (.var 0))

def APPEND : Term :=
  toTerm (TermV.bracket 3 (TermV.bracket 2 (TermV.bracket 1 (TermV.bracket 0 bodyAppend))))

/-- The empty word, and the one- and two-symbol words, as folds. -/
def ENCNIL : Term := toTerm (TermV.bracket 1 (TermV.bracket 0 (.var 0)))

def ENCONE (y : TermV) : Term :=
  toTerm (TermV.bracket 1 (TermV.bracket 0 (TermV.app2 (.var 1) y (.var 0))))

def ENCTWO (y z : TermV) : Term :=
  toTerm (TermV.bracket 1 (TermV.bracket 0
    (TermV.app2 (.var 1) y (TermV.app2 (.var 1) z (.var 0)))))

private def nfOf (t : Term) : Option Term := (normalize 20000 t).map (·.1)
private def ap4 (f a b c d : Term) : Term := Term.app (Term.app (Term.app (Term.app f a) b) c) d

-- **`APPEND` is a constant.** 414 leaves from the NAIVE bracket algorithm (no occurs check — an optimised
-- abstraction would be far smaller), and the same 414 whatever it is applied to.
#guard leafCount APPEND = 414
#guard leafCount ENCNIL = 8

-- Appending agrees with direct encoding, checked against two different observers `(c, n)` so the test is
-- not passing by collapse: `(K, S)` keeps only the head, `(I, K)` keeps the structure.
#guard nfOf (ap4 APPEND ENCNIL S K S) = nfOf (Term.app (Term.app (ENCONE .S) K) S)
#guard nfOf (ap4 APPEND ENCNIL S (app2 S K K) K)
  = nfOf (Term.app (Term.app (ENCONE .S) (app2 S K K)) K)
#guard nfOf (ap4 APPEND (ENCONE .S) K K S) = nfOf (Term.app (Term.app (ENCTWO .S .K) K) S)
#guard nfOf (ap4 APPEND (ENCONE .S) K (app2 S K K) K)
  = nfOf (Term.app (Term.app (ENCTWO .S .K) (app2 S K K)) K)

-- ## What that does to the remaining work
-- Stage 59's premise was wrong, and in the useful direction. The append is not the last unmeasured
-- component; it is not a component. With a fold encoding both of a tag step's halves — take from the front,
-- add at the back — are fixed combinators, so a driver needs no recursion for its LIST operations at all.
--
-- What a driver does still need recursion for is SELF-REPRODUCTION: `enc w` must reduce to `enc w'`, and the
-- encoding contains the driver, so the driver must rebuild itself. That is self-application, and it is
-- exactly what Stages 50–52 isolated and could not settle without building the thing.
--
-- So piece (v) has one unresolved ingredient rather than three, and it is the one already named. Symbol
-- dispatch: measured compatible (Stage 50). Rule append: constant, shown here. Self-reproduction: open.

-- ## Stage 61: self-reproduction, without a fixpoint combinator
-- Stage 60 left exactly one ingredient open: the driver must rebuild itself, because `enc w` contains it and
-- has to reduce to `enc w'`. I had been assuming that meant a fixpoint combinator and the sprawl Stage 50
-- measured. It does not. Two abstractions suffice:
--
--     W = λx.λd. x x (F d)      and then      W W d ⟶* W W (F d)
--
-- for an ARBITRARY step function `F`. The data advances, the driver reappears, and nothing recurses — the
-- self-application is a single `S`-redex, not an unfolding. Bracket-abstracting by hand keeps it small.

/-- `λx.λd. x x (F d)`, abstracted by hand: `λd. x x (F d)` is `S (K (x x)) F`, and abstracting `x` from that
gives `S (S (K S) (S (K K) (S I I))) (K F)`. -/
def selfRepW (F : Term) : Term :=
  app2 S (app2 S (Term.app K S) (app2 S (Term.app K K) (app2 S I I))) (Term.app K F)

/-- The driver: the wrapper applied to itself. -/
def selfRep (F : Term) : Term := Term.app (selfRepW F) (selfRepW F)

/-- The wrapper's self-application exposes the shape that advances data. -/
theorem selfRepW_unfold (F : Term) :
    selfRep F ⟶* app2 S (Term.app K (selfRep F)) F := by
  have hI : ∀ x : Term, Term.app I x ⟶* x := I_reduces
  -- `S I I W ⟶* W W`
  have hSII : Term.app (app2 S I I) (selfRepW F) ⟶* selfRep F :=
    Steps.tail (Step.S_red I I (selfRepW F))
      (Steps.congApp (hI (selfRepW F)) (hI (selfRepW F)))
  -- `S (K K) (S I I) W ⟶* K (W W)`
  have hB : Term.app (app2 S (Term.app K K) (app2 S I I)) (selfRepW F)
      ⟶* Term.app K (selfRep F) :=
    Steps.tail (Step.S_red (Term.app K K) (app2 S I I) (selfRepW F))
      (Steps.congApp (Steps.single (Step.K_red K (selfRepW F))) hSII)
  -- `S (K S) B W ⟶* S (K (W W))`
  have hA : Term.app (app2 S (Term.app K S) (app2 S (Term.app K K) (app2 S I I))) (selfRepW F)
      ⟶* Term.app S (Term.app K (selfRep F)) :=
    Steps.tail (Step.S_red (Term.app K S) (app2 S (Term.app K K) (app2 S I I)) (selfRepW F))
      (Steps.congApp (Steps.single (Step.K_red S (selfRepW F))) hB)
  -- and the outer self-application
  refine Steps.tail (Step.S_red _ _ (selfRepW F)) ?_
  exact Steps.congApp hA (Steps.single (Step.K_red F (selfRepW F)))

/-- **Self-reproduction with advancing data.** For any step function `F`, the driver applied to `d` reduces
to the driver applied to `F d`. This is the ingredient Stage 60 left open, and it needs no fixpoint. -/
theorem selfRep_advances (F d : Term) :
    Term.app (selfRep F) d ⟶* Term.app (selfRep F) (Term.app F d) := by
  refine Steps.trans (Steps.congL (selfRepW_unfold F)) ?_
  refine Steps.tail (Step.S_red (Term.app K (selfRep F)) F d) ?_
  exact Steps.congL (Steps.single (Step.K_red (selfRep F) d))

-- Small, and the size is independent of `F` apart from carrying `F` itself.
#guard leafCount (selfRepW S) = 16
#guard (List.range 5).all (fun n => leafCount (selfRepW (Itower n)) = 15 + leafCount (Itower n))

-- ## Stage 62: the fold-list toolkit, and why it needed the occurs check
-- Assembling the step function needs `head`, `tail`, `cons`, `nil` and pairs on fold-encoded words. All are
-- fixed combinators — the traversal in `tail` is performed BY THE DATA's own fold, not by driver recursion.
--
-- Compiled with the naive `bracket` they are unusable: `TAIL` came out at 14100 leaves and `normalize`
-- ABORTED on it. Compiled with `bracketOpt` (Stage 62, Bracket.lean) the same definitions give 192 leaves and
-- run in a third of a second. The occurs check was the difference between a design and a program.

private def V (n : Nat) : TermV := .var n
private def o1 (b : TermV) : Term := toTerm (TermV.bracketOpt 0 b)
private def o3 (b : TermV) : Term :=
  toTerm (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b)))
private def o4 (b : TermV) : Term :=
  toTerm (TermV.bracketOpt 3 (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b))))

/-- `[]` as a fold: `λc n. n`. -/
def NILf : Term := toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0 (V 0)))
/-- `cons`: `λx L c n. c x (L c n)`. -/
def CONSf : Term := o4 (TermV.app2 (V 1) (V 3) (TermV.app2 (V 2) (V 1) (V 0)))
/-- `head`: `λL. L K K` — `c := K` discards the recursive part, `n := K` is the default. -/
def HEADf : Term := o1 (TermV.app2 (V 0) .K .K)
def PAIRf : Term := o3 (TermV.app2 (V 0) (V 2) (V 1))
def FSTf : Term := o1 (TermV.app (V 0) .K)
def SNDf : Term := o1 (TermV.app (V 0) (TermV.app .S .K))

/-- `tail`, by the standard pair trick: fold building `⟨cons x (fst p), fst p⟩` and take the second. -/
def TAILSTEPf : Term :=
  toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0 (TermV.app2 (ofTerm PAIRf)
    (TermV.app2 (ofTerm CONSf) (V 1) (TermV.app (ofTerm FSTf) (V 0)))
    (TermV.app (ofTerm FSTf) (V 0)))))

def TAILf : Term := o1 (TermV.app (ofTerm SNDf)
  (TermV.app2 (V 0) (ofTerm TAILSTEPf) (TermV.app2 (ofTerm PAIRf) (ofTerm NILf) (ofTerm NILf))))

-- Sizes, all constant in the word:
#guard (leafCount NILf, leafCount CONSf, leafCount HEADf) = (4, 66, 9)
#guard (leafCount PAIRf, leafCount FSTf, leafCount SNDf) = (29, 6, 7)
#guard (leafCount TAILSTEPf, leafCount TAILf) = (139, 192)

private def nfOf' (t : Term) : Option Term := (normalize 100000 t).map (·.1)
private def obs (L c n : Term) : Term := Term.app (Term.app L c) n
private def LSK : Term := Term.app (Term.app CONSf S) (Term.app (Term.app CONSf K) NILf)
private def LK : Term := Term.app (Term.app CONSf K) NILf

-- `head [S,K] = S`, and `tail [S,K]` agrees with `[K]` under two different observers, so the agreement is
-- not by collapse.
#guard nfOf' (Term.app HEADf LSK) = some S
#guard nfOf' (obs (Term.app TAILf LSK) I S) = nfOf' (obs LK I S)
#guard nfOf' (obs (Term.app TAILf LSK) K S) = nfOf' (obs LK K S)

-- ## Where the driver stands
-- Every component now exists and runs: `head` and `tail` here, `APPEND` in Stage 60, dispatch for free
-- (Stage 50 — symbols encoded as `K` and `S K` select branches by application), and self-reproduction in
-- Stage 61. What remains is to write the m = 2 step function as one term and prove `fwd` for it, which is
-- assembly rather than design — and which will be a long proof, because `fwd` has to be a reduction chain
-- and the assembled term will be in the hundreds of leaves.

-- ## Stage 63: the m = 2 step function, assembled and validated
-- Every piece is constant-size, including the rule append — concatenating two folds is
-- `λL M c n. L c (M c n)`, which is cheaper than Stage 60's single-element append and handles rules of any
-- length. The system below is a genuine two-symbol, deletion-number-two tag system: `a ↦ [b]`, `b ↦ [a,b]`.

/-- Symbols as booleans, so dispatch is application (Stage 50). -/
def symA : Term := K
def symB : Term := Term.app S K

/-- Fold concatenation: `λL M c n. L c (M c n)`. -/
def CONCATf : Term := o4 (TermV.app2 (V 3) (V 1) (TermV.app2 (V 2) (V 1) (V 0)))

/-- The word `[b]`, and the word `[a,b]` — the two rule outputs. -/
def ruleOutA : Term := Term.app (Term.app CONSf symB) NILf
def ruleOutB : Term := Term.app (Term.app CONSf symA) (Term.app (Term.app CONSf symB) NILf)

/-- `λs. s ruleOutA ruleOutB` — the dispatch. -/
def RULEf : Term := o1 (TermV.app2 (V 0) (ofTerm ruleOutA) (ofTerm ruleOutB))

/-- **The step function.** `λL. CONCAT (TAIL (TAIL L)) (RULE (HEAD L))` — drop two, append the head's rule. -/
def STEPf : Term := o1 (TermV.app2 (ofTerm CONCATf)
  (TermV.app (ofTerm TAILf) (TermV.app (ofTerm TAILf) (V 0)))
  (TermV.app (ofTerm RULEf) (TermV.app (ofTerm HEADf) (V 0))))

/-- Words as fold-encoded lists. -/
def mkWord : List Term → Term
  | [] => NILf
  | x :: xs => Term.app (Term.app CONSf x) (mkWord xs)

#guard (leafCount CONCATf, leafCount RULEf, leafCount STEPf) = (68, 218, 696)

private def nfW (t : Term) : Option Term := (normalize 300000 t).map (·.1)
private def agrees (w w' : List Term) : Bool :=
  (nfW (obs (Term.app STEPf (mkWord w)) I S) == nfW (obs (mkWord w') I S)) &&
  (nfW (obs (Term.app STEPf (mkWord w)) K S) == nfW (obs (mkWord w') K S))

-- Four steps of the system, each checked under two observers so agreement cannot be by collapse.
#guard agrees [symA, symA, symB] [symB, symB]          -- drop 2 = [b], append [b]
#guard agrees [symB, symA, symA] [symA, symA, symB]    -- drop 2 = [a], append [a,b]
#guard agrees [symA, symB] [symB]                      -- drop 2 = [],  append [b]
#guard agrees [symB, symB] [symA, symB]                -- drop 2 = [],  append [a,b]
-- ...and a wrong target really does fail, so the checks are not vacuous.
#guard !(agrees [symA, symA, symB] [symA, symB])

/-- **`fwd` follows from step-correctness alone.** The driver half is already proved for any `F`
(`selfRep_advances`), so all that a tag simulation needs is that the step function computes the step. -/
theorem tagFwd_of_step {F d d' : Term} (h : Term.app F d ⟶* d') :
    Term.app (selfRep F) d ⟶* Term.app (selfRep F) d' :=
  Steps.trans (selfRep_advances F d) (Steps.congR h)

-- ## What remains, and a correction to Stage 62's outlook
-- Stage 62 said proving `fwd` would be "a reduction chain over a term in the hundreds of leaves" and called
-- that a proof-engineering problem. Assembling the thing shows a better route, and it was available all along.
--
-- `tagFwd_of_step` reduces `fwd` to `STEPf (mkWord w) ⟶* mkWord w'`, and THAT does not have to be proved by
-- chasing the compiled 696-leaf term. `TermV.bracketOpt_beta` says an abstraction applied to an argument
-- reduces to the substituted body, so the compiled pieces can be reasoned about at the LAMBDA level and
-- composed: `HEADf (mkWord (x :: xs)) ⟶* x`, `TAILf (mkWord (x :: xs)) ⟶* mkWord xs`,
-- `CONCATf (mkWord u) (mkWord v) ⟶* mkWord (u ++ v)`, and the two-case dispatch. Each is an induction over a
-- list, not a walk through a large term.
--
-- So the remaining work is four compositional lemmas and their assembly — real work, but ordinary, and of a
-- kind this development has done many times. What it is NOT is a chain over hundreds of leaves, which is what
-- I expected before writing the term down.

-- ## Stage 64: the four lemmas, step-correctness, and `fwd`
--
-- One of Stage 63's four lemmas is FALSE AS STATED, and it is worth recording why before proving the fixed
-- version. `CONCATf (mkWord u) (mkWord v) ⟶* mkWord (u ++ v)` cannot hold: the left side reduces to a
-- compiled abstraction whose top spine is `S` applied to TWO arguments, and no reduction ever fires a
-- top-level redex there again, while a nonempty `mkWord` is `S` applied to FOUR arguments at its spine. The
-- two are observationally equal — which is exactly what Stage 63's two-observer guards checked — but SK has
-- no extensionality, so observational equality is not reachability. The fix is the classic cons-directed
-- concatenation `CAT = λL M. L CONS M`: folding the left word with `CONS` itself REBUILDS it, symbol by
-- symbol, on top of the right word, so every intermediate stays in `mkWord` form. (It costs 14 more leaves
-- than `CONCATf`, because it carries `CONSf` as a constant — reachability is what the extra leaves buy.)
-- The mistake is the same species as Stage 60's — an unexamined representation assumption, this time
-- "a fold-shaped combinator that computes the right list IS the right list."
--
-- Everything below is at the `Term` level via the β-ladder (`bracketOpt_beta*_Term`, Bracket.lean): first a
-- β-lemma per compiled combinator, then the compositional lemmas over `mkWord`, then assembly.

-- ### β: each compiled combinator applied to arguments reduces to its instantiated body

/-- `[] c n ⟶* n`. -/
theorem NILf_beta (c n : Term) : Term.app (Term.app NILf c) n ⟶* n := by
  have h := bracketOpt_beta2_Term (V 0) c n
  simpa [V, TermV.subst] using h

/-- `cons x L c n ⟶* c x (L c n)`. -/
theorem CONSf_beta (x L c n : Term) :
    Term.app (Term.app (Term.app (Term.app CONSf x) L) c) n
      ⟶* Term.app (Term.app c x) (Term.app (Term.app L c) n) := by
  have h := bracketOpt_beta4_Term (TermV.app2 (V 1) (V 3) (TermV.app2 (V 2) (V 1) (V 0))) x L c n
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

/-- `head L ⟶* L K K`. -/
theorem HEADf_beta (L : Term) : Term.app HEADf L ⟶* Term.app (Term.app L K) K := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (V 0) .K .K) L
  simpa [V, TermV.app2, TermV.subst, toTerm] using h

/-- `pair a b s ⟶* s a b`. -/
theorem PAIRf_beta (a b s : Term) :
    Term.app (Term.app (Term.app PAIRf a) b) s ⟶* Term.app (Term.app s a) b := by
  have h := bracketOpt_beta3_Term (TermV.app2 (V 0) (V 2) (V 1)) a b s
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

/-- `fst p ⟶* p K`. -/
theorem FSTf_beta (p : Term) : Term.app FSTf p ⟶* Term.app p K := by
  have h := bracketOpt_beta_Term 0 (TermV.app (V 0) .K) p
  simpa [V, TermV.subst, toTerm] using h

/-- `snd p ⟶* p (S K)`. -/
theorem SNDf_beta (p : Term) : Term.app SNDf p ⟶* Term.app p (Term.app S K) := by
  have h := bracketOpt_beta_Term 0 (TermV.app (V 0) (TermV.app .S .K)) p
  simpa [V, TermV.subst, toTerm] using h

theorem TAILSTEPf_beta (x p : Term) :
    Term.app (Term.app TAILSTEPf x) p
      ⟶* Term.app (Term.app PAIRf (Term.app (Term.app CONSf x) (Term.app FSTf p)))
          (Term.app FSTf p) := by
  have h := bracketOpt_beta2_Term (TermV.app2 (ofTerm PAIRf)
    (TermV.app2 (ofTerm CONSf) (V 1) (TermV.app (ofTerm FSTf) (V 0)))
    (TermV.app (ofTerm FSTf) (V 0))) x p
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

/-- The initial accumulator of `tail`'s fold: the pair `⟨[], []⟩`. -/
def TAILZf : Term := Term.app (Term.app PAIRf NILf) NILf

theorem TAILf_beta (L : Term) :
    Term.app TAILf L ⟶* Term.app SNDf (Term.app (Term.app L TAILSTEPf) TAILZf) := by
  have h := bracketOpt_beta_Term 0 (TermV.app (ofTerm SNDf)
    (TermV.app2 (V 0) (ofTerm TAILSTEPf)
      (TermV.app2 (ofTerm PAIRf) (ofTerm NILf) (ofTerm NILf)))) L
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm, TAILZf] using h

/-- `rule s ⟶* s ruleOutA ruleOutB` — dispatch is application. -/
theorem RULEf_beta (s : Term) :
    Term.app RULEf s ⟶* Term.app (Term.app s ruleOutA) ruleOutB := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (V 0) (ofTerm ruleOutA) (ofTerm ruleOutB)) s
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

-- ### The pair projections really project
theorem FSTf_pair (a b : Term) :
    Term.app FSTf (Term.app (Term.app PAIRf a) b) ⟶* a := by
  refine Steps.trans (FSTf_beta _) ?_
  refine Steps.trans (PAIRf_beta a b K) ?_
  exact Steps.single (Step.K_red a b)

theorem SNDf_pair (a b : Term) :
    Term.app SNDf (Term.app (Term.app PAIRf a) b) ⟶* b := by
  refine Steps.trans (SNDf_beta _) ?_
  refine Steps.trans (PAIRf_beta a b (Term.app S K)) ?_
  exact Steps.tail (Step.S_red K a b) (Steps.single (Step.K_red b (Term.app a b)))

-- ### The four compositional lemmas

/-- **Lemma 1 (head).** No induction at all: one β exposes `K x (…)` and the `K` fires. -/
theorem HEADf_mkWord (x : Term) (xs : List Term) :
    Term.app HEADf (mkWord (x :: xs)) ⟶* x := by
  refine Steps.trans (HEADf_beta _) ?_
  refine Steps.trans (CONSf_beta x (mkWord xs) K K) ?_
  exact Steps.single (Step.K_red x (Term.app (Term.app (mkWord xs) K) K))

/-- The fold underneath `tail` computes the pair `⟨word, its tail⟩` — and both components come out
CONS-BUILT, because `TAILSTEPf` rebuilds them with the genuine `CONSf`. That is what makes the tail of a
`mkWord` literally a `mkWord`. -/
theorem mkWord_tailPair : ∀ (w : List Term),
    Term.app (Term.app (mkWord w) TAILSTEPf) TAILZf
      ⟶* Term.app (Term.app PAIRf (mkWord w)) (mkWord w.tail) := by
  intro w
  induction w with
  | nil => exact NILf_beta TAILSTEPf TAILZf
  | cons x xs ih =>
      refine Steps.trans (CONSf_beta x (mkWord xs) TAILSTEPf TAILZf) ?_
      refine Steps.trans (Steps.congR ih) ?_
      refine Steps.trans (TAILSTEPf_beta x _) ?_
      exact Steps.congApp (Steps.congR (Steps.congR (FSTf_pair _ _))) (FSTf_pair _ _)

/-- **Lemma 2 (tail).** -/
theorem TAILf_mkWord (x : Term) (xs : List Term) :
    Term.app TAILf (mkWord (x :: xs)) ⟶* mkWord xs := by
  refine Steps.trans (TAILf_beta _) ?_
  refine Steps.trans (Steps.congR (mkWord_tailPair (x :: xs))) ?_
  exact SNDf_pair _ _

/-- Cons-directed concatenation: `λL M. L CONS M`. Folding the left word with `CONS` itself rebuilds it on
top of the right word, so the output is cons-built — reachable, not merely observationally equal. -/
def CATf : Term := toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0
  (TermV.app2 (V 1) (ofTerm CONSf) (V 0))))

theorem CATf_beta (u v : Term) :
    Term.app (Term.app CATf u) v ⟶* Term.app (Term.app u CONSf) v := by
  have h := bracketOpt_beta2_Term (TermV.app2 (V 1) (ofTerm CONSf) (V 0)) u v
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

theorem mkWord_fold_cons : ∀ (u : List Term) (v : List Term),
    Term.app (Term.app (mkWord u) CONSf) (mkWord v) ⟶* mkWord (u ++ v) := by
  intro u v
  induction u with
  | nil => exact NILf_beta CONSf (mkWord v)
  | cons x u' ih =>
      refine Steps.trans (CONSf_beta x (mkWord u') CONSf (mkWord v)) ?_
      exact Steps.congR ih

/-- **Lemma 3 (concat), on the corrected combinator.** -/
theorem CATf_mkWord (u v : List Term) :
    Term.app (Term.app CATf (mkWord u)) (mkWord v) ⟶* mkWord (u ++ v) :=
  Steps.trans (CATf_beta _ _) (mkWord_fold_cons u v)

/-- **Lemma 4 (dispatch), case `a`:** `K` selects the first rule output. -/
theorem RULEf_symA : Term.app RULEf symA ⟶* mkWord [symB] := by
  refine Steps.trans (RULEf_beta symA) ?_
  exact Steps.single (Step.K_red ruleOutA ruleOutB)

/-- **Lemma 4 (dispatch), case `b`:** `S K` selects the second. -/
theorem RULEf_symB : Term.app RULEf symB ⟶* mkWord [symA, symB] := by
  refine Steps.trans (RULEf_beta symB) ?_
  exact Steps.tail (Step.S_red K ruleOutA ruleOutB)
    (Steps.single (Step.K_red ruleOutB (Term.app ruleOutA ruleOutB)))

-- ### The corrected step function, and the machine it simulates

/-- `STEPf` with `CATf` in place of `CONCATf` — same shape, reachable output. -/
def STEPc : Term := o1 (TermV.app2 (ofTerm CATf)
  (TermV.app (ofTerm TAILf) (TermV.app (ofTerm TAILf) (V 0)))
  (TermV.app (ofTerm RULEf) (TermV.app (ofTerm HEADf) (V 0))))

theorem STEPc_beta (L : Term) :
    Term.app STEPc L ⟶* Term.app (Term.app CATf (Term.app TAILf (Term.app TAILf L)))
      (Term.app RULEf (Term.app HEADf L)) := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (ofTerm CATf)
    (TermV.app (ofTerm TAILf) (TermV.app (ofTerm TAILf) (V 0)))
    (TermV.app (ofTerm RULEf) (TermV.app (ofTerm HEADf) (V 0)))) L
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

/-- The rule of the source machine, named so statements below stay in `List Bool` syntactically:
`a := true ↦ [b]`, `b := false ↦ [a, b]`. -/
def ruleAB (s : Bool) : List Bool := if s then [false] else [true, false]

/-- The source machine, as data: two symbols, deletion number 2, `ruleAB`. -/
def tagAB : TagSystem := ⟨Bool, 2, ruleAB⟩

/-- Symbols to combinators, the Stage 50 dispatch encoding: `a ↦ K`, `b ↦ S K`. -/
def encSym (s : Bool) : Term := if s then symA else symB

/-- Words to fold-encoded lists of encoded symbols. -/
def encWord (w : List Bool) : Term := mkWord (w.map encSym)

/-- Dispatch computes the rule, uniformly over the alphabet. -/
theorem RULEf_encSym (s : Bool) :
    Term.app RULEf (encSym s) ⟶* encWord (ruleAB s) := by
  cases s
  · exact RULEf_symB
  · exact RULEf_symA

/-- **Step-correctness.** On any word long enough to tag-step, the compiled step function computes the tag
step LITERALLY: drop two symbols, append the head's rule, all inside `mkWord`. This is the composition of
the four lemmas, and it never mentions the 710-leaf compiled term. -/
theorem STEPc_mkWord (s y : Bool) (rest : List Bool) :
    Term.app STEPc (encWord (s :: y :: rest)) ⟶* encWord (rest ++ ruleAB s) := by
  refine Steps.trans (STEPc_beta _) ?_
  have htail : Term.app TAILf (Term.app TAILf (encWord (s :: y :: rest))) ⟶* encWord rest := by
    refine Steps.trans (Steps.congR (TAILf_mkWord (encSym s) ((y :: rest).map encSym))) ?_
    exact TAILf_mkWord (encSym y) (rest.map encSym)
  have hrule : Term.app RULEf (Term.app HEADf (encWord (s :: y :: rest)))
      ⟶* encWord (ruleAB s) := by
    refine Steps.trans (Steps.congR (HEADf_mkWord (encSym s) ((y :: rest).map encSym))) ?_
    exact RULEf_encSym s
  refine Steps.trans (Steps.congApp (Steps.congR htail) hrule) ?_
  rw [show encWord (rest ++ ruleAB s)
      = mkWord (rest.map encSym ++ (ruleAB s).map encSym) by simp [encWord]]
  exact CATf_mkWord (rest.map encSym) ((ruleAB s).map encSym)

/-- **`fwd` for a genuine m = 2 tag system.** The driver advances for any step function (Stage 61's
`selfRep_advances`), the step function computes the step (`STEPc_mkWord`), and `tagFwd_of_step` is their
composition: every source step is simulated by actual SK reduction on the encoded word. -/
theorem tagAB_fwd {w w' : List Bool} (h : (RS.Tag tagAB).step w w') :
    Term.app (selfRep STEPc) (encWord w) ⟶* Term.app (selfRep STEPc) (encWord w') := by
  obtain ⟨a, rest, hw, hlen, hw'⟩ := h
  subst hw
  cases rest with
  | nil => simp [tagAB] at hlen
  | cons y rest' =>
      subst hw'
      exact tagFwd_of_step (STEPc_mkWord a y rest')

/-- The same statement in the `RS` language, where a future `Simulation (RS.Tag tagAB) RS.SK` will want
it: this is that structure's `fwd` field, verbatim. -/
theorem tagAB_fwd_SK {w w' : List Bool} (h : (RS.Tag tagAB).step w w') :
    RS.SK.Steps (Term.app (selfRep STEPc) (encWord w)) (Term.app (selfRep STEPc) (encWord w')) :=
  RS.SK_steps_iff.mpr (tagAB_fwd h)

-- Anchors. The source machine really steps, and the compiled step function's output NORMALIZES to the same
-- term as the encoded target word — a stronger check than Stage 63's two-observer agreement, available now
-- because the output is reachable rather than merely observationally equal.
example : (RS.Tag tagAB).step [true, true, false] [false, false] :=
  ⟨true, [true, false], rfl, by decide, rfl⟩
example : (RS.Tag tagAB).step [false, true] [true, false] :=
  ⟨false, [true], rfl, by decide, rfl⟩
#guard nfW (Term.app STEPc (encWord [true, true, false])) == nfW (encWord [false, false])
#guard nfW (Term.app STEPc (encWord [false, true])) == nfW (encWord [true, false])
#guard !(nfW (Term.app STEPc (encWord [true, true, false])) == nfW (encWord [true, false]))
#guard (leafCount CATf, leafCount STEPc) = (82, 710)

-- ## What this settles, and what remains
-- SETTLED: piece (v)'s forward half, end to end. A genuine two-symbol, deletion-number-two tag system is
-- driven inside SK: `selfRep STEPc` applied to an encoded word reduces to itself applied to the encoded
-- successor word, for every source step. The proof is the four compositional lemmas composed — head is one
-- β and a `K`-firing, tail and concat are one list induction each, dispatch is two firings — plus Stage
-- 61's driver lemma. The compiled term's size never entered.
--
-- NOT SETTLED, and now the only thing between this development and `Simulation (RS.Tag tagAB) RS.SK`:
-- a decoder (`dec`/`dec_enc`, mechanical) and adequacy (`bwd`) — the demanding half, as it was for the
-- countdown, where it took Stages 45–48 (K-normal forms) and 49–58 (trajectory relation) to discharge.
-- The structural difference this time: `enc`'s image contains the driver, which duplicates ITSELF at every
-- step, so the Stage 11 result that machine code is safe to duplicate (`normalForm_bracket`) becomes
-- load-bearing rather than reassuring.

-- ## Stage 65: the decoder, a `PathEncoding` — and `bwd` is FALSE for this encoding
--
-- Toward the `Simulation`, in the order the obligations fall. The decoder is mechanical and done below,
-- and with `fwd` it already yields a machine-checked `PathEncoding (RS.Tag tagAB) RS.SK` — the weaker of
-- the two certificate classes, but a real one: the refutation results are stated over exactly this class.
--
-- Then the demanding half — and checking it produced three theorems, one fatal and two instructive:
--
--   * **`bwd` IS FALSE OUTRIGHT** (`tagAB_bwd_false`). A tag step is PARTIAL — it needs `m ≤ |w|` — but
--     `STEPc` is TOTAL: on the stuck word `[b]` it computes `tail (tail [b]) = []`, `head [b] = b`,
--     appends `[a,b]`, and so the host walks `encTag [b] ⟶* encTag [a,b]` while the source has no step at
--     all. No abstraction, however clever, can prove a false proposition: the DRIVER must change, not the
--     proof technique. The fix is a design item — guard the step on `|w| ≥ 2`, so stuck words self-loop.
--   * ROUTE TWO (trajectory relation) fails at `habs` independently of any driver: `tagAB` has a FIXED
--     POINT, `[b,a,b] ↦ [b,a,b]`, and `OnSegment`'s "not yet past `w`" clause is unsatisfiable at any
--     source self-loop (`onSegment_habs_fails_of_selfLoop`, Countdown.lean). This survives the guard fix —
--     it is a property of the SOURCE.
--   * ROUTE ONE (K-normal form) fails at `hstep` at the VERY FIRST host step out of any encoded state:
--     firing the driver's self-application leaves `(X W)((K STEPc) W) d`, whose K-normal form
--     `(X W) STEPc d` is a mid-step term and provably not an encoding of anything
--     (`tagDriver_knf_hstep_fails`). This also survives the guard fix — any `selfRep`-driven encoding
--     starts with the same self-application. Stage 49 predicted the constraint; this is its concrete bite.

-- ### The decoder

/-- The encoder, named: the driver applied to the encoded word. Its `fwd` is `tagAB_fwd_SK`. -/
def encTag (w : List Bool) : Term := Term.app (selfRep STEPc) (encWord w)

/-- Symbols back from combinators: `K ↦ a`, `S K ↦ b`. -/
def decSym (t : Term) : Option Bool :=
  if t = symA then some true else if t = symB then some false else none

/-- Words back from cons-built folds, syntactically. -/
def decWord : Term → Option (List Bool)
  | Term.app (Term.app c x) r =>
      if c = CONSf then
        match decSym x, decWord r with
        | some s, some w => some (s :: w)
        | _, _ => none
      else if Term.app (Term.app c x) r = NILf then some [] else none
  | t => if t = NILf then some [] else none

/-- The full decoder: peel the driver, decode the word. -/
def decTag (t : Term) : Option (List Bool) :=
  match t with
  | Term.app d w => if d = selfRep STEPc then decWord w else none
  | _ => none

theorem decWord_encWord : ∀ (u : List Bool), decWord (encWord u) = some u := by
  intro u
  induction u with
  | nil => rfl
  | cons s u' ih =>
      have ih' : decWord (mkWord (u'.map encSym)) = some u' := ih
      cases s <;> simp [encWord, encSym, mkWord, decWord, decSym, symA, symB, ih']

/-- **`dec_enc` for the tag driver.** -/
theorem decTag_encTag (u : List Bool) : decTag (encTag u) = some u := by
  show (if selfRep STEPc = selfRep STEPc then decWord (encWord u) else none) = some u
  rw [if_pos rfl]
  exact decWord_encWord u

/-- The encoder is injective — distinct words stay distinct inside SK. -/
theorem encTag_injective {u u' : List Bool} (h : encTag u = encTag u') : u = u' := by
  have h1 := decTag_encTag u
  rw [h, decTag_encTag] at h1
  exact (Option.some.inj h1).symm

/-- `fwd`, iterated to paths. (Raw recursor: `induction` fails on `RS.Steps` at a concrete
instance — the same mkElimApp motive error `SK_steps_iff` works around.) -/
theorem tagAB_path {w w' : List Bool} (h : (RS.Tag tagAB).Steps w w') :
    RS.SK.Steps (encTag w) (encTag w') :=
  h.rec (fun a => @RS.Steps.refl RS.SK (encTag a))
    (fun s _ ih => RS.Steps.trans (tagAB_fwd_SK s) ih)

/-- **The m = 2 tag system PATH-ENCODES into SK, machine-checked.** Injective, path-preserving — the
class every refutation in this development is stated over, now inhabited by a genuine
inspect-dispatch-append machine. (Not yet a `Simulation`: `bwd` is missing, and the two theorems below
say why it will not come from the countdown's templates.) -/
def tagABPathEncoding : PathEncoding (RS.Tag tagAB) RS.SK where
  enc := encTag
  inj := encTag_injective
  path := tagAB_path

-- Anchors: the decoder really decodes, rejects junk, and the pieces are what they say.
#guard decTag (encTag [true, false, false]) = some [true, false, false]
#guard decTag (encTag []) = some []
#guard decWord (encWord [false, true]) = some [false, true]
#guard decSym symA = some true
#guard decSym symB = some false
#guard decSym S = none
#guard decTag S = none
#guard decTag (Term.app S (encWord [])) = none

-- ### The central finding: the host outruns the source on stuck words

/-- `tail` of the EMPTY word is the empty word — the fold's initial pair simply comes back. This is
the benign half of `STEPc`'s totality. -/
theorem TAILf_nil : Term.app TAILf (mkWord []) ⟶* mkWord [] := by
  refine Steps.trans (TAILf_beta _) ?_
  refine Steps.trans (Steps.congR (mkWord_tailPair [])) ?_
  exact SNDf_pair _ _

/-- `head` of the empty word is the DEFAULT `K` — which is `symA`. This is the treacherous half: a
stuck word still dispatches, as if its missing head were `a`. -/
theorem HEADf_nil : Term.app HEADf (mkWord []) ⟶* K := by
  refine Steps.trans (HEADf_beta _) ?_
  exact NILf_beta K K

/-- **The step function steps a stuck word.** `[b]` has length 1 < m = 2, so the tag system halts —
but `STEPc` is total: both tails succeed, the head dispatches, and out comes `[a,b]`. -/
theorem STEPc_stuck : Term.app STEPc (encWord [false]) ⟶* encWord [true, false] := by
  refine Steps.trans (STEPc_beta _) ?_
  have htail : Term.app TAILf (Term.app TAILf (encWord [false])) ⟶* mkWord [] := by
    refine Steps.trans (Steps.congR (TAILf_mkWord symB [])) ?_
    exact TAILf_nil
  have hrule : Term.app RULEf (Term.app HEADf (encWord [false])) ⟶* encWord [true, false] := by
    refine Steps.trans (Steps.congR (HEADf_mkWord symB [])) ?_
    exact RULEf_symB
  refine Steps.trans (Steps.congApp (Steps.congR htail) hrule) ?_
  exact CATf_mkWord [] [symA, symB]

/-- So the host reaches the encoding of a word the source can never reach. -/
theorem encTag_outruns : encTag [false] ⟶* encTag [true, false] :=
  tagFwd_of_step STEPc_stuck

/-- ...and the source really cannot: `[b]` is a tag normal form. -/
theorem tagAB_stuck_singleton : (RS.Tag tagAB).NormalForm [false] := by
  rintro ⟨w', a, rest, _, hlen, _⟩
  exact absurd hlen (by decide)

/-- **`bwd` is FALSE for `encTag`.** Not "hard": false. The tag step is partial and the compiled step
function is total, so the host keeps computing where the source has halted. No choice of abstraction
can rescue this — the adequacy machinery proves `bwd` from its hypotheses, so every instantiation of
it must fail somewhere. The driver needs a LENGTH GUARD, and that is a Stage 66 design item, not a
proof item. -/
theorem tagAB_bwd_false :
    ¬ (∀ {w w' : List Bool}, RS.SK.Steps (encTag w) (encTag w') → (RS.Tag tagAB).Steps w w') := by
  intro hbwd
  have h := hbwd (RS.SK_steps_iff.mpr encTag_outruns)
  have heq : ([false] : List Bool) = [true, false] :=
    RS.NormalForm.steps_eq tagAB_stuck_singleton h
  exact absurd heq (by decide)

-- The outrun is visible to plain evaluation too — kept as an anchor because this is the guard the
-- Stage 63 validation suite COULD have contained and did not: it only ever tested words long enough
-- to step.
#guard nfW (Term.app STEPc (encWord [false])) == nfW (encWord [true, false])

-- ### Route two, refuted for this source: the fixed point

/-- `[b,a,b] ↦ [b,a,b]` — drop two, and `b`'s rule restores exactly what was consumed. -/
theorem tagAB_selfLoop :
    (RS.Tag tagAB).step [false, true, false] [false, true, false] :=
  ⟨false, [true, false], rfl, by decide, rfl⟩

/-- **The trajectory relation cannot start on this source.** Instance of the general obstruction: the
source has a self-loop, so `OnSegment`'s `habs` fails for `encTag` — and for every other encoder. -/
theorem onSegment_habs_fails_tagAB :
    ¬ OnSegment (A := RS.Tag tagAB) encTag (encTag [false, true, false]) [false, true, false] :=
  onSegment_habs_fails_of_selfLoop encTag tagAB_selfLoop

-- ### Route one, refuted for this driver: the first step already leaves the encodings

/-- The applicative part of the driver's wrapper: `selfRepW F = S selfRepX (K F)`. Named so the
mid-step terms below can be written down. -/
def selfRepX : Term :=
  app2 S (Term.app K S) (app2 S (Term.app K K) (app2 S I I))

/-- Every encoded state is K-normal (`habs` would hold — the abstraction APPLIES; it is `hstep` that
fails). Machine code is checked by the Stage 65 decision procedure, the word by induction. -/
theorem kNormalForm_encSym (s : Bool) : KNormalForm (encSym s) := by
  cases s
  · exact kNormalForm_app' rfl kNormalForm_S kNormalForm_K
  · exact kNormalForm_K

theorem kNormalForm_encWord (u : List Bool) : KNormalForm (encWord u) := by
  induction u with
  | nil => exact kNormalForm_of_no_kredex (by decide)
  | cons s u' ih =>
      exact kNormalForm_app' rfl
        (kNormalForm_app' rfl (kNormalForm_of_no_kredex (by decide)) (kNormalForm_encSym s)) ih

theorem kNormalForm_encTag (u : List Bool) : KNormalForm (encTag u) :=
  kNormalForm_app' rfl (kNormalForm_of_no_kredex (by decide)) (kNormalForm_encWord u)

/-- The first host step out of any encoded state: the driver's self-application fires. -/
theorem encTag_first_step (u : List Bool) :
    encTag u ⟶ Term.app (Term.app (Term.app selfRepX (selfRepW STEPc))
      (Term.app (Term.app K STEPc) (selfRepW STEPc))) (encWord u) :=
  Step.appL (Step.S_red selfRepX (Term.app K STEPc) (selfRepW STEPc))

/-- ...and its K-normal form is this mid-step term, which is NOT an encoding. -/
def tagMid (u : List Bool) : Term :=
  Term.app (Term.app (Term.app selfRepX (selfRepW STEPc)) STEPc) (encWord u)

theorem isKNF_first_step (u : List Bool) :
    IsKNF (Term.app (Term.app (Term.app selfRepX (selfRepW STEPc))
      (Term.app (Term.app K STEPc) (selfRepW STEPc))) (encWord u)) (tagMid u) :=
  ⟨KSteps.single (KStep.appL (KStep.appR (KStep.K_red STEPc (selfRepW STEPc)))),
   kNormalForm_app' rfl (kNormalForm_of_no_kredex (by decide)) (kNormalForm_encWord u)⟩

/-- **The K-normal-form abstraction's `hstep` is FALSE for the tag driver.** If it held, Stage 49's
forced consequence (`knf_abstraction_forces_encodings`) would make every reachable term K-normalise
to an encoding — but the very first step out of `encTag []` K-normalises to `tagMid []`, whose head
is `selfRepX (selfRepW STEPc)` where every encoding's head is the driver, and the two differ as
terms. The mechanism that carried the countdown cannot even leave the start state here. -/
theorem tagDriver_knf_hstep_fails :
    ¬ (∀ {b b' : Term} {u : List Bool}, (b ⟶ b') → IsKNF b (encTag u) →
        IsKNF b' (encTag u) ∨ ∃ u', (RS.Tag tagAB).step u u' ∧ IsKNF b' (encTag u')) := by
  intro hstep
  obtain ⟨u₂, _, hknf⟩ := knf_abstraction_forces_encodings (A := RS.Tag tagAB) encTag
    (fun {b b' a} hs habs => hstep hs habs) kNormalForm_encTag
    (Steps.single (encTag_first_step []))
  have heq : encTag u₂ = tagMid [] := hknf.unique (isKNF_first_step [])
  simp only [encTag, tagMid] at heq
  injection heq with h1 _
  exact absurd h1 (by decide)

-- ## Where `bwd` stands after this stage
-- Three theorems, in order of force.
--
-- FIRST, `bwd` for the current encoding is FALSE (`tagAB_bwd_false`), because the tag step is partial
-- and `STEPc` is total. This is a design defect in the driver, found only by attempting the proof —
-- the Stage 63/64 validation could not see it, because every test word was long enough to step. The
-- fix is known and buildable with the existing toolkit: dispatch on "has at least two symbols" (a
-- constant-size fold observer, like `HEADf`) and return the word unchanged when it fails, so stuck
-- words SELF-LOOP in the host. That is Stage 66.
--
-- SECOND AND THIRD, the two adequacy templates are each provably inapplicable, for reasons that
-- SURVIVE the guard fix. Route two's clause is an assumption about the SOURCE (no state on its own
-- trajectory may recur), violated by `tagAB`'s fixed point regardless of encoder. Route one's side
-- condition is an assumption about the HOST (every reachable intermediate K-normalises to an
-- encoding), violated by the driver's own self-application before the word is even touched.
--
-- So after the guard, `bwd` still needs a THIRD abstraction: one that assigns mid-step host terms to
-- a source state (K-normal forms cannot — the S-machinery is visible to them) and that survives
-- source loops (segments cannot — "not yet past" is empty on a loop). The natural candidate — a
-- phase-indexed relation, "b lies on the fwd-path from `enc w`, up to reduction inside doomed
-- subterms" — must quantify over the driver's reachable set, and characterising that set (the
-- analogue of Stage 56's `Tower`, for a 1450-leaf machine) is the genuine remaining obstacle. What
-- this stage contributes is the negative space: the characterisation cannot be avoided by either
-- shortcut that worked before, and it would be wasted effort on the UNGUARDED driver, whose `bwd` no
-- effort can prove.

-- ## Stage 66: the guarded driver — the step function learns that tag steps are partial
--
-- Stage 65 proved `bwd` false for `encTag` because `STEPc` is total where the tag step is partial: it
-- happily "steps" a stuck word. The repair is a guard — dispatch on "has at least two symbols" and
-- return the word UNCHANGED when it fails — built from the same constant-size fold-observer idiom as
-- everything else: `NONNIL = λL. L (λx a. T) F` reads emptiness off the fold, `HASTWO = NONNIL ∘ TAIL`
-- shifts it by one, and the guard is Stage 50's dispatch again, with the whole step in one branch and
-- the identity in the other. On stuck words the doomed `STEP L` branch is DISCARDED UNREDUCED by the
-- `K` that `F = S K` exposes — the guard never runs what it rejects.

/-- `λx a. T` — the fold observer for "nonempty": any cons makes it true. Three leaves. -/
def constTf : Term := toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0 (.K)))

/-- `λL. L (λx a. T) F` — is the word nonempty? -/
def NONNILf : Term := o1 (TermV.app2 (V 0) (ofTerm constTf) (ofTerm symB))

/-- `λL. NONNIL (TAIL L)` — does the word have at least two symbols? (= is its tail nonempty). -/
def HASTWOf : Term := o1 (TermV.app (ofTerm NONNILf) (TermV.app (ofTerm TAILf) (V 0)))

/-- **The guarded step function**: `λL. HASTWO L (STEPc L) L`. -/
def STEPg : Term := o1 (TermV.app2 (TermV.app (ofTerm HASTWOf) (V 0))
  (TermV.app (ofTerm STEPc) (V 0)) (V 0))

-- ### β and the guard's verdicts

theorem constTf_beta (x a : Term) : Term.app (Term.app constTf x) a ⟶* K := by
  have h := bracketOpt_beta2_Term .K x a
  simpa [TermV.subst] using h

theorem NONNILf_beta (L : Term) :
    Term.app NONNILf L ⟶* Term.app (Term.app L constTf) symB := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (V 0) (ofTerm constTf) (ofTerm symB)) L
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

theorem HASTWOf_beta (L : Term) :
    Term.app HASTWOf L ⟶* Term.app NONNILf (Term.app TAILf L) := by
  have h := bracketOpt_beta_Term 0
    (TermV.app (ofTerm NONNILf) (TermV.app (ofTerm TAILf) (V 0))) L
  simpa [V, TermV.subst, subst_ofTerm, toTerm] using h

theorem STEPg_beta (L : Term) :
    Term.app STEPg L ⟶* Term.app (Term.app (Term.app HASTWOf L) (Term.app STEPc L)) L := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (TermV.app (ofTerm HASTWOf) (V 0))
    (TermV.app (ofTerm STEPc) (V 0)) (V 0)) L
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

/-- The emptiness observer says no on `[]`... -/
theorem NONNILf_nil : Term.app NONNILf (mkWord []) ⟶* symB := by
  refine Steps.trans (NONNILf_beta _) ?_
  exact NILf_beta constTf symB

/-- ...and yes on any cons — no induction, one β and one constant observer. -/
theorem NONNILf_cons (x : Term) (xs : List Term) :
    Term.app NONNILf (mkWord (x :: xs)) ⟶* symA := by
  refine Steps.trans (NONNILf_beta _) ?_
  refine Steps.trans (CONSf_beta x (mkWord xs) constTf symB) ?_
  exact constTf_beta x _

/-- The guard's three verdicts, by word length. -/
theorem HASTWOf_nil : Term.app HASTWOf (mkWord []) ⟶* symB := by
  refine Steps.trans (HASTWOf_beta _) ?_
  exact Steps.trans (Steps.congR TAILf_nil) NONNILf_nil

theorem HASTWOf_one (x : Term) : Term.app HASTWOf (mkWord [x]) ⟶* symB := by
  refine Steps.trans (HASTWOf_beta _) ?_
  exact Steps.trans (Steps.congR (TAILf_mkWord x [])) NONNILf_nil

theorem HASTWOf_long (x y : Term) (ys : List Term) :
    Term.app HASTWOf (mkWord (x :: y :: ys)) ⟶* symA := by
  refine Steps.trans (HASTWOf_beta _) ?_
  exact Steps.trans (Steps.congR (TAILf_mkWord x (y :: ys))) (NONNILf_cons y ys)

-- ### The guarded step: computes the tag step where one exists, the identity where none does

/-- **Step-correctness for the guarded driver** — the guard passes and hands the word to `STEPc`. -/
theorem STEPg_mkWord (s y : Bool) (rest : List Bool) :
    Term.app STEPg (encWord (s :: y :: rest)) ⟶* encWord (rest ++ ruleAB s) := by
  refine Steps.trans (STEPg_beta _) ?_
  refine Steps.trans (Steps.congL (Steps.congL
    (HASTWOf_long (encSym s) (encSym y) (rest.map encSym)))) ?_
  refine Steps.trans (Steps.single (Step.K_red _ _)) ?_
  exact STEPc_mkWord s y rest

/-- **Stuck words are FIXED, literally.** `F = S K` selects the identity branch, and the `K` it
exposes discards the doomed `STEPc L` UNREDUCED. This is the repair of Stage 65's falsifier. -/
theorem STEPg_stuck : ∀ {w : List Bool}, w.length < 2 →
    Term.app STEPg (encWord w) ⟶* encWord w := by
  intro w hw
  match w with
  | [] =>
      refine Steps.trans (STEPg_beta _) ?_
      refine Steps.trans (Steps.congL (Steps.congL HASTWOf_nil)) ?_
      exact Steps.tail (Step.S_red K _ _) (Steps.single (Step.K_red _ _))
  | [s] =>
      refine Steps.trans (STEPg_beta _) ?_
      refine Steps.trans (Steps.congL (Steps.congL (HASTWOf_one (encSym s)))) ?_
      exact Steps.tail (Step.S_red K _ _) (Steps.single (Step.K_red _ _))
  | _ :: _ :: _ => exact absurd hw (by simp)

-- ### The guarded encoder, its `fwd`, and its `PathEncoding`

/-- The guarded encoder. Same driver idiom, guarded step function. -/
def encTagG (w : List Bool) : Term := Term.app (selfRep STEPg) (encWord w)

/-- **`fwd` for the guarded driver** — the Stage 64 lemmas carry over untouched. -/
theorem tagABg_fwd {w w' : List Bool} (h : (RS.Tag tagAB).step w w') :
    encTagG w ⟶* encTagG w' := by
  obtain ⟨a, rest, hw, hlen, hw'⟩ := h
  subst hw
  cases rest with
  | nil => simp [tagAB] at hlen
  | cons y rest' =>
      subst hw'
      exact tagFwd_of_step (STEPg_mkWord a y rest')

theorem tagABg_fwd_SK {w w' : List Bool} (h : (RS.Tag tagAB).step w w') :
    RS.SK.Steps (encTagG w) (encTagG w') :=
  RS.SK_steps_iff.mpr (tagABg_fwd h)

/-- **On stuck words the driver IDLES**: its own advance (`selfRep_advances` supplies
`encTagG w ⟶* selfRep STEPg (STEPg (encWord w))`) leads straight back to the encoding. Stage 65's
counterexample path — the only known falsifier of `bwd` — now returns home instead of escaping to
`encTag [a,b]`. What is NOT claimed: that no other path escapes. That is `bwd` itself, and it needs
the reachable-set characterisation. -/
theorem encTagG_stuck_returns {w : List Bool} (hw : w.length < 2) :
    Term.app (selfRep STEPg) (Term.app STEPg (encWord w)) ⟶* encTagG w :=
  Steps.congR (STEPg_stuck hw)

/-- The decoder, retargeted at the guarded driver. -/
def decTagG (t : Term) : Option (List Bool) :=
  match t with
  | Term.app d w => if d = selfRep STEPg then decWord w else none
  | _ => none

theorem decTagG_encTagG (u : List Bool) : decTagG (encTagG u) = some u := by
  show (if selfRep STEPg = selfRep STEPg then decWord (encWord u) else none) = some u
  rw [if_pos rfl]
  exact decWord_encWord u

theorem encTagG_injective {u u' : List Bool} (h : encTagG u = encTagG u') : u = u' := by
  have h1 := decTagG_encTagG u
  rw [h, decTagG_encTagG] at h1
  exact (Option.some.inj h1).symm

theorem tagABg_path {w w' : List Bool} (h : (RS.Tag tagAB).Steps w w') :
    RS.SK.Steps (encTagG w) (encTagG w') :=
  h.rec (fun a => @RS.Steps.refl RS.SK (encTagG a))
    (fun s _ ih => RS.Steps.trans (tagABg_fwd_SK s) ih)

/-- **The `PathEncoding`, on the guarded driver** — the encoding a future `Simulation` will extend,
now that its `bwd` is no longer KNOWN false. -/
def tagABgPathEncoding : PathEncoding (RS.Tag tagAB) RS.SK where
  enc := encTagG
  inj := encTagG_injective
  path := tagABg_path

-- Anchors. Sizes; the guard really dispatches; a long word still steps; and the two tests Stage 63's
-- suite was missing — a stuck word is FIXED, and it provably does NOT step to what the unguarded
-- driver produced.
#guard (leafCount constTf, leafCount NONNILf, leafCount HASTWOf, leafCount STEPg) = (3, 12, 211, 936)
#guard nfW (Term.app STEPg (encWord [true, true, false])) == nfW (encWord [false, false])
#guard nfW (Term.app STEPg (encWord [false, true])) == nfW (encWord [true, false])
#guard nfW (Term.app STEPg (encWord [false])) == nfW (encWord [false])
#guard nfW (Term.app STEPg (encWord [])) == nfW (encWord [])
#guard !(nfW (Term.app STEPg (encWord [false])) == nfW (encWord [true, false]))
#guard decTagG (encTagG [true, false]) = some [true, false]
#guard decTagG (encTag [true, false]) = none   -- the two drivers' encodings do not cross-decode

-- ## Where the Simulation stands after the guard
-- `enc`, `dec`, `dec_enc`, `fwd`: done for the guarded driver, and Stage 65's falsifier is repaired —
-- the stuck-word trajectory returns to its own encoding (`encTagG_stuck_returns`) instead of escaping.
-- `bwd` is now an OPEN obligation rather than a false one. What it needs is unchanged from Stage 65's
-- analysis, and both refutations there survive the guard: a third abstraction (mid-step-aware,
-- loop-tolerant) over a characterisation of the guarded driver's reachable set. That characterisation
-- — the `Tower` analogue for this machine — is the whole of the remaining distance to
-- `Simulation (RS.Tag tagAB) RS.SK`.

-- ## Stage 67: the rigidity audit — shipped code is not normal, and what its drift actually is
--
-- The ranking said to start the reachable-set characterisation with `HEADf`. Before writing any
-- invariant, audit its central prerequisite: that machine CODE is rigid — a normal form, hence
-- drift-free when the driver duplicates it. Stage 11 proved exactly that (`normalForm_bracket`) — but
-- for the NAIVE algorithm on pure bodies. The real toolkit is `bracketOpt` over bodies that embed
-- APPLIED constants, and there the property fails: an x-free application chunk is K-protected AS IT
-- STANDS, live redexes included. The audit below finds every violation and — the useful part —
-- accounts for each one.
--
-- THE ACCOUNTING (each number build-enforced below). `STEPg` ships SIX live redex positions:
--   * three are the rule outputs inside `RULEf` — but those are WORDS, and words in this encoding
--     are non-normal BY DESIGN: `mkWord` IS a chain of `CONSf`-applications, which is what made
--     Stage 64's literal reachability work. Their drift is WORD drift, which any `bwd` abstraction
--     already owes for every word in flight. Not a new obligation.
--   * three are copies of ONE internal constant — `TAILf`'s initial accumulator `PAIRf NILf NILf`
--     (twice via `STEPc`'s two `TAILf`s, once via `HASTWOf`'s). That chunk is NOT data; it is the one
--     genuinely fixable violation. Pre-normalise it — ship the compiled pair `λs. s [] []` directly,
--     which is normal and β-identical — and every remaining live position in shipped code is a word.
--
-- So after one small rebuild (Stage 68), CODE DRIFT AND DATA DRIFT COLLAPSE INTO ONE SPECIES, and the
-- reachable-set characterisation owes exactly one drift family: the reducts of `mkWord w`.

-- ### The verdicts, one line each: pure-body compilations are normal...
theorem NILf_normal : NormalForm NILf := stepOnce_none_normal rfl
theorem CONSf_normal : NormalForm CONSf := stepOnce_none_normal rfl
theorem HEADf_normal : NormalForm HEADf := stepOnce_none_normal rfl
theorem PAIRf_normal : NormalForm PAIRf := stepOnce_none_normal rfl
theorem FSTf_normal : NormalForm FSTf := stepOnce_none_normal rfl
theorem SNDf_normal : NormalForm SNDf := stepOnce_none_normal rfl
theorem TAILSTEPf_normal : NormalForm TAILSTEPf := stepOnce_none_normal rfl
theorem CATf_normal : NormalForm CATf := stepOnce_none_normal rfl
theorem constTf_normal : NormalForm constTf := stepOnce_none_normal rfl
theorem NONNILf_normal : NormalForm NONNILf := stepOnce_none_normal rfl
theorem selfRepX_normal : NormalForm selfRepX := stepOnce_none_normal rfl

-- ### ...and everything that embeds an applied constant is NOT.
theorem TAILf_not_normal : ¬ NormalForm TAILf := fun hn => hn ⟨_, stepOnce_sound rfl⟩
theorem RULEf_not_normal : ¬ NormalForm RULEf := fun hn => hn ⟨_, stepOnce_sound rfl⟩
theorem HASTWOf_not_normal : ¬ NormalForm HASTWOf := fun hn => hn ⟨_, stepOnce_sound rfl⟩
theorem STEPc_not_normal : ¬ NormalForm STEPc := fun hn => hn ⟨_, stepOnce_sound rfl⟩
theorem STEPg_not_normal : ¬ NormalForm STEPg := fun hn => hn ⟨_, stepOnce_sound rfl⟩
/-- The wrapper the driver DUPLICATES at every cycle is itself non-normal — Stage 11's safety
theorem does not cover the machine actually being run. -/
theorem selfRepW_STEPg_not_normal : ¬ NormalForm (selfRepW STEPg) :=
  fun hn => hn ⟨_, stepOnce_sound rfl⟩

-- ### The measurements, build-enforced
-- Live redex positions: 1 in TAILf (the accumulator chunk), 3 in RULEf (all rule-output words),
-- and they compose additively — 5 in STEPc (2 TAILf copies + RULEf's 3), 6 in STEPg (+ HASTWOf's
-- TAILf copy), 6 in the duplicated wrapper.
#guard ([TAILf, RULEf, HASTWOf, STEPc, STEPg, selfRepW STEPg].map (fun t => (succs t).length))
  = [1, 3, 1, 5, 6, 6]
-- Drift distance: steps for the shipped code to quiesce under leftmost-outermost, and the normal
-- form's size. STEPg sits 168 steps from quiescence.
#guard ((normalize 100000 TAILf).map (fun p => (p.2, leafCount p.1))).getD (0, 0) = (20, 170)
#guard ((normalize 100000 RULEf).map (fun p => (p.2, leafCount p.1))).getD (0, 0) = (108, 104)
#guard ((normalize 100000 STEPg).map (fun p => (p.2, leafCount p.1))).getD (0, 0) = (168, 756)
-- Words: non-normal by design — one live redex PER CONS CELL — and they quiesce to compact
-- code-forms. (The empty word is the one normal word.)
#guard ([mkWord [], mkWord [symA], mkWord [symA, symB]].map (fun t => (succs t).length)) = [0, 1, 2]
#guard ((normalize 100000 (mkWord [symA, symB])).map (fun p => (p.2, leafCount p.1))).getD (0, 0)
  = (72, 63)

-- ### What the census tooling could and could not do
-- The state-count question — "how many terms does the drift graph of one shipped combinator hold?" —
-- turned out to be beyond the tree's census tooling: `boundedClosure` on BARE `TAILf` (one live
-- chunk, 192 leaves) did not saturate in twenty-five minutes of interpreter time, where the
-- countdown's ENTIRE reachable set (183 states, ≤ 22 leaves) saturates inside a `#guard`. The listed
-- measurements above are single-path (leftmost-outermost) precisely because single paths are what
-- still computes at this scale. Two consequences, recorded plainly:
--   * an ENUMERATIVE invariant — Tower's four constructors, scaled up — is not writable for these
--     machines, and not even measurable; the drift families must be PARAMETERIZED (Tower's `half`
--     constructor generalised: independent copies, each anywhere in a sub-family), which is what the
--     per-combinator "segment invariant" plan already intended;
--   * the interesting number is not the state count but the SPECIES count, and the accounting above
--     says it is ONE (words), after the Stage 68 rebuild.

-- ## Stage 68: the accumulator rebuild — every live position in the shipped driver is a word
--
-- Stage 67's one fixable rigidity violation was `TAILf`'s accumulator: the body chunk
-- `PAIRf NILf NILf` ships as a live redex, and the driver duplicates it every cycle. The fix is to
-- compile the pair DIRECTLY — `TAILZn = λs. s [] []` — which is normal and β-identical. Rebuilding
-- the stack on it (`TAILn`, `HASTWOn`, `STEPcn`, `STEPgn`) leaves exactly three live positions in the
-- shipped step function, all of them rule-output words: code drift and data drift are now ONE
-- species, build-enforced below.
--
-- A simplification falls out of the rebuild: stating the tail fold's invariant EXISTENTIALLY ("the
-- fold reaches something that PROJECTS like the pair") lets `TAILn_mkWord` cover all words uniformly
-- — the empty word needs no separate lemma, because `TAILZn` projects like `⟨[], []⟩` by β.

/-- The accumulator, compiled rather than applied: `λs. s [] []`. Normal, unlike `PAIRf NILf NILf`. -/
def TAILZn : Term := toTerm (TermV.bracketOpt 0
  (TermV.app2 (V 0) (ofTerm NILf) (ofTerm NILf)))

/-- `tail`, on the compiled accumulator. -/
def TAILn : Term := o1 (TermV.app (ofTerm SNDf)
  (TermV.app2 (V 0) (ofTerm TAILSTEPf) (ofTerm TAILZn)))

/-- The guard, on the new tail. -/
def HASTWOn : Term := o1 (TermV.app (ofTerm NONNILf) (TermV.app (ofTerm TAILn) (V 0)))

/-- The unguarded step, on the new tail. -/
def STEPcn : Term := o1 (TermV.app2 (ofTerm CATf)
  (TermV.app (ofTerm TAILn) (TermV.app (ofTerm TAILn) (V 0)))
  (TermV.app (ofTerm RULEf) (TermV.app (ofTerm HEADf) (V 0))))

/-- **The driver's step function, final form**: guarded, and clean of non-word redexes. -/
def STEPgn : Term := o1 (TermV.app2 (TermV.app (ofTerm HASTWOn) (V 0))
  (TermV.app (ofTerm STEPcn) (V 0)) (V 0))

-- ### β for the rebuilt pieces

theorem TAILZn_beta (s : Term) :
    Term.app TAILZn s ⟶* Term.app (Term.app s NILf) NILf := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (V 0) (ofTerm NILf) (ofTerm NILf)) s
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

theorem TAILn_beta (L : Term) :
    Term.app TAILn L ⟶* Term.app SNDf (Term.app (Term.app L TAILSTEPf) TAILZn) := by
  have h := bracketOpt_beta_Term 0 (TermV.app (ofTerm SNDf)
    (TermV.app2 (V 0) (ofTerm TAILSTEPf) (ofTerm TAILZn))) L
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

theorem HASTWOn_beta (L : Term) :
    Term.app HASTWOn L ⟶* Term.app NONNILf (Term.app TAILn L) := by
  have h := bracketOpt_beta_Term 0
    (TermV.app (ofTerm NONNILf) (TermV.app (ofTerm TAILn) (V 0))) L
  simpa [V, TermV.subst, subst_ofTerm, toTerm] using h

theorem STEPcn_beta (L : Term) :
    Term.app STEPcn L ⟶* Term.app (Term.app CATf (Term.app TAILn (Term.app TAILn L)))
      (Term.app RULEf (Term.app HEADf L)) := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (ofTerm CATf)
    (TermV.app (ofTerm TAILn) (TermV.app (ofTerm TAILn) (V 0)))
    (TermV.app (ofTerm RULEf) (TermV.app (ofTerm HEADf) (V 0)))) L
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

theorem STEPgn_beta (L : Term) :
    Term.app STEPgn L ⟶* Term.app (Term.app (Term.app HASTWOn L) (Term.app STEPcn L)) L := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (TermV.app (ofTerm HASTWOn) (V 0))
    (TermV.app (ofTerm STEPcn) (V 0)) (V 0)) L
  simpa [V, TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

-- ### The compiled accumulator projects like the pair it replaced

theorem FSTf_TAILZn : Term.app FSTf TAILZn ⟶* NILf := by
  refine Steps.trans (FSTf_beta _) ?_
  refine Steps.trans (TAILZn_beta K) ?_
  exact Steps.single (Step.K_red NILf NILf)

theorem SNDf_TAILZn : Term.app SNDf TAILZn ⟶* NILf := by
  refine Steps.trans (SNDf_beta _) ?_
  refine Steps.trans (TAILZn_beta (Term.app S K)) ?_
  exact Steps.tail (Step.S_red K NILf NILf)
    (Steps.single (Step.K_red NILf (Term.app NILf NILf)))

/-- The tail fold, stated existentially: it reaches SOMETHING that projects like `⟨word, tail⟩`.
This is the shape the old invariant should have had — the base case stops needing the accumulator to
literally BE a `PAIRf`-application. -/
theorem mkWord_tailPairN : ∀ (w : List Term),
    ∃ p, (Term.app (Term.app (mkWord w) TAILSTEPf) TAILZn ⟶* p)
      ∧ (Term.app FSTf p ⟶* mkWord w) ∧ (Term.app SNDf p ⟶* mkWord w.tail) := by
  intro w
  induction w with
  | nil => exact ⟨TAILZn, NILf_beta _ _, FSTf_TAILZn, SNDf_TAILZn⟩
  | cons x xs ih =>
      obtain ⟨p', hp', hfst, _⟩ := ih
      refine ⟨Term.app (Term.app PAIRf (Term.app (Term.app CONSf x) (mkWord xs))) (mkWord xs),
        ?_, FSTf_pair _ _, SNDf_pair _ _⟩
      refine Steps.trans (CONSf_beta x (mkWord xs) TAILSTEPf TAILZn) ?_
      refine Steps.trans (Steps.congR hp') ?_
      refine Steps.trans (TAILSTEPf_beta x p') ?_
      exact Steps.congApp (Steps.congR (Steps.congR hfst)) hfst

/-- **`tail`, uniformly over ALL words** — the nil case is no longer special. -/
theorem TAILn_mkWord (w : List Term) : Term.app TAILn (mkWord w) ⟶* mkWord w.tail := by
  obtain ⟨p, hp, _, hsnd⟩ := mkWord_tailPairN w
  refine Steps.trans (TAILn_beta _) ?_
  exact Steps.trans (Steps.congR hp) hsnd

-- ### The guard's verdicts, on the new tail

theorem HASTWOn_nil : Term.app HASTWOn (mkWord []) ⟶* symB := by
  refine Steps.trans (HASTWOn_beta _) ?_
  exact Steps.trans (Steps.congR (TAILn_mkWord [])) NONNILf_nil

theorem HASTWOn_one (x : Term) : Term.app HASTWOn (mkWord [x]) ⟶* symB := by
  refine Steps.trans (HASTWOn_beta _) ?_
  exact Steps.trans (Steps.congR (TAILn_mkWord [x])) NONNILf_nil

theorem HASTWOn_long (x y : Term) (ys : List Term) :
    Term.app HASTWOn (mkWord (x :: y :: ys)) ⟶* symA := by
  refine Steps.trans (HASTWOn_beta _) ?_
  exact Steps.trans (Steps.congR (TAILn_mkWord (x :: y :: ys))) (NONNILf_cons y ys)

-- ### Step-correctness and the stuck case, re-proved on the clean stack

theorem STEPcn_mkWord (s y : Bool) (rest : List Bool) :
    Term.app STEPcn (encWord (s :: y :: rest)) ⟶* encWord (rest ++ ruleAB s) := by
  refine Steps.trans (STEPcn_beta _) ?_
  have htail : Term.app TAILn (Term.app TAILn (encWord (s :: y :: rest))) ⟶* encWord rest := by
    refine Steps.trans (Steps.congR (TAILn_mkWord (encSym s :: encSym y :: rest.map encSym))) ?_
    exact TAILn_mkWord (encSym y :: rest.map encSym)
  have hrule : Term.app RULEf (Term.app HEADf (encWord (s :: y :: rest)))
      ⟶* encWord (ruleAB s) := by
    refine Steps.trans (Steps.congR (HEADf_mkWord (encSym s) ((y :: rest).map encSym))) ?_
    exact RULEf_encSym s
  refine Steps.trans (Steps.congApp (Steps.congR htail) hrule) ?_
  rw [show encWord (rest ++ ruleAB s)
      = mkWord (rest.map encSym ++ (ruleAB s).map encSym) by simp [encWord]]
  exact CATf_mkWord (rest.map encSym) ((ruleAB s).map encSym)

theorem STEPgn_mkWord (s y : Bool) (rest : List Bool) :
    Term.app STEPgn (encWord (s :: y :: rest)) ⟶* encWord (rest ++ ruleAB s) := by
  refine Steps.trans (STEPgn_beta _) ?_
  refine Steps.trans (Steps.congL (Steps.congL
    (HASTWOn_long (encSym s) (encSym y) (rest.map encSym)))) ?_
  refine Steps.trans (Steps.single (Step.K_red _ _)) ?_
  exact STEPcn_mkWord s y rest

theorem STEPgn_stuck : ∀ {w : List Bool}, w.length < 2 →
    Term.app STEPgn (encWord w) ⟶* encWord w := by
  intro w hw
  match w with
  | [] =>
      refine Steps.trans (STEPgn_beta _) ?_
      refine Steps.trans (Steps.congL (Steps.congL HASTWOn_nil)) ?_
      exact Steps.tail (Step.S_red K _ _) (Steps.single (Step.K_red _ _))
  | [s] =>
      refine Steps.trans (STEPgn_beta _) ?_
      refine Steps.trans (Steps.congL (Steps.congL (HASTWOn_one (encSym s)))) ?_
      exact Steps.tail (Step.S_red K _ _) (Steps.single (Step.K_red _ _))
  | _ :: _ :: _ => exact absurd hw (by simp)

-- ### The driver, final form

/-- The encoder a `Simulation` will carry: guarded step function, word-only drift. -/
def encTagN (w : List Bool) : Term := Term.app (selfRep STEPgn) (encWord w)

theorem tagABn_fwd {w w' : List Bool} (h : (RS.Tag tagAB).step w w') :
    encTagN w ⟶* encTagN w' := by
  obtain ⟨a, rest, hw, hlen, hw'⟩ := h
  subst hw
  cases rest with
  | nil => simp [tagAB] at hlen
  | cons y rest' =>
      subst hw'
      exact tagFwd_of_step (STEPgn_mkWord a y rest')

theorem tagABn_fwd_SK {w w' : List Bool} (h : (RS.Tag tagAB).step w w') :
    RS.SK.Steps (encTagN w) (encTagN w') :=
  RS.SK_steps_iff.mpr (tagABn_fwd h)

theorem encTagN_stuck_returns {w : List Bool} (hw : w.length < 2) :
    Term.app (selfRep STEPgn) (Term.app STEPgn (encWord w)) ⟶* encTagN w :=
  Steps.congR (STEPgn_stuck hw)

def decTagN (t : Term) : Option (List Bool) :=
  match t with
  | Term.app d w => if d = selfRep STEPgn then decWord w else none
  | _ => none

theorem decTagN_encTagN (u : List Bool) : decTagN (encTagN u) = some u := by
  show (if selfRep STEPgn = selfRep STEPgn then decWord (encWord u) else none) = some u
  rw [if_pos rfl]
  exact decWord_encWord u

theorem encTagN_injective {u u' : List Bool} (h : encTagN u = encTagN u') : u = u' := by
  have h1 := decTagN_encTagN u
  rw [h, decTagN_encTagN] at h1
  exact (Option.some.inj h1).symm

theorem tagABn_path {w w' : List Bool} (h : (RS.Tag tagAB).Steps w w') :
    RS.SK.Steps (encTagN w) (encTagN w') :=
  h.rec (fun a => @RS.Steps.refl RS.SK (encTagN a))
    (fun s _ ih => RS.Steps.trans (tagABn_fwd_SK s) ih)

/-- **The `PathEncoding`, final form** — guarded step, word-only drift. This is the encoding the
`bwd` work targets from here on. -/
def tagABnPathEncoding : PathEncoding (RS.Tag tagAB) RS.SK where
  enc := encTagN
  inj := encTagN_injective
  path := tagABn_path

-- ### The rigidity dividend, build-enforced
-- The rebuilt tail chain is NORMAL — Stage 67's three accumulator copies are gone...
theorem TAILZn_normal : NormalForm TAILZn := stepOnce_none_normal rfl
theorem TAILn_normal : NormalForm TAILn := stepOnce_none_normal rfl
theorem HASTWOn_normal : NormalForm HASTWOn := stepOnce_none_normal rfl
#guard ([TAILZn, TAILn, HASTWOn].map (fun t => (succs t).length)) = [0, 0, 0]
-- ...and the step function's ONLY live positions are the three rule-output words, through every
-- layer up to the wrapper the driver duplicates.
#guard ([STEPcn, STEPgn, selfRepW STEPgn].map (fun t => (succs t).length)) = [3, 3, 3]
-- Sizes, for the record.
#guard (leafCount TAILZn, leafCount TAILn, leafCount HASTWOn, leafCount STEPgn) = (15, 170, 189, 870)
-- The machine still computes: a long word steps, a stuck word is fixed, and the Stage 65 bug stays
-- dead on the final stack.
#guard nfW (Term.app STEPgn (encWord [true, true, false])) == nfW (encWord [false, false])
#guard nfW (Term.app STEPgn (encWord [false, true])) == nfW (encWord [true, false])
#guard nfW (Term.app STEPgn (encWord [false])) == nfW (encWord [false])
#guard !(nfW (Term.app STEPgn (encWord [false])) == nfW (encWord [true, false]))
#guard decTagN (encTagN [true, false]) = some [true, false]
#guard decTagN (encTagG [true, false]) = none

-- ## Where this leaves `bwd`
-- The stack is final: `enc`/`dec`/`dec_enc`/`fwd` proved, stuck words idle, and the shipped code's
-- drift is confined to embedded WORDS — the same species as the data in flight, characterised once
-- and used everywhere. The remaining obligation is unchanged in name and now minimal in kind: the
-- word-drift family (reducts of `mkWord w`, parameterized over independent copy drift), then the
-- machine phases composed over it, then the third abstraction. Everything else that `bwd` was
-- waiting on has been either proved, repaired, or reduced to that one family.

-- ## Stage 69: the word-drift family, characterised by behaviour — no enumeration
--
-- The ranking asked for an inductive family over the reducts of `mkWord w`, Tower's `half`
-- generalised. Attempting the single cell showed that even it is an interleaved two-layer
-- distribution machine — dozens of drift-parameterized constructors — and Stage 67 already
-- established that such state spaces are beyond measuring, let alone hand enumeration. Stage 68's
-- lesson ("state obligations by behaviour, not by shape") applies one level up, and it DISSOLVES the
-- enumeration: give each word a CANONICAL NORMAL FORM `wordNF w`, prove the word reaches it, and
-- confluence does the rest —
--
--     every reduct of `mkWord w`, however far it has drifted, still reduces to `wordNF w`,
--
-- (`mkWord_drift_complete`). Drift never needs to be described, because it can always be COMPLETED:
-- the family "reducts of `mkWord w`" is exactly the set of terms between `mkWord w` and `wordNF w`,
-- and the second endpoint is canonical because it is normal. Two drifted copies of the same word can
-- never disagree (`mkWord_drift_functional`). This is the entire base layer `bwd`'s abstraction
-- needs about words: identity survives drift.

/-- The code-form of a cons cell: `λc n. c x (M c n)` compiled, with the tail `M` already a term.
This is what a cell β-reduces to once both its arguments have distributed. -/
def wordCode (x M : Term) : Term :=
  toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0
    (TermV.app2 (.var 1) (ofTerm x) (TermV.app2 (ofTerm M) (.var 1) (.var 0)))))

/-- **The canonical normal form of a word**: code-forms all the way down. -/
def wordNF : List Term → Term
  | [] => NILf
  | x :: xs => wordCode x (wordNF xs)

/-- The compiled cell, written out. The `x`- and `M`-holes each occur exactly once, `K`-protected —
which is what makes the congruence and normality arguments below one-line-per-node. -/
theorem wordCode_explicit (x M : Term) :
    wordCode x M
      = app2 S
          (app2 S (Term.app K S) (app2 S (Term.app K K) (app2 S I (Term.app K x))))
          (app2 S
            (app2 S (Term.app K S) (app2 S (Term.app K K) (app2 S (Term.app K M) I)))
            (Term.app K I)) := by
  -- `simp` alone closes this — and drags `Classical.choice` in through the `BEq` layer, the same
  -- trap Stage 9 recorded. So the decidable literals are supplied by hand and `simp only` does the
  -- assembly; the audit stays at `[propext]`.
  have hx : ∀ y, TermV.occurs y (ofTerm x) = false := closedV_ofTerm x
  have hM : ∀ y, TermV.occurs y (ofTerm M) = false := closedV_ofTerm M
  have b00 : ((0 : Nat) == 0) = true := rfl
  have b10 : ((1 : Nat) == 0) = false := rfl
  have b11 : ((1 : Nat) == 1) = true := rfl
  have p10 : ((1 : Nat) = 0) = False := eq_false (by decide)
  simp only [wordCode, TermV.bracketOpt, TermV.occurs, TermV.app2, hx, hM, bracketOpt_ofTerm,
    b00, b10, b11, p10, Bool.or_false, Bool.or_true, Bool.false_eq_true, if_true, if_false,
    toTerm, toTerm_ofTerm, I, _root_.app2]

/-- Code-forms of normal data are NORMAL — assembled from the Stage 11 shape lemmas. -/
theorem wordCode_normal {x M : Term} (hx : NormalForm x) (hM : NormalForm M) :
    NormalForm (wordCode x M) := by
  rw [wordCode_explicit]
  exact normalForm_app_S_two
    (normalForm_app_S_two (normalForm_app_K normalForm_S)
      (normalForm_app_S_two (normalForm_app_K normalForm_K)
        (normalForm_app_S_two normalForm_I (normalForm_app_K hx))))
    (normalForm_app_S_two
      (normalForm_app_S_two (normalForm_app_K normalForm_S)
        (normalForm_app_S_two (normalForm_app_K normalForm_K)
          (normalForm_app_S_two (normalForm_app_K hM) normalForm_I)))
      (normalForm_app_K normalForm_I))

theorem wordNF_normal : ∀ {w : List Term}, (∀ x ∈ w, NormalForm x) → NormalForm (wordNF w) := by
  intro w
  induction w with
  | nil => exact fun _ => NILf_normal
  | cons x xs ih =>
      intro h
      exact wordCode_normal (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Reduction inside the tail hole. -/
theorem wordCode_congR (x : Term) {M M' : Term} (h : M ⟶* M') :
    wordCode x M ⟶* wordCode x M' := by
  rw [wordCode_explicit, wordCode_explicit]
  exact Steps.congR (Steps.congL (Steps.congR (Steps.congR (Steps.congR
    (Steps.congL (Steps.congR (Steps.congR h)))))))

private def bodyCONS : TermV := TermV.app2 (V 1) (V 3) (TermV.app2 (V 2) (V 1) (V 0))

/-- A cons cell distributes its two arguments and lands on the code-form — partial application β,
by the Stage 64 ladder's method. -/
theorem consCell_to_code (x M : Term) :
    Term.app (Term.app CONSf x) M ⟶* wordCode x M := by
  have h1 : Term.app CONSf x
      ⟶* toTerm (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0
          (TermV.subst 3 (ofTerm x) bodyCONS)))) := by
    have h := bracketOpt_beta_Term 3
      (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 bodyCONS))) x
    rwa [bracketOpt_subst_ofTerm (by decide) x (TermV.bracketOpt 1 (TermV.bracketOpt 0 bodyCONS)),
         bracketOpt_subst_ofTerm (by decide) x (TermV.bracketOpt 0 bodyCONS),
         bracketOpt_subst_ofTerm (by decide) x bodyCONS] at h
  have h2 := bracketOpt_beta_Term 2
    (TermV.bracketOpt 1 (TermV.bracketOpt 0 (TermV.subst 3 (ofTerm x) bodyCONS))) M
  rw [bracketOpt_subst_ofTerm (by decide) M
        (TermV.bracketOpt 0 (TermV.subst 3 (ofTerm x) bodyCONS)),
      bracketOpt_subst_ofTerm (by decide) M (TermV.subst 3 (ofTerm x) bodyCONS)] at h2
  have heq : toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0
      (TermV.subst 2 (ofTerm M) (TermV.subst 3 (ofTerm x) bodyCONS)))) = wordCode x M := by
    simp [bodyCONS, wordCode, TermV.subst, subst_ofTerm, TermV.app2, V]
  exact Steps.trans (Steps.congL h1) (heq ▸ h2)

/-- **Every word reaches its canonical normal form.** -/
theorem mkWord_to_wordNF : ∀ (w : List Term), mkWord w ⟶* wordNF w := by
  intro w
  induction w with
  | nil => exact Steps.refl _
  | cons x xs ih =>
      refine Steps.trans (consCell_to_code x (mkWord xs)) ?_
      exact wordCode_congR x ih

/-- **THE DRIFT-COMPLETION THEOREM.** Every reduct of a word — however its copies have drifted —
still reduces to the word's canonical normal form. Confluence supplies the join; normality of
`wordNF` pins the join point. The word-drift family never needs to be enumerated, because membership
comes with a completion. -/
theorem mkWord_drift_complete {w : List Term} (hw : ∀ x ∈ w, NormalForm x)
    {t : Term} (h : mkWord w ⟶* t) : t ⟶* wordNF w := by
  obtain ⟨s, h1, h2⟩ := confluence h (mkWord_to_wordNF w)
  exact ((wordNF_normal hw).steps_eq h2).symm ▸ h1

/-- **Drift cannot conflate words**: two drifted copies with a common reduct came from words with
the same canonical form. (With injectivity of `wordNF` — next on the ranking — this is "the same
word".) -/
theorem mkWord_drift_functional {u v : List Term}
    (hu : ∀ x ∈ u, NormalForm x) (hv : ∀ x ∈ v, NormalForm x) {t : Term}
    (h1 : mkWord u ⟶* t) (h2 : mkWord v ⟶* t) : wordNF u = wordNF v :=
  nf_unique (mkWord_drift_complete hu h1) (mkWord_drift_complete hv h2)
    (wordNF_normal hu) (wordNF_normal hv)

-- ### Instantiation for the tag alphabet
theorem encSym_normal (s : Bool) : NormalForm (encSym s) := by
  cases s
  · exact normalForm_app_S_one normalForm_K
  · exact normalForm_K

theorem encWord_entries_normal (w : List Bool) : ∀ x ∈ w.map encSym, NormalForm x := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨s, _, rfl⟩ := hx
  exact encSym_normal s

/-- The drift-completion theorem, on encoded tag words. -/
theorem encWord_drift_complete {w : List Bool} {t : Term} (h : encWord w ⟶* t) :
    t ⟶* wordNF (w.map encSym) :=
  mkWord_drift_complete (encWord_entries_normal w) h

-- Anchors: the canonical form is what the evaluator computes, and the sizes are linear in the word.
#guard nfW (mkWord [symA, symB]) == some (wordNF [symA, symB])
#guard nfW (mkWord [symB]) == some (wordNF [symB])
#guard nfW (encWord [true, false, false]) == some (wordNF ([true, false, false].map encSym))
#guard (leafCount (wordNF []), leafCount (wordNF [symA]), leafCount (wordNF [symA, symB])) = (4, 33, 63)

-- ## What this buys `bwd`, and what is still owed
-- BOUGHT: the base layer. Words in flight are duplicated and drift independently, and the
-- abstraction must not lose track of which word a copy denotes. It cannot: any reduct completes to
-- `wordNF w` (`mkWord_drift_complete`), and two words' completions collide only if their canonical
-- forms do (`mkWord_drift_functional`). No shape family, no enumeration — the characterisation is
-- "still reaches the canonical form", which is closed under reduction BY CONSTRUCTION.
--
-- STILL OWED: (i) injectivity of `wordNF` on encoded words, making "same canonical form" into "same
-- word" — syntactic, next on the ranking; (ii) the same treatment for the machine's PHASES — the
-- states between `encTagN w` and `encTagN (step w)` — where the driver's shell is the context and
-- words are the holes. The phase layer has what the word layer had: canonical checkpoints (the
-- encodings) and confluence. What it does NOT have is normality of the checkpoints — `encTagN w` is
-- never normal — so the completion argument needs the driver's own structure, not just `nf_unique`.
-- That is the next real problem.

-- ## Stage 70: drift pins the word — injectivity, and the identity layer is complete
--
-- Stage 69 ended one step short: two drifted copies with a common reduct have equal CANONICAL FORMS.
-- Injectivity of `wordNF` upgrades that to equal WORDS. The proof is what the explicit skeleton was
-- for: each entry and the tail sit at fixed positions, so equality of cells is an injection chain,
-- and equality of words is that chain plus one induction.

theorem wordNF_injective : ∀ {u v : List Term}, wordNF u = wordNF v → u = v := by
  intro u
  induction u with
  | nil =>
      intro v h
      cases v with
      | nil => rfl
      | cons y ys =>
          rw [show wordNF (y :: ys) = wordCode y (wordNF ys) from rfl, wordCode_explicit,
              show wordNF [] = Term.app K I from rfl] at h
          injection h with h1 _
          exact Term.noConfusion h1
  | cons x xs ih =>
      intro v h
      cases v with
      | nil =>
          rw [show wordNF (x :: xs) = wordCode x (wordNF xs) from rfl, wordCode_explicit,
              show wordNF [] = Term.app K I from rfl] at h
          injection h with h1 _
          exact Term.noConfusion h1
      | cons y ys =>
          rw [show wordNF (x :: xs) = wordCode x (wordNF xs) from rfl,
              show wordNF (y :: ys) = wordCode y (wordNF ys) from rfl,
              wordCode_explicit, wordCode_explicit] at h
          simp only [_root_.app2, Term.app.injEq, true_and, and_true] at h
          obtain ⟨hx, hM⟩ := h
          rw [hx, ih hM]

/-- **Drift pins the word.** Two words whose (arbitrarily drifted) copies share a reduct are THE SAME
WORD. This is `hfun` at the data level: the relation "t is a reduct of `mkWord w`" is functional in
`w`, with no shape analysis anywhere — confluence, one canonical form, one injection. -/
theorem mkWord_drift_pins {u v : List Term}
    (hu : ∀ x ∈ u, NormalForm x) (hv : ∀ x ∈ v, NormalForm x) {t : Term}
    (h1 : mkWord u ⟶* t) (h2 : mkWord v ⟶* t) : u = v :=
  wordNF_injective (mkWord_drift_functional hu hv h1 h2)

-- ### Down to the tag alphabet
theorem encSym_injective {s s' : Bool} (h : encSym s = encSym s') : s = s' := by
  cases s <;> cases s' <;> first | rfl | exact absurd h (by decide)

theorem map_encSym_injective : ∀ {u v : List Bool}, u.map encSym = v.map encSym → u = v := by
  intro u
  induction u with
  | nil =>
      intro v h
      cases v with
      | nil => rfl
      | cons _ _ =>
          simp only [List.map_nil, List.map_cons] at h
          exact nomatch h
  | cons s u' ih =>
      intro v h
      cases v with
      | nil =>
          simp only [List.map_nil, List.map_cons] at h
          exact nomatch h
      | cons s' v' =>
          simp only [List.map_cons, List.cons.injEq] at h
          rw [encSym_injective h.1, ih h.2]

/-- **The identity layer, complete.** An encoded tag word in flight — duplicated, drifted, reduced by
whatever schedule the host chose — still determines its source word uniquely. -/
theorem encWord_drift_pins {u v : List Bool} {t : Term}
    (h1 : encWord u ⟶* t) (h2 : encWord v ⟶* t) : u = v :=
  map_encSym_injective
    (mkWord_drift_pins (encWord_entries_normal u) (encWord_entries_normal v) h1 h2)

-- Anchors.
#guard wordNF [symA] != wordNF [symB]
#guard wordNF [symA, symB] != wordNF [symB, symA]
example : encSym true ≠ encSym false := fun h => by cases encSym_injective h

-- ## The phase layer, scoped while the identity layer is fresh
-- What `bwd` still needs is the analogue of drift-completion for MACHINE STATES: a relation
-- "b belongs to source state w" that every host step preserves-or-advances. The word layer's recipe
-- was: canonical form + confluence + injectivity. The phase layer has the first and third
-- ingredients — encodings are canonical checkpoints and `encTagN` is injective — but NOT normality:
-- `encTagN w` always carries its driver redex, so `nf_unique` cannot pin join points, and a reduct
-- of `encTagN w` may genuinely never return to `encTagN w` (it may only complete FORWARD, to
-- `encTagN` of a LATER state). The candidate statement, recorded for the next attempt:
--
--     every reduct of `encTagN w` reaches `encTagN w'` for some w' with `Tag.Steps w w'`
--
-- — forward drift-completion, with `encWord_drift_pins` handling the data slots. Proving it needs
-- what no stage has yet built: a completion argument through the driver's own phases. That is the
-- remaining research content of `bwd`, now with its base layer done.
