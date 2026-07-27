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
