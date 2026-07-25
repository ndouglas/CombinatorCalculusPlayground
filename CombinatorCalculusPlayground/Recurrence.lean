--! # C1(a): pure S diverges — PROVED, via a regular-tree-language certificate
-- C1(a) ("some pure-S term has no normal form") has been labelled **external** since Stage 0,
-- and Stages 37–42 tried to reach it by the LOOP route: find `t ⟶⁺ C[t]`. Stage 43 read the
-- literature and found two things.
--
-- First, the loop route is dead and known to be dead. Endrullis & Zantema, *Non-termination
-- using Regular Languages* (IWT 2014), Example 2: "For the S-rule it is known that there are no
-- reductions `t →* C[t]` for ground terms `t`, see [15]" — [15] being Waldmann, *The Combinator
-- S*, Inf. Comput. 159 (2000). So Stages 37–42 were re-deriving Waldmann's theorem, and got as
-- far as reducing it to one size condition. (Their Example 2 also notes the OPEN-TERM version,
-- `t →* C[tσ]`, is open. Everything in this development is ground.)
--
-- Second, and much better: the same paper gives the technique that settles C1(a), and it is
-- small enough to formalize here from nothing.
--
-- ## The method (Endrullis–Zantema Theorem 4)
-- A rewrite system is non-terminating **iff** there is a non-empty set `L` of terms — a
-- *recurrence set* — such that every member has a redex, and every member steps to a member.
-- No infinite object is needed: `L` is the certificate, and for the S-rule `L` can be taken
-- REGULAR, recognised by a tiny tree automaton.
--
-- Their automaton for the S-rule (Example 7) is nondeterministic with five states. Determinizing
-- it by hand gives six reachable state SETS, and that is what `Dst` is:
--
--   s0 ↔ {0}   s1 ↔ {1}   s2 ↔ {2}   s3 ↔ {3}   s34 ↔ {3,4} (accepting)   bot ↔ ∅
--
-- Determinizing costs one state and buys a great deal: the interpretation becomes a plain
-- function `Term → Dst`, closure becomes monotonicity in an order on six elements, and every
-- automaton-level side condition becomes a `cases <;> decide` over at most 216 cases. No lists,
-- no sets, no finiteness infrastructure.
import CombinatorCalculusPlayground.Conservation
import CombinatorCalculusPlayground.Census.Enumerate

open Term

/-- The six reachable states of the determinized Endrullis–Zantema automaton for the S-rule,
named after the state SETS of their nondeterministic original. `bot` is the empty set (the
rejecting sink) and `s34` is the accepting state. -/
inductive Dst
  | s0 | s1 | s2 | s3 | s34 | bot
  deriving DecidableEq, Repr

/-- The transition function, read off the determinization. Every pair not listed lands in `bot`,
which is what makes the table short. -/
def dstep : Dst → Dst → Dst
  | .s0, .s0 => .s1
  | .s0, .s2 => .s2
  | .s0, .s3 => .s2
  | .s0, .s34 => .s2
  | .s1, .s0 => .s2
  | .s2, .s2 => .s3
  | .s2, .s3 => .s3
  | .s2, .s34 => .s3
  | .s3, .s3 => .s34
  | .s3, .s34 => .s34
  | .s34, .s3 => .s34
  | .s34, .s34 => .s34
  | _, _ => .bot

/-- The interpretation of a term. `K` is sent to `bot`, so any term containing a `K` anywhere is
rejected — the automaton certifies the *pure S* fragment without being told about it. -/
def st : Term → Dst
  | .S => .s0
  | .K => .bot
  | .app a b => dstep (st a) (st b)

/-- Set inclusion, inherited from the determinization: `bot` (∅) is below everything, and `s3`
({3}) is below `s34` ({3,4}). This is the order the quasi-model condition lives in. -/
def dle : Dst → Dst → Bool
  | .bot, _ => true
  | .s3, .s34 => true
  | a, b => a == b

theorem dstep_bot_left (b : Dst) : dstep .bot b = .bot := by cases b <;> rfl
theorem dstep_bot_right (a : Dst) : dstep a .bot = .bot := by cases a <;> rfl
theorem dle_bot (b : Dst) : dle .bot b = true := by cases b <;> rfl

-- ## The automaton's three side conditions, each a finite check
-- With six states these are 216, 216 and 216 closed cases. `decide` does them; there is nothing
-- to be clever about, which is the point of determinizing.

theorem dstep_mono_left : ∀ a a' b : Dst, dle a a' = true → dle (dstep a b) (dstep a' b) = true := by
  intro a a' b; cases a <;> cases a' <;> cases b <;> decide

theorem dstep_mono_right : ∀ a b b' : Dst, dle b b' = true → dle (dstep a b) (dstep a b') = true := by
  intro a b b'; cases a <;> cases b <;> cases b' <;> decide

/-- **The quasi-model condition for the S-rule** (Endrullis–Zantema Def. 13): the redex's
interpretation is below the reduct's, for every assignment of states to `f`, `g`, `x`. This one
theorem is the whole mathematical content of the certificate. -/
theorem dstep_rule : ∀ a b c : Dst,
    dle (dstep (dstep (dstep .s0 a) b) c) (dstep (dstep a c) (dstep b c)) = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

/-- `s34` is maximal, so nothing can step out of the accepting state. -/
theorem eq_s34_of_dle : ∀ {b : Dst}, dle .s34 b = true → b = .s34 := by
  intro b h; cases b <;> revert h <;> decide

/-- **Closure under rewriting** (their Theorem 17, for this automaton): the interpretation only
climbs along a reduction step. The K-case needs no `KFree` hypothesis — a `K` forces `bot`, and
`bot` is below everything. -/
theorem st_le_of_step : ∀ {t u : Term}, (t ⟶ u) → dle (st t) (st u) = true := by
  intro t u h
  induction h with
  | K_red x y =>
      show dle (dstep (dstep (st Term.K) (st x)) (st y)) (st x) = true
      rw [show st Term.K = Dst.bot from rfl, dstep_bot_left, dstep_bot_left, dle_bot]
  | S_red f g x =>
      show dle (dstep (dstep (dstep (st Term.S) (st f)) (st g)) (st x))
        (dstep (dstep (st f) (st x)) (dstep (st g) (st x))) = true
      exact dstep_rule _ _ _
  | @appL p p' q _ ih => exact dstep_mono_left _ _ _ ih
  | @appR p q q' _ ih => exact dstep_mono_right _ _ _ ih

/-- Hence the accepting state is absolutely stable: once in it, every step stays in it. This is
stronger than the weak closure the method needs, which simplifies the descent below. -/
theorem st_s34_of_step {t u : Term} (h : st t = .s34) (hs : t ⟶ u) : st u = .s34 :=
  eq_s34_of_dle (h ▸ st_le_of_step hs)

-- ## Every accepted term has a redex
-- Endrullis–Zantema get this from a product-automaton inclusion. Here it is cheaper to read the
-- accepting state's shape off the transition table: reaching `s34` forces a left spine of at
-- least three, and a K-free term with spine ≥ 3 cannot be normal (`SNF.spineLength_le`).

theorem dstep_eq_s2_imp : ∀ {a b : Dst}, dstep a b = .s2 → a = .s0 ∨ a = .s1 := by
  intro a b h; cases a <;> cases b <;> revert h <;> decide

theorem dstep_eq_s3_imp : ∀ {a b : Dst}, dstep a b = .s3 → a = .s2 := by
  intro a b h; cases a <;> cases b <;> revert h <;> decide

theorem dstep_eq_s34_imp : ∀ {a b : Dst}, dstep a b = .s34 → a = .s3 ∨ a = .s34 := by
  intro a b h; cases a <;> cases b <;> revert h <;> decide

/-- Only applications reach `s2` — the leaves sit in `s0` and `bot`. -/
theorem st_s2_isApp : ∀ {t : Term}, st t = .s2 → ∃ p q, t = Term.app p q := by
  intro t h
  cases t with
  | S => exact absurd h (by decide)
  | K => exact absurd h (by decide)
  | app p q => exact ⟨p, q, rfl⟩

/-- Reaching `s3` forces two nested applications on the left, because it needs an `s2` there. -/
theorem st_s3_shape : ∀ {t : Term}, st t = .s3 → ∃ p q r, t = Term.app (Term.app p q) r := by
  intro t h
  cases t with
  | S => exact absurd h (by decide)
  | K => exact absurd h (by decide)
  | app a b =>
      obtain ⟨p, q, hpq⟩ := st_s2_isApp (dstep_eq_s3_imp h)
      exact ⟨p, q, b, by rw [hpq]⟩

theorem three_le_spine_of_s34 : ∀ {t : Term}, st t = .s34 → 3 ≤ spineLength t := by
  intro t
  induction t with
  | S => intro h; exact absurd h (by decide)
  | K => intro h; exact absurd h (by decide)
  | app a b iha _ =>
      intro h
      rcases dstep_eq_s34_imp h with ha | ha
      · obtain ⟨p, q, r, hpqr⟩ := st_s3_shape ha
        subst hpqr
        show 3 ≤ spineLength p + 1 + 1 + 1
        omega
      · have := iha ha
        show 3 ≤ spineLength a + 1
        omega

/-- Anything the automaton does not reject is K-free: a `K` sends its own state to `bot`, and
`bot` propagates through every application. -/
theorem kFree_of_st_ne_bot : ∀ {t : Term}, st t ≠ .bot → KFree t := by
  intro t
  induction t with
  | S => intro _; exact KFree.S
  | K => intro h; exact absurd rfl h
  | app a b iha ihb =>
      intro h
      refine KFree.app (iha ?_) (ihb ?_)
      · intro hb
        exact h (by show dstep (st a) (st b) = Dst.bot; rw [hb, dstep_bot_left])
      · intro hb
        exact h (by show dstep (st a) (st b) = Dst.bot; rw [hb, dstep_bot_right])

/-- Condition (i) of the method: every accepted term contains a redex. -/
theorem has_redex_of_s34 {t : Term} (h : st t = .s34) : ∃ u, t ⟶ u := by
  have hk : KFree t := kFree_of_st_ne_bot (by rw [h]; decide)
  have hsp : 3 ≤ spineLength t := three_le_spine_of_s34 h
  cases hso : stepOnce t with
  | none =>
      -- `none` certifies a normal form, and a K-free normal form has spine ≤ 2
      exact absurd (SNF.spineLength_le (SNF.of_normal hk (stepOnce_none_normal hso))) (by omega)
  | some u => exact ⟨u, stepOnce_sound hso⟩

-- ## From the certificate to an infinite reduction
-- The recurrence set is inhabited and closed, so iterating the (total, certified) one-step
-- evaluator never runs out. That gives the `Nat → Term` sequence `InfiniteRed` asks for.

/-- Iterate leftmost-outermost reduction, standing still if there is no redex. -/
def sIter (t : Term) : Nat → Term
  | 0 => t
  | n + 1 => (stepOnce (sIter t n)).getD (sIter t n)

theorem st_sIter {t : Term} (h : st t = .s34) : ∀ n, st (sIter t n) = .s34 := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
      cases hso : stepOnce (sIter t n) with
      | none => show st ((stepOnce (sIter t n)).getD (sIter t n)) = _; rw [hso]; exact ih
      | some w =>
          show st ((stepOnce (sIter t n)).getD (sIter t n)) = _
          rw [hso]
          exact st_s34_of_step ih (stepOnce_sound hso)

/-- **The recurrence-set theorem, instantiated.** An accepted term admits an infinite
reduction. -/
theorem infiniteRed_of_s34 {t : Term} (h : st t = .s34) : InfiniteRed t := by
  refine ⟨sIter t, rfl, ?_⟩
  intro i
  obtain ⟨u, hu⟩ := has_redex_of_s34 (st_sIter h i)
  cases hso : stepOnce (sIter t i) with
  | none => exact absurd (stepOnce_isSome_of_step hu) (by rw [hso]; simp)
  | some w =>
      show sIter t i ⟶ (stepOnce (sIter t i)).getD (sIter t i)
      rw [hso]
      exact stepOnce_sound hso

-- ## The witness
-- Endrullis–Zantema's Example 12 exhibits the accepted term `SSS(SSS) applied to itself`.

/-- `S S S` — the three-leaf term the automaton puts in `s2`. -/
def sss : Term := app2 S S S
/-- `S S S (S S S)` — six leaves, state `s3`. -/
def ezX : Term := app sss sss
/-- `S S S (S S S) (S S S (S S S))` — twelve leaves, state `s34`: **accepted**. -/
def ezWitness : Term := app ezX ezX

#guard leafCount sss = 3
#guard leafCount ezX = 6
#guard leafCount ezWitness = 12
#guard kFree ezWitness

-- The interpretation climbing to the accepting state, one application at a time.
example : st S = Dst.s0 := rfl
example : st (app S S) = Dst.s1 := rfl
example : st sss = Dst.s2 := rfl
example : st ezX = Dst.s3 := rfl
theorem st_ezWitness : st ezWitness = Dst.s34 := rfl

/-- **C1(a), PROVED.** A pure-S term with no normal form. The divergence comes from the
recurrence certificate; C5 (`no_normalForm_of_infiniteRed`) converts "admits an infinite
reduction" into "has no normal form", which for pure S is not automatic — it is exactly the
conservation theorem Stage 31 proved. -/
theorem c1a : ∃ t : Term, KFree t ∧ ¬ ∃ n, (t ⟶* n) ∧ NormalForm n := by
  refine ⟨ezWitness, kFree_iff.mp (by decide), ?_⟩
  exact no_normalForm_of_infiniteRed (kFree_iff.mp (by decide)) (infiniteRed_of_s34 st_ezWitness)

/-- ...and the divergence itself, stated directly. -/
theorem ezWitness_infiniteRed : InfiniteRed ezWitness := infiniteRed_of_s34 st_ezWitness

-- ## How tight is the certificate?
-- Not tight, and it is worth recording by how much. C1(b) (`no_small_divergence`) proves the
-- true floor for pure-S divergence is SEVEN leaves; this witness carries twelve. The automaton
-- rejects both seven-leaf candidates, so `c1` and `c2` remain individually open — a sharper
-- certificate, or Waldmann's decision procedure, would settle them.
/-- Is a term accepted? -/
def accepted (t : Term) : Bool := st t == Dst.s34

#guard accepted ezWitness
#guard !(accepted c1)
#guard !(accepted c2)

-- No pure-S term below twelve leaves is accepted, so twelve is this certificate's own floor —
-- five leaves above the true one.
#guard (List.range 12).all (fun n => (sTerms n).all (fun t => !(accepted t)))

-- ## Independent cross-check
-- The certificate is a claim about an automaton; the census evaluator is a separate mechanism.
-- Running the witness confirms the divergence from the other side — leaf count climbs
-- monotonically and never reaches a normal form. The theorem does not rest on this, but a
-- certificate the evaluator disagreed with would mean one of the two was wrong, and that is worth
-- a build-enforced check rather than a remark.
#guard (trace 40 ezWitness).length = 41
#guard leafCount ((trace 40 ezWitness).getLastD ezWitness) = 776
#guard ((trace 40 ezWitness).map leafCount).all (fun k => 12 ≤ k)
