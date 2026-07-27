--! # The driver shell invariant — the interior factorization, first installment
-- Stage 74. Stage 73 closed the landscape: `bwd` needs a per-step tracking abstraction over the
-- interior factorization, and nothing else can supply it. This file builds the factorization's
-- shell layer: an inductive family `Sh` describing EVERY term reachable from `app (selfRep F) d` —
-- the driver applied to data — as shell machinery over abstract data holes, CLOSED UNDER REDUCTION.
--
-- The design, from tracing the machine:
--   * the engine `W W` (W = selfRepW F) fires into X-machinery over a duplicated argument, a
--     `(K F)`-collapse, and `I`-towers whose copies drift independently; finished `I`-towers
--     reassemble into NESTED engines (the unbounded pre-unfolding of Stage 73);
--   * a half-built layer `S y f` can be APPLIED TO DATA EARLY — the premature states are real
--     reachable states and the family must include them (`ydat`), or closure is false;
--   * data is abstract: two parameter predicates, `D` (data at rest) and `DA` (data applications),
--     both Step-closed by hypothesis, with one hand-off axiom (`F`-reducts applied to data-slot
--     terms land in `DA`). Instantiating them with the actual word/step layer is the NEXT stage;
--     with `DA := fun _ => True` the shell statement already stands on its own.
--
-- Everything generic in `F`: this is driver theory, not tag-system theory.
import CombinatorCalculusPlayground.TagInSK

open Term

/-- The second applicative stage of `selfRepX`: `S (K K) (S I I)`. -/
def Ybody : Term := app2 S (Term.app K K) (app2 S I I)

theorem Ybody_normal : NormalForm Ybody := stepOnce_none_normal rfl

/-- The kinds of the shell family — one per machinery stage. -/
inductive ShK where
  | wcopy   -- a copy of the wrapper W, its F-slot possibly drifted
  | iw      -- I-tower states over engine arguments
  | kf      -- the (K f) w collapse
  | ks | kk -- the (K S) w / (K K) w collapses
  | zw      -- (S I I) w, collapsing to a nested engine
  | yw      -- Y-machinery states
  | xw      -- X-machinery states
  | eng     -- the self-application engine
  | kfd     -- data-slot expressions
  | ydat    -- Y-machinery (or its continuation) prematurely applied to data
  | drv     -- top-level driver states
deriving DecidableEq

/-- **The shell family.** `Sh F D DA k t`: `t` is a `k`-stage state of the driver shell over step
function `F`, data predicate `D`, and data-application predicate `DA`. -/
inductive Sh (F : Term) (D DA : Term → Prop) : ShK → Term → Prop
  | wcopy {f} : (F ⟶* f) →
      Sh F D DA .wcopy (Term.app (Term.app S selfRepX) (Term.app K f))
  | iw_base {w} : Sh F D DA .wcopy w → Sh F D DA .iw w
  | iw_pre {u} : Sh F D DA .iw u → Sh F D DA .iw (Term.app I u)
  | iw_mid {u₁ u₂} : Sh F D DA .iw u₁ → Sh F D DA .iw u₂ →
      Sh F D DA .iw (Term.app (Term.app K u₁) (Term.app K u₂))
  | kf_pend {f u} : (F ⟶* f) → Sh F D DA .iw u →
      Sh F D DA .kf (Term.app (Term.app K f) u)
  | kf_done {f} : (F ⟶* f) → Sh F D DA .kf f
  | ks_pend {u} : Sh F D DA .iw u → Sh F D DA .ks (Term.app (Term.app K S) u)
  | ks_done : Sh F D DA .ks S
  | kk_pend {u} : Sh F D DA .iw u → Sh F D DA .kk (Term.app (Term.app K K) u)
  | kk_done : Sh F D DA .kk K
  | zw_pend {u} : Sh F D DA .iw u →
      Sh F D DA .zw (Term.app (Term.app (Term.app S I) I) u)
  | zw_done {e} : Sh F D DA .eng e → Sh F D DA .zw e
  | yw_pend {u} : Sh F D DA .iw u → Sh F D DA .yw (Term.app Ybody u)
  | yw_fired {a b} : Sh F D DA .kk a → Sh F D DA .zw b →
      Sh F D DA .yw (Term.app a b)
  | xw_pend {u} : Sh F D DA .iw u → Sh F D DA .xw (Term.app selfRepX u)
  | xw_fired {a b} : Sh F D DA .ks a → Sh F D DA .yw b →
      Sh F D DA .xw (Term.app a b)
  | eng_pair {u₁ u₂} : Sh F D DA .iw u₁ → Sh F D DA .iw u₂ →
      Sh F D DA .eng (Term.app u₁ u₂)
  | eng_fired {a b} : Sh F D DA .xw a → Sh F D DA .kf b →
      Sh F D DA .eng (Term.app a b)
  | kfd_dat {t} : D t → Sh F D DA .kfd t
  | kfd_app {t} : DA t → Sh F D DA .kfd t
  | kfd_pend {f u t} : (F ⟶* f) → Sh F D DA .iw u → Sh F D DA .kfd t →
      Sh F D DA .kfd (Term.app (Term.app (Term.app K f) u) t)
  | ydat_yd {y t} : Sh F D DA .yw y → Sh F D DA .kfd t →
      Sh F D DA .ydat (Term.app y t)
  | ydat_done {z} : Sh F D DA .zw z → Sh F D DA .ydat z
  | drv {y t} : Sh F D DA .ydat y → Sh F D DA .kfd t →
      Sh F D DA .drv (Term.app y t)

namespace Sh

variable {F : Term} {D DA : Term → Prop}

/-- **Closure: one host step never leaves the family, kind by kind.** -/
theorem closed
    (hD : ∀ {d d'}, D d → (d ⟶ d') → D d')
    (hDA : ∀ {d d'}, DA d → (d ⟶ d') → DA d')
    (hApp : ∀ {f t}, (F ⟶* f) → Sh F D DA .kfd t → DA (Term.app f t)) :
    ∀ {k t}, Sh F D DA k t → ∀ {t'}, (t ⟶ t') → Sh F D DA k t' := by
  intro k t h
  induction h with
  | @wcopy f hf =>
      intro t' hs
      cases hs with
      | appL h1 =>
          cases h1 with
          | appL h2 => cases h2
          | appR h2 => exact absurd ⟨_, h2⟩ selfRepX_normal
      | appR h1 =>
          cases h1 with
          | appL h2 => cases h2
          | appR h2 => exact .wcopy (Steps.trans hf (Steps.single h2))
  | iw_base _ ih => exact fun hs => .iw_base (ih hs)
  | @iw_pre u hu ih =>
      intro t' hs
      cases hs with
      | S_red => exact .iw_mid hu hu
      | appL h1 => exact absurd ⟨_, h1⟩ normalForm_I
      | appR h1 => exact .iw_pre (ih h1)
  | @iw_mid u₁ u₂ h1 h2 ih1 ih2 =>
      intro t' hs
      cases hs with
      | K_red => exact h1
      | appL h3 =>
          cases h3 with
          | appL h4 => cases h4
          | appR h4 => exact .iw_mid (ih1 h4) h2
      | appR h3 =>
          cases h3 with
          | appL h4 => cases h4
          | appR h4 => exact .iw_mid h1 (ih2 h4)
  | @kf_pend f u hf hu ih =>
      intro t' hs
      cases hs with
      | K_red => exact .kf_done hf
      | appL h1 =>
          cases h1 with
          | appL h2 => cases h2
          | appR h2 => exact .kf_pend (Steps.trans hf (Steps.single h2)) hu
      | appR h1 => exact .kf_pend hf (ih h1)
  | @kf_done f hf =>
      exact fun hs => .kf_done (Steps.trans hf (Steps.single hs))
  | @ks_pend u hu ih =>
      intro t' hs
      cases hs with
      | K_red => exact .ks_done
      | appL h1 =>
          cases h1 with
          | appL h2 => cases h2
          | appR h2 => cases h2
      | appR h1 => exact .ks_pend (ih h1)
  | ks_done => exact fun hs => by cases hs
  | @kk_pend u hu ih =>
      intro t' hs
      cases hs with
      | K_red => exact .kk_done
      | appL h1 =>
          cases h1 with
          | appL h2 => cases h2
          | appR h2 => cases h2
      | appR h1 => exact .kk_pend (ih h1)
  | kk_done => exact fun hs => by cases hs
  | @zw_pend u hu ih =>
      intro t' hs
      cases hs with
      | S_red => exact .zw_done (.eng_pair (.iw_pre hu) (.iw_pre hu))
      | appL h1 =>
          cases h1 with
          | appL h2 =>
              cases h2 with
              | appL h3 => cases h3
              | appR h3 => exact absurd ⟨_, h3⟩ normalForm_I
          | appR h2 => exact absurd ⟨_, h2⟩ normalForm_I
      | appR h1 => exact .zw_pend (ih h1)
  | zw_done _ ih => exact fun hs => .zw_done (ih hs)
  | @yw_pend u hu ih =>
      intro t' hs
      cases hs with
      | S_red => exact .yw_fired (.kk_pend hu) (.zw_pend hu)
      | appL h1 => exact absurd ⟨_, h1⟩ Ybody_normal
      | appR h1 => exact .yw_pend (ih h1)
  | @yw_fired a b ha hb iha ihb =>
      intro t' hs
      cases hs with
      | K_red =>
          -- `a = app K x`: no kk-state has that shape (kk_done is a BARE `K`, one argument short)
          cases ha
      | S_red => cases ha
      | appL h1 => exact .yw_fired (iha h1) hb
      | appR h1 => exact .yw_fired ha (ihb h1)
  | @xw_pend u hu ih =>
      intro t' hs
      cases hs with
      | S_red => exact .xw_fired (.ks_pend hu) (.yw_pend hu)
      | appL h1 => exact absurd ⟨_, h1⟩ selfRepX_normal
      | appR h1 => exact .xw_pend (ih h1)
  | @xw_fired a b ha hb iha ihb =>
      intro t' hs
      cases hs with
      | K_red => cases ha
      | S_red => cases ha
      | appL h1 => exact .xw_fired (iha h1) hb
      | appR h1 => exact .xw_fired ha (ihb h1)
  | @eng_pair u₁ u₂ h1 h2 ih1 ih2 =>
      intro t' hs
      cases hs with
      | K_red =>
          -- `u₁ = app K x`: no iw-state has that shape — every case dies on index clash
          cases h1 with
          | iw_base hw => cases hw
      | S_red =>
          -- `u₁ = app (app S f) g`: only a W-copy matches, and the engine fires
          cases h1 with
          | iw_base hw =>
              cases hw with
              | wcopy hf => exact .eng_fired (.xw_pend h2) (.kf_pend hf h2)
      | appL h3 => exact .eng_pair (ih1 h3) h2
      | appR h3 => exact .eng_pair h1 (ih2 h3)
  | @eng_fired a b ha hb iha ihb =>
      intro t' hs
      cases hs with
      | K_red =>
          cases ha with
          | xw_fired h _ => cases h
      | S_red =>
          cases ha with
          | xw_fired h _ => cases h
      | appL h1 => exact .eng_fired (iha h1) hb
      | appR h1 => exact .eng_fired ha (ihb h1)
  | kfd_dat hd => exact fun hs => .kfd_dat (hD hd hs)
  | kfd_app hda => exact fun hs => .kfd_app (hDA hda hs)
  | @kfd_pend f u t hf hu ht ihu iht =>
      intro t' hs
      cases hs with
      | appL h1 =>
          cases h1 with
          | K_red => exact .kfd_app (hApp hf ht)
          | appL h2 =>
              cases h2 with
              | appL h3 => cases h3
              | appR h3 => exact .kfd_pend (Steps.trans hf (Steps.single h3)) hu ht
          | appR h2 => exact .kfd_pend hf (ihu h2) ht
      | appR h1 => exact .kfd_pend hf hu (iht h1)
  | @ydat_yd y t hy ht ihy iht =>
      intro t' hs
      cases hs with
      | K_red =>
          -- `y = app K z`: the discard fires — only `yw_fired` with a finished K matches
          cases hy with
          | yw_fired hkk hz =>
              cases hkk with
              | kk_done => exact .ydat_done hz
      | S_red =>
          cases hy with
          | yw_fired hkk _ => cases hkk
      | appL h1 => exact .ydat_yd (ihy h1) ht
      | appR h1 => exact .ydat_yd hy (iht h1)
  | ydat_done _ ih => exact fun hs => .ydat_done (ih hs)
  | @drv y t hy ht ihy iht =>
      intro t' hs
      cases hs with
      | K_red =>
          -- `y = app K x`: no ydat-state has that shape
          cases hy with
          | ydat_yd hy' _ => cases hy'
          | ydat_done hz =>
              cases hz with
              | zw_done he =>
                  cases he with
                  | eng_pair h1 _ =>
                      cases h1 with
                      | iw_base hw => cases hw
                  | eng_fired ha _ => cases ha
      | S_red =>
          -- `y = app (app S f) g`: the LAYER FIRE — only via a finished KS inside eng_fired,
          -- or the engine-pair's W-copy
          cases hy with
          | ydat_yd hy' _ =>
              cases hy' with
              | yw_fired hkk _ => cases hkk
          | ydat_done hz =>
              cases hz with
              | zw_done he =>
                  cases he with
                  | eng_pair h1 h2 =>
                      cases h1 with
                      | iw_base hw => cases hw
                  | eng_fired ha hb =>
                      cases ha with
                      | xw_fired hks hyw =>
                          cases hks with
                          | ks_done =>
                              -- the layer fire: S y b t ⟶ (y t) (b t)
                              cases hb with
                              | kf_pend hf hu =>
                                  exact .drv (.ydat_yd hyw ht) (.kfd_pend hf hu ht)
                              | kf_done hf =>
                                  exact .drv (.ydat_yd hyw ht) (.kfd_app (hApp hf ht))
      | appL h1 => exact .drv (ihy h1) ht
      | appR h1 => exact .drv hy (iht h1)

/-- Closure, iterated to paths. -/
theorem closed_steps
    (hD : ∀ {d d'}, D d → (d ⟶ d') → D d')
    (hDA : ∀ {d d'}, DA d → (d ⟶ d') → DA d')
    (hApp : ∀ {f t}, (F ⟶* f) → Sh F D DA .kfd t → DA (Term.app f t)) :
    ∀ {t t'}, (t ⟶* t') → ∀ {k}, Sh F D DA k t → Sh F D DA k t' := by
  intro t t' hs
  induction hs with
  | refl => exact fun h => h
  | tail s _ ih => exact fun h => ih (closed hD hDA hApp h s)

/-- The driver's start state is in the family. -/
theorem start {d : Term} (hd : D d) : Sh F D DA .drv (Term.app (selfRep F) d) :=
  .drv (.ydat_done (.zw_done (.eng_pair
    (.iw_base (.wcopy (Steps.refl F))) (.iw_base (.wcopy (Steps.refl F))))))
    (.kfd_dat hd)

end Sh

/-- **THE FIRST INTERIOR INVARIANT.** Every term reachable from the tag driver factors as shell
machinery over data holes — with the data layer left fully abstract (`DA := True`): the shell's
structure alone is now a theorem. Instantiating `D`/`DA` with the word layer is the next stage. -/
theorem driver_interior_invariant (w : List Bool) {t : Term} (h : encTagN w ⟶* t) :
    Sh STEPgn (fun d => encWord w ⟶* d) (fun _ => True) ShK.drv t :=
  Sh.closed_steps (fun hd hs => Steps.trans hd (Steps.single hs))
    (fun _ _ => trivial) (fun _ _ => trivial) h (Sh.start (Steps.refl _))

-- ## Stage 75: the data layer instantiated — and `bwd` falls
--
-- The right data predicate is SEMANTIC: a slot term denotes the source-reachable word whose
-- canonical form it still reaches. Step-closure is then free (confluence joins, normality of
-- `wordNF` pins — Stage 69's argument, reused as an interface discharge), the hand-off axiom is the
-- Stage 71 suite behind one confluence square, and the instantiated invariant says: every term
-- reachable from `encTagN w` is shell machinery whose EVERY data slot denotes a source-reachable
-- word. Then `bwd` is an inversion: a literal endpoint `encTagN w'` puts `encWord w'` in a data
-- slot, its denotation `u` satisfies `wordNF u = wordNF w'` by uniqueness of normal forms, and
-- injectivity gives `u = w'`. The order was in the slots all along.

/-- The applicative spine length — a cheap shape discriminator: machinery-wrapped slots have spine
3, the empty word 1, a cons cell 4. -/
def spineLen : Term → Nat
  | Term.app a _ => spineLen a + 1
  | _ => 0

/-- The semantic data layer: `t` denotes some word source-reachable from `w`. -/
def DataW (w : List Bool) (t : Term) : Prop :=
  ∃ u, (RS.Tag tagAB).Steps w u ∧ (t ⟶* wordNF (u.map encSym))

/-- Step-closed, for free: confluence joins, normality pins. -/
theorem DataW_step {w : List Bool} {d d' : Term} (h : DataW w d) (hs : d ⟶ d') :
    DataW w d' := by
  obtain ⟨u, hu, hp⟩ := h
  obtain ⟨s, h1, h2⟩ := confluence (Steps.single hs) hp
  exact ⟨u, hu, ((wordNF_normal (encWord_entries_normal u)).steps_eq h2).symm ▸ h1⟩

/-- The step function on a canonical word advances the source by a step — or holds it, stuck. -/
theorem STEPgn_wordNF_all (u : List Bool) :
    ∃ u', (RS.Tag tagAB).Steps u u' ∧
      (Term.app STEPgn (wordNF (u.map encSym)) ⟶* wordNF (u'.map encSym)) := by
  match u with
  | [] => exact ⟨[], RS.Steps.refl _, STEPgn_wordNF_stuck (by simp)⟩
  | [s] => exact ⟨[s], RS.Steps.refl _, STEPgn_wordNF_stuck (by simp)⟩
  | s :: y :: rest =>
      refine ⟨rest ++ ruleAB s, RS.Steps.single ⟨s, y :: rest, rfl, by simp [tagAB], rfl⟩, ?_⟩
      exact Steps.trans (STEPgn_wordNF s y rest) (mkWord_to_wordNF _)

/-- **Applying (any reduct of) the step function to a data term yields a data term** — the hand-off,
discharged: complete the slot, run the canonical step, join the drifted application by confluence. -/
theorem DataW_app {w : List Bool} {t f : Term} (h : DataW w t) (hf : STEPgn ⟶* f) :
    DataW w (Term.app f t) := by
  obtain ⟨u, hu, hp⟩ := h
  obtain ⟨u', hu', hred⟩ := STEPgn_wordNF_all u
  have hjoin : Term.app f (wordNF (u.map encSym)) ⟶* wordNF (u'.map encSym) := by
    obtain ⟨s, h1, h2⟩ := confluence (Steps.congL hf) hred
    exact ((wordNF_normal (encWord_entries_normal u')).steps_eq h2).symm ▸ h1
  exact ⟨u', RS.Steps.trans hu hu',
    Steps.trans (Steps.congR hp) hjoin⟩

/-- The hand-off for machinery-wrapped slots, by induction over the `kfd` fragment. -/
theorem Sh.kfd_data {w : List Bool} : ∀ {k t},
    Sh STEPgn (DataW w) (DataW w) k t → k = ShK.kfd →
      ∀ {f}, (STEPgn ⟶* f) → DataW w (Term.app f t) := by
  intro k t h
  induction h
  case kfd_dat hd =>
      intro _ f hf
      exact DataW_app hd hf
  case kfd_app hd =>
      intro _ f hf
      exact DataW_app hd hf
  case kfd_pend f' u'' t'' hf' hu ht ihu iht =>
      intro _ f hf
      have h1 : DataW w (Term.app f' t'') := iht rfl hf'
      obtain ⟨u', hu', hp⟩ := DataW_app h1 hf
      refine ⟨u', hu', ?_⟩
      refine Steps.trans (Steps.congR (Steps.single (Step.appL (Step.K_red f' u'')))) hp
  all_goals exact fun hk => nomatch hk

/-- **The interior invariant, nothing abstract**: every reduct of `encTagN w` is shell machinery
whose every data slot denotes a source-reachable word. -/
theorem driver_interior_invariant_data (w : List Bool) {t : Term} (h : encTagN w ⟶* t) :
    Sh STEPgn (DataW w) (DataW w) ShK.drv t := by
  refine Sh.closed_steps (fun hd hs => DataW_step hd hs) (fun hd hs => DataW_step hd hs)
    (fun hf ht => Sh.kfd_data ht rfl hf) h (Sh.start ?_)
  exact ⟨w, RS.Steps.refl _, mkWord_to_wordNF _⟩

/-- A denoting slot that IS a literal encoded word pins its source word exactly. -/
theorem DataW_pins {w w' : List Bool} (h : DataW w (encWord w')) :
    (RS.Tag tagAB).Steps w w' := by
  obtain ⟨u, hu, hp⟩ := h
  have heq : wordNF (u.map encSym) = wordNF (w'.map encSym) :=
    nf_unique hp (mkWord_to_wordNF _)
      (wordNF_normal (encWord_entries_normal u)) (wordNF_normal (encWord_entries_normal w'))
  exact (map_encSym_injective (wordNF_injective heq)) ▸ hu

/-- **`bwd`, at last.** A host path between literal encodings forces a source path: the endpoint's
data slot is `encWord w'`, the invariant says it denotes a source-reachable word, and denotation
pins the word. Ten stages after Stage 65 proved the unguarded version FALSE. -/
theorem tagABn_bwd {w w' : List Bool}
    (h : RS.SK.Steps (encTagN w) (encTagN w')) : (RS.Tag tagAB).Steps w w' := by
  have hinv := driver_interior_invariant_data w (RS.SK_steps_iff.mp h)
  have key : ∀ {t}, Sh STEPgn (DataW w) (DataW w) ShK.kfd t → t = encWord w' →
      (RS.Tag tagAB).Steps w w' := by
    intro t ht
    cases ht with
    | kfd_dat hd => exact fun heq => DataW_pins (heq ▸ hd)
    | kfd_app hd => exact fun heq => DataW_pins (heq ▸ hd)
    | kfd_pend hf' hu ht' =>
        intro heq
        exfalso
        cases w' with
        | nil =>
            have h2 : (3 : Nat) = 1 := congrArg spineLen heq
            exact absurd h2 (by decide)
        | cons s w'' =>
            have h2 : (3 : Nat) = 4 := congrArg spineLen heq
            exact absurd h2 (by decide)
  cases hinv with
  | drv hy ht => exact key ht rfl

/-- **THE SIMULATION.** A genuine two-symbol, deletion-number-two tag system — inspect, dispatch,
append, guarded on its halting condition — certifiably hosted inside SK, in the demanding encoding
class: encoder, decoder, `fwd`, and `bwd`, all machine-checked. Spec piece (v), complete. -/
def tagABInSK : Simulation (RS.Tag tagAB) RS.SK where
  enc := encTagN
  dec := decTagN
  dec_enc := decTagN_encTagN
  fwd := tagABn_fwd_SK
  bwd := tagABn_bwd

/-- The taxonomy certifies it: SK hosts the tag system, in the pinned, calibrated sense. -/
theorem universalReach_tagAB_SK : UniversalReach (RS.Tag tagAB) RS.SK :=
  ⟨tagABInSK⟩

-- Anchors: the Simulation is not the diagonal, not an inclusion, and really runs.
example : (RS.Tag tagAB).step [true, true, false] [false, false] :=
  ⟨true, [true, false], rfl, by decide, rfl⟩
example : RS.SK.Steps (encTagN [true, true, false]) (encTagN [false, false]) :=
  tagABInSK.fwd ⟨true, [true, false], rfl, by decide, rfl⟩
#guard decTagN (encTagN [true, false]) = some [true, false]
