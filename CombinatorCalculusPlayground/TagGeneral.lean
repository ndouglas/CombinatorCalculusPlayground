--! # The general tag machine — any m = 2 system, given a dispatch
-- Stage 78. The Stages 63–75 pipeline, re-built once, parametrically: for ANY tag system `T` with
-- deletion number 2, given a symbol encoding and a dispatcher satisfying four hypotheses —
--
--     hNorm  : symbols are normal          hInj  : symbols are injective
--     hRULE  : dispatch computes the rule  hdecS : symbols are decodable
--
-- there is a `Simulation (RS.Tag T) RS.SK`. Everything below is transcription: the word toolkit,
-- `wordNF` theory, guard, shell invariant, and semantic data layer were all generic already; only
-- the step function's assembly and the tag-level glue mention the parameters. One simplification
-- over the two-symbol original: `fwd` routes through drift-completion (Stage 71), so the
-- literal-input step suite never needs restating.
--
-- The interface is discharged for concrete alphabets by Stage 76–77's selectors (`selArgs_normal`,
-- `selArgs_injective`, `dispatchT_correct`); that instantiation is the next stage.
import CombinatorCalculusPlayground.DriverShell

open Term

section GeneralTag

variable {T : TagSystem} (encS : T.Sym → Term) (RULE : Term)

/-- The encoded word. -/
def encWordT (w : List T.Sym) : Term := mkWord (w.map encS)

/-- The unguarded step function over the given dispatch: `λL. CAT (TAIL (TAIL L)) (RULE (HEAD L))`. -/
def STEPcT : Term := toTerm (TermV.bracketOpt 0 (TermV.app2 (ofTerm CATf)
  (TermV.app (ofTerm TAILn) (TermV.app (ofTerm TAILn) (.var 0)))
  (TermV.app (ofTerm RULE) (TermV.app (ofTerm HEADf) (.var 0)))))

/-- ...guarded on the halting condition: `λL. HASTWO L (STEPc L) L`. -/
def STEPgT : Term := toTerm (TermV.bracketOpt 0
  (TermV.app2 (TermV.app (ofTerm HASTWOn) (.var 0))
    (TermV.app (ofTerm (STEPcT RULE)) (.var 0)) (.var 0)))

theorem STEPcT_beta (L : Term) :
    Term.app (STEPcT RULE) L ⟶* Term.app (Term.app CATf (Term.app TAILn (Term.app TAILn L)))
      (Term.app RULE (Term.app HEADf L)) := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (ofTerm CATf)
    (TermV.app (ofTerm TAILn) (TermV.app (ofTerm TAILn) (.var 0)))
    (TermV.app (ofTerm RULE) (TermV.app (ofTerm HEADf) (.var 0)))) L
  simpa [TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

theorem STEPgT_beta (L : Term) :
    Term.app (STEPgT RULE) L
      ⟶* Term.app (Term.app (Term.app HASTWOn L) (Term.app (STEPcT RULE) L)) L := by
  have h := bracketOpt_beta_Term 0 (TermV.app2 (TermV.app (ofTerm HASTWOn) (.var 0))
    (TermV.app (ofTerm (STEPcT RULE)) (.var 0)) (.var 0)) L
  simpa [TermV.app2, TermV.subst, subst_ofTerm, toTerm] using h

-- ### The canonical-input step suite

theorem STEPcT_wordNF
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (s y : T.Sym) (rest : List T.Sym) :
    Term.app (STEPcT RULE) (wordNF ((s :: y :: rest).map encS))
      ⟶* encWordT encS (rest ++ T.rule s) := by
  refine Steps.trans (STEPcT_beta RULE _) ?_
  have htail : Term.app TAILn (Term.app TAILn (wordNF ((s :: y :: rest).map encS)))
      ⟶* encWordT encS rest := by
    refine Steps.trans (Steps.congR (TAILn_wordNF (encS s :: encS y :: rest.map encS))) ?_
    exact TAILn_mkWord (encS y :: rest.map encS)
  have hrule : Term.app RULE (Term.app HEADf (wordNF ((s :: y :: rest).map encS)))
      ⟶* mkWord ((T.rule s).map encS) := by
    refine Steps.trans (Steps.congR (HEADf_wordNF (encS s) ((y :: rest).map encS))) ?_
    exact hRULE s
  refine Steps.trans (Steps.congApp (Steps.congR htail) hrule) ?_
  rw [show encWordT encS (rest ++ T.rule s)
      = mkWord (rest.map encS ++ (T.rule s).map encS) by simp [encWordT]]
  exact CATf_mkWord (rest.map encS) ((T.rule s).map encS)

theorem STEPgT_wordNF
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (s y : T.Sym) (rest : List T.Sym) :
    Term.app (STEPgT RULE) (wordNF ((s :: y :: rest).map encS))
      ⟶* encWordT encS (rest ++ T.rule s) := by
  refine Steps.trans (STEPgT_beta RULE _) ?_
  have hguard : Term.app HASTWOn (wordNF ((s :: y :: rest).map encS)) ⟶* symA := by
    refine Steps.trans (HASTWOn_beta _) ?_
    refine Steps.trans (Steps.congR (TAILn_wordNF (encS s :: encS y :: rest.map encS))) ?_
    exact NONNILf_cons (encS y) (rest.map encS)
  refine Steps.trans (Steps.congL (Steps.congL hguard)) ?_
  refine Steps.trans (Steps.single (Step.K_red _ _)) ?_
  exact STEPcT_wordNF encS RULE hRULE s y rest

theorem STEPgT_wordNF_stuck : ∀ {w : List T.Sym}, w.length < 2 →
    Term.app (STEPgT RULE) (wordNF (w.map encS)) ⟶* wordNF (w.map encS) := by
  intro w hw
  match w with
  | [] =>
      refine Steps.trans (STEPgT_beta RULE _) ?_
      refine Steps.trans (Steps.congL (Steps.congL HASTWOn_nil)) ?_
      exact Steps.tail (Step.S_red K _ _) (Steps.single (Step.K_red _ _))
  | [s] =>
      have hguard : Term.app HASTWOn (wordNF [encS s]) ⟶* symB := by
        refine Steps.trans (HASTWOn_beta _) ?_
        exact Steps.trans (Steps.congR (TAILn_wordNF [encS s])) NONNILf_nil
      refine Steps.trans (STEPgT_beta RULE _) ?_
      refine Steps.trans (Steps.congL (Steps.congL hguard)) ?_
      exact Steps.tail (Step.S_red K _ _) (Steps.single (Step.K_red _ _))
  | _ :: _ :: _ => exact absurd hw (by simp)

-- ### Drift and the driver

theorem encWordT_entries_normal (hNorm : ∀ s : T.Sym, NormalForm (encS s))
    (w : List T.Sym) : ∀ x ∈ w.map encS, NormalForm x := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨s, _, rfl⟩ := hx
  exact hNorm s

theorem encWordT_drift_complete (hNorm : ∀ s : T.Sym, NormalForm (encS s))
    {w : List T.Sym} {t : Term} (h : encWordT encS w ⟶* t) :
    t ⟶* wordNF (w.map encS) :=
  mkWord_drift_complete (encWordT_entries_normal encS hNorm w) h

theorem STEPgT_drift
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s))
    {s y : T.Sym} {rest : List T.Sym} {t : Term}
    (ht : encWordT encS (s :: y :: rest) ⟶* t) :
    Term.app (STEPgT RULE) t ⟶* encWordT encS (rest ++ T.rule s) := by
  refine Steps.trans (Steps.congR (encWordT_drift_complete encS hNorm ht)) ?_
  exact STEPgT_wordNF encS RULE hRULE s y rest

/-- The encoder: the driver applied to the encoded word. -/
def encTagT (w : List T.Sym) : Term := Term.app (selfRep (STEPgT RULE)) (encWordT encS w)

theorem tagT_fwd
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    {w w' : List T.Sym} (h : (RS.Tag T).step w w') :
    encTagT encS RULE w ⟶* encTagT encS RULE w' := by
  obtain ⟨a, rest, hw, hlen, hw'⟩ := h
  subst hw
  rw [hm] at hlen hw'
  cases rest with
  | nil => simp at hlen
  | cons y rest' =>
      subst hw'
      exact tagFwd_of_step (STEPgT_drift encS RULE hRULE hNorm (Steps.refl _))

theorem tagT_fwd_SK
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    {w w' : List T.Sym} (h : (RS.Tag T).step w w') :
    RS.SK.Steps (encTagT encS RULE w) (encTagT encS RULE w') :=
  RS.SK_steps_iff.mpr (tagT_fwd encS RULE hRULE hNorm hm h)

-- ### The decoder

variable (decS : Term → Option T.Sym)

def decWordT : Term → Option (List T.Sym)
  | Term.app (Term.app c x) r =>
      if c = CONSf then
        match decS x, decWordT r with
        | some s, some w => some (s :: w)
        | _, _ => none
      else if Term.app (Term.app c x) r = NILf then some [] else none
  | t => if t = NILf then some [] else none

theorem decWordT_encWordT (hdecS : ∀ s, decS (encS s) = some s) :
    ∀ (w : List T.Sym), decWordT decS (encWordT encS w) = some w := by
  intro w
  induction w with
  | nil => rfl
  | cons s w' ih =>
      have ih' : decWordT decS (mkWord (w'.map encS)) = some w' := ih
      show (if CONSf = CONSf then
          match decS (encS s), decWordT decS (mkWord (w'.map encS)) with
          | some s, some w => some (s :: w)
          | _, _ => none
        else if Term.app (Term.app CONSf (encS s)) (mkWord (w'.map encS)) = NILf
          then some [] else none) = some (s :: w')
      rw [if_pos rfl, hdecS s, ih']

def decTagT (t : Term) : Option (List T.Sym) :=
  match t with
  | Term.app d w => if d = selfRep (STEPgT RULE) then decWordT decS w else none
  | _ => none

theorem decTagT_encTagT (hdecS : ∀ s, decS (encS s) = some s) (w : List T.Sym) :
    decTagT RULE decS (encTagT encS RULE w) = some w := by
  show (if selfRep (STEPgT RULE) = selfRep (STEPgT RULE)
    then decWordT decS (encWordT encS w) else none) = some w
  rw [if_pos rfl]
  exact decWordT_encWordT encS decS hdecS w

-- ### Injectivity

theorem map_encS_injective (hInj : ∀ {s s' : T.Sym}, encS s = encS s' → s = s') :
    ∀ {u v : List T.Sym}, u.map encS = v.map encS → u = v := by
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
          rw [hInj h.1, ih h.2]

-- ### The semantic data layer and `bwd`

/-- `t` denotes a word source-reachable from `w`. -/
def DataT (w : List T.Sym) (t : Term) : Prop :=
  ∃ u, (RS.Tag T).Steps w u ∧ (t ⟶* wordNF (u.map encS))

theorem DataT_step (hNorm : ∀ s : T.Sym, NormalForm (encS s))
    {w : List T.Sym} {d d' : Term} (h : DataT encS w d) (hs : d ⟶ d') :
    DataT encS w d' := by
  obtain ⟨u, hu, hp⟩ := h
  obtain ⟨s, h1, h2⟩ := confluence (Steps.single hs) hp
  exact ⟨u, hu,
    ((wordNF_normal (encWordT_entries_normal encS hNorm u)).steps_eq h2).symm ▸ h1⟩

theorem STEPgT_wordNF_all
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hm : T.m = 2) (u : List T.Sym) :
    ∃ u', (RS.Tag T).Steps u u' ∧
      (Term.app (STEPgT RULE) (wordNF (u.map encS)) ⟶* wordNF (u'.map encS)) := by
  match u with
  | [] => exact ⟨[], RS.Steps.refl _, STEPgT_wordNF_stuck encS RULE (by simp)⟩
  | [s] => exact ⟨[s], RS.Steps.refl _, STEPgT_wordNF_stuck encS RULE (by simp)⟩
  | s :: y :: rest =>
      refine ⟨rest ++ T.rule s, RS.Steps.single ⟨s, y :: rest, rfl, ?_, ?_⟩, ?_⟩
      · rw [hm]; simp
      · rw [hm]
        rfl
      · exact Steps.trans (STEPgT_wordNF encS RULE hRULE s y rest) (mkWord_to_wordNF _)

theorem DataT_app
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    {w : List T.Sym} {t f : Term} (h : DataT encS w t)
    (hf : STEPgT RULE ⟶* f) : DataT encS w (Term.app f t) := by
  obtain ⟨u, hu, hp⟩ := h
  obtain ⟨u', hu', hred⟩ := STEPgT_wordNF_all encS RULE hRULE hm u
  have hjoin : Term.app f (wordNF (u.map encS)) ⟶* wordNF (u'.map encS) := by
    obtain ⟨s, h1, h2⟩ := confluence (Steps.congL hf) hred
    exact ((wordNF_normal (encWordT_entries_normal encS hNorm u')).steps_eq h2).symm ▸ h1
  exact ⟨u', RS.Steps.trans hu hu', Steps.trans (Steps.congR hp) hjoin⟩

theorem kfd_dataT
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    {w : List T.Sym} : ∀ {k t},
    Sh (STEPgT RULE) (DataT encS w) (DataT encS w) k t → k = ShK.kfd →
      ∀ {f}, (STEPgT RULE ⟶* f) → DataT encS w (Term.app f t) := by
  intro k t h
  induction h
  case kfd_dat hd =>
      intro _ f hf
      exact DataT_app encS RULE hRULE hNorm hm hd hf
  case kfd_app hd =>
      intro _ f hf
      exact DataT_app encS RULE hRULE hNorm hm hd hf
  case kfd_pend f' u'' t'' hf' hu ht ihu iht =>
      intro _ f hf
      have h1 : DataT encS w (Term.app f' t'') := iht rfl hf'
      obtain ⟨u', hu', hp⟩ := DataT_app encS RULE hRULE hNorm hm h1 hf
      refine ⟨u', hu', ?_⟩
      exact Steps.trans (Steps.congR (Steps.single (Step.appL (Step.K_red f' u'')))) hp
  all_goals exact fun hk => nomatch hk

theorem driver_invariant_T
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    (w : List T.Sym) {t : Term} (h : encTagT encS RULE w ⟶* t) :
    Sh (STEPgT RULE) (DataT encS w) (DataT encS w) ShK.drv t := by
  refine Sh.closed_steps (fun hd hs => DataT_step encS hNorm hd hs)
    (fun hd hs => DataT_step encS hNorm hd hs)
    (fun hf ht => kfd_dataT encS RULE hRULE hNorm hm ht rfl hf) h (Sh.start ?_)
  exact ⟨w, RS.Steps.refl _, mkWord_to_wordNF _⟩

theorem DataT_pins (hNorm : ∀ s : T.Sym, NormalForm (encS s))
    (hInj : ∀ {s s' : T.Sym}, encS s = encS s' → s = s')
    {w w' : List T.Sym} (h : DataT encS w (encWordT encS w')) :
    (RS.Tag T).Steps w w' := by
  obtain ⟨u, hu, hp⟩ := h
  have heq : wordNF (u.map encS) = wordNF (w'.map encS) :=
    nf_unique hp (mkWord_to_wordNF _)
      (wordNF_normal (encWordT_entries_normal encS hNorm u))
      (wordNF_normal (encWordT_entries_normal encS hNorm w'))
  exact (map_encS_injective encS @hInj (wordNF_injective heq)) ▸ hu

theorem tagT_bwd
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    (hInj : ∀ {s s' : T.Sym}, encS s = encS s' → s = s')
    {w w' : List T.Sym}
    (h : RS.SK.Steps (encTagT encS RULE w) (encTagT encS RULE w')) :
    (RS.Tag T).Steps w w' := by
  have hinv := driver_invariant_T encS RULE hRULE hNorm hm w (RS.SK_steps_iff.mp h)
  have key : ∀ {t}, Sh (STEPgT RULE) (DataT encS w) (DataT encS w) ShK.kfd t →
      t = encWordT encS w' → (RS.Tag T).Steps w w' := by
    intro t ht
    cases ht with
    | kfd_dat hd =>
        exact fun heq => DataT_pins encS hNorm @hInj (heq ▸ hd)
    | kfd_app hd =>
        exact fun heq => DataT_pins encS hNorm @hInj (heq ▸ hd)
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

/-- **THE GENERAL THEOREM.** Any deletion-number-2 tag system whose symbols can be encoded normally,
injectively, decodably, and dispatchably is certifiably hosted inside SK. Every concrete
known-universal 2-tag system is an instance. -/
def tagTInSK
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    (hdecS : ∀ s, decS (encS s) = some s)
    (hInj : ∀ {s s' : T.Sym}, encS s = encS s' → s = s') :
    Simulation (RS.Tag T) RS.SK where
  enc := encTagT encS RULE
  dec := decTagT RULE decS
  dec_enc := decTagT_encTagT encS RULE decS hdecS
  fwd := tagT_fwd_SK encS RULE hRULE hNorm hm
  bwd := tagT_bwd encS RULE hRULE hNorm hm @hInj

theorem universalReach_tagT
    (hRULE : ∀ s : T.Sym, Term.app RULE (encS s) ⟶* mkWord ((T.rule s).map encS))
    (hNorm : ∀ s : T.Sym, NormalForm (encS s)) (hm : T.m = 2)
    (hdecS : ∀ s, decS (encS s) = some s)
    (hInj : ∀ {s s' : T.Sym}, encS s = encS s' → s = s') :
    UniversalReach (RS.Tag T) RS.SK :=
  ⟨tagTInSK encS RULE decS hRULE hNorm hm hdecS @hInj⟩

end GeneralTag

-- Anchor: the Stage 75 two-symbol system is an instance of the general theorem — every hypothesis
-- discharged by a lemma that already existed.
example : Simulation (RS.Tag tagAB) RS.SK :=
  tagTInSK encSym RULEf decSym RULEf_encSym encSym_normal rfl
    (fun s => by cases s <;> rfl) (fun {s s'} h => encSym_injective h)
