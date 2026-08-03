--! # The build-enforced axiom audit
-- Stage 76 found the development's SIXTH `Classical.choice` leak — and unlike the first five, it
-- was PRE-EXISTING: `occurs_bracket`'s `grind` had been leaking since it was written, the Goal 1
-- headline `combinatory_completeness` sat downstream, and the per-stage audit never re-checks old
-- theorems. The global "no Classical.choice" claim was false for an unknown span. This file makes
-- the claim BUILD-ENFORCED: every headline theorem's exact axiom footprint is pinned with
-- `#guard_msgs`, so any future leak — in new code or old — fails the build.
import CombinatorCalculusPlayground.TagGeneral
import CombinatorCalculusPlayground.Universality.RungTermination
import CombinatorCalculusPlayground.Universality.SCConfluence
import CombinatorCalculusPlayground.Universality.SCDecidability
import CombinatorCalculusPlayground.Universality.SCMembers
import CombinatorCalculusPlayground.Universality.DecEngine
import CombinatorCalculusPlayground.Conservation
import CombinatorCalculusPlayground.Recurrence
import CombinatorCalculusPlayground.Universality.OneRule

/-- info: 'confluence' depends on axioms: [propext] -/
#guard_msgs in #print axioms confluence

/-- info: 'nf_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms nf_unique

/-- info: 'TermV.combinatory_completeness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms TermV.combinatory_completeness

/-- info: 'no_pure_S_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_pure_S_cycle

/-- info: 'conservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms conservation

/-- info: 'c1a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms c1a

/-- info: 'no_pathEncoding_SK_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_pathEncoding_SK_poly

/-- info: 'countdownInSK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms countdownInSK

/-- info: 'tagABInSK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tagABInSK

/-- info: 'universalReach_tagAB_SK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms universalReach_tagAB_SK

/-- info: 'absArgs_beta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms absArgs_beta

/-- info: 'selArgs_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms selArgs_normal

/-- info: 'finTagInSK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms finTagInSK

/-- info: 'universalReach_finTag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms universalReach_finTag

/-- info: 'SB_acyclic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SB_acyclic

/-- info: 'no_pathEncoding_SK_SB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_pathEncoding_SK_SB

/-- info: 'sc_no_leaf_self_embed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_no_leaf_self_embed

/-- info: 'scCycle_second_redex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scCycle_second_redex

/-- info: 'sc_no_leaf_collapse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_no_leaf_collapse

/-- info: 'sc_collapse_needs_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_collapse_needs_root

/-- info: 'sc_root_S_anatomy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_root_S_anatomy

/-- info: 'sc_root_C_anatomy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_root_C_anatomy

/-- info: 'scCycle_rotate_or_descend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scCycle_rotate_or_descend

/-- info: 'RS.acyclic_of_cycle_descent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RS.acyclic_of_cycle_descent

/-- info: 'scRootCycle_rotate_same_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scRootCycle_rotate_same_length

/-- info: 'sc_minimal_cycle_is_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_minimal_cycle_is_root

/-- info: 'sc_cycle_length_ge_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_cycle_length_ge_two

/-- info: 'sc_no_root_two_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_no_root_two_cycle

/-- info: 'sc_cycle_length_ge_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_cycle_length_ge_three

/-- info: 'sc_collapse_length_ge_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_collapse_length_ge_two

/-- info: 'sc_root_S_return_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_root_S_return_length

/-- info: 'SC_cycle' does not depend on any axioms -/
#guard_msgs in #print axioms SC_cycle

/-- info: 'SC_not_acyclic' does not depend on any axioms -/
#guard_msgs in #print axioms SC_not_acyclic

/-- info: 'sc_minimal_cycle_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_minimal_cycle_length

/-- info: 'sc_no_I_like' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_no_I_like

/-- info: 'sb_no_I_like' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sb_no_I_like

/-- info: 'SC_second_cycle' does not depend on any axioms -/
#guard_msgs in #print axioms SC_second_cycle

/-- info: 'sc_min_cycle_not_unique' does not depend on any axioms -/
#guard_msgs in #print axioms sc_min_cycle_not_unique

/-- info: 'sc_no_step_right_embed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_no_step_right_embed

/-- info: 'scInSK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scInSK

/-- info: 'sc_cycle_pump' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cycle_pump

/-- info: 'sc_root_three_cycle_classified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_root_three_cycle_classified

/-- info: 'sc_three_cycles_are_known' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_three_cycles_are_known

/-- info: 'sc_unbounded_convergence' does not depend on any axioms -/
#guard_msgs in #print axioms sc_unbounded_convergence

/-- info: 'scv_no_single_selector' does not depend on any axioms -/
#guard_msgs in #print axioms scv_no_single_selector

/-- info: 'scRot_beta' does not depend on any axioms -/
#guard_msgs in #print axioms scRot_beta

/-- info: 'scTagA_dispatch' does not depend on any axioms -/
#guard_msgs in #print axioms scTagA_dispatch

/-- info: 'scTagB_dispatch' does not depend on any axioms -/
#guard_msgs in #print axioms scTagB_dispatch

/-- info: 'scWord_step_false' does not depend on any axioms -/
#guard_msgs in #print axioms scWord_step_false

/-- info: 'scWord_step_true' does not depend on any axioms -/
#guard_msgs in #print axioms scWord_step_true

/-- info: 'scWord_normal' does not depend on any axioms -/
#guard_msgs in #print axioms scWord_normal

/-- info: 'scTraversal_step_false' does not depend on any axioms -/
#guard_msgs in #print axioms scTraversal_step_false

/-- info: 'scTraversal_step_true' does not depend on any axioms -/
#guard_msgs in #print axioms scTraversal_step_true

/-- info: 'scRun' does not depend on any axioms -/
#guard_msgs in #print axioms scRun

/-- info: 'tailInSC' does not depend on any axioms -/
#guard_msgs in #print axioms tailInSC

/-- info: 'scPCell_step_acc' does not depend on any axioms -/
#guard_msgs in #print axioms scPCell_step_acc

/-- info: 'scCons_beta' does not depend on any axioms -/
#guard_msgs in #print axioms scCons_beta

/-- info: 'scv_varHead2_step' does not depend on any axioms -/
#guard_msgs in #print axioms scv_varHead2_step

/-- info: 'scTCell_step' does not depend on any axioms -/
#guard_msgs in #print axioms scTCell_step

/-- info: 'scTWord_step' does not depend on any axioms -/
#guard_msgs in #print axioms scTWord_step

/-- info: 'scTCell2_step' does not depend on any axioms -/
#guard_msgs in #print axioms scTCell2_step

/-- info: 'Simulation.steps_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Simulation.steps_iff

/-- info: 'scStepsC_conservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scStepsC_conservation

/-- info: 'SCC_acyclic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SCC_acyclic

/-- info: 'scSteps_shrink_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scSteps_shrink_le

/-- info: 'scSteps_growth_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scSteps_growth_le

/-- info: 'SC_confluence' depends on axioms: [propext] -/
#guard_msgs in #print axioms SC_confluence

/-- info: 'sc_nf_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_nf_unique

/-- info: 'SCNF_iff' does not depend on any axioms -/
#guard_msgs in #print axioms SCNF_iff

/-- info: 'scReachFrom_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scReachFrom_iff

/-- info: 'scvStep_members' depends on axioms: [propext] -/
#guard_msgs in #print axioms scvStep_members

/-- info: 'scvSteps_countVar_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scvSteps_countVar_mono

/-- info: 'scv_cross_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_cross_last

/-- info: 'scv_lastVar_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_lastVar_step

/-- info: 'scv_lastVar_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_lastVar_steps

/-- info: 'scv_varHead_frozen' depends on axioms: [propext] -/
#guard_msgs in #print axioms scv_varHead_frozen

/-- info: 'scv_pair_pred' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_pair_pred

/-- info: 'scv_pair_funnel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_pair_funnel

/-- info: 'scv_stuck_steps' depends on axioms: [propext] -/
#guard_msgs in #print axioms scv_stuck_steps

/-- info: 'scv_stuck_no_pairPre' depends on axioms: [propext] -/
#guard_msgs in #print axioms scv_stuck_no_pairPre

/-- info: 'scv_sfire_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_sfire_count

/-- info: 'scv_ahead_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_ahead_steps

/-- info: 'scv_no_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_no_pair

/-- info: 'scv_no_pair_swapped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scv_no_pair_swapped

/-- info: 'scv_swap_reachable' does not depend on any axioms -/
#guard_msgs in #print axioms scv_swap_reachable

/-- info: 'sc_no_max_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_no_max_bound

/-- info: 'scMt_steps' does not depend on any axioms -/
#guard_msgs in #print axioms scMt_steps

/-- info: 'RS.Steps.exists_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms RS.Steps.exists_le

/-- info: 'List.nodup_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms List.nodup_length_le

/-- info: 'scReachCapped_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scReachCapped_sound

/-- info: 'scReachCapped_complete_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scReachCapped_complete_start

/-- info: 'scEnumLe_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scEnumLe_complete

/-- info: 'scReachCapped_saturates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scReachCapped_saturates

/-- info: 'scStepsLe_decidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scStepsLe_decidable

/-- info: 'sc_decidable_of_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_decidable_of_bound

/-- info: 'scCore_pump' does not depend on any axioms -/
#guard_msgs in #print axioms scCore_pump

/-- info: 'sc_glider' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_glider

/-- info: 'scGlider_deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scGlider_deterministic

/-- info: 'scGlider_no_normal_form' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scGlider_no_normal_form

/-- info: 'scReachCapped_excludes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scReachCapped_excludes

/-- info: 'scMt_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt_no_capped_path

/-- info: 'sc_bound_of_decidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_of_decidable

/-- info: 'sc_decidable_iff_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_decidable_iff_bound

/-- info: 'scChained_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scChained_steps

/-- info: 'scForced_mountain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scForced_mountain

/-- info: 'scMt2_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt2_no_capped_path

/-- info: 'sc_bound_floor_44' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_44

/-- info: 'scGlider_march_unbounded' depends on axioms: [propext] -/
#guard_msgs in #print axioms scGlider_march_unbounded

/-- info: 'RS.SuccKit.decidable_iff_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RS.SuccKit.decidable_iff_bound

/-- info: 'sk_decidable_iff_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sk_decidable_iff_bound

/-- info: 'sc_bound_floor_25' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_25

/-- info: 'sb_decidable_iff_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sb_decidable_iff_bound

/-- info: 'si_decidable_iff_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms si_decidable_iff_bound

/-- info: 'sc_cell_synth' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cell_synth

/-- info: 'scv_cell_synth' does not depend on any axioms -/
#guard_msgs in #print axioms scv_cell_synth

/-- info: 'scQCell_fire' does not depend on any axioms -/
#guard_msgs in #print axioms scQCell_fire

/-- info: 'scQWord_step' does not depend on any axioms -/
#guard_msgs in #print axioms scQWord_step

/-- info: 'sc_qcell_synth₃' does not depend on any axioms -/
#guard_msgs in #print axioms sc_qcell_synth₃

/-- info: 'scBCell_fire' does not depend on any axioms -/
#guard_msgs in #print axioms scBCell_fire

/-- info: 'scBWord_two' does not depend on any axioms -/
#guard_msgs in #print axioms scBWord_two
