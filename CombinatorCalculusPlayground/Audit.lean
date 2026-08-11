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

/-- info: 'scBWord_run' does not depend on any axioms -/
#guard_msgs in #print axioms scBWord_run

/-- info: 'scBCell_fuel_blind' does not depend on any axioms -/
#guard_msgs in #print axioms scBCell_fuel_blind

/-- info: 'sc_generation_cycle' does not depend on any axioms -/
#guard_msgs in #print axioms sc_generation_cycle

/-- info: 'sc_words_decay' does not depend on any axioms -/
#guard_msgs in #print axioms sc_words_decay

/-- info: 'sc_harvest_rebuild' does not depend on any axioms -/
#guard_msgs in #print axioms sc_harvest_rebuild

/-- info: 'sc_growth_step' does not depend on any axioms -/
#guard_msgs in #print axioms sc_growth_step

/-- info: 'sc_cellArm_pop' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cellArm_pop

/-- info: 'sc_spiral_descends' does not depend on any axioms -/
#guard_msgs in #print axioms sc_spiral_descends

/-- info: 'sc_pulse14' does not depend on any axioms -/
#guard_msgs in #print axioms sc_pulse14

/-- info: 'sc_read_bitC' does not depend on any axioms -/
#guard_msgs in #print axioms sc_read_bitC

/-- info: 'sc_read_bitB' does not depend on any axioms -/
#guard_msgs in #print axioms sc_read_bitB

/-- info: 'scLatch_run_C' does not depend on any axioms -/
#guard_msgs in #print axioms scLatch_run_C

/-- info: 'scLatch_run_B' does not depend on any axioms -/
#guard_msgs in #print axioms scLatch_run_B

/-- info: 'scModeC_pulse' does not depend on any axioms -/
#guard_msgs in #print axioms scModeC_pulse

/-- info: 'scModeB_pulse' does not depend on any axioms -/
#guard_msgs in #print axioms scModeB_pulse

/-- info: 'scForced_chained' depends on axioms: [propext] -/
#guard_msgs in #print axioms scForced_chained

/-- info: 'sc_reg_write' does not depend on any axioms -/
#guard_msgs in #print axioms sc_reg_write

/-- info: 'sc_two_clocks' does not depend on any axioms -/
#guard_msgs in #print axioms sc_two_clocks

/-- info: 'sc_independent_registers' does not depend on any axioms -/
#guard_msgs in #print axioms sc_independent_registers

/-- info: 'sc_ztest_zero' does not depend on any axioms -/
#guard_msgs in #print axioms sc_ztest_zero

/-- info: 'sc_ztest_nonzero' does not depend on any axioms -/
#guard_msgs in #print axioms sc_ztest_nonzero

/-- info: 'sc_testdec' does not depend on any axioms -/
#guard_msgs in #print axioms sc_testdec

/-- info: 'sc_testdec_twice' does not depend on any axioms -/
#guard_msgs in #print axioms sc_testdec_twice

/-- info: 'scReader_period' does not depend on any axioms -/
#guard_msgs in #print axioms scReader_period

/-- info: 'scReader_unbounded' does not depend on any axioms -/
#guard_msgs in #print axioms scReader_unbounded

/-- info: 'sc_pulse_parametric' does not depend on any axioms -/
#guard_msgs in #print axioms sc_pulse_parametric

/-- info: 'scOrb_forced' depends on axioms: [propext] -/
#guard_msgs in #print axioms scOrb_forced

/-- info: 'scOrb_cycle' does not depend on any axioms -/
#guard_msgs in #print axioms scOrb_cycle

/-- info: 'sc_park' does not depend on any axioms -/
#guard_msgs in #print axioms sc_park

/-- info: 'sc_park_forever' does not depend on any axioms -/
#guard_msgs in #print axioms sc_park_forever

/-- info: 'scPark_entry_C' does not depend on any axioms -/
#guard_msgs in #print axioms scPark_entry_C

/-- info: 'scPark_entry_CC' does not depend on any axioms -/
#guard_msgs in #print axioms scPark_entry_CC

/-- info: 'sc_phase_distinct' does not depend on any axioms -/
#guard_msgs in #print axioms sc_phase_distinct

/-- info: 'scParkTraceC_chained' depends on axioms: [propext] -/
#guard_msgs in #print axioms scParkTraceC_chained

/-- info: 'scParkTraceCC_chained' depends on axioms: [propext] -/
#guard_msgs in #print axioms scParkTraceCC_chained

/-- info: 'scMt4_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt4_steps

/-- info: 'scMt4_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt4_no_capped_path

/-- info: 'sc_bound_floor_186' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_186

/-- info: 'scFate_entry' does not depend on any axioms -/
#guard_msgs in #print axioms scFate_entry

/-- info: 'scFate_cycle' does not depend on any axioms -/
#guard_msgs in #print axioms scFate_cycle

/-- info: 'scFate_forever' does not depend on any axioms -/
#guard_msgs in #print axioms scFate_forever

/-- info: 'scFate_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scFate_runs

/-- info: 'scFate_halts' does not depend on any axioms -/
#guard_msgs in #print axioms scFate_halts

/-- info: 'scFateNf_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scFateNf_normal

/-- info: 'sc_fate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_fate

/-- info: 'scFateLap_chained' depends on axioms: [propext] -/
#guard_msgs in #print axioms scFateLap_chained

/-- info: 'scRanked_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scRanked_bound

/-- info: 'scFateSpace_ranked' depends on axioms: [propext] -/
#guard_msgs in #print axioms scFateSpace_ranked

/-- info: 'sc_fate_all_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_fate_all_bounded

/-- info: 'sc_fate_unique_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_fate_unique_exit

/-- info: 'sc_fate_universal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_fate_universal

/-- info: 'scPair_inv' does not depend on any axioms -/
#guard_msgs in #print axioms scPair_inv

/-- info: 'scPair_decompose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scPair_decompose

/-- info: 'scPair_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scPair_bounded

/-- info: 'scPair_normal' does not depend on any axioms -/
#guard_msgs in #print axioms scPair_normal

/-- info: 'sc_four_fates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_four_fates

/-- info: 'scStep_no_bit' does not depend on any axioms -/
#guard_msgs in #print axioms scStep_no_bit

/-- info: 'sc_bits_are_sources' does not depend on any axioms -/
#guard_msgs in #print axioms sc_bits_are_sources

/-- info: 'scRelay_decompose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scRelay_decompose

/-- info: 'sc_relay_wall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_relay_wall

/-- info: 'sc_relay_fates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_relay_fates

/-- info: 'sc_pair_reachable_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_pair_reachable_iff

/-- info: 'sc_shadow_drifts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_shadow_drifts

/-- info: 'scMt5_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt5_steps

/-- info: 'scMt5_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt5_no_capped_path

/-- info: 'sc_bound_floor_291' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_291

/-- info: 'sc_metabolic_assembly' does not depend on any axioms -/
#guard_msgs in #print axioms sc_metabolic_assembly

/-- info: 'sc_metabolic_assembly_bit' does not depend on any axioms -/
#guard_msgs in #print axioms sc_metabolic_assembly_bit

/-- info: 'sc_fate_assembly' does not depend on any axioms -/
#guard_msgs in #print axioms sc_fate_assembly

/-- info: 'sc_fate_assembly_halt' does not depend on any axioms -/
#guard_msgs in #print axioms sc_fate_assembly_halt

/-- info: 'sc_fate_assembly_universal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_fate_assembly_universal

/-- info: 'sc_assembly_line' does not depend on any axioms -/
#guard_msgs in #print axioms sc_assembly_line

/-- info: 'scFate_is_frame' does not depend on any axioms -/
#guard_msgs in #print axioms scFate_is_frame

/-- info: 'sc_frame_halt' does not depend on any axioms -/
#guard_msgs in #print axioms sc_frame_halt

/-- info: 'sc_frame_halt_universal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_frame_halt_universal

/-- info: 'scFrame_cycle' does not depend on any axioms -/
#guard_msgs in #print axioms scFrame_cycle

/-- info: 'scGrow_period' does not depend on any axioms -/
#guard_msgs in #print axioms scGrow_period

/-- info: 'sc_frame_grow_unbounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_frame_grow_unbounded

/-- info: 'sc_frame_trichotomy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_frame_trichotomy

/-- info: 'sc_cycle_forever' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cycle_forever

/-- info: 'sc_cycle_unbounded' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cycle_unbounded

/-- info: 'sc_parity_hosted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_parity_hosted

/-- info: 'sc_frame_prelude' does not depend on any axioms -/
#guard_msgs in #print axioms sc_frame_prelude

/-- info: 'scParityNfT_normal' does not depend on any axioms -/
#guard_msgs in #print axioms scParityNfT_normal

/-- info: 'sc_parity_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_parity_even

/-- info: 'sc_parity_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_parity_entry

/-- info: 'sc_parity_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_parity_cycle

/-- info: 'sc_frame_parity_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_frame_parity_law

/-- info: 'sc_frame_handoff' does not depend on any axioms -/
#guard_msgs in #print axioms sc_frame_handoff

/-- info: 'sc_frame_shield' does not depend on any axioms -/
#guard_msgs in #print axioms sc_frame_shield

/-- info: 'sc_wrapper_isa' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_wrapper_isa

/-- info: 'sc_frame_omega' does not depend on any axioms -/
#guard_msgs in #print axioms sc_frame_omega

/-- info: 'sc_omega_to_loop' does not depend on any axioms -/
#guard_msgs in #print axioms sc_omega_to_loop

/-- info: 'sc_dispatch_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_dispatch_even

/-- info: 'sc_dispatch_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_dispatch_odd

/-- info: 'sc_addressed_fetch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_addressed_fetch

/-- info: 'scCellArm_popN' does not depend on any axioms -/
#guard_msgs in #print axioms scCellArm_popN

/-- info: 'sc_gene_express' does not depend on any axioms -/
#guard_msgs in #print axioms sc_gene_express

/-- info: 'sc_reproduction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_reproduction

/-- info: 'sc_machines_beget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_machines_beget

/-- info: 'sc_lineage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_lineage

/-- info: 'sc_dynasty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_dynasty

/-- info: 'sc_branch_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_branch_even

/-- info: 'sc_branch_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_branch_odd

/-- info: 'sc_conditional_dynasty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_conditional_dynasty

/-- info: 'sc_gene_anywhere' does not depend on any axioms -/
#guard_msgs in #print axioms sc_gene_anywhere

/-- info: 'sc_tape_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_tape_run

/-- info: 'sc_tape_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_tape_stop

/-- info: 'sc_successor' does not depend on any axioms -/
#guard_msgs in #print axioms sc_successor

/-- info: 'sc_routed_successor' does not depend on any axioms -/
#guard_msgs in #print axioms sc_routed_successor

/-- info: 'sc_successor_numeral' does not depend on any axioms -/
#guard_msgs in #print axioms sc_successor_numeral

/-- info: 'scMt6_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt6_no_capped_path

/-- info: 'sc_bound_floor_87' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_87

/-- info: 'sc_cheap_omega' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cheap_omega

/-- info: 'sc_successor_call' does not depend on any axioms -/
#guard_msgs in #print axioms sc_successor_call

/-- info: 'sc_chain_fire' does not depend on any axioms -/
#guard_msgs in #print axioms sc_chain_fire

/-- info: 'sc_chain_run' does not depend on any axioms -/
#guard_msgs in #print axioms sc_chain_run

/-- info: 'sc_bounded_odometer' does not depend on any axioms -/
#guard_msgs in #print axioms sc_bounded_odometer

/-- info: 'scMt7_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt7_no_capped_path

/-- info: 'sc_bound_floor_366' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_366

/-- info: 'sc_spine_dichotomy' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_spine_dichotomy

/-- info: 'sc_call_source' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_call_source

/-- info: 'sc_head_provenance' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_head_provenance

/-- info: 'sc_numerals_are_sources' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_numerals_are_sources

/-- info: 'sc_numeral_speed_limit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_numeral_speed_limit

/-- info: 'sc_numeral_speed_limit_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_numeral_speed_limit_run

/-- info: 'sc_cargo_law' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_cargo_law

/-- info: 'sc_stamp' does not depend on any axioms -/
#guard_msgs in #print axioms sc_stamp

/-- info: 'sc_cell_mint' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cell_mint

/-- info: 'scStepAt_split' does not depend on any axioms -/
#guard_msgs in #print axioms scStepAt_split

/-- info: 'sc_suffix_law' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_suffix_law

/-- info: 'sc_passthrough' does not depend on any axioms -/
#guard_msgs in #print axioms sc_passthrough

/-- info: 'sc_cword_run' does not depend on any axioms -/
#guard_msgs in #print axioms sc_cword_run

/-- info: 'sc_junk_ignition' does not depend on any axioms -/
#guard_msgs in #print axioms sc_junk_ignition

/-- info: 'sc_junk_is_cell' does not depend on any axioms -/
#guard_msgs in #print axioms sc_junk_is_cell

/-- info: 'sc_pulse_core' does not depend on any axioms -/
#guard_msgs in #print axioms sc_pulse_core

/-- info: 'sc_pulse_law' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_pulse_law

/-- info: 'sc_burn_wave' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_burn_wave

/-- info: 'sc_alternator_coexist' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_alternator_coexist

/-- info: 'sc_ouro_writes' does not depend on any axioms -/
#guard_msgs in #print axioms sc_ouro_writes

/-- info: 'sc_ouroboros' does not depend on any axioms -/
#guard_msgs in #print axioms sc_ouroboros

/-- info: 'sc_ouroWave_core' does not depend on any axioms -/
#guard_msgs in #print axioms sc_ouroWave_core

/-- info: 'sc_ouroWave_law' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_ouroWave_law

/-- info: 'sc_ouro_eternal' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_ouro_eternal

/-- info: 'scMaxReg_appList_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms scMaxReg_appList_zero

/-- info: 'sc_pulse_numeral_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_pulse_numeral_free

/-- info: 'sc_ouroWave_numeral_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_ouroWave_numeral_free

/-- info: 'scMaxReg_parityReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMaxReg_parityReg

/-- info: 'sc_orbit_carries_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_orbit_carries_depth

/-- info: 'sc_depth_breadth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_depth_breadth

/-- info: 'sc_depth_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_depth_cost

/-- info: 'sc_order_halts' does not depend on any axioms -/
#guard_msgs in #print axioms sc_order_halts

/-- info: 'scOrderNf_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scOrderNf_normal

/-- info: 'scMt8_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt8_no_capped_path

/-- info: 'sc_bound_floor_308' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_308

/-- info: 'scForced_mountain_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scForced_mountain_last

/-- info: 'scMt9_no_capped_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt9_no_capped_path

/-- info: 'sc_bound_floor_666' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_bound_floor_666

/-- info: 'sc_spiral_anchor' does not depend on any axioms -/
#guard_msgs in #print axioms sc_spiral_anchor

/-- info: 'sc_spiral_turn0' does not depend on any axioms -/
#guard_msgs in #print axioms sc_spiral_turn0

/-- info: 'sc_spiral_turn1' does not depend on any axioms -/
#guard_msgs in #print axioms sc_spiral_turn1

/-- info: 'sc_spiral_turn2' does not depend on any axioms -/
#guard_msgs in #print axioms sc_spiral_turn2

/-- info: 'sc_spiral_reach3' does not depend on any axioms -/
#guard_msgs in #print axioms sc_spiral_reach3

/-- info: 'sc_mill_descent' does not depend on any axioms -/
#guard_msgs in #print axioms sc_mill_descent

/-- info: 'sc_mill_turnover' does not depend on any axioms -/
#guard_msgs in #print axioms sc_mill_turnover

/-- info: 'sc_mill_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mill_cycle

/-- info: 'sc_mill_eternal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mill_eternal

/-- info: 'sc_corridor_unbounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_corridor_unbounded

/-- info: 'scMillT_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMillT_normal

/-- info: 'sc_mill_descent_forced' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_mill_descent_forced

/-- info: 'sc_mill_turnover_forced' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_mill_turnover_forced

/-- info: 'sc_mill_descent_run_forced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mill_descent_run_forced

/-- info: 'sc_forced_rider' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_forced_rider

/-- info: 'sc_forced_forever_no_nf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_forced_forever_no_nf

/-- info: 'scMillRevStates_forced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMillRevStates_forced

/-- info: 'sc_forced_riders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_forced_riders

/-- info: 'sc_mt5T_no_nf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mt5T_no_nf

/-- info: 'scNoNFF_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scNoNFF_steps

/-- info: 'sc_corridor_excess' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_corridor_excess

/-- info: 'sc_forced_family_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_forced_family_mem

/-- info: 'sc_mt5T_reach_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mt5T_reach_iff

/-- info: 'scMt5TReach_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt5TReach_iff

/-- info: 'scMt5TReach_decidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMt5TReach_decidable

/-- info: 'sc_champ211_corridor' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_champ211_corridor

/-- info: 'sc_champ159_corridor' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_champ159_corridor

/-- info: 'sc_mt5T_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mt5T_flat

/-- info: 'sc_mt5T_not_deepening' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mt5T_not_deepening

/-- info: 'scChained_comparable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scChained_comparable

/-- info: 'sc_mt5T_line' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_mt5T_line

/-- info: 'sc_swap_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swap_run

/-- info: 'sc_swap_turnover' does not depend on any axioms -/
#guard_msgs in #print axioms sc_swap_turnover

/-- info: 'sc_swap_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swap_cycle

/-- info: 'sc_swap_reseed' does not depend on any axioms -/
#guard_msgs in #print axioms sc_swap_reseed

/-- info: 'sc_unit_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_unit_drop

/-- info: 'sc_descent_speed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_descent_speed

/-- info: 'scStepC_psi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scStepC_psi

/-- info: 'sc_cold_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_cold_law

/-- info: 'scCInv_succ_le_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scCInv_succ_le_leaf

/-- info: 'sc_minting_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_minting_law

/-- info: 'sc_minting_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_minting_run

/-- info: 'sc_swap_rebirth' does not depend on any axioms -/
#guard_msgs in #print axioms sc_swap_rebirth

/-- info: 'sc_swap_revolution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swap_revolution

/-- info: 'sc_swap_eternal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swap_eternal

/-- info: 'sc_swap_unbounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swap_unbounded

/-- info: 'scSwapRun_forced' depends on axioms: [propext] -/
#guard_msgs in #print axioms scSwapRun_forced

/-- info: 'sc_swap_turnover_forced' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_swap_turnover_forced

/-- info: 'sc_swap_rebirth_forced' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_swap_rebirth_forced

/-- info: 'sc_swap_rev_forced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swap_rev_forced

/-- info: 'sc_swapseed_no_nf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swapseed_no_nf

/-- info: 'sc_swapseed_reach_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swapseed_reach_iff

/-- info: 'sc_forced_family_line' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_forced_family_line

/-- info: 'sc_swapseed_line' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_swapseed_line

/-- info: 'scSwapReach_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scSwapReach_iff

/-- info: 'scSwapReach_decidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scSwapReach_decidable

/-- info: 'sc_champ170_anchor' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_champ170_anchor

/-- info: 'sc_champ170_no_nf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_champ170_no_nf

/-- info: 'sc_c12_decides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_c12_decides

/-- info: 'sc_driver_law' does not depend on any axioms -/
#guard_msgs in #print axioms sc_driver_law

/-- info: 'sc_l3_descent' does not depend on any axioms -/
#guard_msgs in #print axioms sc_l3_descent

/-- info: 'sc_l3_descent_forced' depends on axioms: [propext] -/
#guard_msgs in #print axioms sc_l3_descent_forced

/-- info: 'sc_metro_law' does not depend on any axioms -/
#guard_msgs in #print axioms sc_metro_law

/-- info: 'sc_metro_eternal' does not depend on any axioms -/
#guard_msgs in #print axioms sc_metro_eternal

/-- info: 'sc_metro_no_nf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_metro_no_nf

/-- info: 'sc_metro_reach_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sc_metro_reach_iff

/-- info: 'scMetroReach_decidable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scMetroReach_decidable
