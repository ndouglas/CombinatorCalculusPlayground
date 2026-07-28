--! # The build-enforced axiom audit
-- Stage 76 found the development's SIXTH `Classical.choice` leak — and unlike the first five, it
-- was PRE-EXISTING: `occurs_bracket`'s `grind` had been leaking since it was written, the Goal 1
-- headline `combinatory_completeness` sat downstream, and the per-stage audit never re-checks old
-- theorems. The global "no Classical.choice" claim was false for an unknown span. This file makes
-- the claim BUILD-ENFORCED: every headline theorem's exact axiom footprint is pinned with
-- `#guard_msgs`, so any future leak — in new code or old — fails the build.
import CombinatorCalculusPlayground.TagGeneral
import CombinatorCalculusPlayground.Universality.RungTermination
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
