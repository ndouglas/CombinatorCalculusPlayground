--! # The build-enforced axiom audit
-- Stage 76 found the development's SIXTH `Classical.choice` leak — and unlike the first five, it
-- was PRE-EXISTING: `occurs_bracket`'s `grind` had been leaking since it was written, the Goal 1
-- headline `combinatory_completeness` sat downstream, and the per-stage audit never re-checks old
-- theorems. The global "no Classical.choice" claim was false for an unknown span. This file makes
-- the claim BUILD-ENFORCED: every headline theorem's exact axiom footprint is pinned with
-- `#guard_msgs`, so any future leak — in new code or old — fails the build.
import CombinatorCalculusPlayground.TagGeneral
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
