/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.Conjecture

/-!
# Mechanical audit

Every `#guard_msgs` block below makes the build **fail** if the axiom dependencies of the
named theorem change.  So this file is a machine-checked version of the claim "these
results are complete proofs, and the conjecture is not".

* The results listed first depend only on `propext`, `Classical.choice` and `Quot.sound`
  -- the standard axioms of Lean's logic.  In particular they do not depend on `sorryAx`,
  so they contain no holes.
* `P_ne_NP` and `P_eq_NP` do depend on `sorryAx`.  That is asserted here too, so nobody
  can quietly discharge the `sorry` and have the audit still pass unnoticed, and nobody
  can mistake the file for a proof.
-/

/-! ### Complete proofs -/

/-- info: 'PvsNP.Inventory.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Inventory.encode_injective

/-- info: 'PvsNP.Inventory.structural_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Inventory.structural_lower_bound

/-- info: 'PvsNP.Inventory.toPNatHom_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Inventory.toPNatHom_injective

/-- info: 'PvsNP.Inventory.invMap_not_injective_of_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Inventory.invMap_not_injective_of_idempotent

/-- info: 'PvsNP.ExactCover.prod_eq_target_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.ExactCover.prod_eq_target_iff

/-- info: 'PvsNP.ExactCover.Example.unique_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.ExactCover.Example.unique_solution

/-- info: 'PvsNP.Matching.pairwise_tests_insufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Matching.pairwise_tests_insufficient

/-- info: 'PvsNP.Matching.det_coeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Matching.det_coeff_eq_zero

/-- info: 'PvsNP.Matching.rainbow_det_coeff_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Matching.rainbow_det_coeff_ne_zero

/-- info: 'PvsNP.SelfReduction.search_from_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.SelfReduction.search_from_decision

/-- info: 'PvsNP.Complexity.InP.inNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.InP.inNP

/-- info: 'PvsNP.Complexity.inP_const_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.inP_const_true

/-- info: 'PvsNP.Complexity.inP_const_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.inP_const_false

/-- info: 'PvsNP.Complexity.peqNP_iff_not_pneNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.peqNP_iff_not_pneNP

/-! ### The gap -/

/-- info: 'PvsNP.Unproved.P_ne_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Unproved.P_ne_NP

/-- info: 'PvsNP.Unproved.P_eq_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Unproved.P_eq_NP

/-! ### The general determinant criterion -/

/-- info: 'PvsNP.Determinant.coeff_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Determinant.coeff_det

/-- info: 'PvsNP.Determinant.colorCoeff_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Determinant.colorCoeff_ne_zero_iff

/-- info: 'PvsNP.Determinant.coeff_det_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Determinant.coeff_det_ne_zero_iff

/-- info: 'PvsNP.Determinant.ColoredSquare.coeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Determinant.ColoredSquare.coeff_eq_zero

/-! ### Machines are finite data; the classes are proper -/

/-- info: 'PvsNP.Complexity.instCountableNTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.instCountableNTM

/-- info: 'PvsNP.Complexity.uncountable_lang' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.uncountable_lang

/-- info: 'PvsNP.Complexity.countable_inNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.countable_inNP

/-- info: 'PvsNP.Complexity.exists_not_inNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.exists_not_inNP

/-- info: 'PvsNP.Complexity.exists_not_inP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.exists_not_inP

/-! ### Oracle machinery -/

/-- info: 'PvsNP.Relativization.OTM.isPath_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.isPath_congr

/-- info: 'PvsNP.Relativization.OTM.exists_unqueried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.exists_unqueried

/-- info: 'PvsNP.Relativization.OTM.accepts_of_isPath_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.accepts_of_isPath_congr

/-- info: 'PvsNP.Relativization.instCountableOTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.instCountableOTM

/-- info: 'PvsNP.Relativization.InPRel.inNPRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.InPRel.inNPRel
