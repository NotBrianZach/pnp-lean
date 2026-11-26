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

/-- info: 'PvsNP.Relativization.OTM.Run.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.Run.congr

/-- info: 'PvsNP.Relativization.exists_unqueried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.exists_unqueried

/-- info: 'PvsNP.Relativization.OTM.accepts_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.accepts_congr

/-- info: 'PvsNP.Relativization.instCountableOTM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.instCountableOTM

/-- info: 'PvsNP.Relativization.InPRel.inNPRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.InPRel.inNPRel

/-! ### The Baker-Gill-Solovay test language is in NP^B -/

/-- info: 'PvsNP.Relativization.bgs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.bgs_run

/-- info: 'PvsNP.Relativization.bgs_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.bgs_inv

/-- info: 'PvsNP.Relativization.bgsLang_inNPRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.bgsLang_inNPRel

/-! ### The diagonalisation step -/

/-- info: 'PvsNP.Relativization.OTM.mem_succs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.mem_succs_iff

/-- info: 'PvsNP.Relativization.OTM.traj_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.traj_congr

/-- info: 'PvsNP.Relativization.OTM.eq_traj_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.eq_traj_of_run

/-- info: 'PvsNP.Relativization.OTM.not_accepts_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.not_accepts_congr

/-- info: 'PvsNP.Relativization.exists_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.exists_flip

/-- info: 'PvsNP.Relativization.exists_enumeration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.exists_enumeration

/-! ### Ingredients for the stage recursion -/

/-- info: 'PvsNP.Relativization.OTM.qlist_init_length_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.OTM.qlist_init_length_bound

/-- info: 'PvsNP.Relativization.poly_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.poly_lt_two_pow

/-- info: 'PvsNP.Relativization.exists_long_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.exists_long_input

/-! ### Baker-Gill-Solovay, separating half -/

/-- info: 'PvsNP.Relativization.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.agree

/-- info: 'PvsNP.Relativization.mem_or_long' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.mem_or_long

/-- info: 'PvsNP.Relativization.not_inPRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.not_inPRel

/-- info: 'PvsNP.Relativization.exists_oracle_pne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Relativization.exists_oracle_pne

/-! ### The rectangle case of the three-dimensional threshold -/

/-- info: 'PvsNP.Determinant.has3DM_rectangle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Determinant.has3DM_rectangle_iff

/-! ### Space-bounded computation -/

/-- info: 'PvsNP.Complexity.NTM.posRun_toRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.NTM.posRun_toRun

/-- info: 'PvsNP.Complexity.NTM.exists_posRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.NTM.exists_posRun

/-- info: 'PvsNP.Complexity.NTM.offset_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.NTM.offset_bounds

/-- info: 'PvsNP.Complexity.acceptsInSpace_of_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvsNP.Complexity.acceptsInSpace_of_accepts
