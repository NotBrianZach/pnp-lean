/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.Complexity
import PvsNP.Enumeration
import PvsNP.Oracle
import PvsNP.ExactCover
import PvsNP.Inventory
import PvsNP.Matching
import PvsNP.Determinant
import PvsNP.SelfReduction

/-!
# The conjecture, and an honest account of the gap

This file states `P ≠ NP` in the model of `PvsNP/Complexity.lean` and **does not prove
it**.  The one `sorry` in this development is here, and `PvsNP/Audit.lean` asserts
mechanically that it is the only one.

## What the surrounding files actually establish

Everything below is proved, with no `sorry` and no axioms beyond `propext`,
`Classical.choice`, `Quot.sound`:

* Distinguishable independent primitives contain `(ℕ₊, ×)`:
  `Inventory.structural_lower_bound`, `Inventory.toPNatHom_injective`
* The prime encoding of inventories is multiplicative and injective:
  `Inventory.encode_add`, `Inventory.encode_injective`
* Idempotent primitives collapse the counts `1` and `2`:
  `Inventory.invMap_not_injective_of_idempotent`
* Inventories forget the order of composition:
  `Inventory.comp_ne`, `Inventory.same_inventory`
* `∏_{j∈J} b_j = T` iff `J` is an exact cover: `ExactCover.prod_eq_target_iff`
* The `{6,10,15,35}` instance has the unique solution `{A, D}`:
  `ExactCover.Example.unique_solution`
* Deletion-based search reduces to decision: `SelfReduction.search_from_decision`
* The colored square beats every pairwise summary:
  `Matching.pairwise_tests_insufficient`
* …and its determinant has no `rb` term: `Matching.det_coeff_eq_zero`
* The tagged determinant decides 3DM for every `n`: `Determinant.coeff_det`,
  `Determinant.colorCoeff_ne_zero_iff`, `Determinant.coeff_det_ne_zero_iff`
* `P ⊆ NP`: `Complexity.InP.inNP`
* A machine is finite data, so `P` and `NP` are countable and therefore proper:
  `Complexity.instCountableNTM`, `Complexity.countable_inNP`,
  `Complexity.exists_not_inNP`, `Complexity.exists_not_inP`
* Oracle sensitivity and the pigeonhole -- the two lemmas every relativization argument
  runs on: `Relativization.OTM.Run.congr`, `Relativization.exists_unqueried`
* The Baker-Gill-Solovay test language is in `NPᴮ`: `Relativization.bgsLang_inNPRel`
* A single diagonalisation stage: `Relativization.OTM.not_accepts_congr`,
  `Relativization.exists_flip`, `Relativization.exists_enumeration`

## What is *not* established, and why each gap is real

1. **NP-completeness of the arithmetic Exact Cover problem.**  `prod_eq_target_iff` proves
   the reduction maps solutions to solutions.  It says nothing about *cost*.  To get
   NP-completeness one must also encode instances as bit strings, exhibit a machine that
   computes the first `n` primes and their products within a polynomial bound, and build a
   reduction from a known NP-complete language.  None of that is here.  The essay's
   remark that `T` has `O(n log n)` bits is the right observation, but a bit count is not
   a machine.

2. **The cost of the tagged-determinant criterion.**  The criterion itself *is* now proved
   for every `n`, in `PvsNP/Determinant.lean`: `Determinant.coeff_det` computes the
   coefficient of `z₁⋯zₙ` exactly, as a signed sum of tag monomials over solutions, and
   `Determinant.coeff_det_ne_zero_iff` turns that into the iff.  What remains unproved --
   and is the whole difficulty -- is any *cost* claim about extracting that coefficient.
   The criterion is a restatement of the hard problem, not a reduction of it: the essay's
   inclusion-exclusion needs `2ⁿ` evaluations, and compressing those is precisely the open
   question.  Note also that the algebrization barrier below applies directly to this
   route, since it is exactly an algebraic reformulation.

3. **`P ≠ NP` itself.**  The gap is not a missing lemma.  Three known barriers say that no
   argument of the kinds sketched in the essay can close it:

   * **Relativization** (Baker-Gill-Solovay 1975).  There are oracles `A`, `B` with
     `Pᴬ = NPᴬ` and `Pᴮ ≠ NPᴮ`.  Any argument that would survive adding an oracle --
     including counting arguments about the number of candidate compositions, and
     anything that treats the machine as a black box -- cannot settle the question.  The
     essay's observation that the search space is enormous is of exactly this kind, which
     is why ordinary matching is the right cautionary example.

   * **Natural proofs** (Razborov-Rudich 1997).  If strong pseudorandom functions exist,
     no "natural" combinatorial property -- one that is checkable in exponential time and
     shared by a large fraction of all functions -- can separate `P` from `NP`.  Lower
     bounds obtained by showing "random-looking functions are hard, and SAT looks random"
     fall under this.

   * **Algebrization** (Aaronson-Wigderson 2008).  Techniques that survive extending
     oracles to low-degree polynomials over a field -- which includes the determinant and
     polynomial-identity machinery used above -- cannot separate `P` from `NP` either.
     This bears directly on item 2: the tagged determinant is an algebraic reformulation,
     and algebrization is the statement that reformulating algebraically is not enough.

   The essay already anticipates the shape of the problem in its own terms: ruling out one
   class of summaries or circuits gives a lower bound for that class, and monotone circuit
   lower bounds hold even for problems that are in `P`.  That is the correct reading.

## What would count as progress here

A formalization project on this material could, without solving anything open:

* finish item 1 (an encoding plus a cost model, giving a formal NP-completeness theorem);
* formalize the Baker-Gill-Solovay oracle separation, which is a self-contained
  diagonalization and would make the relativization barrier a theorem rather than a
  citation.  `PvsNP/Oracle.lean` now has the model, the enumerability
  (`Relativization.instCountableOTM`), the two working lemmas -- oracle sensitivity
  (`Run.congr`) and the pigeonhole (`exists_unqueried`) -- the test language's membership
  in `NPᴮ` (`bgsLang_inNPRel`), and a single diagonalisation stage (`exists_flip`, built on
  `not_accepts_congr`).  Still missing: the recursion that runs the stages, with lengths
  chosen so each stage's queries stay below everything later stages touch; and -- for the
  `Pᴬ = NPᴬ` half -- enough `PSPACE` theory to know that a `PSPACE`-complete oracle
  collapses the two classes;
* formalize Razborov's monotone lower bound for clique, which is a real lower bound
  against a real circuit class.

None of these implies `P ≠ NP`.  That is the point of listing them.
-/

namespace PvsNP

open Complexity

namespace Unproved

/--
**NOT PROVED.**  This is the Clay problem, stated in the model of
`PvsNP/Complexity.lean`: there is a language accepted by a nondeterministic machine in
polynomial time that no deterministic machine accepts in polynomial time.

The proof is `sorry`.  Nothing else in this development depends on it, and
`PvsNP/Audit.lean` checks mechanically that this is the only incomplete proof here.  Do
not use this lemma.
-/
theorem P_ne_NP : PneNP := by
  sorry

/--
**NOT PROVED.**  The opposite resolution, stated for completeness.  `peqNP_iff_not_pneNP`
shows the two are negations of one another, so at most one of these two `sorry`s can ever
be discharged.
-/
theorem P_eq_NP : PeqNP := by
  sorry

end Unproved

end PvsNP
