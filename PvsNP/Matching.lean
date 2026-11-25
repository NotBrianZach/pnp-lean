/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-!
# Two dimensions are easy, three are not: the colored square

The essay's proposed line of attack restricts bundles to pairs, where exact coverage is
bipartite perfect matching and augmenting paths repair a partial solution.  Adding a third
coordinate ("give each allowed pair a color, require every color exactly once") gives
three-dimensional matching, and the repair argument breaks.

This file formalises the essay's minimal witness for that break, the colored square

```
        y₁    y₂
  x₁   Red   Blue
  x₂   Blue  Red
```

* `no_matching` : the instance has **no** three-dimensional matching.
* `projXY_matching`, `projXZ_matching`, `projYZ_matching` : yet each of the three
  two-dimensional projections **does** have a perfect matching.  So no summary retaining
  only the three pairwise yes/no answers can decide 3DM.
* `det_coeff_eq_zero` : the determinant `r² - b²` has no `rb` term -- the algebraic form
  of the same obstruction.
* `rainbow_det_coeff_ne_zero`, `rainbow_has_matching` : on an instance that *does* have a
  matching, the same coefficient is nonzero.  So the test is not vacuous.

The general-`n` theorem ("the coefficient of `z₁⋯zₙ` in the tagged determinant is a
nonzero polynomial iff a matching exists") is **not** proved here; see `PvsNP/Gaps.lean`.
-/

namespace PvsNP.Matching

/-! ### Three-dimensional matching -/

/-- A three-dimensional matching of an instance `allowed` on `Fin n × Fin n × Fin n`:
bijections `f, g` such that every triple `(i, f i, g i)` is allowed.  Bijectivity is
"each `y` and each `z` used exactly once"; `i` ranges over all of `Fin n`. -/
def HasMatching {n : ℕ} (allowed : Fin n → Fin n → Fin n → Prop) : Prop :=
  ∃ f g : Fin n → Fin n, Function.Bijective f ∧ Function.Bijective g ∧
    ∀ i, allowed i (f i) (g i)

/-- A perfect matching of a two-dimensional (bipartite) instance. -/
def HasMatching₂ {n : ℕ} (allowed : Fin n → Fin n → Prop) : Prop :=
  ∃ f : Fin n → Fin n, Function.Bijective f ∧ ∀ i, allowed i (f i)

/-! ### The colored square -/

/-- The colors of the four cells: `0 = Red`, `1 = Blue`. -/
def col : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => 0

/-- The triple `(i, j, k)` is allowed exactly when `k` is the color of cell `(i, j)`. -/
def allowed (i j k : Fin 2) : Prop := col i j = k

instance : DecidableEq (Fin 2) := inferInstance

instance (i j k : Fin 2) : Decidable (allowed i j k) := inferInstanceAs (Decidable (_ = _))

/-- **The diagonal repeats red and the other pairing repeats blue.**  There is no
three-dimensional matching. -/
theorem no_matching : ¬ HasMatching allowed := by unfold HasMatching; decide

/-! ### …but every two-dimensional projection matches -/

/-- The `x`-`y` projection: some color is available in cell `(i, j)`. -/
def projXY (i j : Fin 2) : Prop := ∃ k, allowed i j k

/-- The `x`-`z` projection: color `k` is available somewhere in row `i`. -/
def projXZ (i k : Fin 2) : Prop := ∃ j, allowed i j k

/-- The `y`-`z` projection: color `k` is available somewhere in column `j`. -/
def projYZ (j k : Fin 2) : Prop := ∃ i, allowed i j k

instance (i j : Fin 2) : Decidable (projXY i j) := inferInstanceAs (Decidable (∃ _, _))
instance (i k : Fin 2) : Decidable (projXZ i k) := inferInstanceAs (Decidable (∃ _, _))
instance (j k : Fin 2) : Decidable (projYZ j k) := inferInstanceAs (Decidable (∃ _, _))

theorem projXY_matching : HasMatching₂ projXY := by unfold HasMatching₂; decide

theorem projXZ_matching : HasMatching₂ projXZ := by unfold HasMatching₂; decide

theorem projYZ_matching : HasMatching₂ projYZ := by unfold HasMatching₂; decide

/--
**No pairwise summary can decide 3DM.**  The colored square passes all three
two-dimensional tests and still has no solution.
-/
theorem pairwise_tests_insufficient :
    HasMatching₂ projXY ∧ HasMatching₂ projXZ ∧ HasMatching₂ projYZ ∧ ¬ HasMatching allowed :=
  ⟨projXY_matching, projXZ_matching, projYZ_matching, no_matching⟩

/-! ### The algebraic form of the obstruction

Put a color variable in each cell and take the determinant.  A solution would show up as a
term using each color exactly once, i.e. as the coefficient of `r¹b¹`.  For the colored
square the determinant is `r² - b²`, which has no such term.

We work in `ℤ[r][b]`: `r = X` in the outer variable, `b = C X` in the inner one, so
"coefficient of `r¹b¹`" is `(·.coeff 1).coeff 1`.
-/

open Polynomial

/-- The color variable `r` (Red). -/
noncomputable def r : Polynomial (Polynomial ℤ) := X

/-- The color variable `b` (Blue). -/
noncomputable def b : Polynomial (Polynomial ℤ) := C X

/-- The color matrix of the colored square. -/
noncomputable def colorMatrix : Matrix (Fin 2) (Fin 2) (Polynomial (Polynomial ℤ)) :=
  Matrix.of fun i j => if col i j = 0 then r else b

theorem colorMatrix_det : colorMatrix.det = r * r - b * b := by
  rw [Matrix.det_fin_two]
  norm_num [colorMatrix, col, r, b]

/-- **The missing `rb` term.**  The determinant of the colored square has no term using
each color exactly once, so the instance has no solution. -/
theorem det_coeff_eq_zero : (colorMatrix.det.coeff 1).coeff 1 = 0 := by
  rw [colorMatrix_det, r, b, ← sq, ← sq, coeff_sub, ← C_pow, coeff_C, coeff_X_pow]
  simp

/-! ### A contrasting instance that does have a solution -/

/-- Only the two diagonal triples are allowed, and they use different colors. -/
def rainbow (i j k : Fin 2) : Prop := i = j ∧ i = k

instance (i j k : Fin 2) : Decidable (rainbow i j k) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem rainbow_has_matching : HasMatching rainbow := by unfold HasMatching; decide

/-- The matrix of the contrasting instance: `r` and `b` on the diagonal. -/
noncomputable def rainbowMatrix : Matrix (Fin 2) (Fin 2) (Polynomial (Polynomial ℤ)) :=
  Matrix.of fun i j => if i = j then (if i = 0 then r else b) else 0

theorem rainbowMatrix_det : rainbowMatrix.det = r * b := by
  rw [Matrix.det_fin_two]
  norm_num [rainbowMatrix]

/-- Here the `rb` coefficient is nonzero, witnessing the solution. -/
theorem rainbow_det_coeff_ne_zero : (rainbowMatrix.det.coeff 1).coeff 1 = 1 := by
  rw [rainbowMatrix_det, r, b, coeff_mul_C]
  simp

end PvsNP.Matching
