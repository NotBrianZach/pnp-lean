/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Pi

/-!
# The tagged determinant decides three-dimensional matching

This file proves the general-`n` criterion that `PvsNP/Matching.lean` only exhibits for
`n = 2`.  It is the essay's construction, verbatim:

> For a general instance, build an `n`-by-`n` matrix.  In entry `(i,j)` place the sum of
> `w_e z_k` over allowed triples `e = (i,j,k)`.  Each `z_k` marks a color and each `w_e`
> uniquely tags a triple.  In the determinant, each nonzero expanded term selects one
> triple per row and column.  Distinct selections have different tag monomials, so they
> cannot cancel.  A solution exists precisely when the coefficient of `z_1 ⋯ z_n` is a
> nonzero polynomial in the tags.

We work in `ℤ[w][z]`: `MvPolynomial (Fin n) (MvPolynomial (Tag n) ℤ)`, polynomials in the
colour variables `z` whose coefficients are polynomials in the tag variables `w`.  So
"the coefficient of `z_1 ⋯ z_n`" is literally `coeff (allOnes n)`, an element of the tag
ring.

Main results:

* `coeff_det` : the exact coefficient, as a signed sum of tag monomials over the
  solutions -- one term per (permutation, colour assignment) pair that is allowed and uses
  every colour once.
* `colorCoeff_ne_zero_iff` : that sum is nonzero iff a three-dimensional matching exists.
  This is the non-cancellation step: distinct selections carry distinct tag monomials, so
  the `±1` coefficients cannot destroy each other.
* `coeff_det_ne_zero_iff` : the two combined, which is the criterion as stated.

**This is not progress on `P` vs `NP`.**  The criterion replaces "does a matching exist?"
with "is this coefficient nonzero?", and extracting the coefficient is itself the hard
step; the essay says so, and the algebrization barrier
(`PvsNP/Conjecture.lean`) says that reformulating algebraically cannot be enough.
-/

namespace PvsNP.Determinant

open MvPolynomial Finset Equiv

variable {n : ℕ}

/-- A triple `(row, column, colour)`, which gets its own tag variable. -/
abbrev Tag (n : ℕ) := Fin n × Fin n × Fin n

/-! ### Two general lemmas -/

/-- A product of distinct variables is the obvious monomial. -/
theorem prod_X_eq_monomial {ι α : Type*} {R : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → α) :
    ∏ i ∈ s, (X (f i) : MvPolynomial α R) = monomial (∑ i ∈ s, Finsupp.single (f i) 1) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
      show (X (f a) : MvPolynomial α R) = monomial (Finsupp.single (f a) 1) 1 by
        rw [← X_pow_eq_monomial, pow_one],
      monomial_mul_monomial, one_mul]

/-- The exponent vector of `z_1 ⋯ z_n`. -/
noncomputable def allOnes (n : ℕ) : Fin n →₀ ℕ := ∑ k, Finsupp.single k 1

@[simp] theorem allOnes_apply (k : Fin n) : allOnes n k = 1 := by
  simp [allOnes, Finset.sum_apply', Finsupp.single_apply]

theorem sum_single_apply (g : Fin n → Fin n) (k : Fin n) :
    (∑ i, Finsupp.single (g i) 1) k = (Finset.univ.filter fun i => g i = k).card := by
  rw [Finset.sum_apply', Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => by simp [Finsupp.single_apply]

/-- A colour assignment uses every colour exactly once iff it is a bijection.  This is why
the coefficient of `z_1 ⋯ z_n`, rather than of some other monomial, is the right thing to
look at. -/
theorem sum_single_eq_allOnes_iff (g : Fin n → Fin n) :
    (∑ i, Finsupp.single (g i) 1) = allOnes n ↔ Function.Bijective g := by
  rw [Function.bijective_iff_existsUnique]
  constructor
  · intro h k
    have hc : (Finset.univ.filter fun i => g i = k).card = 1 := by
      rw [← sum_single_apply g k, h, allOnes_apply]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    refine ⟨a, ?_, ?_⟩
    · have hmem : a ∈ Finset.univ.filter fun i => g i = k := by
        rw [ha]; exact Finset.mem_singleton_self a
      simpa using hmem
    · intro y hy
      have hmem : y ∈ Finset.univ.filter fun i => g i = k := by simp [hy]
      rw [ha, Finset.mem_singleton] at hmem
      exact hmem
  · intro h
    refine Finsupp.ext fun k => ?_
    rw [sum_single_apply, allOnes_apply]
    obtain ⟨a, ha, hu⟩ := h k
    rw [show (Finset.univ.filter fun i => g i = k) = {a} by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hi => hu i hi, fun hi => by rw [hi]; exact ha⟩]
    simp

/-! ### The instance, the matrix, and the claim -/

/-- A three-dimensional matching instance: `A i j` is the set of colours allowed in cell
`(i, j)`. -/
abbrev Instance (n : ℕ) := Fin n → Fin n → Finset (Fin n)

/-- A three-dimensional matching: a permutation choosing one cell per row and column, and
a bijection assigning an allowed colour to each, so that every colour is used once. -/
def Has3DM (A : Instance n) : Prop :=
  ∃ (f g : Fin n → Fin n), Function.Bijective f ∧ Function.Bijective g ∧
    ∀ i, g i ∈ A i (f i)

/-- The tagged colour matrix: entry `(i, j)` is `∑_{k allowed} w_{ijk} z_k`. -/
noncomputable def mat (A : Instance n) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) (MvPolynomial (Tag n) ℤ)) :=
  Matrix.of fun i j => ∑ k ∈ A i j, C (X (i, j, k)) * X k

/-- The tag monomial of a selection: one tag variable per chosen triple. -/
noncomputable def tagExp (σ : Perm (Fin n)) (g : Fin n → Fin n) : Tag n →₀ ℕ :=
  ∑ i, Finsupp.single (i, σ i, g i) 1

/-- The colour assignments that are allowed for `σ` and use every colour once. -/
noncomputable def goodSel (A : Instance n) (σ : Perm (Fin n)) : Finset (Fin n → Fin n) :=
  (Fintype.piFinset fun i => A i (σ i)).filter fun g => Function.Bijective g

/-- The signed sum of tag monomials over all solutions.  `coeff_det` identifies this with
the coefficient of `z_1 ⋯ z_n` in the determinant. -/
noncomputable def colorCoeff (A : Instance n) : MvPolynomial (Tag n) ℤ :=
  ∑ σ : Perm (Fin n), ∑ g ∈ goodSel A σ, monomial (tagExp σ g) ((Equiv.Perm.sign σ : ℤ))

/-! ### The coefficient of `z_1 ⋯ z_n` -/

theorem coeff_prod (A : Instance n) (σ : Perm (Fin n)) :
    (∏ i, (mat A) i (σ i)).coeff (allOnes n)
      = ∑ g ∈ goodSel A σ, monomial (tagExp σ g) (1 : ℤ) := by
  have hexp : (∏ i, (mat A) i (σ i))
      = ∑ g ∈ Fintype.piFinset (fun i => A i (σ i)), ∏ i, (C (X (i, σ i, g i)) * X (g i)) :=
    Finset.prod_univ_sum _ _
  rw [hexp, coeff_sum]
  simp only [goodSel]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, prod_X_eq_monomial, prod_X_eq_monomial,
    coeff_C_mul, coeff_monomial]
  by_cases hb : Function.Bijective g
  · rw [ite_eq_left ((sum_single_eq_allOnes_iff g).2 hb), ite_eq_left hb, mul_one]
    rfl
  · rw [ite_eq_right (fun h => hb ((sum_single_eq_allOnes_iff g).1 h)), ite_eq_right hb,
      mul_zero]

/--
**The coefficient, exactly.**  Expanding the determinant, every surviving term is a
solution: a permutation `σ` together with a bijective allowed colour assignment.  Each
contributes its tag monomial with the sign of `σ`.
-/
theorem coeff_det (A : Instance n) :
    ((mat A).det).coeff (allOnes n) = colorCoeff A := by
  rw [← Matrix.det_transpose (mat A), Matrix.det_apply', coeff_sum]
  simp only [colorCoeff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hT : (∏ i, (mat A).transpose (σ i) i) = ∏ i, (mat A) i (σ i) := rfl
  rw [hT, ← map_intCast (C : MvPolynomial (Tag n) ℤ →+*
      MvPolynomial (Fin n) (MvPolynomial (Tag n) ℤ)) ((Equiv.Perm.sign σ : ℤ)),
    coeff_C_mul, coeff_prod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← map_intCast (C : ℤ →+* MvPolynomial (Tag n) ℤ) ((Equiv.Perm.sign σ : ℤ)),
    C_mul_monomial, mul_one, Int.cast_id]

/-! ### Non-cancellation

Distinct selections carry distinct tag monomials.  This is the whole point of the tags,
and it is why the signs cannot cause cancellation.
-/

theorem tagExp_apply (σ : Perm (Fin n)) (g : Fin n → Fin n) (i₀ j₀ k₀ : Fin n) :
    tagExp σ g (i₀, j₀, k₀) = if σ i₀ = j₀ ∧ g i₀ = k₀ then 1 else 0 := by
  simp only [tagExp]
  rw [Finset.sum_apply', Finset.sum_eq_single i₀]
  · simp [Finsupp.single_apply, Prod.ext_iff]
  · intro i _ hi
    simp [Prod.ext_iff, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- The tag monomial determines the selection. -/
theorem tagExp_injective {σ σ' : Perm (Fin n)} {g g' : Fin n → Fin n}
    (h : tagExp σ g = tagExp σ' g') : σ = σ' ∧ g = g' := by
  have key : ∀ i, σ i = σ' i ∧ g i = g' i := by
    intro i
    by_cases hc : σ i = σ' i ∧ g i = g' i
    · exact hc
    · have h1 : tagExp σ g (i, σ' i, g' i) = tagExp σ' g' (i, σ' i, g' i) := by rw [h]
      rw [tagExp_apply, tagExp_apply, ite_eq_right hc,
        ite_eq_left (show σ' i = σ' i ∧ g' i = g' i from ⟨rfl, rfl⟩)] at h1
      exact absurd h1 (by norm_num)
  exact ⟨Equiv.ext fun i => (key i).1, funext fun i => (key i).2⟩

/--
**Non-cancellation.**  The signed sum is nonzero exactly when there is something to sum
over.  Because each selection has its own tag monomial, no two terms can interfere.
-/
theorem colorCoeff_ne_zero_iff (A : Instance n) : colorCoeff A ≠ 0 ↔ Has3DM A := by
  constructor
  · intro h
    by_contra hno
    apply h
    simp only [colorCoeff]
    refine Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun g hg => ?_
    simp only [goodSel, Finset.mem_filter, Fintype.mem_piFinset] at hg
    exact absurd ⟨σ, g, σ.bijective, hg.2, hg.1⟩ hno
  · rintro ⟨f, g, hf, hg, hallow⟩
    -- turn the bijection `f` into a permutation
    set σ : Perm (Fin n) := Equiv.ofBijective f hf with hσ
    have hσa : ∀ i, σ i = f i := fun i => Equiv.ofBijective_apply f hf i
    have hmem : g ∈ goodSel A σ := by
      simp only [goodSel, Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun i => by rw [hσa i]; exact hallow i, hg⟩
    -- the coefficient of this selection's own tag monomial is the sign of `σ`
    have hco : (colorCoeff A).coeff (tagExp σ g) = ((Equiv.Perm.sign σ : ℤ)) := by
      simp only [colorCoeff, coeff_sum]
      rw [Finset.sum_eq_single σ]
      · rw [Finset.sum_eq_single g]
        · rw [coeff_monomial, ite_eq_left rfl]
        · intro g' _ hne
          rw [coeff_monomial]
          exact ite_eq_right fun hEq => hne (tagExp_injective hEq).2
        · intro hng; exact absurd hmem hng
      · intro σ' _ hne
        refine Finset.sum_eq_zero fun g' _ => ?_
        rw [coeff_monomial]
        exact ite_eq_right fun hEq => hne (tagExp_injective hEq).1
      · intro hnu; exact absurd (Finset.mem_univ σ) hnu
    intro hzero
    rw [hzero] at hco
    have h0 : ((0 : MvPolynomial (Tag n) ℤ)).coeff (tagExp σ g) = 0 := by simp
    rw [h0] at hco
    exact Units.ne_zero _ hco.symm

/--
**The criterion.**  A three-dimensional matching exists precisely when the coefficient of
`z_1 ⋯ z_n` in the tagged determinant is a nonzero polynomial in the tags.
-/
theorem coeff_det_ne_zero_iff (A : Instance n) :
    ((mat A).det).coeff (allOnes n) ≠ 0 ↔ Has3DM A := by
  rw [coeff_det]
  exact colorCoeff_ne_zero_iff A

/-! ### Consistency with the worked example

The colored square of `PvsNP/Matching.lean`, fed to the general criterion.  There, the
`rb` coefficient of `r² - b²` was computed by hand to be zero; here the same conclusion
comes out of `coeff_det_ne_zero_iff` and a decision procedure on the instance.
-/

namespace ColoredSquare

/-- Cell colours: red on the diagonal, blue off it. -/
def col : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => 0

/-- Each cell admits exactly its own colour. -/
def inst : Instance 2 := fun i j => {col i j}

theorem not_has3DM : ¬ Has3DM inst := by unfold Has3DM; decide

/-- The coefficient of `z₁z₂` in the tagged determinant vanishes, as computed by hand for
`r² - b²` in `PvsNP/Matching.lean`. -/
theorem coeff_eq_zero : ((mat inst).det).coeff (allOnes 2) = 0 := by
  by_contra h
  exact not_has3DM ((coeff_det_ne_zero_iff inst).1 h)

end ColoredSquare

end PvsNP.Determinant
