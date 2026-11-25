/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.Inventory

/-!
# The prime-encoding reduction from Exact Cover

The essay encodes an Exact Cover instance arithmetically: observation `i` gets the prime
`p i`, bundle `j` gets the product `b j = ∏_{i ∈ S j} p i`, and the target is
`T = ∏_i p i`.  The claim to be checked is

  `∏_{j ∈ J} b j = T  ↔  every observation lies in exactly one selected bundle`.

`prod_eq_target_iff` is that claim, proved.  This is the *correctness* of the reduction;
it is the part of "Exact Cover is NP-complete" that is pure number theory.  The other part
-- that the encoding is computable in polynomial time, and that the resulting decision
problem is NP-hard -- needs a machine model and is **not** proved here.  See
`PvsNP/Gaps.lean`.

`Example` at the end is the essay's four-bundle instance `{6, 10, 15, 35}` with target
`210`, where the unique solution is checked by decision procedure.
-/

namespace PvsNP.ExactCover

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {β : Type*} [DecidableEq β]

/-- The arithmetic code of a bundle: the product of the primes of the observations it
covers. -/
def code (p : ι → ℕ) (B : β → Finset ι) (j : β) : ℕ := ∏ i ∈ B j, p i

/-- The target: the product of all the observation primes, each to the first power. -/
def target (p : ι → ℕ) : ℕ := ∏ i, p i

/-- `J` is an exact cover: every observation belongs to exactly one selected bundle. -/
def IsExactCover (B : β → Finset ι) (J : Finset β) : Prop :=
  ∀ i : ι, (J.filter fun j => i ∈ B j).card = 1

instance (B : β → Finset ι) (J : Finset β) : Decidable (IsExactCover B J) :=
  inferInstanceAs (Decidable (∀ _, _))

/-! ### Exponent bookkeeping -/

section Exponents

variable {p : ι → ℕ} (hp : ∀ i, (p i).Prime)

include hp

omit [DecidableEq ι] [Fintype ι] in
theorem prod_primes_ne_zero (s : Finset ι) : (∏ i ∈ s, p i) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => (hp i).pos.ne'

omit [DecidableEq ι] [Fintype ι] in
/-- The exponent of a prime `q` in a squarefree product of distinct primes counts the
factors that equal `q`. -/
theorem factorization_prod_primes (s : Finset ι) (q : ℕ) :
    (∏ i ∈ s, p i).factorization q = (s.filter fun i => p i = q).card := by
  rw [Nat.factorization_prod fun i _ => (hp i).pos.ne', Finset.sum_apply', Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hp i).factorization, Finsupp.single_apply]

omit [DecidableEq ι] [Fintype ι] [DecidableEq β] in
theorem factorization_code (B : β → Finset ι) (J : Finset β) (q : ℕ) :
    (∏ j ∈ J, code p B j).factorization q
      = ∑ j ∈ J, ((B j).filter fun i => p i = q).card := by
  simp only [code]
  rw [Nat.factorization_prod fun j _ => prod_primes_ne_zero hp (B j), Finset.sum_apply']
  exact Finset.sum_congr rfl fun j _ => factorization_prod_primes hp (B j) q

variable (hinj : Function.Injective p)
include hinj

omit [Fintype ι] hp in
theorem filter_eq_card (s : Finset ι) (i₀ : ι) :
    (s.filter fun i => p i = p i₀).card = if i₀ ∈ s then 1 else 0 := by
  have h : (s.filter fun i => p i = p i₀) = s.filter fun i => i = i₀ :=
    Finset.filter_congr fun i _ => by
      exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  rw [h, Finset.filter_eq']
  by_cases hi : i₀ ∈ s <;> simp [hi]

omit [DecidableEq ι] [Fintype ι] hp hinj in
/-- Primes outside the image of `p` never occur. -/
theorem filter_eq_empty {q : ℕ} (hq : ∀ i, p i ≠ q) (s : Finset ι) :
    (s.filter fun i => p i = q) = ∅ :=
  Finset.filter_eq_empty_iff.2 fun {i} _ => hq i

end Exponents

/-! ### Correctness of the reduction -/

omit [DecidableEq β] in
/--
**The reduction is correct.**  Selecting bundles whose codes multiply to the target is the
same thing as selecting an exact cover.  Unique factorization does all the work: the
exponent of `p i` on the left counts how many selected bundles contain observation `i`,
and on the right it is `1`.
-/
theorem prod_eq_target_iff {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B : β → Finset ι) (J : Finset β) :
    (∏ j ∈ J, code p B j) = target p ↔ IsExactCover B J := by
  have hL : (∏ j ∈ J, code p B j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => prod_primes_ne_zero hp (B j)
  have hR : target p ≠ 0 := prod_primes_ne_zero hp Finset.univ
  -- the exponent of `p i` on each side
  have key : ∀ i : ι, (∏ j ∈ J, code p B j).factorization (p i)
      = (J.filter fun j => i ∈ B j).card := by
    intro i
    rw [factorization_code hp B J (p i), Finset.card_filter]
    exact Finset.sum_congr rfl fun j _ => filter_eq_card hinj (B j) i
  have keyR : ∀ i : ι, (target p).factorization (p i) = 1 := by
    intro i
    rw [target, factorization_prod_primes hp Finset.univ (p i),
      filter_eq_card hinj Finset.univ i]
    simp
  constructor
  · intro h i
    rw [← key i, h, keyR i]
  · intro h
    refine Nat.factorization_inj hL hR (Finsupp.ext fun q => ?_)
    by_cases hq : ∃ i, p i = q
    · obtain ⟨i, rfl⟩ := hq
      rw [key i, keyR i, h i]
    · have hq' : ∀ i, p i ≠ q := fun i hi => hq ⟨i, hi⟩
      rw [factorization_code hp B J q, target, factorization_prod_primes hp Finset.univ q,
        filter_eq_empty hq' Finset.univ]
      simp [filter_eq_empty hq']

omit [DecidableEq β] in
/--
A selection of bundles is a solution iff its product hits the target.  Stated as the
existence form that a decision procedure would answer.
-/
theorem exists_iff {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B : β → Finset ι) (S : Finset (Finset β)) :
    (∃ J ∈ S, (∏ j ∈ J, code p B j) = target p) ↔ ∃ J ∈ S, IsExactCover B J :=
  ⟨fun ⟨J, hJ, h⟩ => ⟨J, hJ, (prod_eq_target_iff hp hinj B J).1 h⟩,
    fun ⟨J, hJ, h⟩ => ⟨J, hJ, (prod_eq_target_iff hp hinj B J).2 h⟩⟩

/-! ### The essay's worked example

Observations `2, 3, 5, 7`; bundles `A = {2,3} ↦ 6`, `B = {2,5} ↦ 10`, `C = {3,5} ↦ 15`,
`D = {5,7} ↦ 35`; target `210`.  Only `D` covers `7`, so `D` is forced; its `5` rules out
`B` and `C`; `A` supplies the rest.
-/

namespace Example

/-- Observation primes `2, 3, 5, 7`. -/
def p : Fin 4 → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7

/-- Bundles `A, B, C, D` as sets of observations. -/
def B : Fin 4 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {1, 2}
  | 3 => {2, 3}

theorem p_prime : ∀ i, (p i).Prime := by decide

theorem p_injective : Function.Injective p := by decide

theorem codes : code p B 0 = 6 ∧ code p B 1 = 10 ∧ code p B 2 = 15 ∧ code p B 3 = 35 := by
  decide

theorem target_eq : target p = 210 := by decide

/-- The unique selection whose product is the target is `{A, D}`. -/
theorem unique_solution (J : Finset (Fin 4)) :
    (∏ j ∈ J, code p B j) = 210 ↔ J = {0, 3} := by
  revert J; decide

/-- …and it is indeed the unique exact cover. -/
theorem unique_exact_cover (J : Finset (Fin 4)) : IsExactCover B J ↔ J = {0, 3} := by
  revert J; decide

end Example

end PvsNP.ExactCover
