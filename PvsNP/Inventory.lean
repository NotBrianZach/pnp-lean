/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.PNat.Basic

/-!
# Arithmetic inventories

This file formalises the "provable core" of the essay: the claim that a system of
composition which keeps independent primitives distinguishable, together with their
multiplicities, necessarily contains the positive integers under multiplication.

An *inventory* over a set `S` of primitive kinds is a finitely supported function
`u : S →₀ ℕ` recording how many copies of each kind are used.  Inventories compose by
addition, so `S →₀ ℕ` is the free commutative monoid on `S` (written additively).

The main results:

* `encode_add`, `encode_zero` : the prime encoding `E u = ∏ p a ^ u a` is a monoid
  homomorphism from inventories (under `+`) to `ℕ` (under `*`).
* `factorization_encode` : the exponent of `p a` in `E u` is exactly `u a`.
* `encode_injective` : distinct inventories get distinct codes (unique factorization).
* `structural_lower_bound` : the conditional lower bound stated in the essay.
* `toPNatHom_injective` : the same statement packaged as an injective monoid
  homomorphism `ℕ+ →* M`, i.e. "`M` contains a copy of the positive integers under
  multiplication".
* `invMap_not_injective_of_idempotent` : the hypothesis is not free.  If two copies of a
  primitive mean the same as one, then the counts `1` and `2` already collapse and no such
  embedding is obtained this way.

Nothing in this file says anything about computational complexity.  That is the point:
the inventory argument is a statement about *structure*, and it is logically independent
of the running time of any search problem.  See `PvsNP/Gaps.lean`.
-/

namespace PvsNP.Inventory

open Finsupp

/-! ### The prime encoding of inventories -/

section Encode

variable {S : Type*} (p : S → ℕ)

/-- The multiplicative code of an inventory: `E u = ∏ a, (p a) ^ u a`. -/
def encode (u : S →₀ ℕ) : ℕ := u.prod fun a k => p a ^ k

@[simp] theorem encode_zero : encode p (0 : S →₀ ℕ) = 1 := by
  simp [encode]

/-- Composing inventories multiplies their codes: `E` is a monoid homomorphism. -/
theorem encode_add (u v : S →₀ ℕ) : encode p (u + v) = encode p u * encode p v := by
  classical
  exact prod_add_index (fun _ _ => pow_zero _) fun _ _ b₁ b₂ => pow_add _ b₁ b₂

theorem encode_ne_zero (hp : ∀ a, (p a).Prime) (u : S →₀ ℕ) : encode p u ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ ?_
  exact (hp a).pos.ne'

/-- Unique factorization, read off one prime at a time: the exponent of `p a` in the code
of `u` is the number of copies of `a` that `u` prescribes. -/
theorem factorization_encode (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u : S →₀ ℕ) (a : S) : (encode p u).factorization (p a) = u a := by
  classical
  rw [encode, Finsupp.prod,
    Nat.factorization_prod fun x _ => pow_ne_zero _ (hp x).pos.ne']
  rw [Finset.sum_apply']
  have key : ∀ x ∈ u.support, ((p x) ^ (u x)).factorization (p a) = if x = a then u x else 0 := by
    intro x _
    rw [(hp x).factorization_pow]
    by_cases h : x = a
    · subst h; simp
    · have hne : p x ≠ p a := fun hh => h (hinj hh)
      simp [h, hne]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' u.support a]
  by_cases h : a ∈ u.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.1 h]

/-- Distinguishability: different inventories of independent primitives have different
codes.  This is exactly unique factorization. -/
theorem encode_injective (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p) :
    Function.Injective (encode p) := by
  intro u v h
  ext a
  rw [← factorization_encode p hp hinj u a, ← factorization_encode p hp hinj v a, h]

end Encode

/-! ### The conditional structural lower bound

We now replace `ℕ` by an arbitrary commutative monoid `M` carrying countably many
primitives `ι : ℕ → M` (the essay's "associative operation for placing components
alongside one another, an empty component, and countably many commuting primitives").
-/

section LowerBound

variable {M : Type*} [CommMonoid M] (ι : ℕ → M)

/-- The result of assembling the inventory `u` out of the primitives `ι`. -/
def invMap (u : ℕ →₀ ℕ) : M := u.prod fun a k => ι a ^ k

@[simp] theorem invMap_zero : invMap ι 0 = 1 := by simp [invMap]

theorem invMap_add (u v : ℕ →₀ ℕ) : invMap ι (u + v) = invMap ι u * invMap ι v :=
  prod_add_index (fun _ _ => pow_zero _) fun _ _ b₁ b₂ => pow_add _ b₁ b₂

/-- Inventories supported on primes.  These are exactly the inventories that arise as
prime factorisations, so this is the only distinguishability we need to assume. -/
def PrimeSupported (u : ℕ →₀ ℕ) : Prop := ∀ q ∈ u.support, Nat.Prime q

theorem primeSupported_factorization (n : ℕ) : PrimeSupported n.factorization :=
  fun _ hq => Nat.prime_of_mem_primeFactors (by simpa using hq)

/-- The assembly of `n`'s prime inventory. -/
def ofNat (n : ℕ) : M := invMap ι n.factorization

@[simp] theorem ofNat_one : ofNat ι 1 = 1 := by simp [ofNat]

theorem ofNat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ofNat ι (m * n) = ofNat ι m * ofNat ι n := by
  rw [ofNat, Nat.factorization_mul hm hn, invMap_add, ofNat, ofNat]

/--
**The structural lower bound.**  Suppose a commutative monoid `M` has countably many
primitives `ι` such that distinct finite inventories of them (supported on the primes)
give distinguishable results.  Then `M` contains a copy of the positive integers under
multiplication: the map `ofNat` is multiplicative and injective on positives.
-/
theorem structural_lower_bound (h : Set.InjOn (invMap ι) {u | PrimeSupported u}) :
    ofNat ι 1 = 1 ∧ (∀ m n : ℕ, m ≠ 0 → n ≠ 0 → ofNat ι (m * n) = ofNat ι m * ofNat ι n) ∧
      Set.InjOn (ofNat ι) {n : ℕ | n ≠ 0} := by
  refine ⟨ofNat_one ι, fun m n hm hn => ofNat_mul ι hm hn, fun m hm n hn hmn => ?_⟩
  exact Nat.factorization_inj hm hn
    (h (primeSupported_factorization m) (primeSupported_factorization n) hmn)

/-- The same conclusion packaged as a monoid homomorphism out of `ℕ+`. -/
def toPNatHom : ℕ+ →* M where
  toFun n := ofNat ι (n : ℕ)
  map_one' := by simp
  map_mul' m n := by
    simpa [PNat.mul_coe] using ofNat_mul ι (m.ne_zero) (n.ne_zero)

/-- "The system contains a copy of the positive integers under multiplication." -/
theorem toPNatHom_injective (h : Set.InjOn (invMap ι) {u | PrimeSupported u}) :
    Function.Injective (toPNatHom ι) := by
  intro m n hmn
  have : ((m : ℕ)) = (n : ℕ) :=
    (structural_lower_bound ι h).2.2 m.ne_zero n.ne_zero hmn
  exact PNat.coe_injective this

end LowerBound

/-! ### The hypothesis is not free

If a primitive is idempotent -- "two copies of a claim mean the same thing as one" -- the
inventories `1` and `2` already collapse, so the distinguishability hypothesis fails and
the embedding is not obtained.
-/

section Idempotent

variable {M : Type*} [CommMonoid M] (ι : ℕ → M)

theorem invMap_not_injective_of_idempotent {a : ℕ} (ha : Nat.Prime a)
    (hidem : ι a * ι a = ι a) : ¬ Set.InjOn (invMap ι) {u | PrimeSupported u} := by
  intro h
  have supp : ∀ k : ℕ, PrimeSupported (Finsupp.single a k) := by
    intro k q hq
    rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hq
    by_cases hqa : a = q
    · exact hqa ▸ ha
    · simp [hqa] at hq
  have e1 : invMap ι (Finsupp.single a 1) = ι a := by
    have : invMap ι (Finsupp.single a 1) = ι a ^ 1 :=
      Finsupp.prod_single_index (pow_zero (ι a))
    rw [this, pow_one]
  have e2 : invMap ι (Finsupp.single a 2) = ι a := by
    have : invMap ι (Finsupp.single a 2) = ι a ^ 2 :=
      Finsupp.prod_single_index (pow_zero (ι a))
    rw [this, pow_two, hidem]
  have hsingle := h (supp 1) (supp 2) (by rw [e1, e2])
  have : (1 : ℕ) = 2 := by
    have := congrArg (fun f => f a) hsingle
    simp at this
  omega

end Idempotent

/-! ### Inventories forget order

Labelling occurrences with primes records *what* was used, never *how* it was combined.
The essay's example: `A x = x + 1` and `B x = 2 * x` have the same inventory in either
order, but the two composites differ. -/

section Order

/-- `A x = x + 1`. -/
def A (x : ℕ) : ℕ := x + 1

/-- `B x = 2 * x`. -/
def B (x : ℕ) : ℕ := 2 * x

theorem comp_ne : B ∘ A ≠ A ∘ B := by
  intro h
  have := congrFun h 0
  simp [A, B] at this

/-- Both orders have the same inventory `2 * 3 = 6`, recorded by the primes `2` and `3`
assigned to the two occurrences. -/
theorem same_inventory : (2 : ℕ) * 3 = 6 ∧ (3 : ℕ) * 2 = 6 := by decide

end Order

end PvsNP.Inventory
