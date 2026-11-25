/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.Complexity
import Mathlib.Basic.Denumerable
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Function.Basic

/-!
# Machines are finite data, so `P` and `NP` are countable

A machine in `PvsNP/Complexity.lean` is a triple `(size, start, step)` with `step` a
finite table.  So `NTM` is a countable type (`instCountableNTM`), and therefore only
countably many languages can be in `NP`.  Since there are uncountably many languages, some
language is outside `NP` -- and hence outside `P`.

Main results:

* `instCountableNTM` : `Countable NTM`.
* `countable_inNP`, `countable_inP` : the two classes are countable sets of languages.
* `exists_not_inNP`, `exists_not_inP` : so neither class is all languages.

Together with `inP_const_true` and `inP_const_false` this pins the classes down from both
sides: they are nonempty and proper.

## Why this matters beyond a sanity check

Every diagonalisation argument in complexity theory -- the time hierarchy theorem, and the
Baker-Gill-Solovay oracle separation that underwrites the relativization barrier in
`PvsNP/Conjecture.lean` -- begins by enumerating machines.  That is only possible if a
machine is finite data.  `instCountableNTM` is the statement that this model supports such
an enumeration; the diagonalisations themselves are not formalised here.
-/

namespace PvsNP.Complexity

open Turing

/-! ### The action type is finite -/

/-- A tape direction is one of two things. -/
def dirEquiv : Turing.Dir ≃ Bool where
  toFun d := match d with
    | Turing.Dir.left => false
    | Turing.Dir.right => true
  invFun b := match b with
    | false => Turing.Dir.left
    | true => Turing.Dir.right
  left_inv d := by cases d <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype Turing.Dir := Fintype.ofEquiv Bool dirEquiv.symm

/-- A machine action is a direction or a symbol to write. -/
def stmtEquiv : TM0.Stmt Sym ≃ (Turing.Dir ⊕ Sym) where
  toFun s := match s with
    | TM0.Stmt.move d => Sum.inl d
    | TM0.Stmt.write a => Sum.inr a
  invFun s := match s with
    | Sum.inl d => TM0.Stmt.move d
    | Sum.inr a => TM0.Stmt.write a
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

instance : DecidableEq (TM0.Stmt Sym) := stmtEquiv.decidableEq

instance : Fintype (TM0.Stmt Sym) := Fintype.ofEquiv (Turing.Dir ⊕ Sym) stmtEquiv.symm

/-! ### `NTM` is countable -/

/-- The raw data of a machine: the number of states, the start state, and the transition
table. -/
abbrev NTMData := Σ m : ℕ, Fin m × (Fin m → Sym → Finset (Fin m × TM0.Stmt Sym))

/-- Reading off a machine's data loses nothing. -/
def NTM.data (N : NTM) : NTMData := ⟨N.size, N.start, N.step⟩

theorem NTM.data_injective : Function.Injective NTM.data := by
  intro N₁ N₂ h
  obtain ⟨m₁, s₁, f₁⟩ := N₁
  obtain ⟨m₂, s₂, f₂⟩ := N₂
  simp only [NTM.data, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rfl

/-- **A machine is finite data.**  This is what makes the model usable for
diagonalisation. -/
instance instCountableNTM : Countable NTM := NTM.data_injective.countable

/-! ### There are uncountably many languages -/

/-- Cantor: the languages over `{0,1}*` are uncountable. -/
theorem uncountable_lang : Uncountable (List Bool → Bool) := by
  classical
  rw [← not_countable_iff]
  intro hc
  have : Denumerable (List Bool) := Denumerable.ofEncodableOfInfinite _
  obtain ⟨f, hf⟩ := exists_surjective_nat (List Bool → Bool)
  have hsurj : Function.Surjective
      (fun l : List Bool => {x | f (Denumerable.eqv (List Bool) l) x = true} :
        List Bool → Set (List Bool)) := by
    intro s
    obtain ⟨n, hn⟩ := hf (fun x => if x ∈ s then true else false)
    obtain ⟨l, hl⟩ := (Denumerable.eqv (List Bool)).surjective n
    refine ⟨l, ?_⟩
    simp only [hl, hn]
    ext x
    simp
  exact Function.cantor_surjective _ hsurj

/-! ### Consequences -/

open scoped Classical in
/-- The language a machine decides, given its time budget.  Noncomputable only because it
reads a `Prop` as a `Bool`. -/
noncomputable def langOf (p : NTM × ℕ × ℕ) : List Bool → Bool := fun x =>
  if p.1.Accepts (polyBound p.2.1 p.2.2 x.length) x then true else false

theorem exists_langOf {L : List Bool → Bool} (h : InNP L) : ∃ p, L = langOf p := by
  classical
  obtain ⟨N, k, c, hc⟩ := h
  refine ⟨(N, k, c), funext fun x => ?_⟩
  simp only [langOf]
  by_cases hA : N.Accepts (polyBound k c x.length) x
  · rw [ite_eq_left hA]
    exact (hc x).2 hA
  · rw [ite_eq_right hA]
    rcases Bool.eq_false_or_eq_true (L x) with hL | hL
    · exact absurd ((hc x).1 hL) hA
    · exact hL

/-- **`NP` is countable.**  Only countably many languages have a machine at all. -/
theorem countable_inNP : {L : List Bool → Bool | InNP L}.Countable := by
  refine (Set.countable_range langOf).mono fun L hL => ?_
  obtain ⟨p, hp⟩ := exists_langOf hL
  exact ⟨p, hp.symm⟩

/-- `P` is countable, being contained in `NP`. -/
theorem countable_inP : {L : List Bool → Bool | InP L}.Countable :=
  countable_inNP.mono fun _ hL => hL.inNP

/-- **Some language is not in `NP`.**  So `InNP` is not accidentally everything. -/
theorem exists_not_inNP : ∃ L, ¬ InNP L := by
  by_contra h
  have hall : ∀ L, InNP L := by
    intro L
    by_contra hL
    exact h ⟨L, hL⟩
  have huniv : (Set.univ : Set (List Bool → Bool)).Countable := by
    have heq : {L : List Bool → Bool | InNP L} = Set.univ := Set.eq_univ_of_forall hall
    rw [← heq]
    exact countable_inNP
  exact (not_countable_iff.2 uncountable_lang) (Set.countable_univ_iff.mp huniv)

/-- Some language is not in `P`. -/
theorem exists_not_inP : ∃ L, ¬ InP L := by
  obtain ⟨L, hL⟩ := exists_not_inNP
  exact ⟨L, fun hP => hL hP.inNP⟩

end PvsNP.Complexity
