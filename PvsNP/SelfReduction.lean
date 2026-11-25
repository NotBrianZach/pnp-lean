/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.ExactCover

/-!
# Search reduces to decision

The essay: *"If we had an efficient decision procedure, we could recover a witness by
trying to delete each bundle in turn and keeping the deletion whenever a cover still
exists.  At the end every surviving bundle is indispensable, so the survivors form a
cover."*

This file formalises that argument.  `prune` is the greedy deletion loop; its only access
to the instance is through the predicate `Admits` -- "does some subfamily of this family
cover?" -- which is exactly one decision query per step.  `search_from_decision` proves
that what survives is itself an exact cover.

What is proved: **correctness** of the self-reduction, and that it uses one decision query
per bundle.  What is *not* proved: that each query is answerable in polynomial time (that
is the hypothesis `P = NP`), nor a formal cost model for `prune`.  The count of queries is
visible in the definition rather than stated as a theorem.
-/

namespace PvsNP.SelfReduction

open PvsNP.ExactCover

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {β : Type*} [DecidableEq β]

/-- `Admits B J` : some subfamily of `J` is an exact cover.  This is the single
yes/no question the loop is allowed to ask. -/
def Admits (B : β → Finset ι) (J : Finset β) : Prop :=
  ∃ J' ∈ J.powerset, IsExactCover B J'

instance (B : β → Finset ι) (J : Finset β) : Decidable (Admits B J) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

omit [Fintype ι] [DecidableEq β] in
theorem Admits.mono {B : β → Finset ι} {J K : Finset β} (hA : Admits B J) (h : J ⊆ K) :
    Admits B K := by
  obtain ⟨J', hmem, hcov⟩ := hA
  exact ⟨J', Finset.mem_powerset.2 ((Finset.mem_powerset.1 hmem).trans h), hcov⟩

/-- The greedy deletion loop: walk down the list of bundles, dropping each one whenever a
cover still exists without it. -/
def prune (B : β → Finset ι) : List β → Finset β → Finset β
  | [], J => J
  | j :: l, J => if Admits B (J.erase j) then prune B l (J.erase j) else prune B l J

theorem prune_nil (B : β → Finset ι) (J : Finset β) : prune B [] J = J := rfl

theorem prune_cons (B : β → Finset ι) (j : β) (l : List β) (J : Finset β) :
    prune B (j :: l) J =
      if Admits B (J.erase j) then prune B l (J.erase j) else prune B l J := rfl

/-- Pruning only removes bundles. -/
theorem prune_subset (B : β → Finset ι) : ∀ (l : List β) (J : Finset β), prune B l J ⊆ J := by
  intro l
  induction l with
  | nil => intro J; exact Finset.Subset.refl J
  | cons a l ih =>
    intro J
    rw [prune_cons]
    by_cases h : Admits B (J.erase a)
    · rw [ite_eq_left h]
      exact (ih (J.erase a)).trans (Finset.erase_subset a J)
    · rw [ite_eq_right h]
      exact ih J

/-- Pruning preserves solvability: that is the loop invariant. -/
theorem prune_admits (B : β → Finset ι) :
    ∀ (l : List β) (J : Finset β), Admits B J → Admits B (prune B l J) := by
  intro l
  induction l with
  | nil => intro J hJ; exact hJ
  | cons a l ih =>
    intro J hJ
    rw [prune_cons]
    by_cases h : Admits B (J.erase a)
    · rw [ite_eq_left h]; exact ih (J.erase a) h
    · rw [ite_eq_right h]; exact ih J hJ

/-- Every bundle the loop considered and kept is indispensable. -/
theorem prune_indispensable (B : β → Finset ι) :
    ∀ (l : List β) (J : Finset β), Admits B J → ∀ j ∈ l, j ∈ prune B l J →
      ¬ Admits B ((prune B l J).erase j) := by
  intro l
  induction l with
  | nil => intro J _ j hj; simp at hj
  | cons a l ih =>
    intro J hJ j hjl hjmem hadm
    rw [prune_cons] at hjmem hadm
    by_cases h : Admits B (J.erase a)
    · rw [ite_eq_left h] at hjmem hadm
      rcases List.mem_cons.1 hjl with rfl | hj
      · exact (Finset.notMem_erase j J) (prune_subset B l (J.erase j) hjmem)
      · exact ih (J.erase a) h j hj hjmem hadm
    · rw [ite_eq_right h] at hjmem hadm
      rcases List.mem_cons.1 hjl with rfl | hj
      · exact h (hadm.mono (Finset.erase_subset_erase j (prune_subset B l J)))
      · exact ih J hJ j hj hjmem hadm

/--
**The survivors form a cover.**  If the loop sees every bundle of a solvable family, what
it returns is an exact cover, not merely a family that contains one.
-/
theorem prune_isExactCover (B : β → Finset ι) (l : List β) (J : Finset β)
    (hall : ∀ j ∈ J, j ∈ l) (h : Admits B J) : IsExactCover B (prune B l J) := by
  obtain ⟨J', hJ'mem, hJ'cov⟩ := prune_admits B l J h
  have hsub : J' ⊆ prune B l J := Finset.mem_powerset.1 hJ'mem
  have hsup : prune B l J ⊆ J' := by
    intro j hj
    by_contra hjn
    have h1 : J' ⊆ (prune B l J).erase j := Finset.subset_erase.2 ⟨hsub, hjn⟩
    exact prune_indispensable B l J h j (hall j (prune_subset B l J hj)) hj
      ⟨J', Finset.mem_powerset.2 h1, hJ'cov⟩
  rw [Finset.Subset.antisymm hsup hsub]
  exact hJ'cov

/-- The self-reduction, run over all bundles: a decision oracle for "is this family
solvable?" yields an actual cover. -/
theorem search_from_decision [Fintype β] (B : β → Finset ι) (J : Finset β)
    (h : Admits B J) : IsExactCover B (prune B Finset.univ.toList J) :=
  prune_isExactCover B _ J (fun j _ => Finset.mem_toList.2 (Finset.mem_univ j)) h

end PvsNP.SelfReduction
