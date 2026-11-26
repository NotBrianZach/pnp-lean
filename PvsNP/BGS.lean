/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.Oracle

/-!
# Baker-Gill-Solovay, the separating half

This file runs the stage construction and proves

  `∃ B, Pᴮ ≠ NPᴮ`  (`exists_oracle_pne`)

so the relativization barrier is a theorem here rather than a citation.  The other half of
Baker-Gill-Solovay, `∃ A, Pᴬ = NPᴬ`, needs `PSPACE` theory and is still not formalized;
see `PvsNP/Conjecture.lean`.

## The construction

`enum` lists every candidate: a machine together with the two numbers fixing its
polynomial budget.  Stage `i` carries a state `St` with a strict upper bound `bnd` on every
length used so far, and the list `ins` of strings committed to the oracle.  At stage `i`:

* pick an input length `len` above `bnd` on which the candidate's whole budget cannot
  exhaust the strings of that length (`exists_long_input`);
* run the candidate on `inp = 0^len` against the oracle built from `ins` alone;
* if it **accepts**, commit nothing -- then no string of length `len` is ever in the oracle,
  so the input is outside `bgsLang` while the machine accepts it;
* if it **rejects**, commit one string of length `len` that the run never consulted
  (`exists_unqueried`) -- then the input is inside `bgsLang`, and by
  `not_accepts_congr` the machine still rejects it;
* either way advance `bnd` past both `len` and the budget, so later stages act strictly
  beyond this stage's reach.

The two facts that make the stages independent are `qlist_init_length_bound` (a `t`-step
run only builds buffers of length at most `t`) and the `bnd` bookkeeping (later stages only
ever commit longer strings).  Together they give `agree`: the final oracle and the stage's
partial oracle agree on everything that stage looked at.
-/

namespace PvsNP.Relativization

open Turing PvsNP.Complexity

open scoped Classical in
/-- A listing of all candidates: machine, exponent, coefficient. -/
noncomputable def enum : ℕ → OTM × ℕ × ℕ := Classical.choose exists_enumeration

theorem enum_surjective : Function.Surjective enum :=
  Classical.choose_spec exists_enumeration

/-- The state carried between stages. -/
structure St where
  /-- Every length used so far is strictly below this. -/
  bnd : ℕ
  /-- The strings committed to the oracle so far. -/
  ins : List (List Bool)

namespace St

/-- The machine at stage `i`. -/
noncomputable def mach (i : ℕ) : OTM := (enum i).1

/-- The input length chosen at stage `i`. -/
noncomputable def len (i : ℕ) (s : St) : ℕ :=
  Classical.choose (exists_long_input (enum i).2.1 (enum i).2.2 s.bnd)

/-- The budget the candidate gets on that input. -/
noncomputable def budget (i : ℕ) (s : St) : ℕ :=
  polyBound (enum i).2.1 (enum i).2.2 (s.len i)

/-- The input used at stage `i`. -/
noncomputable def inp (i : ℕ) (s : St) : List Bool := List.replicate (s.len i) false

@[simp] theorem inp_length (i : ℕ) (s : St) : (s.inp i).length = s.len i := by
  simp [inp]

/-- The oracle built from what has been committed so far. -/
noncomputable def prev (s : St) : Oracle := fun w => decide (w ∈ s.ins)

theorem len_ge (i : ℕ) (s : St) : s.bnd ≤ s.len i :=
  (Classical.choose_spec (exists_long_input (enum i).2.1 (enum i).2.2 s.bnd)).1

theorem budget_lt (i : ℕ) (s : St) : s.budget i + 1 < 2 ^ s.len i :=
  (Classical.choose_spec (exists_long_input (enum i).2.1 (enum i).2.2 s.bnd)).2

/-- The query list of the stage-`i` run. -/
noncomputable def qs (i : ℕ) (s : St) : List (List Bool) :=
  (mach i).qlist s.prev (s.budget i) ((mach i).init (s.inp i))

theorem qs_length_lt (i : ℕ) (s : St) : (s.qs i).length < 2 ^ s.len i :=
  lt_of_le_of_lt ((mach i).qlist_length_le s.prev (s.budget i) _) (s.budget_lt i)

/-- A string of length `len` that the stage-`i` run never consults. -/
noncomputable def pick (i : ℕ) (s : St) : List Bool :=
  Classical.choose (exists_unqueried (s.qs i) (s.len i) (s.qs_length_lt i))

theorem pick_length (i : ℕ) (s : St) : (s.pick i).length = s.len i :=
  (Classical.choose_spec (exists_unqueried (s.qs i) (s.len i) (s.qs_length_lt i))).1

theorem pick_notMem (i : ℕ) (s : St) : s.pick i ∉ s.qs i :=
  (Classical.choose_spec (exists_unqueried (s.qs i) (s.len i) (s.qs_length_lt i))).2

/-- The next bound: strictly past both the length used and the budget spent. -/
noncomputable def nextBnd (i : ℕ) (s : St) : ℕ :=
  max s.bnd (max (s.budget i + 1) (s.len i + 1))

open scoped Classical in
/-- One stage. -/
noncomputable def next (i : ℕ) (s : St) : St :=
  if (mach i).Det ∧ ¬ (mach i).Accepts s.prev (s.budget i) (s.inp i) then
    ⟨s.nextBnd i, s.pick i :: s.ins⟩
  else
    ⟨s.nextBnd i, s.ins⟩

@[simp] theorem next_bnd (i : ℕ) (s : St) : (s.next i).bnd = s.nextBnd i := by
  unfold next; split <;> rfl

theorem mem_next_ins (i : ℕ) (s : St) {w : List Bool} (h : w ∈ (s.next i).ins) :
    w ∈ s.ins ∨ w = s.pick i := by
  unfold next at h
  split at h
  · rcases List.mem_cons.1 h with rfl | h'
    · exact Or.inr rfl
    · exact Or.inl h'
  · exact Or.inl h

theorem ins_sub_next (i : ℕ) (s : St) {w : List Bool} (h : w ∈ s.ins) :
    w ∈ (s.next i).ins := by
  unfold next; split
  · exact List.mem_cons_of_mem _ h
  · exact h

end St

/-- The state after `i` stages. -/
noncomputable def stAt : ℕ → St
  | 0 => ⟨0, []⟩
  | i + 1 => (stAt i).next i

open scoped Classical in
/-- **The oracle the construction builds.** -/
noncomputable def oracle : Oracle := fun w => decide (∃ i, w ∈ (stAt i).ins)

theorem mem_oracle_iff (w : List Bool) : oracle w = true ↔ ∃ i, w ∈ (stAt i).ins := by
  simp only [oracle, decide_eq_true_eq]

/-! ### The invariants -/

theorem bnd_le_succ (i : ℕ) : (stAt i).bnd ≤ (stAt (i + 1)).bnd := by
  change (stAt i).bnd ≤ ((stAt i).next i).bnd
  rw [St.next_bnd]
  exact le_max_left _ _

theorem bnd_mono {i j : ℕ} (h : i ≤ j) : (stAt i).bnd ≤ (stAt j).bnd := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact le_trans (ih (by omega)) (bnd_le_succ j)
    · have : i = j + 1 := by omega
      subst this
      exact le_refl _

theorem ins_mono {i j : ℕ} (h : i ≤ j) {w : List Bool} (hw : w ∈ (stAt i).ins) :
    w ∈ (stAt j).ins := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact hw
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact (stAt j).ins_sub_next j (ih (by omega))
    · have : i = j + 1 := by omega
      subst this; exact hw

/-- Everything committed is shorter than the running bound. -/
theorem length_lt_bnd (i : ℕ) {w : List Bool} (hw : w ∈ (stAt i).ins) :
    w.length < (stAt i).bnd := by
  induction i with
  | zero => simp [stAt] at hw
  | succ i ih =>
    have hb : (stAt (i + 1)).bnd = (stAt i).nextBnd i := by
      change ((stAt i).next i).bnd = _
      rw [St.next_bnd]
    rcases (stAt i).mem_next_ins i hw with h' | rfl
    · have := ih h'
      rw [hb]
      simp only [St.nextBnd]
      omega
    · rw [(stAt i).pick_length i, hb]
      simp only [St.nextBnd]
      omega

/--
**Later stages act beyond earlier reach.**  Anything the oracle ever commits is either
already committed by stage `i`, or longer than stage `i`'s bound.
-/
theorem mem_or_long {i j : ℕ} (h : i ≤ j) {w : List Bool} (hw : w ∈ (stAt j).ins) :
    w ∈ (stAt i).ins ∨ (stAt i).bnd ≤ w.length := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Or.inl hw
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have hij : i ≤ j := by omega
      rcases (stAt j).mem_next_ins j hw with h'' | rfl
      · exact ih hij h''
      · refine Or.inr ?_
        rw [(stAt j).pick_length j]
        exact le_trans (bnd_mono hij) ((stAt j).len_ge j)
    · have : i = j + 1 := by omega
      subst this; exact Or.inl hw

/-! ### The agreement lemma -/

/--
**The final oracle and the stage's partial oracle agree on everything the stage looked
at.**  Strings committed later are too long for the stage's run to have written down, and
the one string committed *at* this stage was chosen unconsulted.
-/
theorem agree (i : ℕ) {w : List Bool} (hw : w ∈ (stAt i).qs i) :
    (stAt i).prev w = oracle w := by
  classical
  have hlen : w.length ≤ (stAt i).budget i :=
    (St.mach i).qlist_init_length_bound (stAt i).prev ((stAt i).budget i) _ w hw
  have hbnd : (stAt i).budget i < (stAt (i + 1)).bnd := by
    have : (stAt (i + 1)).bnd = (stAt i).nextBnd i := by
      change ((stAt i).next i).bnd = _
      rw [St.next_bnd]
    rw [this]
    simp only [St.nextBnd]
    omega
  -- the two memberships are equivalent: anything committed later is too long, and the one
  -- string committed at this stage was chosen unconsulted
  have key : (w ∈ (stAt i).ins) ↔ (∃ j, w ∈ (stAt j).ins) := by
    refine ⟨fun h => ⟨i, h⟩, ?_⟩
    rintro ⟨j, hj⟩
    rcases Nat.lt_or_ge j (i + 1) with hji | hji
    · exact ins_mono (by omega) hj
    · rcases mem_or_long hji hj with h' | h'
      · rcases (stAt i).mem_next_ins i h' with h'' | rfl
        · exact h''
        · exact absurd hw ((stAt i).pick_notMem i)
      · omega
  change decide (w ∈ (stAt i).ins) = decide (∃ j, w ∈ (stAt j).ins)
  exact decide_eq_decide.2 key

/-! ### The separation -/

/--
**`bgsLang oracle` is not in `Pᴬ` for the constructed oracle.**  Every candidate is
defeated at its own stage.
-/
theorem not_inPRel : ¬ InPRel oracle (bgsLang oracle) := by
  rintro ⟨N, k, c, hdet, hiff⟩
  -- the stage that handles this candidate
  obtain ⟨i, hi⟩ := enum_surjective (N, k, c)
  have hmach : St.mach i = N := by rw [St.mach, hi]
  have hk : (enum i).2.1 = k := by rw [hi]
  have hc : (enum i).2.2 = c := by rw [hi]
  have hdet' : (St.mach i).Det := by rw [hmach]; exact hdet
  have hxlen : ((stAt i).inp i).length = (stAt i).len i := St.inp_length i (stAt i)
  have hbud : polyBound k c ((stAt i).len i) = (stAt i).budget i := by
    rw [St.budget, hk, hc]
  have hbnd_le : (stAt i).bnd ≤ (stAt i).len i := (stAt i).len_ge i
  have hnext : (stAt (i + 1)).bnd = (stAt i).nextBnd i := by
    change ((stAt i).next i).bnd = _
    rw [St.next_bnd]
  have hnb : (stAt i).len i < (stAt (i + 1)).bnd := by
    rw [hnext]; simp only [St.nextBnd]; omega
  by_cases hacc : (St.mach i).Accepts (stAt i).prev ((stAt i).budget i) ((stAt i).inp i)
  · -- it accepts, so the input must be in the language; but no string of length `len` is
    -- ever committed
    have hrun : N.Accepts oracle (polyBound k c ((stAt i).inp i).length) ((stAt i).inp i) := by
      obtain ⟨c', qsl, hr, hlenq, hacc'⟩ := hacc
      obtain ⟨h1, h2⟩ := (St.mach i).eq_traj_of_run hdet' hr
      have hsub : ∀ u ∈ qsl, u ∈ (stAt i).qs i := by
        intro u hu
        rw [h2] at hu
        exact (St.mach i).qlist_mono (stAt i).prev (by omega) _ u hu
      rw [hxlen, hbud, ← hmach]
      exact (St.mach i).accepts_congr hr hlenq hacc' fun u hu => agree i (hsub u hu)
    obtain ⟨w, hwlen, hwB⟩ := (bgsLang_eq_true_iff _ _).1 ((hiff _).2 hrun)
    rw [hxlen] at hwlen
    obtain ⟨j, hj⟩ := (mem_oracle_iff w).1 hwB
    -- nothing committed has length `len`
    have hcontra : w.length < (stAt i).bnd ∨ (stAt (i + 1)).bnd ≤ w.length := by
      rcases Nat.lt_or_ge j (i + 1) with hji | hji
      · exact Or.inl (length_lt_bnd i (ins_mono (by omega) hj))
      · rcases mem_or_long hji hj with h' | h'
        · rcases (stAt i).mem_next_ins i h' with h'' | rfl
          · exact Or.inl (length_lt_bnd i h'')
          · -- in this branch stage `i` committed nothing, so `pick` is not in the oracle
            have hne : (stAt (i + 1)).ins = (stAt i).ins := by
              change ((stAt i).next i).ins = _
              unfold St.next
              split
              · rename_i hcon; exact absurd hacc hcon.2
              · rfl
            rw [hne] at h'
            exact Or.inl (length_lt_bnd i h')
        · exact Or.inr h'
    omega
  · -- it rejects, so the input must be outside the language; but we commit a witness it
    -- never looked at
    have hcommit : (stAt i).pick i ∈ (stAt (i + 1)).ins := by
      change (stAt i).pick i ∈ ((stAt i).next i).ins
      unfold St.next
      split
      · exact List.mem_cons_self ..
      · rename_i hcon
        exact absurd ⟨hdet', hacc⟩ hcon
    have hlang : bgsLang oracle ((stAt i).inp i) = true := by
      rw [bgsLang_eq_true_iff]
      refine ⟨(stAt i).pick i, ?_, (mem_oracle_iff _).2 ⟨i + 1, hcommit⟩⟩
      rw [(stAt i).pick_length i, hxlen]
    have hno : ¬ N.Accepts oracle (polyBound k c ((stAt i).inp i).length) ((stAt i).inp i) := by
      rw [hxlen, hbud, ← hmach]
      exact (St.mach i).not_accepts_congr hdet' (fun u hu => agree i hu) hacc
    exact hno ((hiff _).1 hlang)

/--
**Baker-Gill-Solovay, separating half.**  There is an oracle `B` with `Pᴮ ≠ NPᴮ`.  So no
argument that survives the addition of an oracle can prove `P ≠ NP`.
-/
theorem exists_oracle_pne : ∃ B : Oracle, ¬ PeqNPRel B :=
  ⟨oracle, fun h => not_inPRel (h _ (bgsLang_inNPRel oracle))⟩

end PvsNP.Relativization
