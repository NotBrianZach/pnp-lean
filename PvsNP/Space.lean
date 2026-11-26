/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.Complexity

/-!
# Space-bounded computation

The collapsing half of Baker-Gill-Solovay (`∃ A, Pᴬ = NPᴬ`) runs through `PSPACE`: for a
`PSPACE`-complete oracle `A`, both `Pᴬ` and `NPᴬ` equal `PSPACE`.  This file lays the
groundwork by giving the model of `PvsNP/Complexity.lean` a notion of space.

The tape of `PvsNP/Complexity.lean` is two-way infinite and is a quotient structure, so
"cells visited" is not directly readable off a configuration.  Instead we track the head's
**offset from its starting cell** explicitly, as an integer carried alongside the
configuration, and record the whole list of offsets a run passes through -- exactly the way
`PvsNP/Oracle.lean` records the strings a run consults.  The space used is then the largest
offset reached, bounded two-sidedly so that `omega` can reason about it.

Main results:

* `PosRun` : a run that remembers where the head went.
* `posRun_toRun` and `exists_posRun` : the position-tracking run and the ordinary
  `ReachesIn` run are the same thing.  Tracking the head loses and invents nothing.
* `offset_bounds` : **space is at most time.**  A run through `zs` keeps the head
  within `zs.length` cells of where it started, since one step moves it by at most one.
* `InPSPACE` : polynomial space.

## What is *not* here

`P ⊆ PSPACE`, and so the collapse itself.  The obstruction is not the space bound -- that
is `offset_bounds` -- but the shape of `Accepts` in this model: it says "reaches an
accepting configuration **within** `t` steps", whereas `AcceptsInSpace` below puts no bound
on time.  A machine from `InP` may well wander into an accepting configuration after its
budget has expired, so the same machine does not witness both.  Bridging that needs a
machine carrying a step counter, which is ordinary Turing-machine programming -- cheap on
paper and expensive here, since this model was chosen to make complexity classes easy to
*state* rather than to make machines easy to *write*.  The same clock is the first thing the
collapse argument would need, so it is the honest next step rather than a detail.
-/

namespace PvsNP.Complexity

open Turing

namespace NTM

variable (N : NTM)

/-- How far one action moves the head. -/
def delta : TM0.Stmt Sym → ℤ
  | TM0.Stmt.move Turing.Dir.left => -1
  | TM0.Stmt.move Turing.Dir.right => 1
  | TM0.Stmt.write _ => 0

theorem delta_bounds (stmt : TM0.Stmt Sym) : -1 ≤ delta stmt ∧ delta stmt ≤ 1 := by
  cases stmt with
  | move d => cases d <;> simp [delta]
  | write a => simp [delta]

/-- A configuration together with the head's offset from its starting cell. -/
def SCfg : Type := N.Cfg × ℤ

/-- One step, also moving the recorded offset. -/
def posSuccs (c : N.SCfg) : Set N.SCfg :=
  {c' | ∃ y ∈ N.step c.1.1 c.1.2.head, c' = ((y.1, act y.2 c.1.2), c.2 + delta y.2)}

/-- `N.PosRun c c' zs` : a computation from `c` to `c'` passing through exactly the head
offsets `zs`, one per configuration visited. -/
inductive PosRun (N : NTM) : N.SCfg → N.SCfg → List ℤ → Prop
  | refl (c : N.SCfg) : PosRun N c c [c.2]
  | step {c c' c'' : N.SCfg} {zs : List ℤ} :
      c' ∈ N.posSuccs c → PosRun N c' c'' zs → PosRun N c c'' (c.2 :: zs)

theorem PosRun.length_pos {c c' : N.SCfg} {zs : List ℤ} (r : N.PosRun c c' zs) :
    0 < zs.length := by
  induction r with
  | refl c => simp
  | step _ _ _ => simp

/-! ### Tracking the head loses nothing -/

/-- A position-tracking run projects to an ordinary run. -/
theorem posRun_toRun {c c' : N.SCfg} {zs : List ℤ} (r : N.PosRun c c' zs) :
    N.ReachesIn (zs.length - 1) c.1 c'.1 := by
  induction r with
  | refl c => exact N.reachesIn_refl _ _
  | @step c c' c'' zs hs r ih =>
    have hpos : 0 < zs.length := r.length_pos
    obtain ⟨y, hy, hcc⟩ := hs
    simp only [List.length_cons]
    rw [show zs.length + 1 - 1 = (zs.length - 1) + 1 by omega, reachesIn_succ]
    refine Or.inr ⟨c'.1, ⟨y, hy, ?_⟩, ih⟩
    rw [hcc]

/-- Conversely, every ordinary run can be tracked.  The offsets are determined by the
actions the run chose. -/
theorem exists_posRun : ∀ {t : ℕ} {c c' : N.Cfg}, N.ReachesIn t c c' →
    ∀ z : ℤ, ∃ (q : N.SCfg) (zs : List ℤ),
      N.PosRun (c, z) q zs ∧ q.1 = c' ∧ zs.length ≤ t + 1 ∧ zs.head? = some z := by
  intro t
  induction t with
  | zero =>
    intro c c' hr z
    rw [reachesIn_zero] at hr
    subst hr
    exact ⟨(c, z), [z], PosRun.refl _, rfl, by simp, by simp⟩
  | succ t ih =>
    intro c c' hr z
    rw [reachesIn_succ] at hr
    rcases hr with rfl | ⟨c₁, hc₁, hrest⟩
    · exact ⟨(c, z), [z], PosRun.refl _, rfl, by simp, by simp⟩
    · obtain ⟨y, hy, rfl⟩ := hc₁
      obtain ⟨q, zs, hq, hq1, hlen, -⟩ := ih hrest (z + delta y.2)
      refine ⟨q, z :: zs, PosRun.step ⟨y, hy, rfl⟩ hq, hq1, by simpa using hlen, by simp⟩

/-! ### Space is at most time -/

/-- One step moves the head by at most one cell, so a run through `zs` stays within
`zs.length` cells of where it began.  Stated with two-sided bounds rather than `|·|` so
that `omega` can see it. -/
theorem offset_bounds : ∀ {c c' : N.SCfg} {zs : List ℤ}, N.PosRun c c' zs →
    ∀ z ∈ zs, c.2 - (zs.length : ℤ) ≤ z ∧ z ≤ c.2 + (zs.length : ℤ) := by
  intro c c' zs r
  induction r with
  | refl c =>
    intro z hz
    rw [List.mem_singleton] at hz
    subst hz
    have hl : ([c.2] : List ℤ).length = 1 := rfl
    rw [hl]
    omega
  | @step c c' c'' zs hs r ih =>
    intro z hz
    obtain ⟨y, -, hcc⟩ := hs
    have hstep : c'.2 = c.2 + delta y.2 := by rw [hcc]
    obtain ⟨hd1, hd2⟩ := delta_bounds y.2
    have hl : (c.2 :: zs).length = zs.length + 1 := rfl
    rw [hl]
    rcases List.mem_cons.1 hz with rfl | hz'
    · omega
    · obtain ⟨h1, h2⟩ := ih z hz'
      omega

/-- From the starting cell, the head stays within `zs.length`. -/
theorem offset_bounds_zero {c c' : N.SCfg} {zs : List ℤ} (hc : c.2 = 0)
    (r : N.PosRun c c' zs) : ∀ z ∈ zs, -(zs.length : ℤ) ≤ z ∧ z ≤ (zs.length : ℤ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := N.offset_bounds r z hz
  rw [hc] at h1 h2
  omega

/-! ### The class -/

/-- `N` accepts `x` using head offsets within `s` of the start.  No bound on time: that is
the point of a space class. -/
def AcceptsInSpace (s : ℕ) (x : List Bool) : Prop :=
  ∃ (q : N.SCfg) (zs : List ℤ), N.PosRun (N.init x, 0) q zs ∧
    (∀ z ∈ zs, -(s : ℤ) ≤ z ∧ z ≤ (s : ℤ)) ∧ N.Accepting q.1

end NTM

/-- **PSPACE**: decided within a polynomial number of cells of the starting position. -/
def InPSPACE (L : List Bool → Bool) : Prop :=
  ∃ (N : NTM) (k c : ℕ), ∀ x, L x = true ↔ N.AcceptsInSpace (polyBound k c x.length) x

/--
**The space bound a time bound gives you.**  A run through `zs` keeps the head within
`zs.length` of the start, so a time-bounded run *is* space-bounded by the same polynomial.
This is the half of `P ⊆ PSPACE` that is genuinely about space; the missing half is the
clock, see the module header.
-/
theorem acceptsInSpace_of_posRun {N : NTM} {s : ℕ} {x : List Bool} {q : N.SCfg}
    {zs : List ℤ} (r : N.PosRun (N.init x, 0) q zs) (hlen : zs.length ≤ s)
    (hacc : N.Accepting q.1) : N.AcceptsInSpace s x := by
  refine ⟨q, zs, r, fun z hz => ?_, hacc⟩
  obtain ⟨h1, h2⟩ := N.offset_bounds_zero rfl r z hz
  have hs : (zs.length : ℤ) ≤ (s : ℤ) := by exact_mod_cast hlen
  omega

/--
**Every time-bounded accepting computation is space-bounded.**  Combining the lift with the
offset bound: a machine accepting `x` within `t` steps has an accepting run confined to
`t + 1` cells either side of the start.
-/
theorem acceptsInSpace_of_accepts {N : NTM} {t : ℕ} {x : List Bool}
    (h : N.Accepts t x) : N.AcceptsInSpace (t + 1) x := by
  obtain ⟨c', hr, hacc⟩ := h
  obtain ⟨q, zs, hq, hq1, hlen, -⟩ := N.exists_posRun hr 0
  exact acceptsInSpace_of_posRun hq hlen (hq1 ▸ hacc)

end PvsNP.Complexity
