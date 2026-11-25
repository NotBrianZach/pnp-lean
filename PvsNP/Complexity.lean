/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# A formal statement of P and NP

Mathlib has Turing machines but no complexity classes, so this file defines them.

The model is a **nondeterministic Post-Turing machine**: a finite state set, a two-way
infinite tape over the three-symbol alphabet `Sym = Option Bool` (blank, `0`, `1`), and a
transition *relation* assigning to each (state, symbol) pair a set of (new state, action)
options, where an action is a move or a write.  The input `x : List Bool` is written on
the tape; the machine accepts if some computation path of length at most `t` reaches a
halted configuration whose head symbol is `1`.

* `InNP L` : some machine accepts exactly `L`, within a bound polynomial in `|x|`.
* `InP L`  : the same, with the extra requirement that the machine is **deterministic**
  (at most one transition is available at any state and symbol).

For a deterministic machine the acceptance predicate `Accepts N t x` is itself decidable
by simulating at most `t` steps, so `InP` is the usual deterministic polynomial time, and
`InP → InNP` holds by dropping a hypothesis (`InP.inNP`).

## Modelling caveats (not formalised)

Two claims are used informally and are *not* theorems here:

1. This single-tape Post-Turing model is polynomially equivalent to the textbook
   multi-tape Turing machine model.  (True, and standard; at most a quadratic slowdown.)
2. Nondeterministic polynomial time as defined here coincides with the
   verifier/certificate definition of NP.  (True, and standard.)

Both are routine but unformalised, so results below are theorems *about this model*.
Anyone relying on them for a claim about the Clay problem must also accept (1) and (2).
-/

namespace PvsNP.Complexity

open Turing

/-- The tape alphabet: blank (`none`), `0`, and `1`. -/
abbrev Sym := Option Bool

/--
A nondeterministic Post-Turing machine: finitely many states `Fin size`, a start state,
and a transition relation given by a finite set of options for each (state, symbol).
`step q a = ∅` means "halt".

The states are `Fin size` rather than an arbitrary finite type on purpose.  It costs
nothing in expressiveness, and it makes an `NTM` a piece of *finite data*: `NTM` lands in
`Type`, and `Countable NTM` holds (`PvsNP/Enumeration.lean`).  Any diagonalisation
argument -- Baker-Gill-Solovay, time hierarchy -- needs that.
-/
structure NTM where
  /-- The number of states. -/
  size : ℕ
  /-- The initial state. -/
  start : Fin size
  /-- The transition relation. -/
  step : Fin size → Sym → Finset (Fin size × TM0.Stmt Sym)

namespace NTM

/-- Carry out one machine action on the tape. -/
def act : TM0.Stmt Sym → Tape Sym → Tape Sym
  | TM0.Stmt.move d, T => T.move d
  | TM0.Stmt.write a, T => T.write a

variable (N : NTM)

/-- A configuration: current state together with the tape. -/
def Cfg : Type := Fin N.size × Tape Sym

/-- The starting configuration on input `x`, written as a list of bits on a blank tape. -/
def init (x : List Bool) : N.Cfg := (N.start, Tape.mk₁ (x.map some))

/-- The configurations reachable in one step. -/
def succs (c : N.Cfg) : Set N.Cfg :=
  {c' | ∃ y ∈ N.step c.1 c.2.head, c' = (y.1, act y.2 c.2)}

/-- `N.ReachesIn t c c'` : `c'` is reachable from `c` along some path of at most `t`
steps. -/
def ReachesIn : ℕ → N.Cfg → N.Cfg → Prop
  | 0 => fun c c' => c = c'
  | t + 1 => fun c c' => c = c' ∨ ∃ c₁ ∈ N.succs c, ReachesIn t c₁ c'

@[simp] theorem reachesIn_zero {c c' : N.Cfg} : N.ReachesIn 0 c c' ↔ c = c' := ⟨id, id⟩

@[simp] theorem reachesIn_succ {t : ℕ} {c c' : N.Cfg} :
    N.ReachesIn (t + 1) c c' ↔ (c = c' ∨ ∃ c₁ ∈ N.succs c, N.ReachesIn t c₁ c') := ⟨id, id⟩

/-- A configuration with no available transition. -/
def Halted (c : N.Cfg) : Prop := N.step c.1 c.2.head = ∅

/-- Halted with a `1` under the head. -/
def Accepting (c : N.Cfg) : Prop := N.Halted c ∧ c.2.head = some true

/-- `N` accepts `x` within `t` steps. -/
def Accepts (t : ℕ) (x : List Bool) : Prop :=
  ∃ c, N.ReachesIn t (N.init x) c ∧ N.Accepting c

/-- Determinism: at most one transition is available at any (state, symbol). -/
def Det : Prop := ∀ q a, (N.step q a).card ≤ 1

theorem reachesIn_refl (t : ℕ) (c : N.Cfg) : N.ReachesIn t c c := by
  cases t with
  | zero => rfl
  | succ t => exact Or.inl rfl

theorem reachesIn_mono : ∀ {t₁ t₂ : ℕ}, t₁ ≤ t₂ → ∀ {c c' : N.Cfg},
    N.ReachesIn t₁ c c' → N.ReachesIn t₂ c c' := by
  intro t₁
  induction t₁ with
  | zero =>
    intro t₂ _ c c' hr
    rw [reachesIn_zero] at hr
    subst hr
    exact N.reachesIn_refl _ _
  | succ t ih =>
    intro t₂ h c c' hr
    cases t₂ with
    | zero => omega
    | succ t₂ =>
      rw [reachesIn_succ] at hr ⊢
      rcases hr with rfl | ⟨c₁, hc₁, hrest⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨c₁, hc₁, ih (by omega) hrest⟩

theorem accepts_mono {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) {x : List Bool} (ha : N.Accepts t₁ x) :
    N.Accepts t₂ x := by
  obtain ⟨c, hr, hacc⟩ := ha
  exact ⟨c, N.reachesIn_mono h hr, hacc⟩

end NTM

/-- The time budget allowed on an input of length `n`: `c * (n+1)^k + c`.  As `k` and `c`
range over `ℕ` this family is cofinal in the polynomials. -/
def polyBound (k c n : ℕ) : ℕ := c * (n + 1) ^ k + c

/-- **NP**: accepted by a nondeterministic machine within a polynomial bound. -/
def InNP (L : List Bool → Bool) : Prop :=
  ∃ (N : NTM) (k c : ℕ), ∀ x, L x = true ↔ N.Accepts (polyBound k c x.length) x

/-- **P**: the same, by a *deterministic* machine. -/
def InP (L : List Bool → Bool) : Prop :=
  ∃ (N : NTM) (k c : ℕ), N.Det ∧ ∀ x, L x = true ↔ N.Accepts (polyBound k c x.length) x

theorem InP.inNP {L : List Bool → Bool} (h : InP L) : InNP L := by
  obtain ⟨N, k, c, _, hc⟩ := h
  exact ⟨N, k, c, hc⟩

/-! ### The two forms of the question -/

/-- The statement `P = NP`. -/
def PeqNP : Prop := ∀ L, InNP L → InP L

/-- The statement `P ≠ NP`. -/
def PneNP : Prop := ∃ L, InNP L ∧ ¬ InP L

theorem peqNP_iff_not_pneNP : PeqNP ↔ ¬ PneNP := by
  constructor
  · intro h ⟨L, hNP, hP⟩; exact hP (h L hNP)
  · intro h L hNP
    by_contra hP
    exact h ⟨L, hNP, hP⟩

/-! ### The definitions are not vacuous

Two sanity checks, so that `InP` is not accidentally empty and `InNP` not accidentally
everything.
-/

/-- The machine that writes `1` and halts: from state `0` it writes `1` and moves to
state `1`, where it has no transition. -/
@[reducible] def yesMachine : NTM where
  size := 2
  start := 0
  step := fun q _ => if q = 0 then {(1, TM0.Stmt.write (some true))} else ∅

theorem yesMachine_det : yesMachine.Det := by
  intro q a
  by_cases hq : q = 0 <;> simp [yesMachine, hq]

/-- The always-true language is in `P`. -/
theorem inP_const_true : InP (fun _ => true) := by
  refine ⟨yesMachine, 0, 1, yesMachine_det, fun x => ?_⟩
  refine ⟨fun _ => ?_, fun _ => rfl⟩
  have hstep : ((1 : Fin 2), TM0.Stmt.write (some true)) ∈
      yesMachine.step yesMachine.start (Tape.mk₁ (x.map some)).head := by
    exact Finset.mem_singleton_self _
  refine NTM.accepts_mono _ (show 1 ≤ polyBound 0 1 x.length by simp [polyBound]) ?_
  refine ⟨((1 : Fin 2), (Tape.mk₁ (x.map some)).write (some true)), ?_, ?_, rfl⟩
  · exact Or.inr ⟨_, ⟨_, hstep, rfl⟩, rfl⟩
  · change yesMachine.step 1 _ = ∅
    simp [yesMachine]

/-- The machine that overwrites with a blank forever: it never halts, so it never
accepts. -/
@[reducible] def noMachine : NTM where
  size := 1
  start := 0
  step := fun _ _ => {(0, TM0.Stmt.write none)}

theorem noMachine_det : noMachine.Det := by
  intro q a
  simp [noMachine]

theorem noMachine_never_accepts (t : ℕ) (x : List Bool) : ¬ noMachine.Accepts t x := by
  rintro ⟨c, -, hhalt, -⟩
  have hmem : ((0 : Fin 1), TM0.Stmt.write none) ∈ noMachine.step c.1 c.2.head :=
    Finset.mem_singleton_self _
  rw [hhalt] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- The always-false language is in `P`. -/
theorem inP_const_false : InP (fun _ => false) := by
  refine ⟨noMachine, 0, 1, noMachine_det, fun x => ?_⟩
  exact ⟨fun h => absurd h (by simp), fun h => absurd h (noMachine_never_accepts _ x)⟩

end PvsNP.Complexity
