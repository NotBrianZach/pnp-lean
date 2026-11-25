/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import PvsNP.Complexity
import PvsNP.Enumeration
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sets

/-!
# Oracle machines, and the technical core of relativization

`PvsNP/Conjecture.lean` cites the relativization barrier (Baker-Gill-Solovay): there are
oracles `A`, `B` with `Pᴬ = NPᴬ` and `Pᴮ ≠ NPᴮ`, so no argument that survives the addition
of an oracle can settle `P` vs `NP`.  This file builds the machinery that any such argument
needs, and proves the two lemmas that do the actual work in all of them.

The model extends `PvsNP/Complexity.lean` with a **query buffer**.  A machine may push bits
onto the buffer or clear it, and each transition may branch on the oracle's answer for the
buffer's current contents.  (Consulting the oracle at every step rather than on demand
costs nothing: building a query of length `ℓ` already takes `ℓ` steps.)

Acceptance is phrased in terms of explicit computation **paths**, because that is what the
relativization arguments reason about.

Main results:

* `isPath_congr` : **oracle sensitivity.**  A computation path is valid under `B` iff it is
  valid under `B'`, whenever the two oracles agree on the strings that path actually
  consults.  Everything an oracle argument does rests on this.
* `exists_unqueried` : **the pigeonhole.**  A path of length `< 2ⁿ` leaves some string of
  length `n` unconsulted, so the oracle can still be redefined there without disturbing the
  computation.
* `instCountableOTM` : oracle machines are finite data, so they can be enumerated.
* `InPRel`, `InNPRel`, `InPRel.inNPRel` : the relativized classes, and `Pᴮ ⊆ NPᴮ`.
* `bgsLang` : the language Baker-Gill-Solovay diagonalises against.

## What is *not* here

Baker-Gill-Solovay itself.  Three pieces are missing, and none of them is a detail:

1. `bgsLang B ∈ NPᴮ`.  The machine is small -- walk the input, nondeterministically
   pushing a guessed bit per symbol, then consult the oracle on the buffer -- but proving
   it correct means reasoning about `Tape.mk₁` under repeated right-moves, which is not
   done here.
2. The stage construction for `∃ B, Pᴮ ≠ NPᴮ`: enumerate the deterministic
   polynomial-time oracle machines (`instCountableOTM` makes this possible) and at stage
   `i` use `exists_unqueried` to defeat machine `i` on some input `1ⁿ`.
3. For the other half, `∃ A, Pᴬ = NPᴬ`: enough `PSPACE` theory to see that a
   `PSPACE`-complete oracle collapses the two classes.  This is the expensive one.

No result below is stated as if any of this were done.
-/

namespace PvsNP.Relativization

open Turing PvsNP.Complexity

/-- An oracle is a language, presented as a predicate on strings. -/
abbrev Oracle := List Bool → Bool

/-- A machine action: move, write, push a bit onto the query buffer, or clear it. -/
inductive OStmt
  | move : Turing.Dir → OStmt
  | write : Sym → OStmt
  | push : Bool → OStmt
  | clear : OStmt
  deriving DecidableEq

/--
A nondeterministic oracle machine.  As in `PvsNP/Complexity.lean` the states are
`Fin size` and the transition table is finite, so a machine is finite data.  The extra
`Bool` argument of `step` is the oracle's answer for the current query buffer.
-/
structure OTM where
  /-- The number of states. -/
  size : ℕ
  /-- The initial state. -/
  start : Fin size
  /-- The transition relation, which may branch on the oracle's answer. -/
  step : Fin size → Sym → Bool → Finset (Fin size × OStmt)

/-- An action is a direction, a symbol, a bit, or the clear instruction. -/
def oStmtEquiv : OStmt ≃ (Turing.Dir ⊕ Sym ⊕ Bool ⊕ Unit) where
  toFun s := match s with
    | OStmt.move d => Sum.inl d
    | OStmt.write a => Sum.inr (Sum.inl a)
    | OStmt.push b => Sum.inr (Sum.inr (Sum.inl b))
    | OStmt.clear => Sum.inr (Sum.inr (Sum.inr ()))
  invFun s := match s with
    | Sum.inl d => OStmt.move d
    | Sum.inr (Sum.inl a) => OStmt.write a
    | Sum.inr (Sum.inr (Sum.inl b)) => OStmt.push b
    | Sum.inr (Sum.inr (Sum.inr _)) => OStmt.clear
  left_inv s := by cases s <;> rfl
  right_inv s := by
    rcases s with _ | s
    · rfl
    · rcases s with _ | s
      · rfl
      · rcases s with _ | s <;> rfl

instance : Fintype OStmt := Fintype.ofEquiv _ oStmtEquiv.symm

/-- The raw data of an oracle machine. -/
abbrev OTMData := Σ m : ℕ, Fin m × (Fin m → Sym → Bool → Finset (Fin m × OStmt))

/-- Reading off an oracle machine's data loses nothing. -/
def OTM.data (N : OTM) : OTMData := ⟨N.size, N.start, N.step⟩

theorem OTM.data_injective : Function.Injective OTM.data := by
  intro N₁ N₂ h
  obtain ⟨m₁, s₁, f₁⟩ := N₁
  obtain ⟨m₂, s₂, f₂⟩ := N₂
  simp only [OTM.data, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rfl

/-- **Oracle machines are finite data too**, so a stage construction can enumerate them. -/
instance instCountableOTM : Countable OTM := OTM.data_injective.countable

namespace OTM

variable (N : OTM)

/-- A configuration: state, tape, and query buffer. -/
def Cfg : Type := Fin N.size × Tape Sym × List Bool

/-- Carry out one action on the tape and buffer. -/
def act : OStmt → Tape Sym × List Bool → Tape Sym × List Bool
  | OStmt.move d, p => (p.1.move d, p.2)
  | OStmt.write a, p => (p.1.write a, p.2)
  | OStmt.push b, p => (p.1, p.2 ++ [b])
  | OStmt.clear, p => (p.1, [])

/-- The starting configuration: the input on the tape, the buffer empty. -/
def init (x : List Bool) : N.Cfg := (N.start, Tape.mk₁ (x.map some), [])

/-- The configurations reachable in one step, under oracle `B`. -/
def succs (B : Oracle) (c : N.Cfg) : Set N.Cfg :=
  {c' | ∃ y ∈ N.step c.1 c.2.1.head (B c.2.2), c' = (y.1, act y.2 c.2)}

/-- A configuration with no available transition under `B`. -/
def Halted (B : Oracle) (c : N.Cfg) : Prop := N.step c.1 c.2.1.head (B c.2.2) = ∅

/-- Halted with a `1` under the head. -/
def Accepting (B : Oracle) (c : N.Cfg) : Prop := N.Halted B c ∧ c.2.1.head = some true

/-- Determinism: at most one transition is ever available. -/
def Det : Prop := ∀ q a b, (N.step q a b).card ≤ 1

/-! ### Computation paths -/

/-- `N.IsPath B p` : consecutive configurations in `p` are related by a step of `N` under
oracle `B`. -/
def IsPath (B : Oracle) : List N.Cfg → Prop
  | [] => True
  | [_] => True
  | c :: c' :: rest => c' ∈ N.succs B c ∧ IsPath B (c' :: rest)

@[simp] theorem isPath_nil {B : Oracle} : N.IsPath B [] ↔ True := ⟨id, id⟩

@[simp] theorem isPath_singleton {B : Oracle} (c : N.Cfg) : N.IsPath B [c] ↔ True := ⟨id, id⟩

@[simp] theorem isPath_cons₂ {B : Oracle} (c c' : N.Cfg) (rest : List N.Cfg) :
    N.IsPath B (c :: c' :: rest) ↔ (c' ∈ N.succs B c ∧ N.IsPath B (c' :: rest)) := ⟨id, id⟩

/-- The strings a path consults: one per configuration. -/
def buffers (p : List N.Cfg) : List (List Bool) := p.map fun c => c.2.2

@[simp] theorem buffers_length (p : List N.Cfg) : (N.buffers p).length = p.length :=
  List.length_map ..

@[simp] theorem buffers_cons (c : N.Cfg) (p : List N.Cfg) :
    N.buffers (c :: p) = c.2.2 :: N.buffers p := rfl

/-- `N` accepts `x` within `t` steps under `B`: there is a valid path of at most `t + 1`
configurations from the initial one to an accepting one. -/
def Accepts (B : Oracle) (t : ℕ) (x : List Bool) : Prop :=
  ∃ p : List N.Cfg, N.IsPath B p ∧ p.length ≤ t + 1 ∧ p.head? = some (N.init x) ∧
    ∃ c, p.getLast? = some c ∧ N.Accepting B c

/-! ### Oracle sensitivity

A step depends on the oracle only through its value at the current buffer.  So two oracles
that agree on everything a path consults cannot tell that path apart.  This is the lemma
every relativization argument runs on.
-/

theorem succs_congr {B B' : Oracle} (c : N.Cfg) (h : B c.2.2 = B' c.2.2) :
    N.succs B c = N.succs B' c := by
  simp only [succs, h]

theorem halted_congr {B B' : Oracle} (c : N.Cfg) (h : B c.2.2 = B' c.2.2) :
    N.Halted B c ↔ N.Halted B' c := by
  simp only [Halted, h]

theorem accepting_congr {B B' : Oracle} (c : N.Cfg) (h : B c.2.2 = B' c.2.2) :
    N.Accepting B c ↔ N.Accepting B' c := by
  simp only [Accepting, halted_congr N c h]

/--
**Oracle sensitivity.**  A path is valid under `B` exactly when it is valid under `B'`,
provided the two oracles agree on the strings the path consults.
-/
theorem isPath_congr {B B' : Oracle} :
    ∀ p : List N.Cfg, (∀ s ∈ N.buffers p, B s = B' s) → (N.IsPath B p ↔ N.IsPath B' p) := by
  intro p
  induction p with
  | nil => intro _; simp
  | cons c rest ih =>
    intro h
    cases rest with
    | nil => simp
    | cons c' rest' =>
      have hb : B c.2.2 = B' c.2.2 := h _ (by simp)
      have hrest : ∀ s ∈ N.buffers (c' :: rest'), B s = B' s := by
        intro s hs
        apply h s
        rw [buffers_cons]
        exact List.mem_cons_of_mem _ hs
      rw [isPath_cons₂, isPath_cons₂, succs_congr N c hb, ih hrest]

/-- Acceptance transfers too, as long as the witnessing path's queries are respected. -/
theorem accepts_of_isPath_congr {B B' : Oracle} {t : ℕ} {x : List Bool}
    {p : List N.Cfg} (hp : N.IsPath B p) (hlen : p.length ≤ t + 1)
    (hhead : p.head? = some (N.init x)) {c : N.Cfg} (hlast : p.getLast? = some c)
    (hacc : N.Accepting B c) (h : ∀ s ∈ N.buffers p, B s = B' s) :
    N.Accepts B' t x := by
  refine ⟨p, (N.isPath_congr p h).1 hp, hlen, hhead, c, hlast, ?_⟩
  refine (N.accepting_congr c ?_).1 hacc
  exact h _ (by
    simp only [buffers, List.mem_map]
    exact ⟨c, List.mem_of_getLast? hlast, rfl⟩)

/-! ### The pigeonhole

A short path cannot have looked at every string of a given length.  That is exactly the
freedom a stage construction needs: it can redefine the oracle on an unconsulted string
without disturbing the computation it has already run.
-/

/--
**Some string of length `n` is never consulted**, as soon as the path is shorter than the
number of such strings.
-/
theorem exists_unqueried (p : List N.Cfg) (n : ℕ) (h : p.length < 2 ^ n) :
    ∃ w : List Bool, w.length = n ∧ w ∉ N.buffers p := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  -- every length-`n` string occurs among the buffers
  have hsub : (Finset.univ.image fun g : Fin n → Bool => List.ofFn g) ⊆
      (N.buffers p).toFinset := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨g, rfl⟩ := hw
    exact List.mem_toFinset.2 (hcon _ (List.length_ofFn ..))
  have hcard : 2 ^ n ≤ (N.buffers p).toFinset.card := by
    calc 2 ^ n = (Finset.univ : Finset (Fin n → Bool)).card := by
          simp [Finset.card_univ]
      _ = (Finset.univ.image fun g : Fin n → Bool => List.ofFn g).card :=
          (Finset.card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ (N.buffers p).toFinset.card := Finset.card_le_card hsub
  have hle : (N.buffers p).toFinset.card ≤ p.length := by
    calc (N.buffers p).toFinset.card ≤ (N.buffers p).length := List.toFinset_card_le _
      _ = p.length := N.buffers_length p
  omega

end OTM

/-! ### The relativized classes -/

/-- **`Pᴮ`**: decided by a deterministic oracle machine within a polynomial bound. -/
def InPRel (B : Oracle) (L : List Bool → Bool) : Prop :=
  ∃ (N : OTM) (k c : ℕ), N.Det ∧
    ∀ x, L x = true ↔ N.Accepts B (polyBound k c x.length) x

/-- **`NPᴮ`**: the same, without determinism. -/
def InNPRel (B : Oracle) (L : List Bool → Bool) : Prop :=
  ∃ (N : OTM) (k c : ℕ), ∀ x, L x = true ↔ N.Accepts B (polyBound k c x.length) x

theorem InPRel.inNPRel {B : Oracle} {L : List Bool → Bool} (h : InPRel B L) :
    InNPRel B L := by
  obtain ⟨N, k, c, _, hc⟩ := h
  exact ⟨N, k, c, hc⟩

/-- The statement `Pᴮ = NPᴮ`, for a fixed oracle. -/
def PeqNPRel (B : Oracle) : Prop := ∀ L, InNPRel B L → InPRel B L

open scoped Classical in
/-- The language Baker-Gill-Solovay diagonalises against: the unary strings `1ⁿ` such that
`B` contains *some* string of length `n`. -/
noncomputable def bgsLang (B : Oracle) : List Bool → Bool := fun x =>
  x.all id && decide (∃ w : List Bool, w.length = x.length ∧ B w = true)

/-- Membership in `bgsLang` is what it looks like. -/
theorem bgsLang_eq_true_iff (B : Oracle) (x : List Bool) :
    bgsLang B x = true ↔
      (∀ b ∈ x, b = true) ∧ ∃ w : List Bool, w.length = x.length ∧ B w = true := by
  simp only [bgsLang, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, id_eq]

end PvsNP.Relativization
