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

Acceptance is phrased in terms of an inductive `Run` relation that carries the list of
strings consulted along the way, because that list is exactly what the relativization
arguments reason about.

Main results:

* `Run.congr` : **oracle sensitivity.**  A run under `B` is a run under `B'`, whenever the
  two oracles agree on the strings that run actually consults.  Everything an oracle
  argument does rests on this.
* `exists_unqueried` : **the pigeonhole.**  A run consulting fewer than `2ⁿ` strings leaves
  some string of length `n` untouched, so the oracle can still be redefined there without
  disturbing the computation.
* `instCountableOTM` : oracle machines are finite data, so they can be enumerated.
* `InPRel`, `InNPRel`, `InPRel.inNPRel` : the relativized classes, and `Pᴮ ⊆ NPᴮ`.
* `bgsLang_inNPRel` : **`bgsLang B ∈ NPᴮ`**, via the three-state guessing machine
  `bgsMachine`, proved in both directions (`bgsMachine_accepts` and `bgs_inv`).
* `not_accepts_congr` : **the diagonalisation step.**  A *deterministic* machine that
  rejects still rejects after the oracle is changed away from the strings its own
  trajectory consults.  Sensitivity alone does not give this -- an accepting run under the
  new oracle might be exactly one that queries the changed string -- and ruling that out
  is what determinism buys.  To use it, the step relation is turned into a function
  (`nextCfg`, `traj`, `qlist`, legitimate under `Det` by `mem_succs_iff`).
* `exists_flip` : the two halves of a stage combined -- an unconsulted string of length `n`
  exists, and flipping the oracle there preserves rejection.
* `exists_enumeration` : the candidates can be listed.

## What is *not* here

Baker-Gill-Solovay itself.  Two pieces remain:

1. The stage recursion for `∃ B, Pᴮ ≠ NPᴮ`.  Each individual stage is now a theorem
   (`exists_flip`), and the candidates can be enumerated (`exists_enumeration`), but the
   recursion that runs the stages is not written.  The bookkeeping it needs: lengths
   `n 0 < n 1 < ⋯` chosen so that stage `i`'s budget `tᵢ` satisfies `tᵢ + 1 < 2 ^ n i` and
   `n (i+1) > tᵢ`, so that stage `i`'s queries are all shorter than anything later stages
   touch, and the final oracle therefore agrees with the stage-`i` partial oracle on
   exactly the strings stage `i` looked at.
2. For the other half, `∃ A, Pᴬ = NPᴬ`: enough `PSPACE` theory to see that a
   `PSPACE`-complete oracle collapses the two classes.  This is the expensive one.

No result below is stated as if either were done.
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

/-- A machine with one state and no transitions. -/
instance instNonemptyOTM : Nonempty OTM := ⟨⟨1, 0, fun _ _ _ => ∅⟩⟩

/-- The candidates a stage construction has to defeat -- a machine together with its
polynomial bound -- can be listed. -/
theorem exists_enumeration : ∃ e : ℕ → OTM × ℕ × ℕ, Function.Surjective e :=
  exists_surjective_nat _

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
/-! ### Computation runs

A run is recorded together with the list of strings it consults: one per configuration
visited, in order.  Carrying the query list in the relation is what makes both the
sensitivity lemma and the pigeonhole one-line consequences of an induction.
-/

/-- `N.Run B c c' qs` : a computation from `c` to `c'` under oracle `B`, consulting exactly
the strings `qs` (one per configuration visited, both endpoints included). -/
inductive Run (N : OTM) (B : Oracle) : N.Cfg → N.Cfg → List (List Bool) → Prop
  | refl (c : N.Cfg) : Run N B c c [c.2.2]
  | step {c c' c'' : N.Cfg} {qs : List (List Bool)} :
      c' ∈ N.succs B c → Run N B c' c'' qs → Run N B c c'' (c.2.2 :: qs)

/-- A run of `k` steps consults `k + 1` strings, so the query list is never empty. -/
theorem Run.length_pos {B : Oracle} {c c' : N.Cfg} {qs : List (List Bool)}
    (r : N.Run B c c' qs) : 0 < qs.length := by
  induction r with
  | refl c => simp
  | step _ _ ih => simp

theorem Run.head_mem {B : Oracle} {c c' : N.Cfg} {qs : List (List Bool)}
    (r : N.Run B c c' qs) : c.2.2 ∈ qs := by
  induction r with
  | refl c => simp
  | step _ _ _ => simp

theorem Run.last_mem {B : Oracle} {c c' : N.Cfg} {qs : List (List Bool)}
    (r : N.Run B c c' qs) : c'.2.2 ∈ qs := by
  induction r with
  | refl c => simp
  | step _ _ ih => exact List.mem_cons_of_mem _ ih

/-- `N` accepts `x` within `t` steps under `B`. -/
def Accepts (B : Oracle) (t : ℕ) (x : List Bool) : Prop :=
  ∃ (c : N.Cfg) (qs : List (List Bool)),
    N.Run B (N.init x) c qs ∧ qs.length ≤ t + 1 ∧ N.Accepting B c

theorem accepts_mono {B : Oracle} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) {x : List Bool}
    (ha : N.Accepts B t₁ x) : N.Accepts B t₂ x := by
  obtain ⟨c, qs, hr, hlen, hacc⟩ := ha
  exact ⟨c, qs, hr, by omega, hacc⟩

/-! ### Oracle sensitivity

A step depends on the oracle only through its value at the current buffer.  So two oracles
that agree on everything a run consults cannot tell that run apart.  This is the lemma
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
**Oracle sensitivity.**  A run under `B` is a run under `B'`, provided the two oracles
agree on the strings the run consults.  The query list is unchanged.
-/
theorem Run.congr {B B' : Oracle} : ∀ {c c' : N.Cfg} {qs : List (List Bool)},
    N.Run B c c' qs → (∀ s ∈ qs, B s = B' s) → N.Run B' c c' qs := by
  intro c c' qs r
  induction r with
  | refl c => intro _; exact Run.refl c
  | @step c c' c'' qs hs r ih =>
    intro h
    refine Run.step ?_ (ih fun s hs' => h s (List.mem_cons_of_mem _ hs'))
    rw [← succs_congr N c (h _ (by simp))]
    exact hs

/-- Acceptance transfers along `Run.congr`. -/
theorem accepts_congr {B B' : Oracle} {t : ℕ} {x : List Bool} {c : N.Cfg}
    {qs : List (List Bool)} (hr : N.Run B (N.init x) c qs) (hlen : qs.length ≤ t + 1)
    (hacc : N.Accepting B c) (h : ∀ s ∈ qs, B s = B' s) : N.Accepts B' t x :=
  ⟨c, qs, Run.congr N hr h, hlen,
    (N.accepting_congr c (h _ (Run.last_mem N hr))).1 hacc⟩

/-! ### Deterministic trajectories

The diagonalisation needs more than sensitivity: it needs to know that a *deterministic*
machine which **fails** to accept still fails after the oracle is changed away from its own
queries.  Sensitivity alone does not give this, because an accepting run under the new
oracle might be one that queries the changed string.  Determinism is what rules that out,
and to exploit it we turn the step relation into a function.
-/

/-- The unique successor of a configuration, when there is one.  (For a nondeterministic
machine this picks an arbitrary option; every lemma below about it assumes `Det`.) -/
noncomputable def nextCfg (B : Oracle) (c : N.Cfg) : Option N.Cfg :=
  if h : (N.step c.1 c.2.1.head (B c.2.2)).Nonempty then
    some (h.choose.1, act h.choose.2 c.2)
  else none

/-- Whatever `nextCfg` picks really is a successor; no determinism needed. -/
theorem mem_succs_of_nextCfg (B : Oracle) (c c' : N.Cfg)
    (h : N.nextCfg B c = some c') : c' ∈ N.succs B c := by
  rw [nextCfg] at h
  split at h
  · rename_i hne
    exact ⟨hne.choose, hne.choose_spec, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- For a deterministic machine, `nextCfg` *is* the step relation. -/
theorem mem_succs_iff (hdet : N.Det) (B : Oracle) (c c' : N.Cfg) :
    c' ∈ N.succs B c ↔ N.nextCfg B c = some c' := by
  refine ⟨?_, N.mem_succs_of_nextCfg B c c'⟩
  rintro ⟨y, hy, rfl⟩
  have hne : (N.step c.1 c.2.1.head (B c.2.2)).Nonempty := ⟨y, hy⟩
  rw [nextCfg, dite_eq_left hne]
  have hch : hne.choose = y :=
    Finset.card_le_one.1 (hdet _ _ _) _ hne.choose_spec _ hy
  rw [hch]

/-- The configuration after at most `t` steps, standing still once halted. -/
noncomputable def traj (B : Oracle) : ℕ → N.Cfg → N.Cfg
  | 0, c => c
  | t + 1, c => match N.nextCfg B c with
    | none => c
    | some c' => traj B t c'

/-- The strings consulted in the first `t` steps. -/
noncomputable def qlist (B : Oracle) : ℕ → N.Cfg → List (List Bool)
  | 0, c => [c.2.2]
  | t + 1, c => c.2.2 :: match N.nextCfg B c with
    | none => []
    | some c' => qlist B t c'

@[simp] theorem traj_zero (B : Oracle) (c : N.Cfg) : N.traj B 0 c = c := rfl

@[simp] theorem qlist_zero (B : Oracle) (c : N.Cfg) : N.qlist B 0 c = [c.2.2] := rfl

theorem qlist_length_le (B : Oracle) : ∀ (t : ℕ) (c : N.Cfg),
    (N.qlist B t c).length ≤ t + 1 := by
  intro t
  induction t with
  | zero => intro c; simp
  | succ t ih =>
    intro c
    rw [qlist]
    cases h : N.nextCfg B c with
    | none => simp
    | some c' =>
      simp only [List.length_cons]
      have := ih c'
      omega

/-- Every string a short run consults is also consulted by a longer one. -/
theorem qlist_mono (B : Oracle) : ∀ {t t' : ℕ}, t ≤ t' → ∀ (c : N.Cfg),
    ∀ s ∈ N.qlist B t c, s ∈ N.qlist B t' c := by
  intro t
  induction t with
  | zero =>
    intro t' _ c s hs
    rw [qlist_zero] at hs
    cases t' with
    | zero => exact hs
    | succ t' => simp only [qlist, List.mem_cons]; exact Or.inl (by simpa using hs)
  | succ t ih =>
    intro t' ht c s hs
    cases t' with
    | zero => exact absurd ht (by omega)
    | succ t' =>
      rw [qlist] at hs ⊢
      cases h : N.nextCfg B c with
      | none =>
        rw [h] at hs
        simpa using hs
      | some c' =>
        rw [h] at hs
        simp only [List.mem_cons] at hs ⊢
        exact hs.imp id fun hs' => ih (by omega) c' s hs'

/-- The trajectory really is a run, with the query list it records. -/
theorem run_traj (B : Oracle) : ∀ (t : ℕ) (c : N.Cfg),
    N.Run B c (N.traj B t c) (N.qlist B t c) := by
  intro t
  induction t with
  | zero => intro c; exact Run.refl c
  | succ t ih =>
    intro c
    rw [traj, qlist]
    cases h : N.nextCfg B c with
    | none => simpa using Run.refl c
    | some c' => exact Run.step (N.mem_succs_of_nextCfg B c c' h) (ih c')

/--
**A deterministic machine cannot notice an oracle change away from its own queries.**  If
`B'` agrees with `B` on everything the first `t` steps consult, the trajectory and the
query list are unchanged.
-/
theorem traj_congr {B B' : Oracle} : ∀ (t : ℕ) (c : N.Cfg),
    (∀ s ∈ N.qlist B t c, B s = B' s) →
      N.traj B' t c = N.traj B t c ∧ N.qlist B' t c = N.qlist B t c := by
  intro t
  induction t with
  | zero => intro c _; exact ⟨rfl, rfl⟩
  | succ t ih =>
    intro c h
    have hb : B c.2.2 = B' c.2.2 := h _ (by rw [qlist]; exact List.mem_cons_self ..)
    have hnext : N.nextCfg B' c = N.nextCfg B c := by
      simp only [nextCfg, hb]
    rw [traj, qlist, traj, qlist, hnext]
    cases hc : N.nextCfg B c with
    | none => exact ⟨rfl, rfl⟩
    | some c' =>
      have hrest : ∀ s ∈ N.qlist B t c', B s = B' s := by
        intro s hs
        refine h s ?_
        rw [qlist, hc]
        exact List.mem_cons_of_mem _ hs
      obtain ⟨h1, h2⟩ := ih c' hrest
      simp [h1, h2]

/-- Conversely, for a deterministic machine every run is an initial segment of the
trajectory. -/
theorem eq_traj_of_run (hdet : N.Det) {B : Oracle} : ∀ {c c' : N.Cfg} {qs},
    N.Run B c c' qs → c' = N.traj B (qs.length - 1) c ∧ qs = N.qlist B (qs.length - 1) c := by
  intro c c' qs r
  induction r with
  | refl c => exact ⟨rfl, rfl⟩
  | @step c c' c'' qs hs r ih =>
    obtain ⟨h1, h2⟩ := ih
    have hpos : 0 < qs.length := r.length_pos
    have hnext : N.nextCfg B c = some c' := (N.mem_succs_iff hdet B c c').1 hs
    refine ⟨?_, ?_⟩
    · simp only [List.length_cons]
      rw [show qs.length + 1 - 1 = (qs.length - 1) + 1 by omega, traj, hnext]
      exact h1
    · simp only [List.length_cons]
      rw [show qs.length + 1 - 1 = (qs.length - 1) + 1 by omega, qlist, hnext]
      exact congrArg _ h2

/--
**The diagonalisation step.**  A deterministic machine that does not accept `x` within `t`
steps still does not accept it after the oracle is changed away from the strings its own
`t`-step trajectory consults.
-/
theorem not_accepts_congr (hdet : N.Det) {B B' : Oracle} {t : ℕ} {x : List Bool}
    (h : ∀ s ∈ N.qlist B t (N.init x), B s = B' s) (hno : ¬ N.Accepts B t x) :
    ¬ N.Accepts B' t x := by
  rintro ⟨c, qs, hr, hlen, hacc⟩
  obtain ⟨h1, h2⟩ := N.eq_traj_of_run hdet hr
  have hle : qs.length - 1 ≤ t := by omega
  have hagree : ∀ s ∈ N.qlist B (qs.length - 1) (N.init x), B s = B' s := fun s hs =>
    h s (N.qlist_mono B hle _ s hs)
  obtain ⟨ht, hq⟩ := N.traj_congr (qs.length - 1) (N.init x) hagree
  refine hno ⟨N.traj B (qs.length - 1) (N.init x), N.qlist B (qs.length - 1) (N.init x),
    N.run_traj B _ _, ?_, ?_⟩
  · have := N.qlist_length_le B (qs.length - 1) (N.init x)
    omega
  · have hc' : c = N.traj B (qs.length - 1) (N.init x) := h1.trans ht
    rw [hc'] at hacc
    refine (N.accepting_congr _ ?_).2 hacc
    exact h _ (N.qlist_mono B hle _ _ (N.run_traj B (qs.length - 1) (N.init x)).last_mem)

end OTM

/-! ### The pigeonhole

A short run cannot have looked at every string of a given length.  That is exactly the
freedom a stage construction needs: it can redefine the oracle on an unconsulted string
without disturbing the computation it has already run.
-/

/--
**Some string of length `n` is never consulted**, as soon as the run is shorter than the
number of such strings.
-/
theorem exists_unqueried (qs : List (List Bool)) (n : ℕ) (h : qs.length < 2 ^ n) :
    ∃ w : List Bool, w.length = n ∧ w ∉ qs := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hsub : (Finset.univ.image fun g : Fin n → Bool => List.ofFn g) ⊆ qs.toFinset := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨g, rfl⟩ := hw
    exact List.mem_toFinset.2 (hcon _ (List.length_ofFn ..))
  have hcard : 2 ^ n ≤ qs.toFinset.card := by
    calc 2 ^ n = (Finset.univ : Finset (Fin n → Bool)).card := by
          simp [Finset.card_univ]
      _ = (Finset.univ.image fun g : Fin n → Bool => List.ofFn g).card :=
          (Finset.card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ qs.toFinset.card := Finset.card_le_card hsub
  have hle : qs.toFinset.card ≤ qs.length := List.toFinset_card_le _
  omega


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
/--
The language Baker-Gill-Solovay diagonalises against: the strings `x` such that `B`
contains *some* string of length `|x|`.  Membership depends only on `|x|`, which is all the
diagonalisation uses; the textbook version restricts to unary `1ⁿ`, and dropping that
restriction costs nothing and saves the machine a symbol check.
-/
noncomputable def bgsLang (B : Oracle) : List Bool → Bool := fun x =>
  decide (∃ w : List Bool, w.length = x.length ∧ B w = true)

@[simp] theorem bgsLang_eq_true_iff (B : Oracle) (x : List Bool) :
    bgsLang B x = true ↔ ∃ w : List Bool, w.length = x.length ∧ B w = true := by
  simp only [bgsLang, decide_eq_true_eq]

/-! ### The witness-guessing machine

In state `0`, reading an input cell, guess a bit and push it onto the query buffer; in
state `1`, move right and go back to state `0`.  So after `2i` steps the buffer holds `i`
guessed bits and the head sits on cell `i`.  On reaching the blank past the input, consult
the oracle on the buffer: if it answers yes, write `1` and halt in state `2`, which
accepts.
-/

/-- The transition table of the guessing machine. -/
def bgsStep : Fin 3 → Sym → Bool → Finset (Fin 3 × OStmt)
  | ⟨0, _⟩, some _, _ => {(1, OStmt.push false), (1, OStmt.push true)}
  | ⟨0, _⟩, none, true => {(2, OStmt.write (some true))}
  | ⟨1, _⟩, _, _ => {(0, OStmt.move Turing.Dir.right)}
  | _, _, _ => ∅

@[simp] theorem bgsStep_zero_some (s : Bool) (o : Bool) :
    bgsStep 0 (some s) o = {(1, OStmt.push false), (1, OStmt.push true)} := rfl

@[simp] theorem bgsStep_zero_none_true :
    bgsStep 0 none true = {(2, OStmt.write (some true))} := rfl

@[simp] theorem bgsStep_zero_none_false : bgsStep 0 none false = ∅ := rfl

@[simp] theorem bgsStep_one (a : Sym) (o : Bool) :
    bgsStep 1 a o = {(0, OStmt.move Turing.Dir.right)} := rfl

@[simp] theorem bgsStep_two (a : Sym) (o : Bool) : bgsStep 2 a o = ∅ := rfl

/-- The machine for `bgsLang`. -/
@[reducible] def bgsMachine : OTM where
  size := 3
  start := 0
  step := bgsStep

/--
**The guessing machine accepts, on the nose.**  Given a witness `w` as long as the
remaining input `l`, there is an accepting run of exactly `2|l| + 1` steps.  The induction
is on `l`, so the tape only ever has to be pushed one cell to the right -- no reasoning
about iterated moves or tape indices is needed.
-/
theorem bgs_run (B : Oracle) : ∀ (l w : List Bool) (L : ListBlank Sym) (buf : List Bool),
    w.length = l.length → B (buf ++ w) = true →
    ∃ (c : bgsMachine.Cfg) (qs : List (List Bool)),
      bgsMachine.Run B ((0 : Fin 3), Tape.mk' L (ListBlank.mk (l.map some)), buf) c qs ∧
      qs.length = 2 * l.length + 2 ∧ bgsMachine.Accepting B c := by
  intro l
  induction l with
  | nil =>
    intro w L buf hw hB
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
    subst hw0
    rw [List.append_nil] at hB
    have hhead : (Tape.mk' L (ListBlank.mk ([] : List Sym))).head = none := rfl
    refine ⟨((2 : Fin 3),
      (Tape.mk' L (ListBlank.mk ([] : List Sym))).write (some true), buf), _,
      OTM.Run.step ?_ (OTM.Run.refl _), by simp, ?_, rfl⟩
    · refine ⟨((2 : Fin 3), OStmt.write (some true)), ?_, rfl⟩
      have hstep : bgsMachine.step 0
          (Tape.mk' L (ListBlank.mk (([] : List Bool).map some))).head (B buf)
          = {((2 : Fin 3), OStmt.write (some true))} := by
        simp only [List.map_nil, hhead, hB]
        rfl
      rw [hstep]
      exact Finset.mem_singleton_self _
    · rfl
  | cons a l' ih =>
    intro w L buf hw hB
    obtain ⟨b, w', rfl⟩ : ∃ b w', w = b :: w' := by
      cases w with
      | nil => simp at hw
      | cons b w' => exact ⟨b, w', rfl⟩
    have hhead : (Tape.mk' L (ListBlank.mk ((a :: l').map some))).head = some a := by simp
    have hB' : B ((buf ++ [b]) ++ w') = true := by
      rw [List.append_assoc]; simpa using hB
    obtain ⟨c, qs, hrun, hqs, hacc⟩ :=
      ih w' (ListBlank.cons (some a) L) (buf ++ [b]) (by simpa using hw) hB'
    have hmove : (Tape.mk' L (ListBlank.mk ((a :: l').map some))).move Turing.Dir.right =
        Tape.mk' (ListBlank.cons (some a) L) (ListBlank.mk (l'.map some)) := by
      simp
    refine ⟨c, buf :: (buf ++ [b]) :: qs,
      OTM.Run.step
          (c' := ((1 : Fin 3), Tape.mk' L (ListBlank.mk ((a :: l').map some)), buf ++ [b]))
          ?_
          (OTM.Run.step
            (c' := ((0 : Fin 3),
              Tape.mk' (ListBlank.cons (some a) L) (ListBlank.mk (l'.map some)), buf ++ [b]))
            ?_ hrun), ?_, hacc⟩
    · refine ⟨((1 : Fin 3), OStmt.push b), ?_, rfl⟩
      have hstep : bgsMachine.step 0
          (Tape.mk' L (ListBlank.mk ((a :: l').map some))).head (B buf)
          = {((1 : Fin 3), OStmt.push false), ((1 : Fin 3), OStmt.push true)} := by
        rw [hhead]; rfl
      rw [hstep]
      cases b <;> simp
    · refine ⟨((0 : Fin 3), OStmt.move Turing.Dir.right), ?_, ?_⟩
      · have hstep : bgsMachine.step 1
            (Tape.mk' L (ListBlank.mk ((a :: l').map some))).head (B (buf ++ [b]))
            = {((0 : Fin 3), OStmt.move Turing.Dir.right)} := rfl
        rw [hstep]
        exact Finset.mem_singleton_self _
      · simp only [OTM.act]
        rw [hmove]
    · simp only [List.length_cons, hqs, List.length_cons]
      omega

/--
**The converse: only members are accepted.**  Inverting an accepting run.  The two clauses
are the invariants for the two live states: in state `0` the machine still has to guess a
bit for the current cell, in state `1` it has already pushed one.
-/
theorem bgsMachine_not_halted_one (B : Oracle) (T : Tape Sym) (buf : List Bool) :
    ¬ bgsMachine.Halted B ((1 : Fin 3), T, buf) := by
  intro h
  have h' : bgsMachine.step 1 T.head (B buf) = ∅ := h
  have hm : ((0 : Fin 3), OStmt.move Turing.Dir.right) ∈ bgsMachine.step 1 T.head (B buf) :=
    Finset.mem_singleton_self _
  rw [h'] at hm
  exact absurd hm (Finset.notMem_empty _)

theorem bgsMachine_not_halted_zero (B : Oracle) (T : Tape Sym) (buf : List Bool) (s : Bool)
    (hs : T.head = some s) : ¬ bgsMachine.Halted B ((0 : Fin 3), T, buf) := by
  intro h
  have h' : bgsMachine.step 0 T.head (B buf) = ∅ := h
  rw [hs] at h'
  have hm : ((1 : Fin 3), OStmt.push false) ∈ bgsMachine.step 0 (some s) (B buf) := by
    simp [bgsMachine]
  rw [h'] at hm
  exact absurd hm (Finset.notMem_empty _)

theorem bgs_inv (B : Oracle) : ∀ {c₀ c : bgsMachine.Cfg} {qs : List (List Bool)},
    bgsMachine.Run B c₀ c qs → bgsMachine.Accepting B c →
      ∀ (L : ListBlank Sym) (l buf : List Bool),
        (c₀ = ((0 : Fin 3), Tape.mk' L (ListBlank.mk (l.map some)), buf) →
          ∃ w, w.length = l.length ∧ B (buf ++ w) = true) ∧
        (c₀ = ((1 : Fin 3), Tape.mk' L (ListBlank.mk (l.map some)), buf) →
          ∃ w, w.length = l.length - 1 ∧ B (buf ++ w) = true) := by
  intro c₀ c qs r
  induction r with
  | refl c₀ =>
    -- an accepting configuration is halted, and states `0` and `1` are not
    intro hacc L l buf
    constructor
    · intro h0
      exfalso
      rw [h0] at hacc
      exact bgsMachine_not_halted_zero B _ buf true hacc.2 hacc.1
    · intro h1
      exfalso
      rw [h1] at hacc
      exact bgsMachine_not_halted_one B _ buf hacc.1
  | @step c₁ c₂ c₃ qs' hs r' ih =>
    intro hacc L l buf
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · subst h0
      obtain ⟨y, hy, rfl⟩ := hs
      cases l with
      | nil =>
        -- at the blank: a step exists only if the oracle said yes
        refine ⟨[], by simp, ?_⟩
        rw [List.append_nil]
        by_cases hB : B buf = true
        · exact hB
        · exfalso
          have hB0 : B buf = false := by simpa using hB
          have h' : y ∈ bgsMachine.step 0
              (Tape.mk' L (ListBlank.mk (([] : List Bool).map some))).head (B buf) := hy
          rw [show (Tape.mk' L (ListBlank.mk (([] : List Bool).map some))).head = none from rfl,
            hB0] at h'
          simp [bgsMachine] at h'
      | cons a l' =>
        -- guess a bit, landing in state `1`
        have hhd : (Tape.mk' L (ListBlank.mk ((a :: l').map some))).head = some a := by simp
        have h' : y ∈ bgsMachine.step 0 (some a) (B buf) := by rw [← hhd]; exact hy
        obtain ⟨b, rfl⟩ : ∃ b, y = ((1 : Fin 3), OStmt.push b) := by
          simp only [bgsMachine, bgsStep_zero_some, Finset.mem_insert,
            Finset.mem_singleton] at h'
          rcases h' with rfl | rfl
          · exact ⟨false, rfl⟩
          · exact ⟨true, rfl⟩
        obtain ⟨w, hwlen, hwB⟩ := (ih hacc L (a :: l') (buf ++ [b])).2 rfl
        refine ⟨b :: w, by simp at hwlen ⊢; omega, ?_⟩
        rw [show buf ++ b :: w = (buf ++ [b]) ++ w by simp]
        exact hwB
    · subst h1
      obtain ⟨y, hy, rfl⟩ := hs
      obtain rfl : y = ((0 : Fin 3), OStmt.move Turing.Dir.right) := by
        have h' : y ∈ bgsMachine.step 1
            (Tape.mk' L (ListBlank.mk (l.map some))).head (B buf) := hy
        simpa [bgsMachine] using h'
      cases l with
      | nil =>
        obtain ⟨w, hwlen, hwB⟩ :=
          (ih hacc (ListBlank.cons (default : Sym) L) [] buf).1 rfl
        exact ⟨w, by simpa using hwlen, hwB⟩
      | cons a l' =>
        obtain ⟨w, hwlen, hwB⟩ :=
          (ih hacc (ListBlank.cons (some a) L) l' buf).1 rfl
        exact ⟨w, by simpa using hwlen, hwB⟩

/-- **One direction of `bgsLang B ∈ NPᴮ`**: every member is accepted inside the bound. -/
theorem bgsMachine_accepts (B : Oracle) (x : List Bool) (h : bgsLang B x = true) :
    bgsMachine.Accepts B (polyBound 1 2 x.length) x := by
  obtain ⟨w, hwlen, hBw⟩ := (bgsLang_eq_true_iff B x).1 h
  obtain ⟨c, qs, hrun, hqs, hacc⟩ :=
    bgs_run B x w (ListBlank.mk []) [] hwlen (by simpa using hBw)
  refine ⟨c, qs, hrun, ?_, hacc⟩
  rw [hqs]
  simp only [polyBound, pow_one]
  omega

/--
**`bgsLang B ∈ NPᴮ`.**  The guessing machine decides it within the bound
`2(n+1) + 2`, in both directions.
-/
theorem bgsLang_inNPRel (B : Oracle) : InNPRel B (bgsLang B) := by
  refine ⟨bgsMachine, 1, 2, fun x => ⟨bgsMachine_accepts B x, ?_⟩⟩
  rintro ⟨c, qs, hrun, -, hacc⟩
  rw [bgsLang_eq_true_iff]
  obtain ⟨w, hwlen, hwB⟩ := (bgs_inv B hrun hacc (ListBlank.mk []) x []).1 rfl
  exact ⟨w, hwlen, by simpa using hwB⟩

/--
**The two halves of a diagonalisation stage, combined.**  For a deterministic machine with
a `t`-step budget, if `2ⁿ` exceeds the budget then there is a string of length `n` the
machine never consults, and flipping the oracle there alone cannot turn a rejection into an
acceptance.  This is the move the stage construction makes at every stage.
-/
theorem exists_flip (N : OTM) (hdet : N.Det) (B : Oracle) (t n : ℕ) (x : List Bool)
    (hn : t + 1 < 2 ^ n) (hno : ¬ N.Accepts B t x) :
    ∃ w : List Bool, w.length = n ∧ w ∉ N.qlist B t (N.init x) ∧
      ∀ B' : Oracle, (∀ s, s ≠ w → B s = B' s) → ¬ N.Accepts B' t x := by
  obtain ⟨w, hwlen, hwmem⟩ :=
    exists_unqueried (N.qlist B t (N.init x)) n
      (lt_of_le_of_lt (N.qlist_length_le B t (N.init x)) hn)
  refine ⟨w, hwlen, hwmem, fun B' hagree => ?_⟩
  refine N.not_accepts_congr hdet (fun s hs => hagree s ?_) hno
  intro hsw
  exact hwmem (hsw ▸ hs)

end PvsNP.Relativization
