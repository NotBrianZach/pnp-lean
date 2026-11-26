# P vs NP in Lean 4 — what the "primes, programs, and composition" argument does and does not give

**Bottom line: this does not prove `P ≠ NP`, and it does not prove `P = NP`.** The essay
that seeded it contains no proof of either, and neither does any known argument. What this
repository does is take every claim in the essay that *is* provable, prove it in Lean 4
with Mathlib, state `P ≠ NP` precisely, and then mark the gap mechanically so it cannot be
mistaken for progress.

The project builds with exactly **two** warnings, both deliberate: the two `sorry`s in
`PvsNP/Conjecture.lean` (`P_ne_NP`, `P_eq_NP`). Everything else is complete — including
the essay's general-`n` determinant criterion for three-dimensional matching, which is
proved in full in `PvsNP/Determinant.lean`.

## Build

```bash
export PATH=/nix/store/aidjqiqb58j26if2jq5h193dnzdw6dvv-elan-4.2.1/bin:$PATH
export ELAN_HOME=$HOME/.elan
lake exe cache get      # already done; ~7 GB of Mathlib oleans
lake build
```

Lean `v4.36.0`, Mathlib `v4.36.0`.

## Files

| File | Content |
| --- | --- |
| `PvsNP/Inventory.lean` | Inventories as the free commutative monoid; the prime encoding; the structural lower bound |
| `PvsNP/ExactCover.lean` | The prime-encoding reduction from Exact Cover, proved correct; the `{6,10,15,35}` example |
| `PvsNP/SelfReduction.lean` | Greedy deletion: search reduces to decision |
| `PvsNP/Matching.lean` | The colored square: no 3D matching, yet all three pairwise projections match; `r² − b²` |
| `PvsNP/Determinant.lean` | The general-`n` tagged determinant: its `z₁⋯zₙ` coefficient is nonzero iff a 3D matching exists |
| `PvsNP/Complexity.lean` | Nondeterministic Post-Turing machines; definitions of `P` and `NP`; `P ⊆ NP` |
| `PvsNP/Enumeration.lean` | Machines are finite data: `Countable NTM`, so `P` and `NP` are countable and proper |
| `PvsNP/Oracle.lean` | Oracle machines, relativized `Pᴮ`/`NPᴮ`, and the two lemmas every relativization argument runs on |
| `PvsNP/Conjecture.lean` | `P ≠ NP` stated, **not proved**, plus a written account of the barriers |
| `PvsNP/Audit.lean` | `#guard_msgs` over `#print axioms`: machine-checks which results are hole-free |

## Proved (no `sorry`, no axioms beyond `propext` / `Classical.choice` / `Quot.sound`)

- `Inventory.encode_add`, `Inventory.encode_injective` — the prime encoding
  `E u = ∏ pₐ^{u a}` is a monoid homomorphism from inventories under `+` to `ℕ` under `×`,
  and it is injective. `Inventory.factorization_encode` is the sharp form: the exponent of
  `pₐ` in `E u` is exactly `u a`.
- `Inventory.structural_lower_bound` / `Inventory.toPNatHom_injective` — the essay's
  conditional claim, in full: if a commutative monoid has countably many primitives whose
  distinct finite inventories stay distinguishable, it contains an injective copy of
  `(ℕ₊, ×)`.
- `Inventory.invMap_not_injective_of_idempotent` — the hypothesis is not free: one
  idempotent primitive collapses the counts `1` and `2`.
- `Inventory.comp_ne` — `x ↦ 2x` and `x ↦ x+1` compose differently in the two orders even
  though the inventory is `6` either way. Inventories record what was used, not how.
- `ExactCover.prod_eq_target_iff` — `∏_{j∈J} bⱼ = T` **iff** every observation lies in
  exactly one selected bundle. This is the number-theoretic core of the reduction.
- `ExactCover.Example.unique_solution` / `unique_exact_cover` — for the four-bundle
  instance with target `210`, `{A, D}` is the unique solution, by decision procedure.
- `SelfReduction.search_from_decision` — the greedy deletion loop, which asks one
  "does a cover still exist?" query per bundle, returns a set that *is* an exact cover.
- `Matching.pairwise_tests_insufficient` — the colored square has no three-dimensional
  matching, yet each of its three two-dimensional projections has a perfect matching. So
  no summary that keeps only the three pairwise yes/no answers can decide 3DM.
- `Matching.det_coeff_eq_zero` — the determinant `r² − b²` has zero `rb` coefficient;
  `Matching.rainbow_det_coeff_ne_zero` shows the test is not vacuous.
- `Determinant.coeff_det` — the essay's general construction, proved for every `n`: the
  coefficient of `z₁⋯zₙ` in `det(∑_{(i,j,k) allowed} w_{ijk} z_k)` is exactly the signed
  sum of tag monomials over solutions. `Determinant.colorCoeff_ne_zero_iff` is the
  non-cancellation step (`Determinant.tagExp_injective`: distinct selections carry
  distinct tag monomials), and `Determinant.coeff_det_ne_zero_iff` is the criterion:
  **nonzero coefficient ⟺ a three-dimensional matching exists**.
  `Determinant.ColoredSquare.coeff_eq_zero` rederives the hand computation above from the
  general theorem.
- `Complexity.InP.inNP` — `P ⊆ NP` in the model defined here.
- `Complexity.inP_const_true` / `inP_const_false` — the definitions are not empty.
- `Complexity.instCountableNTM` — a machine is finite data (`size`, `start`, and a finite
  transition table), so `NTM` is a countable type. With
  `Complexity.uncountable_lang` (Cantor) this gives `Complexity.countable_inNP`,
  `countable_inP`, and hence `exists_not_inNP` / `exists_not_inP`: the classes are proper,
  not just nonempty. Enumerability of machines is also the prerequisite for any
  diagonalisation argument (time hierarchy, Baker–Gill–Solovay).
- `Relativization.OTM.Run.congr` — **oracle sensitivity**: a run under `B` is a run under
  `B'`, whenever the two oracles agree on the strings that run consults. Every oracle
  argument rests on this.
- `Relativization.exists_unqueried` — **the pigeonhole**: a run consulting fewer than `2ⁿ`
  strings leaves some length-`n` string untouched, so the oracle can be redefined there
  without disturbing the computation. Plus `instCountableOTM` and `Pᴮ ⊆ NPᴮ`.
- `Relativization.OTM.not_accepts_congr` — **the diagonalisation step**: a *deterministic*
  machine that rejects still rejects after the oracle is changed away from the strings its
  own trajectory consults. Sensitivity alone doesn't give this (an accepting run under the
  new oracle might be exactly one that queries the changed string); ruling that out is
  what determinism buys, via a functional trajectory (`nextCfg`, `traj`, `qlist`,
  legitimised under `Det` by `mem_succs_iff`). `exists_flip` packages a whole stage, and
  `exists_enumeration` lists the candidates.
- `Relativization.bgsLang_inNPRel` — **`bgsLang B ∈ NPᴮ`**, both directions, via a
  three-state guessing machine: push a guessed bit per input cell, move right, then
  consult the oracle on the buffer at the blank. `bgs_run` builds the accepting run by
  induction on the remaining input (so the tape only ever moves one cell, no iterated-move
  reasoning); `bgs_inv` inverts an arbitrary accepting run.

## Not proved, deliberately

1. **NP-completeness of the arithmetic problem.** `prod_eq_target_iff` is about solutions,
   not cost. Formal NP-completeness needs a bit-string encoding, a machine that builds the
   primes and products inside a polynomial bound, and a reduction from a known-hard
   language. The essay's `O(n log n)`-bit observation is correct but is not a machine.
2. **The *cost* of the tagged-determinant criterion.** The criterion itself is proved, for
   every `n`. What is not proved — and is the entire difficulty — is any claim about how
   cheaply the coefficient can be extracted. The essay's inclusion–exclusion takes `2ⁿ`
   evaluations; compressing those is the open question. The criterion restates the hard
   problem, it does not reduce it.
3. **Baker–Gill–Solovay.** Every ingredient is in (`PvsNP/Oracle.lean`): the model,
   enumerability, sensitivity, the pigeonhole, `bgsLang B ∈ NPᴮ`, and one complete
   diagonalisation stage (`exists_flip`). Still missing: the recursion that *runs* the
   stages. Its bookkeeping is lengths `n 0 < n 1 < ⋯` with stage `i`'s budget `tᵢ`
   satisfying `tᵢ + 1 < 2^(n i)` and `n (i+1) > tᵢ`, so stage `i`'s queries all fall below
   what later stages touch. And — for the `Pᴬ = NPᴬ` half — `PSPACE` theory.
4. **`P ≠ NP`.** Not a missing lemma. Relativization (Baker–Gill–Solovay),
   natural proofs (Razborov–Rudich) and algebrization (Aaronson–Wigderson) each rule out
   a class of arguments that includes the ones sketched in the essay — in particular,
   algebrization bears directly on the determinant route, since that route is exactly an
   algebraic reformulation. `PvsNP/Conjecture.lean` spells this out.

## Modelling caveats

`P` and `NP` are defined over single-tape nondeterministic Post-Turing machines with
states `Fin size` and a finite transition table, alphabet `{blank, 0, 1}`, with acceptance
meaning "some path of length ≤ `c·(n+1)^k + c` reaches a halted configuration showing
`1`". Two standard facts are used informally and
are **not** theorems here: that this model is polynomially equivalent to multi-tape Turing
machines, and that nondeterministic polynomial time coincides with the
verifier/certificate definition of NP. Anything claimed about the Clay problem rather than
about this model depends on those two.

## Honest assessment of the starting intuition

The inventory argument is sound and now formal, but it is a statement about *structure*,
and it is independent of running time: `ℕ₊` under multiplication sits inside any system
that keeps independent multiplicities apart, and that fact is compatible with either
answer to `P` vs `NP`. The essay's own closing position is the accurate one — the
arithmetic model is expressive enough to *pose* the question, and posing it is not
answering it. The genuinely load-bearing observation in the essay is the negative one, now
proved as `Matching.pairwise_tests_insufficient`: local repair plus pairwise certificates
suffice for matching and demonstrably fail for 3DM. That is a lower bound against a
specific strategy, which is exactly what it claims to be.
