# Definitional audit: Anthropic's VP ≠ VNP Lean formalization

*2026-11-25. Audited against [kim-em/vp-vnp](https://github.com/kim-em/vp-vnp), a fork of
`anthropics/formal-math@918c8e2:vp-vnp` bumped to Lean v4.37.0-rc1 with independent-kernel
CI. Upstream published 2026-11-23.*

## What this audit does and does not cover

The formalization is ~72,700 lines of Lean across `Statement/`, `Nc/`, `NS1/`, `Ov/`,
`Paper/`. A kernel can check all of it. What a kernel **cannot** check is whether the
formal statement says what the paper claims — and since Anthropic states that no human
mathematician has audited the proof, that was the open question worth attacking.

**This audit covers the statement only**: the 98 lines of `Statement.lean`, plus the
question of whether the statement that is *audited* is the same one that is *proved*. It
does not verify the mathematics. Nobody has.

**Finding: I could not find a definitional gap.** Where conventions differ from textbooks
the difference is immaterial at the scale involved, and where there is a genuine choice the
definitions are the *strong* one.

## The audit surface is smaller than it looks

The proof develops its own classes in `Nc/Final/CClasses.lean` (`Nc.Family`, `Nc.VP`,
`Nc.VNP`) and `Nc/LowDegree.lean` (`Nc.Computes`). A natural worry: the Statement-level
definitions a reader audits might not be the ones the proof actually uses.

They are. `Solution.lean` bridges them by **type ascription**:

```lean
theorem separation : Separation.{u} := fun F _ =>
  ⟨fun f hf => ((Paper.cor_allclasses F).1 (hf : toNc f ∈ Nc.VP F) : toNc f ∈ Nc.VNP F), …⟩
```

`hf : f ∈ Statement.VP F` is ascribed as `toNc f ∈ Nc.VP F`. For that to typecheck the two
propositions must be **definitionally equal** — so Lean itself verifies that the audited
definitions and the proved ones coincide. (Reading them confirms it: they are identical
modulo field names, `vars`/`X`, `r`/`m`, `g`/`q`.)

That is a good design decision, and it means the audit surface genuinely collapses to
`Statement.lean`.

## The five claimed theorems

From `comparator.json`, with `Challenge.lean` stating them as `sorry` and `Solution.lean`
discharging each:

| Theorem | Content |
|---|---|
| `mainTheorem` | superpolynomial gate lower bound for `hc` over every field; for `perm` when char ≠ 2 |
| `mainTheoremApprox` | same, for circuits that only *approximate* |
| `separation` | `∀ F [Field F], VP F ⊂ VNP F` |
| `separationClosure` | `∀ F [Field F], ¬ VNP F ⊆ VPBar F` |
| `permanent_over_real` | the headline special case: permanent over ℝ |

Note `separation` uses `⊂` (strict), so it carries **both** `VP ⊆ VNP` and `VP ≠ VNP` —
the full conjecture, not just non-inclusion.

## Definition-by-definition

### `Computes f s` — circuit size

```lean
∃ l : ℕ → MvPolynomial V R,
  (∀ k < s, (∃ v, l k = X v) ∨ (∃ a, l k = C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)) ∧
  ∃ k < s, l k = f
```

A straight-line program of length `s`: gate `k` is a variable, a constant, or the sum or
product of two **strictly earlier** gates, and `f` appears among the first `s`. Gate 0 is
forced to be a leaf. No cycles possible. This is exactly size-`s` SLP computability — the
arbitrary function `l` can't smuggle anything, since every index below `s` is constrained.

Three conventions to note:

- **Inputs and constants count as gates.** This makes the lower bound *weaker* than the
  arithmetic-gates-only convention, by at most an additive `m²`. The bound proved is
  superpolynomial, so the difference is immaterial.
- **Arbitrary constants from `F` are free.** This is Valiant's `VP`, not constant-free
  `VP⁰`. More constants ⇒ stronger lower bound. Correct choice.
- **Division-free.** Standard for `VP`.

### `perm` and `hc`

```lean
perm F m = ∑ σ : Equiv.Perm (Fin m), ∏ i, X (σ i, i)
hc   F m = ∑ σ with σ.IsCycleOn Set.univ, ∏ i, X (i, σ i)
```

Permanent of the generic `m × m` matrix (`m²` distinct variables, no signs — the signs
would make it the determinant). Hamiltonian-cycle polynomial as the sum over
single-cycle permutations. Both standard.

### `Beyond c m s` — the bound

```lean
(m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s
```

`m ^ (c · (log₂ m)^{1/3})` = `2 ^ (c · (log₂ m)^{4/3})`. Since
`(log₂ m)^{4/3} / log₂ m = (log₂ m)^{1/3} → ∞`, this is **superpolynomial** — and
superpolynomial is exactly what `VP ≠ VNP` needs, since `VP` caps size at `n^a + a`. It is
sub-exponential, which is fine: the conjecture asks for superpolynomial, not exponential.

### `VP`, `VNP`

```lean
VP  = {f | ∃ a, ∀ n, card (f.vars n) ≤ n^a + a ∧ (f.poly n).totalDegree ≤ n^a + a ∧
                     Computes (f.poly n) (n^a + a)}
VNP = {f | ∃ r g, ⟨fun n => f.vars n ⊕ Fin (r n), g⟩ ∈ VP F ∧
                  ∀ n, f.poly n = ∑ e : Fin (r n) → Bool, aeval (Sum.elim X …) (g n)}
```

`VP` carries all three of Valiant's bounds: variable count, **total degree**, and circuit
size. The degree bound is present and matters — without it `VP` would be the wrong class.

`VNP` is `f n = ∑_{e ∈ {0,1}^{r n}} g n (x, e)` for `g ∈ VP`. The polynomial bound on
`r n` is not stated separately but **follows**, because `g`'s family being in `VP` forces
`card (vars n ⊕ Fin (r n)) ≤ n^a + a` and `card (A ⊕ B) ≥ card B`. Neat, and correct.

`VP ⊆ VNP` is witnessed by `r = 0` (a single empty assignment), so the `⊂` is meaningful.

### The characteristic-2 carve-out

`mainTheorem` claims the bound for `hc` over every field, but for `perm` **only when
char ≠ 2**. This is a sign of care, not a gap: in characteristic 2 the permanent equals the
determinant, which *is* in `VP`, so the permanent genuinely is not hard there. Claiming
otherwise would have been a red flag. `hc` is the right family to carry all
characteristics.

### The closure version

`VPBar` uses `Approximates`: a circuit over `LaurentSeries F` computing `q` with
`q = f + ε·(…)`, formalized as "coefficients of `ε^i` vanish for `i < 0`, and equal `f`'s at
`i = 0`". That is the standard border/approximative-complexity notion.

`SeparationClosure : ¬ VNP F ⊆ VPBar F` is **strictly stronger** than `VP ≠ VNP`, since
`VP ⊆ VPBar`. Worth flagging: a border-complexity separation is closer to what Geometric
Complexity Theory aims at, so if this survives scrutiny it is the more consequential of the
two statements.

## Residual risk

1. **The mathematics is unaudited.** ~72,700 lines. The kernel checks it; no human has
   read it. Three kernels agreeing (Lean, `con-leche`, `con-ron`, plus `nanoda`) is strong
   evidence against *implementation* error and no evidence at all about *conceptual*
   error — but there isn't much room for conceptual error in a statement this short once
   the kernel accepts the proof.
2. **Universe handling.** `Family.vars : ℕ → Type` (universe 0) with `F : Type u`;
   `Separation.{u}` is per-universe. Standard, but a reader wanting the absolutely general
   statement should notice the quantifier is over `Type u` for the instantiated `u`.
3. **This audit is one reader.** The value of a definitional audit scales with the number
   of independent readers; treat this as one data point, not a verdict.

## What this means for `pnp-lean`

- **`VP ≠ VNP` does not imply `P ≠ NP`.** The upstream README says so explicitly, and
  nothing in `PvsNP/Conjecture.lean` needs revising on that account.
- The directly reusable artifact is `Statement.Computes` — a now kernel-exercised
  definition of arithmetic circuit size. If this repo ever wants to state algebraic circuit
  lower bounds for its own polynomials (e.g. about `Determinant.colorCoeff`), that is the
  definition to copy. Upstream does not accept contributions, so copy with attribution
  rather than depend.
- The connection to `PvsNP/Determinant.lean` is thematic, not technical:
  `Determinant.coeff_det` is a combinatorial identity about a determinant's coefficient,
  whereas this work is a *size* lower bound for `perm`/`hc`. Different kinds of statement
  about neighbouring objects.
