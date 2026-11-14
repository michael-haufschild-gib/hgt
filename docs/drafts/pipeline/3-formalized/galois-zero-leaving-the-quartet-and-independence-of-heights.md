# Leaving the quartet; independence of heights

- **ID:** gtz-leaving-the-quartet-and-independence-of-heights
- **Stage:** 3-formalized
- **Type:** THEOREM (reduction + independence)
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, problems 1 and 2 (review-1411 §2.19).
- **Statement:** `G = Gal(E/B)`, `ρ = β + iγ`, quartet `Q(ρ) = {ρ, ρ̄, 1−ρ, 1−ρ̄}`.
  (A) if `σρ ∉ Q(ρ)` then `β ≠ ½`, `|Im σρ| = |γ|`, `Re σρ ∉ {½, β, 1 − β}`;
  (B) if every off-line zero of absolute ordinate `|γ|` has real part `β` or `1 − β`, then the
  orbit lies in `Q(ρ)` and `u + v, uv ∈ B` (ordinate and width values);
  (C) if `2cos(2γ log q) ∈ B` for one prime `q`, then `σ(p^{2β}) = p^{2 Re σρ}` for all `σ`, and
  the orbit lies in `Q(ρ)` iff every conjugate of `p^{2β}` is `p^{2β}` or `p^{2−2β}`;
  (D) for a finite set `S` of nonnegative heights and `a : ℝ → ℂ`: if `Σ_{t∈S} a_t T_t(m) = 0`
  for all prime vectors `m`, then `a_t = 0` at every `t ∈ S` carrying a zero.

## Goal

Problem 2 asked for the orbits that leave the quartet: (A)/(B) reduce leaving to a coincidence of
absolute ordinates of two distinct off-line quartets (a statement on the zero configuration);
(C) reads the orbit off the conjugates of the weight value when conjugation is central.
Problem 1 asked for relations among traces of different heights: (D) excludes all linear ones.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

(A) Height is kept; a critical `ρ` has orbit `{ρ, ρ̄}`; an orbit meets the line only if it starts
there; outside `Q(ρ)` the real part differs from `β, 1 − β` (`|Im|` fixed). (B) contrapositive.
(C) `σρ̄ = conj σρ` (ordinate criterion) gives `σ(ρ + ρ̄) = σρ + conj σρ`; `p^x` is injective on
reals. (D) `T_t = Σ_{copies q} χ_q` with `χ_q(m) = n_m^q`; distinct zeros give distinct
characters (two primes); Dedekind independence makes `Σ_t a_t Σ_q δ_{χ_q} = 0`; the coefficient
at `χ_ρ`, `Im ρ = t₀ ∈ S`, is `a_{t₀}·#copies(ρ)`, because no other nonnegative height carries
`ρ`. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A, B | `AnOrbitLeavesItsQuartetOnlyThroughAnotherOffLineQuartetOfTheSameOrdinate` | `exists_offLine_of_not_mem_quartet`, `mem_quartet_of_offLine_unique`, `sum_prod_mem_of_offLine_unique` |
| C | same | `primeTraceExponentHom_weight_of_conj`, `primeWeightValue_map_of_ordinate_mem`, `primeWeightValue_eq_iff`, `mem_quartet_iff_weight_conjugates` |
| D | `TheTracesOfDistinctHeightsAreLinearlyIndependent` | `trace_coeff_eq_zero` |

## Open

Algebraic (non-linear) relations among the traces of different heights; whether two off-line
quartets can share an ordinate.
