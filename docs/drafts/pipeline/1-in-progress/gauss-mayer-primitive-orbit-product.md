# Actual Mayer determinant and primitive modular orbits

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [three approaches, A](argon-three-orthogonal-rh-approaches.md).
- **Inputs:** [power traces](../3-formalized/gauss-mayer-countable-word-traces.md), [primitive modular coding](../3-formalized/gauss-mayer-modular-primitive-coding.md).

## Target

Let `D(w,z)` be the actual Mayer Fredholm determinant. Let `c` range over
nonempty primitive digit-pair cycles, with pair length `ℓ(c)` and expanding
matrix multiplier `λ_c>1`. Prove, initially for `Re w>1` and sufficiently
small `|z|`, the absolutely convergent identity

```text
D(w,z) D(w,−z) = ∏_c ∏_(m≥0) (1−z^(2ℓ(c)) λ_c^(−w−2m)).
```

Then establish convergence at `z=1` on `Re w>2`. The certified conjugacy and
root classification should identify these cycles with primitive positive-trace
hyperbolic integral determinant-one classes. Inverse classes remain distinct
unless the proved inverse-class criterion identifies them.

## Exact missing mathematics

1. **Certified:** The actual signed determinant product equals its even-word
   trace exponential near zero, with absolute summation over all lengths and
   words. [Paper proof and Lean certificate](../3-formalized/gauss-mayer-even-word-determinant.md).
2. Decompose every nonempty pair word into a primitive cycle and a repetition.
   Prove that a repetition of a primitive pair word of length `ℓ` has exactly
   `ℓ` distinct pair rotations. Ordinary digit primitivity is incorrect.
3. Prove multiplier invariance under pair rotation and the exact power law
   under repetition. Reindex the absolutely convergent even-word trace series:
   its coefficient `1/n` must become `1/r` for a primitive cycle repeated `r`
   times. Expand `(1−λ_c^(−2r))⁻¹` and sum the logarithmic factor series.
4. **Certified:** Exact Gauss-word probability gives geometric absolute trace
   decay for `Re w>2`. The even-word identity now holds throughout `|z|≤1`,
   including `z=1`; the full word series converges absolutely and the actual
   determinant has no spectral zero in this disk.
   [Continuation proof and Lean certificate](../3-formalized/gauss-mayer-unit-even-word-determinant.md).

The local Hilbert–Schmidt exponential determinant is a convergent-series
representation only near zero. Its totalized exponential cannot replace the
global Fredholm determinant away from that domain.

## Certified source probability and decay

The bottom-row weight `P=1/[d(c+d)]` has total mass one over all words of
every fixed length. Its exact successor telescope and `0≤c≤d` give
`Σ d⁻²≤2`. Each digit pair doubles the denominator, so `d≥2^n` at length
`2n`. The actual expanding multiplier satisfies `λ≥d`.

For `Re w>2`, `q=exp(−(Re w−2)log 2)∈(0,1)` and the complete absolute
trace mass at length `2n+2` is at most `(8/3)q^(n+1)`.
[Paper proof and nine clean production audits](../3-formalized/gauss-mayer-word-probability-and-trace-decay.md).

## Scope

This is the missing determinant-to-modular-cycle bridge. It does not yet
identify geometric geodesic lengths, prove the scattering normalization, or
exclude complex resonances. The local determinant-to-even-word identity is
certified through the closed unit disk for `Re w>2`; primitive-cycle
reindexing and the Euler product remain open.
