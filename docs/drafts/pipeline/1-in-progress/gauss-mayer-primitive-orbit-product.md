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

1. Identify the global determinant with its locally convergent trace exponent,
   including the first trace and the sign cancellation in `D(w,z)D(w,−z)`.
2. Decompose every nonempty pair word into a primitive cycle and a repetition.
   Prove that a repetition of a primitive pair word of length `ℓ` has exactly
   `ℓ` distinct pair rotations. Ordinary digit primitivity is incorrect.
3. Prove multiplier invariance under pair rotation and the exact power law
   under repetition. Reindex the absolutely convergent even-word trace series:
   its coefficient `1/n` must become `1/r` for a primitive cycle repeated `r`
   times. Expand `(1−λ_c^(−2r))⁻¹` and sum the logarithmic factor series.
4. Supply a source estimate extending convergence to `z=1` for `Re w>2`;
   the existing fixed-length digit bound alone does not imply this.

The local Hilbert–Schmidt exponential determinant is a convergent-series
representation only near zero. Its totalized exponential cannot replace the
global Fredholm determinant away from that domain.

## Source estimate to formalize

For the real branch map, `h(x)=1/(1+x)` satisfies `L₂h=h` on `[0,1]`
by the telescoping series `Σ_(a≥1) 1/((a+x)(a+x+1))=1/(1+x)`.
An even word of length `2n` has bottom-right matrix entry `d≥2^n`:
each pair multiplies the positive denominator by at least two. Since
`1/2≤h≤1`, iteration gives `Σ_words d⁻²≤2`. Its expanding multiplier
satisfies `λ≥d`; therefore, for real `σ>2`,

```text
Σ_words λ^(−σ)/(1−λ⁻²) ≤ (8/3) 2^(−n(σ−2)).
```

This would supply absolute convergence of the complete even-word logarithm
at `|z|≤1`. An equivalent matrix-only telescope uses the bottom row `(c,d)`:
`P=1/[d(c+d)]`. Appending a Gauss digit on the right gives
`(c,d)↦(d,c+(a+1)d)` and

```text
Σ_(a≥0) 1/[(c+(a+1)d)(c+(a+2)d)] = 1/[d(c+d)].
```

Thus the exact word probability has total mass one at every length. The
certified inequality `0≤c≤d` gives `d⁻²≤2P`, avoiding an auxiliary analytic
realization of the harmonic function. Denominator growth and the complete
trace bound remain proof obligations, not yet Lean-certified results.

## Scope

This is the missing determinant-to-modular-cycle bridge. It does not yet
identify geometric geodesic lengths, prove the scattering normalization, or
exclude complex resonances. No product identity is certified yet.
