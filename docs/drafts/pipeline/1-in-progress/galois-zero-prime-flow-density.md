# Prime-time density in the integral zero motive

- **ID:** galois-zero-prime-flow-density
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Questions:** Arithmetic observables of the full zero motive; exact relations at prime times.

## Target

For the full original integer zero group `Δ⊆ℂ`, construct its coordinate
algebra `ℂ[Δ]` and identify its complex algebra points with all characters
`Δ→ℂˣ`. Evaluate it on the exponential characters
`χᵤ(z)=exp(uz)`. Prove that evaluation at all prime times `u=log p`
is injective. Thus prime-time points are Zariski dense in the full
possibly infinite-dimensional diagonalizable zero motive.

Translate this into an exact criterion for polynomial identities among
`p^ρ`: coefficients cancel precisely among monomials with equal sums of
zero exponents. These are the actual additive zero relations, with no
independence premise and no bounded-height replacement.

## Paper argument

The universal property of the group algebra identifies algebra maps to
`ℂ` with multiplicative characters of `Δ`. Basis elements are units, with
inverse indexed by the negative exponent, so every algebra point gives
values in `ℂˣ`.

A coordinate-algebra element is a finite sum `F(t)=Σ c_z exp(tz)` with
distinct `z∈Δ`. It is entire of finite exponential type. If it vanishes at
every `log p`, prime-log uniqueness gives `F=0`. Distinct exponential
functions are linearly independent by independence of multiplicative
characters. Hence every coefficient vanishes.

Corpus inputs: `RHTower.eq_zero_of_exponentialType_of_primeLog_zeros`
uses Jensen's linear zero-count bound and Chebyshev's prime-count lower
bound. `HTGeometry.exp_coeff_eq_zero_of_sum_eq_zero` supplies independence
of finite exponential families. Both source statements and proofs were inspected.

## Boundary

This is faithful algebraic sampling, not a bounded inverse or a purity
criterion. It does not determine the actual integer relation group.
