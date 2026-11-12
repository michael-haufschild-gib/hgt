# Prime-time density in the integral zero motive

- **ID:** galois-zero-prime-flow-density
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Arithmetic observables of the full zero motive; exact relations at prime times.

## Theorem

The full original integer zero group `Δ⊆ℂ` has coordinate algebra `ℂ[Δ]`.
Its complex algebra points are exactly the characters `Δ→ℂˣ`, and the
exponential flow corresponds to evaluation `[z]↦exp(uz)`.

Evaluation at prime times `u=log p` is injective after discarding any finite
set of primes. Thus every cofinite prime-time family is Zariski dense in
the coordinate-algebra sense. Every nonzero regular function has a prime
witness outside any prescribed finite exceptional set.

A polynomial identity among prime-time zero coordinates holds on a
cofinite prime family exactly when coefficients cancel among all monomials
with the same actual zero exponent sum. No independence of ordinates,
simplicity, or height cutoff is assumed.

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

Finite exceptions are removed by multiplying `F` by the polynomial
vanishing at their prime logarithms. This retains finite exponential type;
prime-log uniqueness kills the product, hence kills `F` by continuity on
the dense complement of the polynomial's finite zero set.

Corpus input `PrimeCancellation.eq_zero_of_exponentialType_of_cofinite_primeLog_zeros`
uses this argument with Jensen's linear zero-count bound and Chebyshev's
prime-count lower bound. `HTGeometry.exp_coeff_eq_zero_of_sum_eq_zero` supplies independence
of finite exponential families.

## Boundary

This is faithful algebraic sampling, not a bounded inverse or a purity
criterion. It does not determine the actual integer relation group.

## Formalization

`GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeTimePointsOfTheZeroMotive.lean`:

- `zeroMotivePointEquiv`, `zeroMotivePointEquiv_flow`.
- `primeZeroEvaluation_injective`, `zeroMotive_eq_iff_prime_values`.
- `primeZeroEvaluationOutside_injective`, `zeroMotive_nonzero_prime_witness`.
- `zeroMotiveCoordinates_monomial`, `zeroMotiveCoordinates_coefficient`.
- `zeroPolynomial_prime_relation_iff_grouped_coefficients`.
- `zeroPolynomial_cofinite_relation_iff_grouped_coefficients`.

Final source check passed. All 13 dependency audits use only `propext`,
`Classical.choice`, `Quot.sound`.
