# Finite-prime rational Euler rigidity

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** O11; strengthening of accepted contribution 1, not separately counted.
- **Statement:** No nontrivial reduced product of rational modifications in `p⁻ˢ`, over a finite
  set of rational primes, has both an entire reflection-symmetric completion and an absolutely
  convergent logarithmic Dirichlet series with nonnegative real coefficients.

## Stronger conclusion

Write the local numerator and denominator as products of `1−a p⁻ˢ`, with nonzero parameters
and no common numerator/denominator root at the same prime. Every nontrivial edit with an
entire reflected completion and any absolutely convergent logarithmic representation has a
fixed edited prime `p` such that, beyond every cutoff, some `Re b(p^k)<0`.

## Proof and connection

1. The progression theorem for ξ gives infinitely many nonzeros in each nonzero Euler fibre.
   Prime-log independence, expressed by `subsingleton_resonantPrimes`, makes fibres of distinct
   primes intersect at most once. Finitely many numerator roots at other primes therefore
   cannot cover a denominator fibre. Reducedness excludes roots at the same prime, so every
   denominator is empty.
2. The canonical logarithm is the zeta logarithm plus the finite sum of local corrections.
   Distinct primes have disjoint positive prime-power supports. Logarithmic coefficient
   uniqueness gives `b(p^k)=(1−Σ_a a^k)/k` at every edited prime.
3. If every numerator parameter had modulus at most one, all numerator zeros would lie in
   `Re s≤0`. Choose one outside ξ's divisor. Reflection gives a zero in `Re s≥1`, where the
   numerator and ξ are nonzero: contradiction.
4. Hence some edited prime has a parameter outside the unit disk. The corpus power-sum
   recurrence forces negative local logarithmic coefficients at arbitrarily large exponents.

## Lean

All three modules passed final plain `lake --old env lean` checks and are umbrella-wired:

- `SelbergClass/FinitePrimeEulerFibres.lean`: `infinite_euler_fibre_xi_ne_zero`,
  `eulerCoordinates_separate`, `exists_euler_fibre_avoiding`.
- `SelbergClass/FinitePrimeEulerLogarithms.lean`: `finite_coeff_prime_pow_eq`,
  `finite_norm_le_one_of_nonnegative_logarithm`.
- `SelbergClass/FinitePrimeRationalEulerRigidity.lean`:
  `finite_rational_twin_has_negative_prime_power_logs`,
  `not_exists_nontrivial_positive_finite_rational_twin`.

Scope is a finite product of local rational functions. Mixed rational functions of several
Euler coordinates and modifications at infinitely many primes are not covered. No external
novelty search or axiom checks.
