# Rational Euler rigidity at one prime

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Obstacle:** O11; strengthening of accepted contribution 1, not an additional count.

## Statement

Let `p` be prime and `P(x)=∏(1−αx)`, `Q(x)=∏(1−βx)` be reduced finite products with nonzero roots. There are no nonconstant such products for which both hold:

1. `e^(cs) ξ(s) P(p⁻ˢ)/Q(p⁻ˢ)` extends to an entire function invariant under `s ↦ 1−s`, for some `c∈ℂ`.
2. `ζ(s)P(p⁻ˢ)/Q(p⁻ˢ)=exp(Σ b(n)n⁻ˢ)` on a right half-plane, with absolute convergence and `Re b(n)≥0`.

Only a right-half-plane identity with the entire completion is required. No Selberg growth bound or assumption on the zeros of ζ enters.

## Proof

1. **One-sided power sums.** Normalize every nonzero root to its phase and send zero to 1. Simultaneous phase return makes `Re αⁿ≥|α|ⁿ/2` for every root at arbitrarily late positive exponents. An exterior root therefore makes the real power sums exceed every bound beyond every cutoff. Conversely, roots in the unit disk give the uniform bound by their number.
2. **Actual logarithm.** The finite Taylor logarithms converge absolutely on a sufficiently far right half-plane. Exponentiating gives the actual polynomial Euler modification. Logarithmic Dirichlet-series uniqueness fixes its repeated-prime coefficients as `(1−Σαᵏ)/k`. Nonnegativity forces all numerator roots into the unit disk.
3. **No denominator.** Holomorphic identity extends `Q(p⁻ˢ)F(s)=e^(cs)P(p⁻ˢ)ξ(s)` globally. Every nonzero Euler-coordinate fibre contains a point where ξ is nonzero. A denominator root thus forces a numerator root at the same coordinate, contradicting reduction. Hence `Q=1`.
4. **Reflection.** For a numerator root α, choose `s` in its fibre with `ξ(s)≠0`. Reflection of the completed zero supplies a numerator root δ at `1−s`. The two Euler coordinates multiply to `p⁻¹`, so `αδ=p`. Their unit-disk bounds contradict `p>1`. Hence `P=1`.

## Corpus connection and exact survivor

`BoundedImagesCertifyPurity.exists_simultaneous_return`, `DirichletSeries.coeff_eq_of_exp_lSeries_eq`, and `InfiniteRankPurityTheory.exists_zero_localFactor_not_zero` join finite-spectrum recurrence, logarithmic arithmetic and ξ's aperiodicity.

The positive survivor is exact: eventual boundedness above of the real power sums is equivalent to all roots lying in the closed unit disk. An exterior root forces negative actual logarithmic coefficients beyond every cutoff. Entire continuation separately forces cancellation of every rational denominator root.

`BoundedImagesCertifyPurity` bounds absolute power sums; `FinitePrimeRigidity` assumes the strict Selberg Euler bound. Neither supplies this one-sided logarithmic sign criterion. Internal overlap was checked; no external literature audit requested.

## Lean declarations

- `ZeroConfigurationGeometry/OneSidedPowerSumsDetectEveryExteriorRoot.lean`: `roots_norm_le_one_iff_eventually_re_powerSum_bounded`.
- `SelbergClass/FiniteEulerLogarithmicPositivity.lean`: `exists_negative_logCoeff`, `coeff_prime_pow_eq`, `norm_le_one_of_nonnegative_logarithm`.
- `SelbergClass/RationalEulerTwinsCannotHavePositiveLogarithms.lean`: `denominator_eq_zero`, `rational_twin_rigidity`, `not_exists_nontrivial_positive_rational_twin`.

All three modules passed final plain `lake --old env lean` checks and are umbrella-wired. Axiom checks skipped at user request. Scope: rational functions of one Euler coordinate `p⁻ˢ`. Simultaneous edits at several primes and arbitrary rational-in-`s` Beurling modifications remain outside the theorem.
