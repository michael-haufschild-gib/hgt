# Central trace-Hankel positivity forces RH

- **ID:** central-trace-hankel-positivity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** actual centered xi-divisor trace spectrum and a source-side quadratic positivity law
- **Statement:** `[CONJECTURE]` If every real polynomial test has nonnegative centered trace-Hankel quadratic value on the actual xi divisor, then every centered reciprocal-square coordinate is positive real and RH follows.

## Goal

Replace per-zero window hypotheses by one target-free positivity statement whose spectrum, weights, convergence, and symmetries are already unconditional. The result is useful only with an unconditional prime-archimedean or theta provider for the quadratic positivity; an equivalence alone is not the endpoint.

## Gates

- [x] 0 → 1 in-progress: the actual trace-class spectrum is formalized and the finite-outer isolation mechanism is explicit
- [ ] 1 → 2 fully-proven: prove polynomial isolation for a summable conjugation-stable spectrum and the positivity-to-positive-real converse
- [ ] 2 → 3 formalized: specialize the converse to `xiCentralReciprocalSquare`
- [ ] 3 → 4 publication-ready: prove the quadratic positivity from the fixed prime-archimedean or theta source and derive RH with no hypothesis

## Approach

For a hypothetical nonreal coordinate `alpha`, let `r = norm alpha`. Trace-class summability makes the set of coordinates of norm at least `r` finite. A real polynomial product kills every point on or outside that radius except the pair `{alpha, conj alpha}`. Multiply it by a bounded real linear phase corrector and `(z/r)^n`. The inner spectrum tends to zero under a summable majorant, while the selected pair tends to a strictly negative quadratic contribution. Positivity forbids the pair. Since the actual xi divisor has no real zeros, all remaining real coordinates are automatically positive and correspond exactly to critical-line zeros.

## Open core

`[OPEN CORE]` Establish the quadratic positivity itself from the fixed completed source, without assuming RH, Laguerre-Pólya membership, a Herglotz realization, or an equivalent spectral-location statement.

## Log

- 2026-07-10 — started after formalizing trace-class centered xi moments, finite outer levels, strip support, and the exact real-coordinate/critical-line equivalence.
