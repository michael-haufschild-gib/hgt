# Central trace-Hankel positivity forces RH

- **ID:** central-trace-hankel-positivity
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean detector) + OPEN SOURCE LAW
- **Source:** actual centered xi-divisor trace spectrum and a source-side quadratic positivity law
- **Statement:** `[PROVED]` Every real-polynomial centered trace-Hankel quadratic value is
  nonnegative if and only if RH.  The difficult direction is formalized on the actual infinite
  divisor: trace-class outer isolation forces every reciprocal-square coordinate real, and the
  strict-strip geometry makes it positive.  `[OPEN CORE]` derive this positivity law from a fixed
  prime-archimedean or theta source without assuming an equivalent spectral-location statement.

## Goal

Replace per-zero window hypotheses by one target-free positivity statement whose spectrum, weights, convergence, and symmetries are already unconditional. The result is useful only with an unconditional prime-archimedean or theta provider for the quadratic positivity; an equivalence alone is not the endpoint.

## Gates

- [x] 0 → 1 in-progress: the actual trace-class spectrum is formalized and the finite-outer isolation mechanism is explicit
- [x] 1 → 2 fully-proven: polynomial isolation for finite and summable conjugation-stable spectra proves the reality converse
- [x] 2 → 3 formalized: `TraceHankelConverse.lean` and `XiTraceHankelCriterion.lean` specialize the converse to the actual xi divisor and prove the exact RH equivalence
- [ ] 3 → 4 publication-ready: prove the quadratic positivity from the fixed prime-archimedean or theta source and derive RH with no hypothesis

## Approach

For a hypothetical nonreal coordinate `alpha`, let `r = norm alpha`. Trace-class summability makes
the set of coordinates of norm at least `r` finite. A real polynomial product kills every point on
or outside that radius except the pair `{alpha, conj alpha}`. A real affine phase corrector and
`(z/r)^n` make the selected pair's quadratic contribution strictly negative. Dominated convergence
kills the inner spectrum, contradicting positivity. The actual xi divisor has no real-axis zeros,
so real reciprocal-square coordinates are positive and correspond exactly to critical-line zeros.

Lean certificates: `finite_traceHankel_nonneg_implies_real`,
`xi_central_spectrum_real_of_traceHankel_nonnegative`,
`riemannHypothesis_of_xiCentralTraceHankelNonnegative`,
`xiCentralTraceHankelNonnegative_of_riemannHypothesis`, and
`xiCentralTraceHankelNonnegative_iff_riemannHypothesis`.

## Open core

`[OPEN CORE]` Establish the quadratic positivity itself from the fixed completed source, without assuming RH, Laguerre-Pólya membership, a Herglotz realization, or an equivalent spectral-location statement.

## Log

- 2026-07-10 — detector completed in Lean, including the infinite dominated-convergence argument
  and reverse RH implication; only the independent source-side positivity law remains open.
