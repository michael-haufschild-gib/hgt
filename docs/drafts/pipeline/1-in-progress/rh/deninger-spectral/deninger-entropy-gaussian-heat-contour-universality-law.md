# Deninger entropy/Gaussian heat-contour universality law

Status: Stage 2 — dependency-closed paper proof; Lean formalization in progress  
Lean target: `GaloisForLFunctions.RHTower.Deninger.DeningerEntropyGaussianHeatContourUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`DeningerEntropyProductionThermodynamicLimitUniversalityLaw` proves that a pointwise finite
Hermitian KMS entropy-production realization of the Deninger divisor resolvent forces source and
cohomological passivity, the one-Cauchy gate, and RH.

`DeningerGaussianLefschetzHeatContourUniversalityLaw` proves that RH is sufficient for every
complex-time Xi Gaussian heat trace in the open right heat half-plane to admit arbitrarily accurate
Deninger-resolvent contour approximants with the sharp inherited vertical norm bound.

`XiWholeCorpusPositivePhaseUniversalityLaw` identifies RH with the parameter-uniform product of
eighteen terminal analytic, geometric, Hankel, dyadic, local, seam, Hurwitz, thermal, Sonin, and
Krylov certificate families.

No corpus theorem feeds the RH output of the first mechanism into both the complete terminal phase
and the all-complex-time contour reconstruction of the second.

## Statement

For every finite Hermitian KMS sequence whose passive responses converge pointwise to the Deninger
divisor resolvent on the admissible centered strip:

1. the same responses converge to the continued prime--archimedean source;
2. source and Deninger divisor responses are upper anti-Herglotz;
3. the one-Cauchy diagonal gate is nonnegative;
4. RH holds;
5. every admissibly parameterized eighteen-family whole-corpus positive certificate holds;
6. for every complex heat time with positive real part and every positive error, a Deninger
   Gaussian contour approximates the complete Xi heat trace within that error and has norm strictly
   below the real heat trace plus the same error.

## Dependency-closed proof

Apply `deninger_entropyProductionThermodynamicLimitUniversality` to obtain the source limit,
passivity statements, Cauchy gate, and RH. Feed that RH proof into
`riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate` for arbitrary admissible
terminal parameters, and into
`deninger_gaussianLefschetz_heatContourUniversality` for arbitrary complex heat time and positive
error. Package the outputs.

No computation, spectral truncation assumption, or new positivity axiom is introduced.

## Novelty audit

Corpus audit: exact search found separate thermodynamic-limit, whole-corpus positive-phase, and
Gaussian-contour laws but no theorem closing finite KMS passivity into the complete terminal phase
and complex-time Deninger spectral reconstruction.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

Pending exact source check and final umbrella audit.
