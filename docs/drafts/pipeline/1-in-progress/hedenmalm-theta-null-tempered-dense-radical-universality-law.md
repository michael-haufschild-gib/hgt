# Hedenmalm theta-null tempered dense-radical universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/SchwartzSesquilinearTempered.lean`
  - `leftTemperedDistribution`
  - `leftTemperedDistribution_apply`
- `RHTower/HedenmalmUniversalPositiveFormClassification.lean`
  - `universalPositiveForm_theta_leftRadical_of_thetaNull`
  - `universalPositiveForm_identicallyZero_iff_canonicalMeasure_zero`
  - `universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_zero`
- `RHTower/XiThetaSchwartzL2Nonclosability.lean`
  - `xiThetaSchwartzTranslationOrbit_mem_leftRadical`
  - `dense_xiThetaL2RadicalImage`
  - `not_isClosed_xiThetaL2RadicalImage`

The generic HT interface curries continuous Schwartz forms into tempered distributions. The first
RHT theorem upgrades one scalar theta-diagonal equality to complete theta left-radical nullity.
The second RHT mechanism converts complete theta nullity into translation-orbit radical density
through ordinary-`L²` cyclicity. No existing module reconnects the scalar classifier to the orbit
and tempered-distribution conclusions.

## Universal law

For every nonnegative momentum-symmetric continuous Schwartz form, vanishing on the single theta
diagonal forces every curried tempered distribution to annihilate every real translate of the
completed theta source and makes the ordinary-`L²` radical image dense. If the form is nonzero,
its canonical divisor measure and some curried tempered distribution are nonzero, the radical
image is proper and nonclosed, and the form is not sequentially closable through ordinary `L²`.
Within the scalar theta-null cone, closability is equivalent to disappearance of the entire
curried tempered-distribution family.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/RHTower/HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
