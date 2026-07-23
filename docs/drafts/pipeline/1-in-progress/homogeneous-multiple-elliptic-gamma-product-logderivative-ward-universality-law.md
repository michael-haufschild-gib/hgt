# Homogeneous multiple elliptic-Gamma product/log-derivative Ward universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; CLASSICAL SPECIAL-FUNCTION INGREDIENTS]`

## Lean-derived conjecture

`HTGeometry/HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw.lean`
imports and uses the full product scale/reflection theorem, but its terminal theorem retains only
hypertranscendence and logarithmic-derivative fields.  The product parity covariance and both
radial Ward jets are dropped.

The missing capstone should retain all six simultaneous consequences of one rank-three normalized
period minor:

- hypertranscendence of product and logarithmic derivative;
- common-scale parity reflection of the homogeneous product;
- zero radial derivative for reflected and unreflected product scale orbits;
- homogeneous weight `-1` for the logarithmic derivative;
- parity reflection of the logarithmic derivative.

## Corpus inputs

- `GaloisForLFunctions.homogeneousMultipleEllipticGamma_scaleReflectionHypertranscendenceUniversality`
- `GaloisForLFunctions.homogeneousMultipleEllipticGamma_logDerivativeScaleReflectionUniversality`

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof targeted searches covered Barnes and multiple elliptic Gamma homogeneity, reflection
formulae, logarithmic derivatives, and period scaling.  Nearby literature establishes
representations and reflection/derivative identities for Barnes-type functions, but no source
found states the exact six-field package under the rank-three-minor hypertranscendence hypothesis:

- Noronha, *Representations for the derivative at zero and finite parts of the Barnes zeta
  function*, arXiv:1703.04817, treats homogeneous Barnes zeta/Gamma representations:
  <https://arxiv.org/abs/1703.04817>
- Hu--Kim, *On p-adic multiple Barnes-Euler zeta functions and the corresponding log gamma
  functions*, arXiv:1703.05434, treats reflection and derivative formulae in a different
  Barnes-Euler setting:
  <https://arxiv.org/abs/1703.05434>

Verdict: individual homogeneity/reflection phenomena belong to classical special-function
theory.  Exact product/log-derivative/Ward/hypertranscendence capstone is absent from the Lean
corpus and was not found in targeted literature.  Novelty claim is restricted to this joint
formulation.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw.lean`

## Verification

- source proof exact, warning-free:
  `lake env lean GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw.lean`
- umbrella already imports target module
- final module build deferred to terminal audit
