# Gaussian-metric Hermite stable-rank fracture universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; LITERATURE AUDITED]`

## Lean-derived conjecture

Reading `HilbertMetric/GaussianMetricStableRankFractureLaw.lean` against
`RHTower/HermiteEvenGaussianSlaterPluckerPhase.lean` exposes a missing cross-folder
classification.

Every nonconstant rank-one Gaussian metric extension has negative log-volume curvature on the
whole nonnegative scale ray.  In the canonical Hermite realization, the simultaneous
nonnormal/quasi-free/Fano/rank-variance/Plücker strict phase occurs exactly at rank at least two.
By contrast, every degree-five unisolvent packet has an eventual punctured neighborhood with
positive raw and normalized Grams and positive isotropic higher-rank curvature.

## Corpus inputs

- `GaloisForLFunctions.HilbertMetric.gaussianMetric_rankOneStrict_degreeFiveStableFracture`
- `RHTower.hermiteEvenGaussianSlaterPluckerStrictPhase_iff`
- `RHTower.hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff`

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof targeted searches covered Gaussian-kernel Gram log determinants, Hermite modes,
quasi-free variance, Slater determinants, Plücker volumes, and rank transitions.  Nearby work
treats Gaussian random determinants, Gaussian-state log-determinant information, or the standard
relation between Slater determinants and quasi-free states, but no source found states this exact
three-phase classification:

- Notarnicola, *Matrix Hermite polynomials, Random determinants and the geometry of Gaussian
  fields*, arXiv:2109.13749, relates Gaussian determinants, Hermite polynomials, and intrinsic
  volumes but not the curvature-sign/rank/Plücker equivalence here:
  <https://arxiv.org/abs/2109.13749>
- Benedikter--Porta--Schlein, *Optimal Upper Bound for the Correlation Energy of a Fermi Gas in
  the Mean-Field Regime*, records the classical Slater/quasi-free connection, not this Gaussian
  metric rank fracture:
  <https://doi.org/10.1007/S00220-019-03505-5>

Verdict: exact theorem is absent from the Lean corpus and was not found in targeted literature.
Novelty claim is restricted to the joint stable-rank phase classification, not its separate
Gaussian, Hermite, or quasi-free ingredients.

## Lean target

`formal/GaloisForLFunctions/RHTower/GaussianMetricHermiteStableRankFractureUniversalityLaw.lean`

## Verification

- scratch proof exact, warning-free:
  `lake env lean /tmp/hgt_law290.lean`
- source proof exact, warning-free:
  `lake env lean GaloisForLFunctions/RHTower/GaussianMetricHermiteStableRankFractureUniversalityLaw.lean`
- final module build deferred to terminal audit
