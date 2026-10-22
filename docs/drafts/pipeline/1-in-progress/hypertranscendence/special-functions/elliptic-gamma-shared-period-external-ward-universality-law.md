# Elliptic-Gamma shared-period external/Ward universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL SHARED-HYPOTHESIS SYNTHESIS; LITERATURE AUDITED]`

## Lean-derived law

For every finite external-shift support and every separated nonresonant shift family, one
rationally linearly independent period triple `(1, sigma, tau)` simultaneously certifies:

- freeness of the external quotient differential-family matroid over `ℂ(z)`;
- exclusion of every nonzero finite constant-coefficient differential combination of external
  additive defects from the elliptic fraction field;
- hypertranscendence of the rank-two multiple elliptic-Gamma product and logarithmic derivative;
- parity-dependent product reflection under every common period scale;
- zero radial Ward jets on both reflection branches;
- logarithmic homogeneous weight `-1`;
- logarithmic parity reflection.

The shared independence hypothesis is not duplicated: it supplies the external translation
theorem directly and constructs the rank-three minor of the normalized rank-two period family
`![sigma, tau] / 1`.

Lean declaration:

`GaloisForLFunctions.ellipticGamma_sharedPeriodExternalWardUniversality`

Certificate:

`GaloisForLFunctions.EllipticGammaSharedPeriodExternalWardCertificate`

## Corpus inputs

- `GaloisForLFunctions.ellipticGamma_twoTierExternalFreenessUniversality`
- `GaloisForLFunctions.homogeneousMultipleEllipticGamma_productLogDerivativeWardUniversality`
- `GaloisForLFunctions.MultipleEllipticGammaHasRankThreeMinor`
- `GaloisForLFunctions.ellipticGammaSourcePeriods`

## Why this is a new connector

Existing terminal laws used the same period triple in disjoint roles:

- as the translation lattice controlling external quotient freeness and defect atomicity;
- as the rank-three normalized-period minor controlling homogeneous multiple elliptic-Gamma
  hypertranscendence and Ward/reflection identities.

No prior theorem exposed that one hypothesis certifies both tiers. The new certificate retains all
conclusions, so both input laws at rank two are recoverable by field projections rather than
replaced by a weaker conjunction.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered multiple elliptic-Gamma modular/reflection identities,
difference-equation hypertranscendence over rational and elliptic function fields, translated
elliptic-Gamma families, and differential algebraic independence.

Nearest sources:

- Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, arXiv:math/0306164, proves modular and integral representations:
  <https://arxiv.org/abs/math/0306164>
- Winding, *Multiple elliptic gamma functions associated to cones*, arXiv:1609.02384, proves
  cone-indexed product and modular properties:
  <https://arxiv.org/abs/1609.02384>
- de Shalit--Hardouin--Roques, *Hypertranscendence and q-difference equations over elliptic
  function fields*, arXiv:2409.10092, classifies differential-algebraic solutions of a different
  elliptic `q`-difference setting:
  <https://arxiv.org/abs/2409.10092>
- Adamczewski--Dreyfus--Hardouin, *Hypertranscendence and linear difference equations*,
  arXiv:1910.01874, treats general shift, `q`-difference, and Mahler equations over genus-zero
  bases:
  <https://arxiv.org/abs/1910.01874>
- Morain, *Geometric families of multiple elliptic Gamma functions and arithmetic applications,
  II*, arXiv:2602.06561, studies modular-symbol and arithmetic consequences of geometric
  multiple elliptic-Gamma families:
  <https://arxiv.org/abs/2602.06561>

No source found states the exact shared-period certificate joining external translation-coset
differential matroid freeness and elliptic defect atomicity to the full rank-two homogeneous
product/log-derivative Ward phase. Novelty claim is restricted to this joint theorem.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw.lean`

## Verification

- source proof exact and warning-free:
  `lake env lean GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw.lean`
- `formal/GaloisForLFunctions/HTGeometry.lean` already imports target module
- final module and umbrella builds deferred to terminal audit
