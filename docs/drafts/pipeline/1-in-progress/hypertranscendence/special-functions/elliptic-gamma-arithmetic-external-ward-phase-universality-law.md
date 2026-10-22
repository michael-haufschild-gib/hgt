# Elliptic-Gamma arithmetic external/Ward phase universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT JOINT PHASE LAW; LITERATURE AUDITED]`

## Lean-derived law

For every finite separated nonresonant external-shift family and every upper-half-plane period
pair `sigma, tau`, exactly one phase occurs.

1. `1, sigma, tau` are rationally linearly independent. Then the shared-period external quotient
   differential matroid is free over `ℂ(z)`, every nonzero finite external defect differential
   combination lies outside the elliptic fraction field, and the rank-two multiple
   elliptic-Gamma product/logarithmic derivative carries its complete hypertranscendence,
   scale, reflection, and two-zero-radial-Ward certificate.
2. `1, sigma, tau` are rationally dependent. Then positive naturals `m, n` and an integer `k`
   satisfy `m * sigma = n * tau + k`, and the associated finite commensurable residue-class
   factorization has exact additive reciprocal reflection.

The phases cannot coexist.

Lean declaration:

- `GaloisForLFunctions.ellipticGamma_arithmeticExternalWardPhaseUniversality`

## Corpus inputs

- `GaloisForLFunctions.ellipticGamma_arithmeticReflectionPhaseUniversality`
- `GaloisForLFunctions.ellipticGamma_sharedPeriodExternalWardUniversality`
- `GaloisForLFunctions.EllipticGammaSharedPeriodExternalWardCertificate`
- `GaloisForLFunctions.EllipticGammaCommensurableReflectionCertificate`
- `GaloisForLFunctions.ellipticGammaCommensurableReflectionCertificate_nonempty_iff`

## New mathematical connector

The corpus separately exposed:

- a shared rational-independence hypothesis controlling external quotient freeness, defect
  atomicity, and homogeneous elliptic-Gamma Ward/reflection behavior;
- an exhaustive arithmetic reflection dichotomy between independent rank-two periods and
  positive-integral commensurability.

Closing these terminal laws yields a single exclusive and exhaustive phase theorem. It transfers
the full external/Ward certificate to the independent branch and preserves the exact finite
reflection factorization on the dependent branch. This joint phase law did not occur elsewhere in
the Lean corpus.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered elliptic-Gamma modularity, reflection and multiplication formulae,
commensurable-period degenerations, algebraic independence for independent shift parameters, and
difference equations over elliptic function fields.

Nearest sources:

- Felder--Varchenko, *The elliptic gamma function and `SL(3,Z) x Z^3`*,
  arXiv:math/9907061, develops elliptic-Gamma automorphic and modular identities:
  <https://arxiv.org/abs/math/9907061>
- Felder--Varchenko, *Multiplication Formulas for the Elliptic Gamma Function*,
  arXiv:math/0212155, proves elliptic-Gamma multiplication formulae:
  <https://arxiv.org/abs/math/0212155>
- Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, arXiv:math/0306164, proves modular and integral representations:
  <https://arxiv.org/abs/math/0306164>
- Adamczewski--Dreyfus--Hardouin--Wibmer, *Algebraic independence and linear difference
  equations*, arXiv:2010.09266, proves independence dichotomies for sufficiently independent
  shift, q-difference, and Mahler parameters:
  <https://arxiv.org/abs/2010.09266>
- de Shalit, *Algebraic independence and difference equations over elliptic function fields*,
  arXiv:2207.13377, proves a distinct elliptic-isogeny algebraic-independence dichotomy:
  <https://arxiv.org/abs/2207.13377>
- de Shalit--Hardouin--Roques, *Hypertranscendence and q-difference equations over elliptic
  function fields*, arXiv:2409.10092, classifies differential-algebraic solutions in an
  elliptic-isogeny setting:
  <https://arxiv.org/abs/2409.10092>

No source found states the exact exclusive/exhaustive phase law joining rational-period
independence to the external quotient differential matroid, finite-defect atomicity, and
homogeneous elliptic-Gamma Ward/reflection certificate, while joining rational dependence to
positive-integral commensurability and finite reciprocal reflection. Novelty claim is restricted
to this joint theorem.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/EllipticGammaArithmeticExternalWardPhaseUniversalityLaw.lean`

## Verification

- exact theorem body checked warning-free in a combined source file:
  `lake env lean /tmp/hgt_law300_combined.lean`
- imported by `formal/GaloisForLFunctions/HTGeometry.lean`
- direct source check awaits parent-module cache creation in final module audit
- final module and umbrella builds deferred to terminal audit
