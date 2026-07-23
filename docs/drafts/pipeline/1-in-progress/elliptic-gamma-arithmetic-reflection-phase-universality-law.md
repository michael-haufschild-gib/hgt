# Elliptic-Gamma arithmetic reflection phase universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT PHASE CLASSIFICATION; LITERATURE AUDITED]`

## Lean-derived law

For every upper-half-plane pair `sigma, tau`, exactly one of two phases occurs.

1. `1, sigma, tau` are rationally linearly independent. The rank-two multiple
   elliptic-Gamma product and logarithmic derivative are hypertranscendental over `ℂ(z)`, the
   product has parity reflection, its logarithmic derivative has signed reflection, and the
   regular reflected product is one.
2. `1, sigma, tau` are rationally dependent. Then there are positive naturals `m, n` and an
   integer `k` with
   `m * sigma = n * tau + k`; the corresponding finite commensurable residue-class
   factorization obeys exact additive reciprocal reflection.

The upper-half-plane signs make this exhaustive: every nonzero rational relation has nonzero
`sigma` and `tau` coefficients of opposite signs. Clearing rational denominators produces the
positive integral relation required by the factorization theorem. Conversely, any such relation
is a nontrivial rational dependence.

Lean declarations:

- `GaloisForLFunctions.not_linearIndependent_ellipticGammaSourcePeriods_iff_positiveCommensurable`
- `GaloisForLFunctions.EllipticGammaRankTwoIndependentReflectionCertificate`
- `GaloisForLFunctions.EllipticGammaCommensurableReflectionCertificate`
- `GaloisForLFunctions.ellipticGamma_arithmeticReflectionPhaseUniversality`

## Corpus inputs

- `GaloisForLFunctions.multipleEllipticGamma_rankThreeMinor_reflectionHypertranscendenceUniversality`
- `GaloisForLFunctions.ellipticGammaCommensurableFamilyProduct_additiveReflection`
- `GaloisForLFunctions.ellipticGammaSourcePeriods`
- `GaloisForLFunctions.MultipleEllipticGammaHasRankThreeMinor`

## New mathematical connector

The two input terminal laws described independent and commensurable regimes separately. The corpus
did not prove that, under positive imaginary parts, these regimes are complementary and exhaustive.
The new arithmetic equivalence supplies that missing connector. Both analytic conclusions are
retained in certificate fields, and the final theorem proves existence of one phase plus
impossibility of both.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered elliptic-Gamma reflection and multiplication formulae, rank-three
period geometry, rational/commensurable period degenerations, multiple elliptic-Gamma modularity,
and difference-equation hypertranscendence over elliptic function fields.

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
- Felder--Henriques--Rossi--Zhu, *A gerbe for the elliptic gamma function*,
  arXiv:math/0601337, organizes rank-three-period elliptic-Gamma identities over triptic curves:
  <https://arxiv.org/abs/math/0601337>
- de Shalit--Hardouin--Roques, *Hypertranscendence and q-difference equations over elliptic
  function fields*, arXiv:2409.10092, classifies differential-algebraic solutions in a distinct
  elliptic-isogeny setting:
  <https://arxiv.org/abs/2409.10092>

No source found states the exact exclusive/exhaustive upper-half-plane phase theorem connecting
rational independence to rank-two multiple elliptic-Gamma hypertranscendental reflection and
rational dependence to positive-integral finite factorized reflection. Novelty claim is restricted
to this joint classification.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/EllipticGammaArithmeticReflectionPhaseUniversalityLaw.lean`

## Verification

- source proof exact and warning-free:
  `lake env lean GaloisForLFunctions/HTGeometry/EllipticGammaArithmeticReflectionPhaseUniversalityLaw.lean`
- imported by `formal/GaloisForLFunctions/HTGeometry.lean`
- final module and umbrella builds deferred to terminal audit
