# Cofinal Nevanlinna-carrier prime--arch Hankel-classifier universality law

- **ID:** cofinal-nevanlinna-carrier-prime-arch-hankel-classifier-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `cofinalCholeskyResidualPhase_dense_gdelta_residual`,
  `cofinalCholeskyResidualPhase_singularContinuous_cauchyHerglotzLocalGlobalUniversality`,
  `NevanlinnaBoundaryFamily.barycenter_moments`,
  `strictHankelRay_of_atomlessProbability_hamburgerMoments`, and the universal
  prime--archimedean strict-ray classifiers
- **Statement:** The dense residual cofinal Cholesky phase in the complete Nevanlinna carrier
  range consists pointwise of singular-continuous, maximally translation-free, locally and
  globally Cauchy--Herglotz hypertranscendental carriers. Every carrier in that phase represents
  the same strict Hamburger Hankel ray and therefore carries exact RH, reconstruction, Sonin,
  and Hedenmalm classifiers.

## Goal

Use membership in the complete canonical carrier range—not a separately chosen positive-chart
parameterization—to attach the whole cofinal singular-continuous phase to strict Hankel and
prime--archimedean classifier structure.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `cofinalCholeskyResidualPhase_dense_gdelta_residual`
- `cofinalCholeskyResidualPhase_singularContinuous_cauchyHerglotzLocalGlobalUniversality`
- `NevanlinnaBoundaryFamily.barycenter_moments`
- `strictHankelRay_of_atomlessProbability_hamburgerMoments`
- `noFiniteSpectralOrStateLocalClosure_of_strictHankelRay`
- `noShiftInvariantGramRealization_of_strictHankelRay`
- `riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay`
- `primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis`
- `primeArchAllStrictHankelRayAdjoiningPhase_iff_allSoninNondegenerateApertureUnitCollarPhase`
- `primeArchSourceMomentHankelExactReconstructionPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate`

## Proof

**[PROVED HERE]** The cofinal-phase theorem gives a dense `Gδ`, hence residual, subset of the
complete Nevanlinna carrier range. Fix any carrier `ν` in this phase. The cofinal local/global
theorem makes `ν` atomless and Lebesgue-singular, maximally translation-differentially free,
upper-half-plane relation-free in its Cauchy and every normalized Herglotz presentation, and
globally hypertranscendental in all those presentations.

By definition of `carrierRange`, there is a projective boundary probability `η` with
`barycenter(η)=ν`. Every boundary barycenter represents the prescribed Hamburger sequence `s`,
so `ν` has moments `s`. Since `ν` is both a probability measure and atomless, the atomless
Hamburger theorem makes every finite moment Hankel matrix of `s` positive definite, with positive
determinant. This strict ray also excludes every fixed finite spectral width, every fixed finite
state-space dimension, and every shift-invariant Gram realization.

The universal strict-ray adjoining theorem now identifies RH with strictness of every nonzero
nonnegative prime--archimedean mixture after adjoining `s`. Existing exact equivalences replace
that cone respectively by prescribed source-moment reconstruction, all nondegenerate Sonin
determinant collars, and—after adjoining Xi-zero simplicity—the Hedenmalm RH-and-simplicity
certificate.

All conclusions hold for every carrier in the same dense residual cofinal phase. No computation
is used. ∎

## Strict gain over corpus endpoints

The cofinal Cauchy--Herglotz theorem stopped at analytic freeness and did not use the fact that
every point lies in the complete moment-carrier range. Existing prime--archimedean laws accepted
an abstract strict Hankel ray but supplied no cofinal singular-continuous Nevanlinna realization.
The closure attaches the exact spectral classifiers pointwise to the entire global cofinal
phase, under a different and more intrinsic parameterization than the positive-chart law.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.CofinalNevanlinnaCarrierPrimeArchHankelClassifierUniversalityLaw`
- Main theorem:
  `cofinalNevanlinnaCarrier_primeArchHankelClassifierUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/CofinalNevanlinnaCarrierPrimeArchHankelClassifierUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for Nevanlinna parametrizations of indeterminate Hamburger moment problems, singular-continuous
canonical carriers, Cauchy--Herglotz hypertranscendence, strict Hankel rays, Sonine spaces, and RH
positivity criteria found no exact collision. Closest primary sources:

- F. Štampach and P. Šťovíček,
  *The Nevanlinna parametrization for q-Lommel polynomials in the indeterminate case*,
  <https://arxiv.org/abs/1407.0217>, explicitly describes N-extremal measures for one
  indeterminate Hamburger problem, not a dense residual singular-continuous carrier phase or RH
  classifier.
- S. M. Zagorodnyuk,
  *The Nevanlinna-type parametrization for the operator Hamburger moment problem*,
  <https://arxiv.org/abs/1605.03217>, gives an operator-valued parametrization, not
  differential-freeness of Cauchy--Herglotz presentations or prime--archimedean adjoining.
- R. Pruckner, J. Reiffenstein, and H. Woracek,
  *An upper bound for the Nevanlinna matrix of an indeterminate moment sequence*,
  <https://arxiv.org/abs/2307.10748>, studies growth of Nevanlinna matrices, not a pointwise
  strict-Hankel classifier across a cofinal carrier phase.
- A. Connes and C. Consani, *The scaling Hamiltonian*,
  <https://arxiv.org/abs/1910.14368>, discusses Sonine spaces and Weil positivity for RH, not
  Nevanlinna carrier-range residuality or translated differential freeness.

## Log

- 2026-07-23 — fresh terminal scan exposed the unused `carrierRange` moment interface behind the
  cofinal Cauchy--Herglotz phase.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
