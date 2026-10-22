# Cofinal singular-continuous Cauchy--Herglotz local/global universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL COFINAL LOCAL/GLOBAL GAUGE LAW; LITERATURE AUDITED]`

## Lean-derived conjecture

Every carrier in the cofinal Cholesky residual phase simultaneously has:

- no atoms;
- singularity with respect to Lebesgue measure;
- maximal finite-configuration translation-differential freeness;
- upper-half-plane differential relation-freeness of its Cauchy transform;
- upper-half-plane differential relation-freeness of every normalized Herglotz presentation;
- global hypertranscendence of the same Cauchy transform;
- global hypertranscendence of every normalized Herglotz presentation.

## Corpus inputs

- `cofinalCholeskyResidualPhase_isSingularContinuous_maximalTranslation`
- `maximalTranslationDifferentialFree_weightedBoundaryProbabilityCarrier`
- `not_differentiallyAlgebraicOn_cauchyTransform_weightedBoundaryCarrier`
- `not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane`
- `cauchyHerglotz_upperHalfPlane_globalHypertranscendence`

## New connector

The cofinal phase theorem exposes intrinsic maximal freeness, while the Herglotz theorem consumes
relation-freeness in the weighted projective chart. Every carrier-range point already has such a
chart representation. Choosing its constant unit density identifies the two carrier measures
exactly, transports maximal freeness back to the weighted relation predicate, and activates both
the local Cauchy/Herglotz and global hypertranscendence conclusions.

No numerical computation is used.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered Nevanlinna parametrization of indeterminate Hamburger moment
problems, singular-continuous solutions, Cauchy/Stieltjes transforms, Herglotz presentations,
translation families, and algebraic differential equations.

Nearest sources:

- Štampach--Šťovíček, *The Nevanlinna parametrization for q-Lommel polynomials in the
  indeterminate case*, arXiv:1407.0217:
  <https://arxiv.org/abs/1407.0217>
- Zagorodnyuk, *The Nevanlinna-type parametrization for the operator Hamburger moment problem*,
  arXiv:1605.03217:
  <https://arxiv.org/abs/1605.03217>
- Pruckner--Reiffenstein--Woracek, *An upper bound for the Nevanlinna matrix of an indeterminate
  moment sequence*, arXiv:2307.10748:
  <https://arxiv.org/abs/2307.10748>

No source found states that every member of one cofinal singular-continuous moment phase is
maximally free under all finite translated differential patterns and, for the identical carrier,
has both upper-half-plane relation-freeness and global hypertranscendence for its Cauchy transform
and every normalized Herglotz gauge. Novelty claim is restricted to this joint law.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/CofinalSingularContinuousCauchyHerglotzLocalGlobalUniversalityLaw.lean`

## Verification

- source proof exact and warning-free:
  `lake env lean GaloisForLFunctions/HTGeometry/CofinalSingularContinuousCauchyHerglotzLocalGlobalUniversalityLaw.lean`
- imported by `formal/GaloisForLFunctions/HTGeometry.lean`
- final module and umbrella builds deferred to terminal audit
