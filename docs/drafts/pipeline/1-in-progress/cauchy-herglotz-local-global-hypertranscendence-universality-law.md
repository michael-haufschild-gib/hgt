# Cauchy–Herglotz local/global hypertranscendence universality law

Status: paper proof complete; Lean exact audit passed.

## Lean sources

- `DifferentiallyAlgebraicOn`
- `DifferentiallyAlgebraic`
- `not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane`
- `singularContinuousCarrier_maximalTranslation_cauchyHerglotzFreeness_denseResidual`
- `cofinalCholeskyResidualPhase_isSingularContinuous_maximalTranslation_hypertranscendental`

## Survivor

For every finite real measure, failure of an algebraic differential equation for its Cauchy
transform on the upper half-plane forces literal global hypertranscendence of both that transform
and every normalized Herglotz presentation
`z M + (1 + z²) C(z)`.

This is the missing connector between the residual singular-continuous phase, which records local
half-plane relation-freeness for Cauchy and Herglotz presentations, and the cofinal phase, which
records only global Cauchy hypertranscendence. The connector upgrades both projections uniformly.

## Proof skeleton

A global differential equation restricts to every subset, hence contradicts upper-half-plane
relation-freeness. The polynomial-gauge theorem first transfers local relation-freeness from the
Cauchy transform to every Herglotz presentation; apply the restriction argument to both.

## Novelty audit

Pending post-formalization literature search.
