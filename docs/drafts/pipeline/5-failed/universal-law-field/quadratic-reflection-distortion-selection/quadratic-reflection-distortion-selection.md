# Quadratic reflection-distortion selection

- **ID:** ULF-QRDS-FAIL-1
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `LiteralSourceReflectionDeterminantCocycle`
- **Statement:** Raw quadratic accumulation of marked-edge reflection multipliers cannot be used as
  invariant selection pressure because literal rank normalization conjugates it to linear growth.

## Proposed mechanism

The raw multiplier at source rank `m` is `-(z^-1)^(2m+1)`.  Its block exponent
`n(2M+n)` suggested that literal-source completion might force subquadratic conditioning and hence
`|z|=1` before Xi specialization.

## Exact killing theorem/mechanism

`RankGaugeLinearizationOfSourceReflection` proves unconditionally that multiplying rank `m`
execution by `(z^-1)^m` makes every edge equal to `1-z`.  In that frame, reflection multiplier is
the rank-independent scalar `-z^-1`; block exponent is `n`.  Pointwise,

`z^m (-(z^-1)^(2m+1)) z^m = -z^-1`.

Thus quadratic term is exact rank-frame coboundary.  Any subquadratic bound is coordinate-dependent
unless source independently forbids this normalization.  Corpus already contains the analogous
warning `deningerExponentExceptionalLineReflectionCoefficient_eq_gaugeCoboundary`.

## Strongest positive survivor

Gauge-normal marked source execution has exact constant form `1-z`, residual reflection character
`-z^-1`, and nonempty-block unit norm exactly when `|z|=1`.  This classification is dependency-closed
on paper and is formalized in the paired universal-law-field module.

## New insight

Raw determinant-rate growth is not candidate universal curvature.  Decisive law must live in a
mixed cross-effect or obstruction invariant under every source-legal rank gauge, or prove from
literal arithmetic why such gauge cannot extend across the second formation operation.

## Status

- Internal audit: exact normalization absent; related coboundary no-gos present.
- Paper proof: `rank-gauge-linearization-of-source-reflection`, fully proven.
- Lean: pending paired module audit.

## Log

- 2026-09-01 — retired after explicit source rank-gauge conjugation killed quadratic rate.
