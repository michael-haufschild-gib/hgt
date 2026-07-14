# Xi endpoint curvature is a boundary value of the central moment germ

- **ID:** `xi-endpoint-central-moment-boundary-value`
- **Stage:** 3-formalized
- **Type:** theorem / exact source-value relation
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiEndpointCentralMomentBoundaryValue.lean`

## Statement

Let

\[
G_\Xi(z)=\sum_{n\ge 0}M_nz^{2n}
\]

be the centered reciprocal-square moment germ, equivalently the Taylor germ of the normalized
completed prime--Gamma relative trace.  Then the source-pure endpoint height gap places every
reciprocal-square coordinate inside the unit disk, so the series and divisor resolvent remain
absolutely convergent at `z=i/2`.  At that point the reciprocal-square resolvent term is exactly
the FE--Schwarz endpoint cross term.  Therefore

\[
G_\Xi(i/2)=C_{\rm endpoint},
\]

where `C_endpoint` is the completed endpoint curvature.  In Taylor-coefficient form,

\[
C_{\rm endpoint}
=\sum_{n\ge0}m_n\left(-\frac14\right)^n,
\qquad
m_n=\operatorname{normalizedPrimeArchMoment}(n),
\]

and this series is absolutely convergent.

## Formal theorem surface

- `xiZeroCopyReciprocalSquare_norm_lt_one`;
- `summable_xiCentralReciprocalMoment_endpointSeries`;
- `xiCentralMomentGerm_I_half_eq_endpointCrossTrace`;
- `xiCentralMomentGerm_I_half_eq_endpointCompletedCurvature`;
- `hasSum_normalizedPrimeArchMoment_endpointCurvature`;
- `tsum_normalizedPrimeArchMoment_endpointCurvature`.

## Proof contribution

This relation removes the completed endpoint curvature as an independent calibration datum from
the central-moment/Hausdorff/Bernstein interfaces.  The endpoint constant is already an exact value
of the same Taylor germ whose coefficients feed the RH moment cones.  Thus a finite or cofinal
moment construction need not separately identify an endpoint source: convergence strong enough to
pass the signed-quarter value automatically carries the calibration.

The theorem does **not** prove moment positivity.  A single positive boundary value cannot select
the complete Hankel or Hausdorff cone; the remaining orientation problem is still a constraint on
the full coefficient family.

## Verification

- The module is imported by `GaloisForLFunctions.RHTower`.
- Direct module checking is the intended validation target; no umbrella or full-project build is
  required for this leaf theorem.
