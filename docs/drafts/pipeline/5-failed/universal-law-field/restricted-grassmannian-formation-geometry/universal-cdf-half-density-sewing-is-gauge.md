# Universal CDF half-density sewing is gauge

- **ID:** ULF-UCHS-001
- **Stage:** 5-failed
- **Type:** FALSIFIED MECHANISM · STATIC COORDINATE EQUIVALENCE
- **Parent:** `ULF-SCIN-001`

## Proposed mechanism

Let `F_theta` be normalized theta-source CDF and `Q_E(u)=-log(1-u)` unit-exponential quantile.
The two maps

```text
h_+(u)=F_theta(Q_E(u)),
h_-(u)=F_theta(-Q_E(u))=1-h_+(u)                     (UCHS.1)
```

identify positive and negative Stokes chambers with right and left halves of theta probability
interval. Their half-density weighted composition maps transport `+A_0,-A_0` to a
reflection-odd nuclear operator on full theta interval.

## Exact killing mechanism

Construction `(UCHS.1)` uses only that target density is positive, continuous, normalized, and
even. It works verbatim for **every** such density. Apparent translation law

```text
h_+(F_E(Q_E(u)+c))
 =F_theta(Q_theta(h_+(u))+c)                         (UCHS.2)
```

is true because both sides were defined by conjugating physical translation through CDFs. It
does not intertwine an independently constructed theta/Poisson operator, constrain target
density, change any spectral invariant of `A_0`, or narrow pre-divisor source model class. It is
therefore coordinate gauge, not completion transport. Using it as missing arrow would merely
rename `A_0` and collide with proved aperture-wall/Xi divisor and projective-jet no-gos.

Fixed integer multiplication also does not rescue it. In Stokes wall coordinate `x=2d log p`,
multiplication by fixed `n` shifts `x` by `2d log n`, which vanishes as `d->0`. Only a cofinal
family `n_d` with `2d log n_d -> c` produces semigroup in `(UCHS.2)`.

## Strongest positive survivor

Sewing has one real analytic consequence. Its right-chart Jacobian is

```text
h_+'(u)=rho_theta(Q_E(u))/(1-u)
       =rho_theta(x) exp(x),                          (UCHS.3)
```

and tends to zero at wall because theta density decays faster than every exponential. Thus
inverse half-density is singular: fixed and theta-completed charts cannot be joined by a bounded
unweighted change of frame. Reflection gives same singularity on left.

This explains how valid relative completion may evade fixed-fibre bounded-intertwiner no-gos,
but does not construct that completion. A successor must make `(UCHS.3)` enter an
**independent** theta/Poisson boundary equation—e.g. a commutator, Schur complement, or relative
determinant identity—not merely a CDF conjugacy.

## Checked locks

- `thetaSource_cdfFun_zero`, `thetaSource_even`: exact median and reflection.
- `thetaIntegerQuantileFlow_mul`, `thetaIntegerQuantileFlow_gt`: theta quantile translation.
- `finiteMeasure_eq_zero_of_map_thetaIntegerQuantileFlow_eq_self`: no stationary finite
  probability fibre.
- `HedenmalmThetaPrimeCriticalRiggingReflectionNoGo`: fixed positive diagonal contraction cannot
  supply missing half-density gain.
- `routePPrimitive_GammaJulia_Stokes_expWallXiTau_projectiveJetNoGo`: scalar wall/Xi tau matching
  is false.
- `RoutePPrimitiveGammaJuliaStokesApertureWallXiDivisorNoGo`: exact wall/Xi divisor matching is
  false.

## New knowledge

It cannot be “transport exponential wall to theta probability coordinates.” That operation is
universal gauge. It must be a theta-specific relative boundary law in which singular Jacobian is
dynamically used and which changes, rather than relabels, divisor-bearing operator.
