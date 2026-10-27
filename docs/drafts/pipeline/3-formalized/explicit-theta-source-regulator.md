# Prescribed positive theta readings with an arithmetic error certificate

- **ID:** CDG-EXPLICIT-THETA-REGULATOR
- **Stage:** 3-formalized
- **Type:** Unconditional theorem supporting the combined arithmetic metric.
- **Source:** Conjugate-Diagonal Geometry question 2.
- **Status:** Paper proof and Lean endpoints complete.
- **Count:** Part of contribution 1; no separate count.

## Exact construction and theorem

Let `chi_n` be the fixed smooth source cutoff, equal to one on the disc of
radius `n+1`, supported in the disc of radius `n+2`. Its derivative control is

```
M_n = 1 + ||D_1 chi_n||_infinity + ||D_i chi_n||_infinity
          + ||Delta chi_n||_infinity >= 1.
K_n = exp((n+1)^4) M_n,
eta_n = exp(-K_n).
```

This is a prescribed source-only regulator: no local-error test, test
function, Hecke scale, moment order, or zero coordinate enters its definition.
The derivative suprema are mathematical constants; no numerical algorithm
or computable convergence modulus is asserted.

Write the literal bilateral completed-theta amplitude and first moment as

```
A(s) = integral k(x) exp((1/2-s)x) dx = xi(s),
B(s) = integral x k(x) exp((1/2-s)x) dx = -xi_prime(s),
P_eta(s) = eta |B(s)|^2 / (|A(s)|^2+eta)^2 >= 0.
```

For a compact C² test f, let F_f be its centred transform and put
`k_L(delta)=2cosh(2L delta)-2`. The positive reading

```
Q_n(f,L,j) = pi^-1 integral chi_n(s) |F_f(s)|^2
                           k_L(Re(s)-1/2)^j P_(eta_n)(s) ds
```

recovers the full multiplicity-weighted collided moment, uniformly for
`|tau|<=n/2` and `j|L|<=2log(n+1)`, with f replaced by its ordinate modulation.
Explicitly, for every f and natural j, there are `B_f,j,D_f,j>=0` such that
for every `n>=1` and both moving parameters in that window,

```
|Q_n(twist_tau f,L,j)
  - sum_rho m_rho |F_f(rho-i tau)|^2 k_L(Re(rho)-1/2)^j|
 <= B_f,j exp(-n^4+56n^2+62)
    + D_f,j (16/n)(C_xi+log(n+4)).
```

The tail term can instead be bounded by
`D_f,j (16/n) Re(xi_prime/xi)(1+n)`. Here `C_xi` is the existing actual
right-half-plane logarithmic-derivative constant. Multiplicities are retained;
no zero separation, simplicity, or critical-line premise is imposed.
The `j=0` reading recovers the collided form; `j=1` recovers the Hecke defect.

## Dependency-closed paper proof

### Actual expanding-disc logarithmic mass

The actual theta growth bound discharges the canonical-factor growth input.
For an auxiliary canonical radius `R_n` with
`4(n+3)<R_n<4(n+3)+1`, the inverse Blaschke decomposition of the Gaussian
normalization `xi_G=-2xi` bounds its logarithm on the inner quarter-disc by

```
|log|xi_G(z)|| <= 2A(R_n+1)^2 + sum_i m_i max(0,log(2R_n/|z-i|)).
```

The residual is normalized to have norm at least one at zero. Its normalized
analytic logarithm vanishes there. Jensen bounds the total canonical divisor
mass by `A(2R_n+1)^2/log 2`.

Planar integration gives the uniform translated kernel estimate

```
integral max(0,log(S/|z-a|))^2 <= 8pi S^2.
```

Weighted Cauchy–Schwarz bounds the integrated square of the finite divisor
sum by the square of its total mass times that kernel bound. Add the residual
and normalization term using `(u+v)^2<=2u^2+2v^2`. The result is one actual
constant `C>0` with

```
integral_(|s|<=n+2) log|xi(s)|^2 <= C(n+1)^6.
```

The proof allows all multiplicities and uses no separation between zeros.

### Prescribed regulator error

For `x>0` and `K>=4`, split at `x=exp(-K/4)` to obtain

```
|0.5log(x^2+exp(-K))-log x|
 <= 0.5exp(-K/2)+(8/K)(log x)^2.
```

Above the split use `log(1+y)<=y`; below it use the logarithmic square to
absorb `2(-log x)`. Actual xi zeros have planar measure zero, so totalized
logarithms at those points do not change the integral.

For `a=exp((n+1)^4)` and `M_n>=1`, elementary exponential bounds give
`M_n exp(-a M_n/2)<=exp(-(n+1)^4)` for `n>=1`, while `M_n/(a M_n)=1/a`.
Consequently

```
M_n integral_(|s|<=n+2) |0.5log(|xi(s)|^2+eta_n)-log|xi(s)||
 <= (pi(n+2)^2/2+8C(n+1)^6) exp(-(n+1)^4).
```

### Compact current and moving window

The regularized potential has Laplacian `2P_eta`. Compact Green testing
moves the Laplacian onto `chi_n |F|^2 k_L^j`. The checked moving C² bound is
`4^(j+1) M_n A_f^2 exp(E_n)`, where

```
E_n = 2((n+3+|tau|)^2+j|L|(n+7/2)) <= 50n^2+56.
```

The local regulator estimate cancels `M_n`. Since
`(n+2)^2<=4(n+1)^6` and `(n+1)^6<=exp(6n)`, the compact-current error is
bounded by a fixed multiple of `exp(-n^4+56n^2+62)`, which tends to zero.
The actual xi current equals its divisor trace, with multiplicities.

### Arithmetic control of the omitted divisor

The C² transform decay and the moving-window restrictions bound every
omitted moment by a fixed multiple of the reference tail

```
T_n = sum_rho (1-chi_n(rho)) m_rho/(1+normSq(gammaOf rho)).
```

An omitted zero has `|Im rho|>n`. Its reference term is at most twice the
width-n Lorentzian term. The existing zero-copy/multiplicity bridge and
right-half-plane arithmetic estimates therefore give

```
T_n <= 2 lorentzMassW(n,0)
    <= (16/n) Re(xi_prime/xi)(1+n)
    <= (16/n)(C_xi+log(n+4)).
```

Adding compact-current and omitted-divisor errors proves the stated full
certificate and uniform recovery. The Lorentzian estimate is reused, not
claimed as a separate contribution.

## Lean verification

Generic analytic leaves, all individually checked:

- `HTGeometry/PlanarLogSquare.lean`
- `HTGeometry/PlanarLogSquareMass.lean`
- `HTGeometry/LogRegularizationSquareError.lean`

Arithmetic and current leaves, all individually checked:

- `ConjugateDiagonalGeometry/XiCanonicalLogBound.lean`
- `ConjugateDiagonalGeometry/XiLogSquareIntegral.lean`
- `ConjugateDiagonalGeometry/XiArbitraryRegulator.lean`
- `ConjugateDiagonalGeometry/XiExpRegulatorError.lean`
- `ConjugateDiagonalGeometry/ExplicitSourceWindowBounds.lean`
- `ConjugateDiagonalGeometry/ExplicitSourceMetric.lean`
- `ConjugateDiagonalGeometry/ExplicitThetaSourceMetric.lean`
- `ConjugateDiagonalGeometry/SourceReferenceTailArithmetic.lean`
- `ConjugateDiagonalGeometry/ExplicitThetaErrorCertificate.lean`

Principal endpoints:

- `explicitThetaSource_uniform_moving_moments`
- `explicitThetaSource_uniform_moving_collided`
- `explicitThetaSource_uniform_moving_heckeDefect`
- `exists_explicitThetaSource_sourceLogDeriv_error_bound`
- `exists_explicitThetaSource_logarithmic_error_bound`

All audited endpoint axiom closures contain only `propext`, `Classical.choice`,
`Quot.sound`. The final error-certificate module passed the direct source-only
command `lake --old env lean .../ExplicitThetaErrorCertificate.lean`.
Imports are wired; no umbrella was compiled and no limits were raised.

## Source context and calibration

The positive Poincaré–Lelong density is established mathematics; see Andersson,
*Poincaré–Lelong Type Formulas and Segre Numbers*, J. Geom. Anal. 35:25 (2025),
§5.6, https://d-nb.info/1355764351/34. Generic current convergence and a
relabelled spectral norm do not count separately. This card supplies the
regulator and arithmetic error certificate for the combined finite-source metric.

The construction carries no successor charge. Planted entire quartets retain
positive current mass. Nothing here bounds the Hecke defect by capacity,
forces its vanishing, or proves RH or simplicity. The constants provide a
mathematical error envelope, not a numerical implementation.

The completed
[finite theta-source collided readings](finite-theta-collided-readings.md)
replace the infinite amplitude by finitely many literal integer theta terms
with a prescribed cofinal coupling and retain the full moving-window certificate.
