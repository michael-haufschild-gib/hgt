# A common positive theta source for moving collided traces

- **ID:** CDG-THETA-MOVING-TRACE
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Conjugate-Diagonal Geometry, question 2; actual xi current, theta transform, and collided depth calculus.
- **Statement:** One regulator defined by arithmetic source integrals recovers every compact C² collided moment uniformly for linearly moving ordinates and logarithmic Hecke scales.
- **Count:** Part of contribution 1; no separate count.

## Goal

Evaluate the full positive conjugate-diagonal trace without selecting zero
coordinates in the approximants or their regulator. The target includes the
Hecke defect at scales proportional to log height. It does not assert a
prime-side upper bound, a convergence algorithm, capacity payment, selective
positivity, or RH.

## Gates

- [x] Source-defined objects, exact parameter window, and proof route specified.
- [x] Complete moving endpoint passes individual `lake --old env lean` checks.
- [x] Transitive axiom audit of the moving endpoint contains only standard Lean axioms.
- [x] Included in the combined finite arithmetic metric; no separate contribution count.

## Exact theorem

Write `F_f(s)=tr f s`, `k_L(d)=2 cosh(2Ld)-2`, and let `theta` be the
literal completed arithmetic theta source already identified with xi.
Define

```
A(s) = integral theta(x) exp((1/2-s)x) dx,
B(s) = integral x theta(x) exp((1/2-s)x) dx,
P_eta(s) = eta |B(s)|²/(|A(s)|²+eta)².
```

The checked theta identities give `A=xi` and `B=-xi'`. Thus `P_eta>=0` for
positive eta. Let `chi_n` be the fixed radial smooth cutoff equal to one on
the disc of radius `n+1`, supported in the disc of radius `n+2`. Put

```
w(s) = exp((Re s)²)/(1+(Im s)²)²,
M_n = 1 + ||D_1 chi_n||infinity + ||D_i chi_n||infinity
        + ||Delta chi_n||infinity,
eta_k = 1/(k+1).
```

Choose `k_n` to be the least `k>=n` satisfying both

```
|pi^-1 integral chi_n w P_eta_k
 - (2pi)^-1 integral log|xi| Delta(chi_n w)| < eta_n,

integral_(disc(n+2))
  |(1/2)log(|xi|²+eta_k)-log|xi|| < exp(-n^4)/M_n.
```

Both requirements involve only xi, its derivative, fixed cutoffs, and planar
integration. Neither tests, scales, moment orders, nor zero positions enter
this choice. Existence and `k_n>=n` are checked in `CommonSourceRegulator`.

For a compact C² test f and fixed natural j, the endpoint is

```
sup_(|tau|<=n/2, j|L|<=2log(n+1))
 |pi^-1 integral chi_n(s) |F_f(s-i tau)|²
     k_L(Re s-1/2)^j P_eta_k_n(s) ds
  - sum_rho m_rho |F_f(rho-i tau)|² k_L(Re rho-1/2)^j|
 -> 0.
```

Lean states uniformity in epsilon form, avoiding any bounded-supremum
convention. All actual multiplicities are retained. At j=0 this computes D;
at j=1 it computes the complete Hecke defect. The j=0 scale condition permits
every L because the zeroth kernel power is one.

## Dependency-closed paper argument

1. The regularized potential `U_eta=(1/2)log(|xi|²+eta)` is smooth and has
   `Delta U_eta=2P_eta`. It converges to `log|xi|` in local L¹. Green's
   identity and the actual xi Poincaré–Lelong theorem therefore identify the
   compact current with its exact multiplicity-weighted zero trace. For a
   compact C² test psi with `|Delta psi|<=H` on the chosen disc, the normalized
   source/current error is at most `(2pi)^-1 H ||U_eta-log|xi|||_1`.

2. The proved compact-test transform decay gives `|F_f(s)|²<=C_f w(s)` on
   the whole plane. In particular `|F_f(s)|<=A_f exp(|s|²)` for some
   `A_f>=1`. For
   `G(s)=exp(u(s-1/2))F_f(s-i tau)`, the unit-circle Cauchy estimate bounds
   both `|G|` and `|G'|` on the disc of radius `n+2` by
   `A_f exp((n+3+|tau|)²+|u|(n+7/2))`.

3. The identities `Delta|G|²=4|G'|²` and
   `|D_v|G|²|<=2|G||G'||v|`, followed by the cutoff product rule, bound
   `|Delta(chi_n|G|²)|` by four times `M_n` times the square of that envelope.
   The exact translation recurrence
   `phi_(j+1)(f)=phi_j(T_L f)+phi_j(T_-L f)-2phi_j(f)` then bounds order j
   by `4^j` times the zeroth envelope at total translation `|u|+j|L|`.

4. The local regulator requirement cancels `M_n`. Throughout
   `|tau|<=n` and `j|L|<=2log(n+1)`, the normalized compact-current error is
   bounded by
   `((2pi)^-1 4^(j+1) A_f²) exp(-n^4+50n²+56)`, which tends to zero.
   The numerical coefficients only record a coarse proof bound; they are
   not a contribution.

5. If an actual zero is omitted by the cutoff, its strip location implies
   `|Im rho|>n`. For `|tau|<=n/2`, this gives
   `|Im rho|<=2|Im rho-tau|`. Also
   `k_L(Re rho-1/2)^j<=2^j(n+1)²` in the stated Hecke window. Combining
   these inequalities with the fourth-order squared-transform decay bounds
   every omitted moving moment by a fixed multiple of
   `m_rho/(1+|gammaOf rho|²)`.

6. That reference density is already summable for the actual zeta divisor.
   Its omitted mass, multiplied by `1-chi_n`, tends to zero by dominated
   convergence. This controls the full moving tail uniformly, including
   equality in `j|L|<=2log(n+1)`. The triangle inequality with step 4 proves
   the full trace formula.

## Formal endpoint and validation

The exact endpoint is `thetaSource_uniform_moving_moments` in
`ConjugateDiagonalGeometry/UniformThetaSourceMetric.lean`, with collided and
Hecke-defect specializations in the same module. All three passed the final
source-only `lake --old env lean` check. Their transitive axiom outputs contain
only `propext`, `Classical.choice`, `Quot.sound`.
`SourceSquareCalculus`, `SourceTransformGrowth`, `SourceMovedTests`,
`SourceMomentLaplacianBound`, `SourceWindowError`, and
`MovingSourceTailControl`, `MovingSourceTail`, and `MovingSourceMetric` have
passed individual checks. The cutoff differential bound, joint
Cauchy envelope, finite-moment recurrence, uniform compact-current limit,
omitted-tail domination, dominated tail limit, and complete moving trace are checked.
The completed leaf is wired into the programme umbrella; no umbrella was compiled.

Checked dependencies include `XiSourceCurrent`, `XiLogRegularization`,
`XiPositiveSourceMetric`, `UniversalSourceWeight`, `XiLogL1Convergence`,
`SourceCutoffControl`, `CommonSourceRegulator`, `CommonSourceMetric`,
`ThetaSourceMetric`, `XiCompactCurrentError`, and `CommonSourceError`.
The principal local-current, common-regulator and fixed-theta axiom outputs
contain only `propext`, `Classical.choice`, `Quot.sound`.

## Historical source context and selectivity

The basic positive density and compact divisor-current convergence are
standard regularization machinery. Andersson's
[Poincaré–Lelong Type Formulas and Segre Numbers, §5.6](https://d-nb.info/1355764351/34)
explicitly records the corresponding regularization. These components cannot
count as new results. The remaining significance question concerns the whole
arithmetic, test-independent, joint moving-window evaluation.

`XiCompactPolarWeilRealization` already proves faithful compact-polar Hilbert
completeness using zero evaluations. That completion and the actual Meyer
source conjugation are existing results. The proposed addition is an integral
evaluation of the absolute norm and its moving Hecke statistics.

`XiArithmeticSourceMixedJetTorelli` already reconstructs finite signed mixed
defects from admissible rectangle contour moments. Its actual theorem was
read: it assumes the contour admission conditions and compares a finite
configuration whose moments agree. The candidate here evaluates the full
infinite positive trace along a source-selected schedule, without contour
admission or a chosen candidate finite configuration. The general fact that
arithmetic source data determine divisor data is already known.

This is conjugate-diagonal positivity with hyperbolic depth kernel. It carries
no successor gauge charge. Entire planted-quartet sources would retain their
additional positive masses and defects; source positivity is not reflection
positivity. Multiplicative twins with the same analytic admission conditions
would also have such positive metrics. Meromorphic pole relaxations fall
outside the globally smooth entire-potential construction. No uniformity over
changing theta characteristics, changing source families, or escape models
is proved.

## Log

- 2026-10-27 — exact moving endpoint isolated from the programme card;
  supporting source/current bounds checked, moving verification pending.
- 2026-10-27 — full moving endpoint and both specializations passed source-only
  checks and transitive axiom audits. Novelty/significance gate remains open;
  no contribution counted.

Current closure status: this supporting theorem is complete and included in
the combined finite arithmetic metric. Earlier audit-status notes above are
historical; no novelty check remains in the authorized workflow. The
already proposed higher-regularity extension is also complete, as recorded below.


## Higher regularity on the same source schedule

For every compact C^(k+2) test f, the same `thetaSourceMomentReading` satisfies

```
forall epsilon>0, exists N, forall n>=N, forall j,L,tau,
 |tau|<=n/2 and j|L|<=(2k+2)log(n+1) imply
 |thetaSourceMomentReading(twist_tau f,L,j,n)-D_j(twist_tau f,L)|/4^j
   < epsilon.
```

The threshold precedes every order, scale and ordinate shift. Equality at the
aperture boundary is included. For a smooth compact test and fixed c,j, the
same schedule gives unnormalized uniform convergence on `|L|<=c log(n+1)`.
This closes the higher-regularity claim already written on the parent card;
it adds no contribution count and changes no source definition.

Put r=k+2, q=2r-2, and choose a>=0 containing the support. Actual integration
by parts gives

```
S_r=2^r(integral|f|+integral|f^(r)|),
|F_f(s-i tau)|^2 <= S_r^2 exp(a)/(1+|Im(s)-tau|)^(2r)
```

on the zero strip. At an omitted zero, X=1+|gamma-tau| satisfies
`n+1<=2X` and `1+|gammaOf(rho)|^2<=5X^2`. Therefore the closed q-logarithmic
window bounds each moving kernel value by
`2^j C_r/(1+|gammaOf(rho)|^2)`, where `C_r=5*2^q*S_r^2*exp(a)`.
Actual summability bounds the omitted trace by
`2^j C_r sourceReferenceTail(n)`.

The same common regulator bounds the compact-current error by
`4^j (2/pi) A_f^2 exp(-n^4+K_b n^2+K_b)` on `j|L|<=b log(n+1)`,
where `K_b=36+14b`. This follows from the existing Cauchy envelope and
`2((n+3+|tau|)^2+j|L|(n+7/2))<=K_b(n^2+1)`.
After division by 4^j, both the quartic envelope and reference tail tend to
zero independently of j,L,tau. For smooth f and fixed c,j, choose k with
`2k+2>=jc` and apply the normalized theorem with tolerance epsilon/4^j.

Exact declarations in `ConjugateDiagonalGeometry/ThetaSourceRegularityMetric.lean`:

- `thetaSource_uniform_regularity_moments`;
- `thetaSource_uniform_smooth_log_windows`.

Final source-only check 12644 passed for both. Their transitive axiom closures
contain only `propext`, `Classical.choice`, `Quot.sound`. Dependencies
`SourceRegularityWindow` (85864) and `SourceRegularityTail` (13962) also pass
individual checks and standard-only endpoint audits. All three leaves are
wired into the programme umbrella; no umbrella was compiled.
