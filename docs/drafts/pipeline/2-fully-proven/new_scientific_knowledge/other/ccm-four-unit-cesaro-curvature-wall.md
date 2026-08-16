# CCM four-unit Cesàro curvature wall

- **ID:** `ccm-four-unit-cesaro-curvature-wall`
- **Stage:** `2-fully-proven/new_scientific_knowledge`
- **Type:** EXACT REPORTER TRANSPORT / SIGNED TWO-CHANNEL LIFT / MERGER BOUNDARY
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Routes:** `CCM-FU`, `CCM-UR`, `CCM-HG`, `CCM-EP`, `G`, `O`, `CCM-GS`
- **Parent:** `ccm-unit-riesz-completed-source-stieltjes-weld`

## Public claim

After passing from the completed Stieltjes current to CCM-FU's Cesàro primitive, the literal
CCM-UR response is an exact second-order curvature reporter.  Its normalized kernel annihilates
affine Cesàro drift, has one oriented sign wall, and converges to a trace-neutral and
barycenter-neutral two-exponential Krein pair.  The limiting sign wall is

```text
log 16 = 4 log 2.
```

Thus the four-unit scale is forced a second time, independently of the finite CCM matrix
construction: it is the unique asymptotic sign wall of the source-side FU-to-UR reporter.

The result also gives a hard merger boundary.  The UR test is eventually not an autocorrelation,
so neither Route O ground positivity nor Route G floor positivity can prove the UR estimate by
identifying it with one positive restricted-Weil vector.  The lawful lift is signed and
two-channel, exactly of the type required by CCM-HG, CCM-EP, and the oriented exterior branch of G.

This does not prove the remaining one-sided source estimate or RH.

## 1. Completed-source test and two-moment collapse

Retain the completed error and positive kernel

```text
E(s) = 4 sinh(s/2) - sum_(n <= exp s) Lambda(n)/sqrt(n),
k(u) = 3(exp(-u)-exp(-3u/2)).
```

For aperture `t >= 0`, the completed-source unit-Riesz test is

```text
F_t(s) = exp(-s/2) k(t-s)
       = 3(exp(-t+s/2)-exp(-3t/2+s)),        0 <= s <= t.             (1)
```

It vanishes at the moving endpoint.  Stieltjes integration by parts therefore gives the exact
literal response

```text
J(t) = integral_(0,t] F_t(s) dE(s)
     = -integral_0^t E(s) F_t'(s) ds
     = integral_0^t E(s)
         [3 exp(-3t/2+s) - (3/2) exp(-t+s/2)] ds.                    (2)
```

Equation `(2)` is already Lean-proved in
`CCMUnitRieszCompletedSourceWeld.lean`.  It is stronger than equality of meromorphic germs: it
identifies the literal finite-aperture source test and removes every Möbius coordinate.

## 2. Exact transport through the CCM-FU cumulative source

Fix `b>0` and put

```text
w(s)=32/s^3,
q_b(s)=-integral_(b,s] w(v) dE(v),
Q_b(s)=integral_b^s q_b(v) dv.                                     (3)
```

This `q_b` is exactly the corpus's third-grade prime-minus-polar cumulative source.  Split `(2)`
at `b`.  Its fixed head is a linear combination of `exp(-t)` and `exp(-3t/2)`.  On `(b,t]`, set

```text
g_t(s) = F_t(s)/w(s)
       = (3/32)s^3[exp(-t+s/2)-exp(-3t/2+s)].                        (4)
```

Since `dq_b=-w dE`, `q_b(b)=Q_b(b)=0`, and `g_t(t)=0`, two integrations by parts give

```text
J_tail(t)
 = Q_b(t) g_t'(t) - integral_b^t Q_b(s) g_t''(s) ds,                 (5)

g_t'(t)=-(3/64)t^3 exp(-t/2).                                      (6)
```

No asymptotic or divisor information enters `(5)`.

Write

```text
P(s)=6s+3s^2+s^3/4,
R(s)=6s+6s^2+s^3.                                                    (7)
```

Direct differentiation of `(4)` yields

```text
g_t''(s)=(3/32)[exp(-t+s/2)P(s)-exp(-3t/2+s)R(s)].                  (8)
```

With lag `u=t-s`, normalize `(5)` by `exp(t/2)/t^3`:

```text
exp(t/2) J_tail(t)/t^3
 = -(3/64)Q_b(t) + integral_0^(t-b) Q_b(t-u) K_t(u) du,              (9)

K_t(u)=(3/32)[exp(-u)R(t-u)/t^3
                  -exp(-u/2)P(t-u)/t^3].                            (10)
```

This is the exact FU-to-UR reporter operator.

## 3. Unique sign wall and the four-unit limit

For `s>0`,

```text
R(s)/P(s)=4(s^2+6s+6)/(s^2+12s+24).                                (11)
```

The ratio in `(11)` is strictly increasing from `1` to `4`, because its derivative has positive
numerator

```text
24(s^2+6s+12).                                                       (12)
```

Consequently `K_t(u)` changes sign exactly once.  Its wall is determined implicitly by

```text
u = 2 log(R(t-u)/P(t-u)),                                           (13)
```

lies strictly between `0` and `log 16`, and tends to `log 16` as `t -> infinity`.  At fixed lag,

```text
K_t(u) -> K_infinity(u)
 = (3/32)[exp(-u)-(1/4)exp(-u/2)].                                  (14)
```

The limiting kernel is positive for `0<u<log 16`, zero at `log 16`, and negative afterward.

## 4. Exact affine blindness

For the full lower endpoint `b=0`, `g_t(0)=g_t'(0)=g_t(t)=0`.  Fundamental theorem and one
integration by parts give

```text
integral_0^t K_t(u) du = 3/64,                                     (15)
integral_0^t u K_t(u) du = 0.                                      (16)
```

The boundary atom `-(3/64)delta_0` in `(9)` therefore makes the complete reporter measure have
both total mass zero and first moment zero.  It annihilates every affine function of the Cesàro
coordinate.  Its second moment is strictly negative:

```text
integral_0^t u^2 K_t(u) du
 = -2 exp(t/2)/t^3 integral_0^t g_t(s) ds < 0,       t>0.            (17)
```

Thus UR does not measure size or slope of `Q`; it measures oriented curvature.  In the abstract
source category even quadratic `Q` can have a UR response of polynomial times `exp(-t/2)` while
violating CCM-FU's linear-growth gate.  Hence no reporter-only reverse implication from UR to FU
exists.  Conversely, CCM-FU's absolute linear bound controls `(9)` and implies the UR bound, but
that direction supplies no new RH evidence because the FU premise already closes RH.

## 5. Canonical signed two-channel lift

The limiting interior kernel has the exact positive-channel decomposition

```text
K_infinity(u)=|ell_fast(u)|^2-|ell_slow(u)|^2,

ell_fast(u)=sqrt(3/32) exp(-u/2),
ell_slow(u)=sqrt(3/128) exp(-u/4).                                  (18)
```

The two positive leak channels obey

```text
integral |ell_fast|^2 - integral |ell_slow|^2 = 3/64,
integral u|ell_fast|^2 = integral u|ell_slow|^2 = 3/32.             (19)
```

The boundary counterterm `-(3/64)delta_0` cancels the mass mismatch, while the barycenters already
match.  This is a canonical **reporter-selected** Krein decomposition: each scalar channel is
positive and the signed scalar reporter is recovered after applying the fundamental symmetry.  It
is not yet a source-selected completed-Xi covariance, and it is not a scalar Herglotz background.
The associated fast-minus-slow operator kernel is indefinite; the separate boundary-pulse card
records the exact negative two-point determinant.

## 6. Autocorrelation obstruction at two units

The derivative of the literal test `(1)` at the origin is

```text
F_t'(0)=3 exp(-3t/2)[exp(t/2)/2-1].                                 (20)
```

It is positive exactly when

```text
t>log 4=2 log 2.                                                     (21)
```

Indeed `F_t` then has its strict maximum at `s=t-log 4`, not at zero.  A stationary Hilbert-space
autocorrelation satisfies `|C(s)|<=C(0)`; a differentiable real autocorrelation has derivative
zero at the origin.  Therefore the cofinal UR test is not one positive restricted-Weil/Sonin
autocorrelation.  Any attempted direct reduction to Route O or G-floor positivity is false.

## 7. Route consequences

- **CCM-FU / CCM-UR:** same source, now with exact reporter ordering.  FU controls global Cesàro
  size; UR detects local curvature and forgets affine drift.  Combining their endpoint criteria
  does not multiply evidence.
- **Route O / G-floor:** direct positive-ground or autocorrelation realization is excluded by
  `(20)--(21)`.  A lawful bridge must retain boundary orientation or an indefinite channel.
- **CCM-HG:** `(18)--(19)` supplies a canonical reporter-selected relative leak pair and boundary
  counterterm.  It yields a positive scalar boundary pulse, but literal completed-Xi source landing
  and the sharp density law remain absent.
- **CCM-EP:** this pair does **not** provide a positive operator-valued lift.  Every separated
  two-point covariance compression has negative determinant.  Any EP background must add genuinely
  operator-valued completed-source structure beyond this rank-two difference.
- **G-exterior:** the fast/slow pair carries a fixed orientation and is not a Gram determinant.
  It is a candidate two-port return class, but completed-mode/root-retained landing remains open.
- **CCM-GS:** the affine-blind second-order law matches reduced-resolvent Hessian order, but gives no
  cofinal separating margin.  Any proposed GS merger must transport this oriented curvature through
  the true ground, not merely compare scalar Hessians.

## 8. Hostile novelty and theatre audit

### Known material

- Riesz and Hardy--Littlewood growth criteria and Báez-Duarte's generic Möbius-convolution theorem
  are literature.
- The completed Stieltjes current, CCM-FU third-grade source, unit-Riesz transform, and common
  meromorphic germ are corpus results.
- Integration by parts and exponential-kernel moment calculations are elementary methods.

### Candidate new residue

Targeted searches found no source containing the exact transport `(5)--(10)`, the unique moving
sign wall `(13)`, its four-unit limit `(14)`, the mass/barycenter cancellation `(15)--(19)`, or the
two-unit autocorrelation obstruction `(20)--(21)`.  Novelty is claimed only for this composition
and route interpretation, not for generic Möbius convolution or Laplace calculus.  No priority
claim is made; status remains `[NOVELTY UNVERIFIED]`.

### Falsifiers

1. If `q_b` is not the literal CCM-FU cumulative source, the claimed merger fails.  Equation `(3)`
   is exactly its proved Stieltjes definition.
2. If the kernel were nonnegative, the route interpretation would collapse.  Equations
   `(11)--(14)` prove one sign change.
3. If the test were a positive autocorrelation cofinally, O/G positivity could close UR.  Equation
   `(20)` gives a direct contradiction after `log 4`.
4. No estimate for the literal `Q_b`, no Hankel density bound, no ground selection, and no RH
   conclusion is asserted.

Verdict: `SURVIVES INTERNAL HOSTILE AUDIT`; significant source geometry and exact merger boundary,
not solution of remaining arithmetic orientation estimate.

## 9. Lean status

`CCMUnitRieszCompletedSourceWeld.lean` proves unconditionally:

- exact pole-filled completed-source factorization;
- strict sign and two-sided bounds of source-free correction;
- positive two-exponential aperture kernel;
- literal Stieltjes test `(1)` and endpoint vanishing;
- completed-error integration-by-parts identity `(2)`.

`CCMUnitRieszFUCurvatureTransport.lean` now formalizes the literal FU source identity, first and
second integrations by parts, exact curvature transport, and endpoint coefficient.  The existing
curvature leaf formalizes `(4)--(21)`.  `CCMUnitRieszHankelBoundaryPulse.lean` formalizes the
fast/slow leak profiles, scalar pulse, four-unit square slack, and operator-covariance obstruction.
All statements are unconditional; no hypothesis stands in for the literal `E`, `q_b`, or `Q_b`.
