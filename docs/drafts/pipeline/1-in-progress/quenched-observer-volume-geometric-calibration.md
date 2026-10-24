# Quenched observer-volume calibration without a minimum gap

- **ID:** quenched-observer-volume-geometric-calibration
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean proof in progress
- **Statement:** Temporal lower-tail control of a normalized observer Gram determinant through geometric aggregation of scalar phase small-ball bounds, with no rank factor.

## Goal

Improve conditioning in the ordinary static-Hamiltonian coarea problem without
assuming spectral separation or independence between spectral coordinates. This
does NOT supply the remaining occupied complete-circuit image estimate.

## Conjecturing and hostile audit

1. Paired-observer injectivity by itself supplies a useful fixed-error circuit
   union bound: rejected. The existing bound amplifies error by 2304 n^3 and
   still pays target image size. It is not the claimed fixed-error estimate.
2. The static Ward reduction alone can exclude the post-ramp circuit set:
   rejected as a proof strategy. It erases time; early easy orbit targets remain
   admissible in the static event. No quantitative post-ramp conclusion follows.
3. Volume, rather than the least singular value, admits a rank-free temporal
   lower tail: the exact statement below has a complete paper proof.

Novelty verdict: **BRIDGE**. Scalar uniform-sinc control is related to
de Pradenne--Cotler--Huang, arXiv:2606.05690. Geometric p-value aggregation with
factor e is known (Mattner; Vovk--Wang, arXiv:1212.4966). Cauchy--Binet and weighted
AM--GM are classical. The observer-volume application and its exact weighted
frequency scale need an application-specific novelty audit; do not advertise the
aggregation inequality or this bridge as a new universal physical law.

## Exact statement

Let J be a real N-by-m matrix, m >= 1, with D = det(J^T J) > 0. Let S run over
m-element row subsets, p_S = det(J_S)^2/D, and

    a_i = (1/m) sum_{S containing i} p_S.

Thus p and a are probability weights. For any real frequencies lambda_i and T>0,
put g_i(t) = |t sinc(lambda_i t/2)|, including g_i(t)=t when lambda_i=0, and

    K_i = |lambda_i|/2 + pi/T,
    K_geo = exp(sum_i a_i log K_i),
    G(t) = [det(J^T diag(g_i(t)^2) J)/D]^(1/(2m)).

For uniform t in [0,T], every x>=0 satisfies

    P(G(t) <= x) <= min(1, e*K_geo*x).

All quantities are explicit from the fixed observer and spectrum. No random
Hamiltonian, nonzero gap, simple spectrum, or independent phase assumptions.
The singular observer has D=0 and must remain an explicit separate branch.

## Dependency-closed paper proof

### Scalar phase bound

For d=|lambda_i|>0, set L=dT/2 and u=dx/2. On [0,pi/2], the chord bound
sin(y)>=2y/pi puts the sublevel |sin(y)|<=u in [0,pi*u/2]. Reflection handles
the other half-period. Hence each complete period of |sin| contributes at most
pi*u. Cover (0,L] by floor(L/pi)+1 complete periods. Consequently

    P(g_i<=x) <= (L+pi)*u/L = d*x/2 + pi*x/T = K_i*x.

For d=0, P(t<=x)<=x/T<=K_i*x. The same bound at x=0 proves each zero set
null. Endpoint conventions do not affect the estimates.

### Gram volume and probability weights

Cauchy--Binet gives sum_S p_S=1 and

    det(J^T diag(g_i^2) J)/D = sum_S p_S prod_{i in S} g_i^2.

Weighted AM--GM, away from the null zero set, gives

    G >= exp(sum_i a_i log g_i).

The definitions imply a_i>=0 and sum_i a_i=1: each subset has m members.

### Arbitrarily dependent geometric aggregation

Put P_i=min(1,K_i*g_i). Then P(P_i<=u)<=u for 0<=u<1. Let Z_i=-log P_i,
defined arbitrarily on the null zero set. Hence Z_i>=0 and P(Z_i>s)<=exp(-s)
for s>=0. For every b>=0, layer-cake gives

    E[(Z_i-b)_+] <= exp(-b).

For Y=sum_i a_i Z_i, convexity of positive part gives

    E[(Y-b)_+] <= sum_i a_i E[(Z_i-b)_+] <= exp(-b).

When y>=1, {Y>=y} forces (Y-(y-1))_+>=1, so Markov gives
P(Y>=y)<=exp(1-y). For y<1 use P<=1. Since

    exp(-Y) = prod_i P_i^a_i <= K_geo*G,

{G<=x} implies {Y>=log(1/(K_geo*x))}, proving the result. At x=0 use the
null zero set; the scalar tail also gives it by continuity from above.

### Limitation and positive content

The lack of an exponential-in-m tail is real: equal nonzero frequencies and
J=I give G(t)=g(t), independently of m. The positive content is that a SINGLE
source-time exceptional set controls volume at any rank, and the geometric
frequency scale replaces a minimum-gap or least-singular-value penalty. It does
not bound sheet multiplicity or occupied circuit-target image; those must not
be silently dropped.

## Formalization plan

1. Exact weighted active-minor identity and normalized minor probabilities.
2. Deterministic logarithmic volume bound without selecting one largest minor.
3. Scalar sinc sublevel estimate on a finite interval.
4. Known geometric aggregation theorem, with all tail inputs proved for sinc.
5. Specialize to the spectral-coordinate differential of one static Hamiltonian.

Only leaf checks with `lake --old env lean`; build missing dependency artifacts
only, no umbrella builds. No new scientific input may be hidden in a capstone
premise. Formalization status remains INCOMPLETE until scalar and physical inputs
are discharged.

## Log

- 2026-10-24: Exact statement and paper proof; parents identified before Lean.
- 2026-10-24: `HTGeometry/ObserverJacobianVolumeResponseLaw.lean` closes the
  exact weighted-minor identity, normalized incidence probabilities, and the
  logarithmic determinant lower bound. Leaf audit passed; the new capstones use
  only `propext`, `Classical.choice`, and `Quot.sound`. Imported by the HTGeometry
  umbrella, which was not compiled. No olean was rebuilt.
- `HTGeometry/SincWindowSmallBallLaw.lean` closes the scalar estimate, including
  zero/negative frequencies, empty windows, and negative thresholds. Scratch
  audit passed with only the three standard logical axioms; identical theorem
  source was installed and wired into the uncompiled umbrella. The complete-
  period cover improves the boundary constant from `2*pi/T` to `pi/T`.
  The probabilistic volume capstone and physical differential specialization
  remain unformalized.
- Anti-theatre verdict: this closes a useful deterministic bridge, not the
  occupied complete-circuit image estimate. No novel physical law or full
  Brown--Susskind theorem has been proved.
