# Actual infinite partition: density-tail and limit-order boundary

- **ID:** LI-CLOCK-INFINITE-PARTITION-DENSITY-TAIL-BOUNDARY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (complete author, root and independent paper/source audits PASS; Lean pending)
- **Source:** [fixed-source endpoint boundary](../3-formalized/li-clock-partition-density-ratio-endpoint-boundary.md), [actual finite Volterra partition](../3-formalized/li-clock-finite-partition-volterra-positive-area.md)
- **Statement:** Literal infinite odd/even interval source has raw difference-density tail `(log(2)/2)*exp(-abs(x)/2)` with sharp error order `exp(-3*abs(x)/2)`. Normalized moment and complete Borel ratios tend `lambda=2*log(2)/Z_A^2<5040/5041<1`. Actual finite sources converge uniformly on growing complex disks `norm(z)<=c*log(2N)`, `0<=c<1/16`, forcing the opposite ratio and kernel-gap limits from fixed-prefix endpoint limits. Exact spatial bulk ratios tend the same lambda. No inverse-clock, compensation or RH sign follows.

## Gates and scope

- [x] Card created before new paper proof or Lean.
- [x] Documented prior search; ALL20 candidates and ALL20 source arguments inspected by author and independent auditor, plus all lexical followup hits.
- [x] Dependency-closed complete density proof, sharp periodic correction and exact symbolic lambda<1 certificate.
- [x] Every moment and full real/complex Borel term retained; exact quantitative finite-source and growing-window exchange.
- [x] Both noncommuting source/order/clock limits and exact spatial-bulk survivor.
- [x] Root READ ALL508+84 proof lines and literal installed source; independent pole READ ALL592/source/overlap PASS.
- [ ] Exact Lean formalization, independent full source review, named/direct/all-public foundational checks and wiring.
- [ ] Publication/novelty audit.

Root owns this card and integration. `LiClockPairedEtaInfinitePartitionMeasure.lean`, `LiClockPairedEtaInfinitePartitionDensityTail.lean` and `LiClockPairedEtaInfinitePartitionBorel.lean` are FINAL/wired for complete M1–M8, T1–T7 and B1–B8 plus the four audited raw-loss interfaces. Current owns the remaining `LiClockPairedEtaInfinitePartitionBoundary.lean`; actual consumers import only exact FINAL dependencies. Boundary L1–L7 implementation is released with every spatial D1–D6 and joint/iterated target retained. Existing FINAL leaves remain frozen. Full relative Volterra/cumulant forcing expansion remains a separate open formal target. The actual residual `Re(C-K_N+H_N)>=0` and RH remain OPEN.

## Immutable paper certificates and source coverage

Main508: `/tmp/li_current_infinite_partition_paper.md`, SHA256 `50886f4d464dee5502ed0ac263632d19613e20c764eaf176f06bfb659da3a315`.
Spatial84: `/tmp/li_current_infinite_partition_spatial_delta.md`, SHA256 `bebe6acd15eb1efecc9a30d7399f24bc842202c03def11729e3460dc52d096aa`.
Independent full certificate: `/tmp/li_pole_infinite_partition_paper_audit.md`. Complete proof texts preserved below for cross-session durability.

Research `/tmp/li_current_infinite_partition_research.json`: direct documented command, terminal0,7.403s, generation1152111 matches63238/63238 indexed files, pendingfiles0, inventory complete, partial=false/errors=[]/unfinished=[], ALL20 candidates+20 source arguments reviewed, no proof ideas/ingredient sets. Compiler43 compiled_snapshot,2 error,10179 notapplicable,47661 pending,2660 stale,38 stale_snapshot,1 umbrella_source_only,2654 unavailable. Semantic coverage unmeasured; background refresh incomplete. Lexical followup `/tmp/li_current_infinite_partition_overlap.json`: terminal0, all20 returned hits reviewed,45 eligible/12 modules, no coverage fields inferred. Existing one-source centered half-density transform overlaps the mechanism, not the literal two-indicator log(2) correlation. No corpus absence, compiled applicability or publication novelty claim.

## Log

- 2026-09-30 08:13 UTC — Created before prior-source and paper exploration. Actual growing-window residual sign and RH remain open.
- 2026-09-30 09:12 UTC — ALL508+84 dependency-closed paper/source proof lines and every research result audited by author, root and independent pole: PASS. Sharp periodic correction, complete complex growing-window exchange, spatial bulk and both noncommuting limits retained. Moved Stage2; formal architecture plan only, no new Lean release or route retirement.

## Complete audited main proof

# Literal infinite eta partition: exact density tail and limit-order boundary

Status: author dependency-closed paper proof PASS; independent complete proof/source audit pending.
Mode: paper only. No Lean/compiler/numerical job or tree write. Source scopes remain frozen.
Parent card: docs/drafts/pipeline/1-in-progress/li-clock-infinite-partition-density-tail-boundary.md.
Date: 2026-09-30. All constants below are exact, never inferred from samples.

## 1. Literal source, domains and probability normalization

Let S = union over n>=0 of (log(2n+1), log(2n+2)], and let nu_A be
Lebesgue measure restricted to S. These intervals are pairwise disjoint; their
countable union, with every interval retained, is the installed actual source.
Let nu_U be Lebesgue measure restricted to (0,infinity). Then nu_A<=nu_U.
No divisor, functional equation, nonvanishing, RH or inverse-clock sign is assumed.

Define f_A(u)=exp(-u/2)*1_S(u), f_U(u)=exp(-u/2)*1_(0,infinity)(u),
Z_A=integral_R f_A, Z_U=integral_R f_U=2. Both are finite and positive;
for A retain the first interval (0,log2]. Also Z_A<2 because the omitted
interval (log2,log3) has positive half-tilted mass. Let Z_*=Z_A,1=2-sqrt2>0.
For the actual finite N>=1, S_N is the union over n<N; its normalizer Z_A,N
satisfies Z_*<=Z_A,N<=Z_A. All normalized laws below retain Z squared.

The normalized one-coordinate laws have densities f_X/Z_X. The literal
independent product law has density f_X(u)f_X(v)/Z_X^2, X=A,U. Its difference
pushforward has the nonnegative raw density

  g_X(x)=integral_R f_X(v+x)f_X(v)dv,
  rho_X(x)=g_X(x)/Z_X^2.

This is a measure identity, not merely a moment formula: substitute u=v+x
in the nonnegative product integral (linear determinant one), and apply Tonelli
for nonnegative Borel tests. For integrable tests apply the corresponding
absolute-integrability statement. In particular integral_R g_X=Z_X^2.
Coordinate swap gives g_X(-x)=g_X(x). For all x, 0<=g_A(x)<=g_U(x), and

  g_U(x)=exp(-|x|/2),  rho_U(x)=exp(-|x|/2)/4.

The raw autocorrelations have continuous representatives given by these very
integrals. For example, for x_k->x the translated indicator converges for
all v outside the countable shifted interval endpoints, and the integrands
are dominated by exp((|x|+1)/2)*exp(-v)*1_(v>0) eventually. Dominated convergence
proves continuity; no pointwise convergence at interval endpoints is asserted.

At Re(s)>0, A(s)=integral_S exp(-su)du is the installed pairedEtaLaplacePartition;
A(s)=pairedEtaCore(s)/s there. Z_A=A(1/2)>0. The difference moment generating
function on |Re(z)|<1/2 is exactly

  M_A(z)=A(1/2-z)*A(1/2+z)/Z_A^2,
  M_U(z)=1/(1-4z^2).

Absolute convergence licenses this Fubini identity: g_A<=g_U and
integral exp(Re(z)*x)g_U(x)dx is finite in this strip. It also licenses all
fixed-order derivatives there (polynomial times a strictly interior
exponential envelope). No identity outside this strip is silently imposed.
The entire Borel kernels below are different transforms from these MGFs.

## 2. Exact arithmetic-space density identity

Let alpha be the 2-periodic indicator of the intervals (2k+1,2k+2], k in Z.
For w>=1, alpha(w)=1_S(log w); all endpoint conventions agree there and in
any event endpoints are Lebesgue-null. For x>=0 set r=exp(x)>=1. Substitution
w=exp(v), including dv=dw/w, gives the exact complete source identity

  exp(x/2)*g_A(x)=H(r),
  H(r)=integral_1^infinity alpha(w)*alpha(rw)/w^2 dw.                 (2.1)

This retains the first indicator and every oscillating second-source interval.
It is not replacement of S by a contiguous interval. Since alpha is bounded,
all integrals and interval sums in this section converge absolutely.

Write a_n=2n+1, b_n=2n+2. Then

  integral_1^infinity alpha(w)/w^2 dw
    = sum_n (1/a_n-1/b_n) = log2.                                  (2.2)

For completeness, the M-pair partial sum equals
integral_0^1 (1-y^(2M))/(1+y)dy. Dominated convergence gives
integral_0^1 1/(1+y)dy=log2. The paired series is positive and convergent;
no rearrangement of a conditionally convergent unpaired series is used.

## 3. Quantitative complete tail: exact periodic primitive

Define the continuous 2-periodic, locally absolutely continuous B by

  B(s)=1/4-s/2       on 0<=s<=1,
  B(s)=s/2-3/4       on 1<=s<=2.

Its a.e. derivative is alpha(s)-1/2, its mean over a period is zero,
|B|<=1/4, B(even integer)=1/4, B(odd integer)=-1/4. For any r>=1,
integration by parts on the full retained interval [a_n,b_n] gives

  integral_a^b (alpha(rw)-1/2)/w^2 dw
    = [B(rw)/(r*w^2)]_a^b + (2/r)*integral_a^b B(rw)/w^3 dw.

The absolute value is at most
(1/(4r))*(a^-2+b^-2)+(1/(4r))*(a^-2-b^-2)=a^-2/(2r).
Summing every retained interval is licensed by this summable absolute bound.
The Basel identity gives sum_n a_n^-2=pi^2/8; therefore, using (2.2),

  |H(r)-log2/2| <= pi^2/(16r)                           for r>=1.   (3.1)

Consequently for every x>=0,

  |exp(x/2)*g_A(x)-log2/2| <= (pi^2/16)*exp(-x),                    (3.2)
  exp(x/2)*g_A(x) -> log2/2                             as x->+infinity.

Evenness extends the exact pointwise discrepancy to all real x:

  |g_A(x)-(log2/2)*exp(-|x|/2)|
    <= (pi^2/16)*exp(-3|x|/2).                                    (3.3)

No pointwise alpha(rw) limit exists or is needed. The averaging estimate, not
an unjustified dominated-convergence claim for this oscillating indicator,
produces the tail constant.

## 4. Stronger arithmetic correction and sharpness of the error order

The same literal computation identifies the first correction completely.
Let D be the continuous 2-periodic primitive of B with D(0)=0:

  D(s)=(s-s^2)/4              on 0<=s<=1,
  D(s)=(s^2-3s+2)/4          on 1<=s<=2.

Then |D|<=1/16 and D'=B a.e. Define the continuous 2-periodic function

  P(r)=sum_n [B(r*b_n)/b_n^2-B(r*a_n)/a_n^2].

The series converges absolutely and uniformly on all real r, by the square
summability of the endpoints. Summing the preceding exact integration-by-
parts identities gives

  H(r)-log2/2=P(r)/r+(2/r)*integral_1^infinity alpha(w)B(rw)/w^3 dw.

A second integration by parts on each retained interval, now with D, bounds
|integral_a^b B(rw)/w^3 dw| by a^-3/(8r). Thus if S_3=sum_n a_n^-3<infinity,

  |H(r)-log2/2-P(r)/r| <= S_3/(4r^2)                  for every r>=1. (4.1)

This has no unproved oscillatory-integral remainder. Exact endpoint values give

  P(2m)=-pi^2/48,   P(2m+1)=pi^2/24.

Indeed sum_n(a_n^-2-b_n^-2)=pi^2/12 and
sum_n(a_n^-2+b_n^-2)=pi^2/6, by separating even and odd Basel terms.
Hence along r=2m and r=2m+1 respectively,

  r*(H(r)-log2/2) -> -pi^2/48 and pi^2/24.

Equivalently the density error in (3.3), multiplied by exp(3x/2), has these
two different nonzero limits along x=log(2m) and x=log(2m+1). Its exponential
order cannot be improved to little-o(exp(-3x/2)). These are exact symbolic
subsequences; no sample or numerical experiment is used.

## 5. Exact normalized constant and a symbolic certificate below one

The infinite half-tilt mass is

  Z_A=integral_1^infinity alpha(w)*w^(-3/2)dw
     =2*sum_n [a_n^(-1/2)-b_n^(-1/2)].                            (5.1)

Again the paired positive series is absolutely convergent as paired terms;
the separate unpaired square-root reciprocal series diverge. Define

  lambda=2*log2/Z_A^2 >0.                                         (5.2)

The normalized tail ratio is exactly lambda because rho_U=exp(-|x|/2)/4.
In particular it is not the fixed-finite-N normalizer ratio (Z_U,N/Z_A,N)^2.

To establish lambda<1 without any numerical inference, retain the first two
arithmetic periods [1,3] and [3,5]. On every remaining period [2n+1,2n+3],
the decreasing function w^(-3/2) has at least half its integral in the
retained first unit interval. Therefore

  Z_A >= 1-sqrt2+2/sqrt3+1/sqrt5.

The exact squared inequalities 9801>9800, 676>675, 81>80 give respectively
sqrt2<99/70, 2/sqrt3>15/13, 1/sqrt5>4/9. Hence

  Z_A > 1-99/70+15/13+4/9 = 9697/8190
      = 71/60+11/16380 >71/60.

Moreover the positive exponential Taylor terms imply
exp(7/10)>=1+7/10+(7/10)^2/2+(7/10)^3/6=12013/6000>2,
so log2<7/10. Combining these strictly proved bounds gives

  0<lambda<5040/5041<1.                                          (5.3)

This crude rational certificate is sufficient; lambda itself, not an
arbitrary rational refinement, is the invariant and sharp asymptotic constant.

## 6. Complete moments: exact geometric remainder

Let d_A,j=integral_R x^(2j)rho_A(x)dx and d_U,j similarly. These are exactly
the even difference moments of the normalized independent half-tilt product.
Their integrability follows from g_A<=exp(-|x|/2). Both zeroth moments are one.
All moments are strictly positive: for A, use two separated positive-length
subintervals inside the first retained logarithmic interval; for U this is
immediate. Integration by parts induction gives
integral_0^infinity x^m exp(-a*x)dx=m!/a^(m+1) for integer m>=0, a>0.
Thus

  d_U,j=4^j*(2j)!,   0<d_A,j<=(4/Z_A^2)*d_U,j.                    (6.1)

Integrate the all-real discrepancy (3.3) against x^(2j), retaining both
halflines. Its absolute raw moment error is at most
2*(pi^2/16)*(2j)!*(2/3)^(2j+1). After both probability normalizers,

  |d_A,j/d_U,j-lambda| <= C*9^(-j),
  C=pi^2/(12*Z_A^2),                              every integer j>=0. (6.2)

In particular d_A,j/d_U,j->lambda<1 as j->infinity.
An optional exact degree certificate follows from pi<4 and Z_A^2>7/5:
C<20/21. For j>=4,

  d_A,j/d_U,j <5040/5041+20/(21*6561)<1,

since 20*5041=100820<137781=21*6561. Therefore every j>=4 has d_A,j<d_U,j.
No all-order inequality d_A,j<=d_U,j is asserted for j=1,2,3; these finitely
many orders are not determined by this coarse discrepancy certificate.

## 7. Entire full Borel kernels and exact infinite-source boundary

Define the complete complex-clock Borel kernels, with BOTH raw even factorials,

  B_A(z)=sum_j d_A,j*z^(2j)/[(2j)!]^2,
  B_U(z)=sum_j d_U,j*z^(2j)/[(2j)!]^2=cosh(2z).

By (6.1), the complete norm sum of B_A terms is at most
(4/Z_A^2)*cosh(2|z|). On |z|<=T the same summable positive coefficient
majorant proves absolute convergence and uniform convergence of the FULL
series, hence entire analytic B_A. The kernel is real and >=1 on real clocks.
The MGF-strip restriction in section 1 is not a restriction on this Borel clock.

Subtract the two absolutely convergent series using (6.2). For every complex z,

  |B_A(z)-lambda*cosh(2z)| <= C*cosh(2|z|/3).                       (7.1)

Thus the exact entire decomposition B_A(z)=lambda*cosh(2z)+R(z) has
|R(z)|<=C*cosh(2|z|/3). For real t>=0,

  |B_A(t)/cosh(2t)-lambda| <=2C*exp(-4t/3).                        (7.2)

The positive denominator is literal cosh(2t), not a totalized complex quotient.
It follows that

  B_A(t)/B_U(t)->lambda<1,
  exp(-2t)*B_A(t)->lambda/2,
  exp(-2t)*(B_U(t)-B_A(t))->(1-lambda)/2>0,
  B_U(t)-B_A(t)->+infinity.                                      (7.3)

No pointwise inverse-clock/cumulant sign follows. Nor does (7.1) assert
B_A(t)<=B_U(t) for every finite clock: at t=0 both equal one, whereas the
asymptotic comparison constant lambda is below one.

## 8. Literal finite-to-infinite convergence, with fixed limits first

For N>=1 let L_N=log(2N), S_N be the actual complete union over n<N, and
U_N=(0,L_N]. EXACTLY S_N=S intersect U_N, since the next retained interval
starts at log(2N+1)>L_N. Write raw and normalized finite densities and moments
as in sections 1 and 6, and use the installed finite-source definitions.

The finite raw product integrands increase pointwise to the infinite actual
ones; same for U_N. For each fixed order j, monotone convergence, followed
by the positive normalizer limit, proves

  Z_A,N->Z_A,  Z_U,N->2,
  d_A,N,j->d_A,j,  d_U,N,j->d_U,j.

This is first a fixed-order assertion. For each fixed compact clock disk |z|<=T,
raw product domination by the infinite reference gives the UNIFORM-IN-N bound

  d_X,N,j<=(4/Z_*^2)*d_U,j,  X=A,U, N>=1.

The complete cosh(2T) coefficient majorant then licenses exchanging the
fixed-N limit with the entire Borel sum, uniformly on this compact disk:
B_A,N->B_A and B_U,N->cosh(2z). A fixed-order or fixed-clock limit alone
would not license any arbitrary growing order/clock diagonal.

For raw densities the noncommutation is already visible: for fixed N,
g_A,N(x)=0 when |x|>=L_N, so its exp(x/2)-normalized positive tail is zero;
for each fixed x, g_A,N(x)->g_A(x), whose normalized tail is log2/2.

## 9. New quantitative growing-window exchange: complete product loss

This section explicitly proves a joint-window estimate rather than relying
on section 8's compact convergence. Fix 0<=c<1/16 and define

  kappa_c=1/2-2*sqrt(c)>0,  alpha_c=1/2-2c>0.

For X=A,U, let R_X,N(z)=Z_X,N^2*B_X,N(z) and R_X(z)=Z_X^2*B_X(z) denote
the complete RAW Borel kernels. Put E(y)=sum_j y^(2j)/[(2j)!]^2. Absolute
moment summability already proved licenses the exact integral representations
R_X(z)=integral_R g_X(x)*E(z*x)dx and their finite counterparts.
For y>=0, E(y)<=exp(2*sqrt(y)): E is a subseries of
sum_m y^m/(m!)^2, whose positive terms are the diagonal subseries in
exp(sqrt(y))*exp(sqrt(y))=exp(2sqrt(y)). For complex y, |E(y)|<=E(|y|).
All these statements concern complete summable positive series.

Any raw product mass removed in passing from the infinite actual source to
S_N has at least one coordinate >L_N. Its positive weight is bounded by
the corresponding removed product mass for U_N. Restricting to u=v+x yields

  0<=g_A(x)-g_A,N(x)<=g_U(x)-g_U,N(x).

For x>=0 the last deficit is EXACTLY

  h_L(x)=exp(x/2-L)   if 0<=x<L,
         exp(-x/2)   if x>=L,                     L=L_N.

(The boundary values agree.) This uses the same full product loss; it does
not discard cross-interval terms. For |z|<=cL, the complete integral bound is

  |R_X(z)-R_X,N(z)|
    <=2*integral_0^infinity h_L(x)*exp(2sqrt(|z|*x))dx
    <=2*(L+1/kappa_c)*exp(-kappa_c*L).                            (9.1)

Indeed on [0,L], both x<=L and |z|<=cL give the integrand <=exp(-kappa_c L).
On [L,infinity), sqrt(|z|x)<=sqrt(c)*x gives integrand <=exp(-kappa_c x).
Thus both integrations are elementary and the inequality is valid for ALL
complex clocks in this disk. Every infinite/finite sum exchange was licensed
by absolute convergence before using the inequality.

For both sources, 0<=Z_X-Z_X,N<=2exp(-L/2), Z_X,N>=Z_*, Z_X<=2,
and |R_X(z)|<=4cosh(2|z|). Therefore

  |B_X,N(z)-B_X(z)|
    <= |R_X,N(z)-R_X(z)|/Z_X,N^2
       +|R_X(z)|*(Z_X^2-Z_X,N^2)/(Z_X,N^2*Z_X^2)
    <= E_N(c),

  E_N(c)=(2/Z_*^2)*(L_N+1/kappa_c)*exp(-kappa_c*L_N)
           +(32/Z_*^4)*exp(-alpha_c*L_N),                         (9.2)

uniformly for |z|<=cL_N and X=A,U. In the second term use
Z_X^2-Z_X,N^2=(Z_X-Z_X,N)*(Z_X+Z_X,N)<=8exp(-L/2),
Z_X,N^2*Z_X^2>=Z_*^4, cosh(2|z|)<=exp(2cL).
All constants are finite, positive and exact. E_N(c)->0 as N->infinity.
The case c=0 is also valid; a growing-clock diagonal requires c>0.

Hence if N_m->infinity, t_m->+infinity and eventually
0<=t_m<=c*log(2N_m), for one fixed 0<c<1/16, then

  B_A,N_m(t_m)/B_U,N_m(t_m)->lambda<1,
  exp(-2t_m)*B_A,N_m(t_m)->lambda/2,
  exp(-2t_m)*B_U,N_m(t_m)->1/2,
  B_A,N_m(t_m)-B_U,N_m(t_m)->-infinity.                           (9.3)

For the ratio, use B_U,N>=1 and B_A/cosh(2t)<=4/Z_A^2: the discrepancy from
the infinite ratio is <=E_N(c)*(1+4/Z_A^2), then apply (7.2).
These are qualified joint limits with a proved uniform absolute bound.
They imply uniform negativity of the kernel gap above a fixed large lower
clock T inside these windows, once N is sufficiently large. They do not
imply any sign of the literal inverse Volterra response or completed eta clock.
No arbitrary N/order or unconstrained N/clock exchange is asserted.

## 10. Fixed finite endpoint limits remain different

The independently audited fixed-N endpoint paper proves, for N>=2,

  lim_(j->infinity) d_A,N,j/d_U,N,j = kappa_N=(Z_U,N/Z_A,N)^2>1,
  lim_(t->infinity) B_A,N(t)/B_U,N(t)=kappa_N,
  B_A,N(t)-B_U,N(t)->+infinity.

For N=1 the actual and reference sources agree identically. In particular

  lim_N lim_j d_A,N,j/d_U,N,j = 4/Z_A^2,
  lim_j lim_N d_A,N,j/d_U,N,j = lambda=2log2/Z_A^2,

and the analogous two iterated real-clock Borel ratios differ in exactly the
same way. Here 4/Z_A^2>1, whereas lambda<1. Thus endpoint passage to a fixed
finite support boundary and infinite-source averaging are distinct mechanisms.
The joint window (9.3) has the infinite-source sign, while each fixed N has
positive gap eventually beyond some N-dependent clock. There is no contradiction:
the fixed-N tail estimate has no uniform threshold across N and its retained
endpoint strip shrinks as N increases.

## 11. Source/API ledger and prior overlap

Source statements below were read from the installed tree, not guessed.
No Lean API applicability/build verification is claimed for this paper-only task.

- InfiniteLaplaceMeasure (full filename below): :34 pairedEtaLogInterval;
  :38 pairedEtaLogSupport; :43 pairedEtaLogMeasure; :47 pairwise disjointness;
  :66 measurability; :73 full sum of restricted measures; :89 positive support;
  :101 first retained interval; :115 pairedEtaLaplacePartition; :150 integrability;
  :178 exact integral/partition; :195 pairedEtaCore=s*partition on Re(s)>0;
  :290 positive real tilted mass.
- InfiniteLaplaceRigidity: :37 pairedEtaLogMeasure_le_volume_restrict_Ioi_zero.
- LeadingLogMoments: :68 partition=complexMGF on Re(s)>0; :93 all-order
  integrability; :126 iterated derivative=(-1)^n*literal log moment;
  :149 positive-half-plane analyticity. No zero/RH consequence is borrowed.
- ContiguousMeasure: :25 reference restriction; :34 normalizer; :38 product
  law; :43 even difference moment; :178 normalized raw double integral;
  :258 full finite difference MGF; :286 full actual finite support;
  :318 actual measure=restriction to union; :327/:332 actual/product domination;
  :338 normalizer domination; :346/:357 raw/normalized moment comparison;
  :478/:492 exact N=1 source/moment; :530 strict missing gap; :587 exact Z_U.
- FinitePartitionVolterra: :35/:39/:44 literal actual normalizer/product/moment;
  :927/:930/:933/:936 positivity/probability/zeroth/strict moments;
  :942 raw moment integral; :957 difference MGF; :915/:1083 full Borel kernel
  and both factorials; :1092 complete summability. Its signed cumulant/Volterra
  identities are not positivity producers for an inverse response.
- Existing CenteredTailSharpAsymptotic: :79 normalized eta support-tail error;
  :147 locally uniform normalized Laplace tail ->1/(2s); :214 shifted tail
  zeroth moment limit; :357 all shifted log moments. This already establishes
  a one-source half-density transform at a receding arithmetic cutoff. It does
  NOT directly identify the two-indicator autocorrelation density or its extra
  retained-source factor log2, but overlaps the periodic half-density mechanism.
- Installed Mathlib/NumberTheory/ZetaValues.lean:452 hasSum_zeta_two gives the
  exact Basel value; Mathlib/Analysis/Real/Pi/Bounds.lean:155 pi_lt_four.

Abbreviated RiemannGaussian filenames expand inside
formal/GaloisForLFunctions/RHTower/RiemannGaussian/ as
RiemannXiSuzukiPositiveCriticalStripEta{InfiniteLaplaceMeasure,
InfiniteLaplaceRigidity,LeadingLogMoments,
LeadingLogMomentFiniteCenteredTailSharpAsymptotic}.lean.
The two LiClock source files are inside formal/GaloisForLFunctions/RHTower/.

Documented research ran FIRST, directly, terminal exit0:

  python3 scripts/formal_tools.py research "infinite odd even logarithmic partition density tail oscillatory indicator moment ratio" --json

Full artifacts: /tmp/li_current_infinite_partition_research.json and matching
.stderr. Elapsed7.40308075s; hybrid, declarations0/exploration0; ALL20 candidate
statements and ALL20 source-argument statements/full proof excerpts/methods read.
proof_ideas0, ingredient_sets0. partial=false, unfinished_stages=[], errors=[].
Index1152111 matched coverage snapshot/current1152111; inventory/index63238/63238,
pending_files0, inventory_complete=true. Compiler coverage was compiled_snapshot43,
error2, not_applicable10179, pending47661, stale2660, stale_snapshot38,
umbrella_source_only1, unavailable2654. Semantic coverage was not measured;
refresh incomplete/background indexer running. Candidate/source arguments were
source_only/not_checked. No compiled applicability or worldwide novelty inferred.

Candidate applicability, ALL20 (index preserved):
0 PNT tail-log moment: assumes a different partial-count asymptotic;
1 finite PMF log partition: different finite source;
2 radial arcsine weak-density convergence: different source plus limit premises;
3 incoming log-integral factorial bound: generic integration overlap;
4 actual shifted eta log-tail definition: source overlap, not autocorrelation;
5 infinite eta iterated derivative/moment: exact source bridge above;
6 finite eta iterated derivative/moment: fixed finite source bridge;
7 repaired frequency factorial-moment inverse: different source/premises;
8 actual shifted eta Fourier tail definition: no pointwise density conclusion;
9 normalized eta tail=shifted log tail: exact one-source prior overlap;
10/11 Barban-Vehov long moments: different sieve source;
12 positive-halfline log moment: generic integral bound;
13 prolate ladder rate: different family;
14 prime remainder half-density measurability: different prime source;
15 RouteE reservoir harmonic moment: different receiver/source;
16 finite partition trace oddness: installed phase, no infinite density bound;
17 all shifted eta tail moments: strongest exact half-density prior overlap;
18 harmonic-window third moment: different source;
19 actual finite-centered complete tail split: preserves intervals, no new sign.

Source-argument applicability, ALL20:
0 actual log-tail integrability: valid source domination;
1 theta tilt-mean derivative: different source;
2 finite PMF doubled gap: different source;
3 exact actual tail=sum over n+N: full interval retention;
4 discrete KL finiteness: unrelated;
5 prime remainder measurability: different source;
6 finite actual moment=iterated derivative: exact fixed-order source identity;
7 actual measure<=positive-halfline volume: exact domination above;
8 stretched-exponential log-gap offset: different source;
9 supremum reflection: generic, no density theorem;
10 Gomes moment pairing: different reconstructed source;
11 theta packet derivative moderation: different source;
12 RouteE Gibbs fibre positivity: different finite receiver;
13 radial arcsine halfline mass: different density;
14 completed odd log derivative moment: no independent positivity;
15 count-formation log increment: different discrete probability;
16 cutoff finite work below zero multiplicity: zero receiver, not used;
17 calibrated theta reciprocal-even-tail measure: different source;
18 prime count measurability: different source;
19 theta likelihood-order even-moment cross bound: requires a specific ordered
   theta density, unavailable for the oscillating actual eta partition.

Broadened direct lexical followup, terminal exit0, elapsed0.28s:

  python3 scripts/formal_tools.py research "pairedEtaLogMeasure pairedEtaLaplacePartition" --any --mode lexical --per-module 0 --explore 0 --json

Artifact /tmp/li_current_infinite_partition_overlap.json, matching .stderr.
ALL20 returned declarations/docs read, 45 eligible across12 modules. This JSON
omitted partial/coverage/freshness fields, so none inferred. Hits group into
actual infinite measure/partition/conjugation, exact complexMGF/log-moment
bridges, reflection-recovery receivers and measure-nonzero/finite-measure APIs.
Relevant primary definitions/measure domination were then read directly.
The inherited 272-line finite-density and 214-line fixed-endpoint papers were
already read completely and source-audited; their fixed-support regime remains
explicitly separate. No absence/novelty claim, redundant broad search or code used.

## 12. Hostile checks, conclusions and limitations

Accepted corrections from adversarial review: indicators have no pointwise
scale limit; averaging requires the bounded primitive. Both product normalizers
must be retained. The infinite tail constant is lambda, not kappa_N. Fixed compact
convergence alone cannot justify a growing-clock conclusion; section 9 supplies
a new full absolute uniform bound. A reciprocal-square moment majorant proves
entire Borel convergence, not an entire difference MGF. Endpoints are null and
no quotient is used beyond its positive domain. Positive differences, cumulants
and inverse convolution are different objects; none is interchanged by sign.

Verdict: PASS author paper proof for the literal density tail, exact discrepancy,
periodic sharp correction, lambda<1 certificate, all-order moment remainder,
entire Borel decomposition, qualified growing-complex-window convergence and
noncommuting endpoint/order/clock limits. Independent full paper audit pending.
Actual eta residual, completed finite-clock orientation and RH remain OPEN.
No route is retired and no new Lean work is authorized by this note.

## Complete audited spatial-bulk proof

# Infinite partition spatial-bulk delta: exact finite-source comparison

Paper only, author complete proof PASS; independent complete audit pending.
Companion frozen508: /tmp/li_current_infinite_partition_paper.md,
SHA256 50886f4d464dee5502ed0ac263632d19613e20c764eaf176f06bfb659da3a315.
No modification to that snapshot, no tree write or compiler.

## Exact statement and domains

Use exactly the literal finite/infinite actual and reference sources and both
half-tilt normalizers defined in frozen sections1/8/9. N>=1, L=log(2N)>0,
c0=log2/2, C0=pi^2/16, Z=Z_A,infinity, Z_*=2-sqrt2>0.
For every real 0<=x<=L,

  0<=exp(x/2)*(g_A,infinity(x)-g_A,N(x))<=exp(x-L),                (D1)
  |exp(x/2)*g_A,N(x)-c0|<=C0*exp(-x)+exp(x-L).                  (D2)

For 0<=x<L the normalized finite density ratio is well-defined and exactly

  r_N(x)=rho_A,N(x)/rho_U,N(x)
        =kappa_N*H_N(x)/(1-exp(x-L)),
  H_N(x)=exp(x/2)*g_A,N(x), kappa_N=(Z_U,N/Z_A,N)^2>0.

Put q=exp(x-L) in (0,1). Then

  |r_N(x)-kappa_N*c0|<=kappa_N*(C0*exp(-x)+q)/(1-q).              (D3)

Consequently, if N_m->infinity, x_m->+infinity, and
L_N_m-x_m->+infinity, then eventually 0<=x_m<L_N_m and

  exp(x_m/2)*g_A,N_m(x_m)->log2/2,
  r_N_m(x_m)->lambda=2log2/Z^2<1.                               (D4)

A complete explicit normalized bound is

  |r_N(x)-lambda|
    <=(4/Z_*^2)*(C0*exp(-x)+q)/(1-q)
       +c0*(8/Z_*^2+32/Z_*^4)*exp(-L/2).                       (D5)

In particular for every K>0, whenever K<=x<=L-K, the right side is at most

  (4/Z_*^2)*(C0+1)*exp(-K)/(1-exp(-K))
    +c0*(8/Z_*^2+32/Z_*^4)*exp(-K).                            (D6)

This is a proved uniform spatial-bulk limit as K->infinity, with all intervals
retained. The bulk condition is sufficient; no necessity or unconstrained
boundary-offset limit is asserted.

## Complete proof

Literal S_N=S intersect(0,L] makes removed actual product density at most
removed reference product density (frozen section9's pointwise proof).
For 0<=x<=L the latter raw deficit is exactly exp(x/2-L).
Multiply by exp(x/2) to prove D1. Apply frozen3.2 and the triangle inequality
to get D2, including the boundary x=L where g_A,N=g_U,N=0; no ratio is used there.
For x<L, the exact positive reference density is
rho_U,N(x)=exp(-x/2)*(1-q)/Z_U,N^2, yielding the ratio identity.
Write H_N=H(exp x)-delta with 0<=delta<=q by D1. Since 0<c0<1,
|c0*q-delta|<=q; and |H(exp x)-c0|<=C0 exp(-x). Thus
|H_N/(1-q)-c0|<= (C0 exp(-x)+q)/(1-q), proving D3.
Normalizers converge by monotone convergence (frozen8), so kappa_N->4/Z^2.
With both x_m and L_m-x_m tending infinity, D2/D3 prove D4.

For the stated quantitative normalization control, 0<=2-Z_U,N<=2exp(-L/2)
and 0<=Z-Z_A,N<=2exp(-L/2); all positive finite/infinite normalizers are >=Z_*,
and <=2. Hence

  |kappa_N-4/Z^2|
    <=|Z_U,N^2-4|/Z_A,N^2
       +4*(Z^2-Z_A,N^2)/(Z_A,N^2*Z^2)
    <=(8/Z_*^2+32/Z_*^4)*exp(-L/2).

Also kappa_N<=4/Z_*^2. Combine this with D3 to obtain D5.
On K<=x<=L-K, q<=exp(-K), exp(-x)<=exp(-K) and L>=2K,
which gives D6. Empty bulk intervals cause no hidden existence premise.

## Scope separation

Each fixed finite N has endpoint ratio kappa_N>1 for N>=2 on its retained
strict endpoint band, while the qualified spatial bulk above has limiting
ratio lambda<1. These quantify different passages to the source boundary.
No global density ratio monotonicity, completed finite-clock sign, inverse
Volterra response sign, RH conclusion or route retirement follows. No spatial
ratio is evaluated at or outside |x|=L, where its denominator vanishes.

2026-09-30 09:32 UTC — Root READ ALL364 formal plan PASS; producer independent ALL364 graph/coverage/source-normalization PASS and pinned actual-source declarations spot-verified. Released current sole NEW common source-measure leaf for ALL M1–M8: literal actual/reference sources, both tilted Z² laws, all moments/source pushforwards, exact finite restriction/product loss and normalizer bounds, strip MGF/derivatives and fixed-source limits. No consumer imports until foundation FINAL. Pole name/type-only40 API probes passed; countable-exception FTC handles periodic corners with continuity/integrability premises intact. Downstream proofs still pending; no inverse-clock/sign or RH conclusion.

## Exact formal dependency plan and released work

Plan `/tmp/li_current_infinite_partition_formal_plan.md`:370 lines, SHA256 `1a7efc8e28d96fdd867acf75750af7821efb7e9f1541390331722f507ff9e1bb`. Root READ ALL364 initial version plus every exact six-line metadata/type-reference delta PASS; producer independent complete plan/source graph PASS before release. Canonical actual source is existing `RiemannGaussian.pairedEtaLogMeasure`; the source leaf supplies exact tilt/density/moment/finite-restriction/strip-MGF bridges. Arithmetic tail consumes that source; Borel consumes source and tail; boundary consumes all three and the FINAL fixed-prefix endpoint comparison. No dependency cycle, alternate actual-source definition or receiver-only premise replaces a paper claim.

| Leaf | Owner | Complete target family | Dependencies |
|---|---|---|---|
| `LiClockPairedEtaInfinitePartitionMeasure` | current | M1–M8: all literal measures, both Z² laws, moments, restrictions, full product losses, normalizer errors, strip MGF/derivatives and fixed-source limits | existing FINAL leaves |
| `LiClockPairedEtaInfinitePartitionDensityTail` | pole | T1–T7: exact alpha/B/D/H/P, Jacobian/IBP, complete lattices, sharp correction/subsequences, global density tail/continuity and full9697/8190/lambda certificates | FINAL source |
| `LiClockPairedEtaInfinitePartitionBorel` | producer | B1–B8: all factorial moments, C<20/21/geometric error/j>=4, entire full series/decomposition, compact convergence and both normalized growing-complex-disk errors | FINAL source/tail |
| `LiClockPairedEtaInfinitePartitionBoundary` | current later | L1–L7: exact spatial inequalities/bulk, every qualified joint and iterated limit, uniform negative kernel gap and fixedN coexistence | FINAL source/tail/Borel/endpoint |

2026-09-30 09:34 UTC — Disjoint source, arithmetic-tail and Borel scratch/proof work released. Pole40 name/type-only probes terminal0; countable-exception FTC route independently source-verified. Arithmetic and complete-kernel ingredients may proceed before dependency completion, but source consumers import only FINAL certified snapshots. Every paper target and spatialD1–D6 retained; boundary implementation/promotion remains pending. No tree promotion until immutable full proof/API/hash audits, then named/direct/all-public foundational gates. RH and actual compensation sign remain OPEN.

2026-09-30 09:38 UTC — Producer independent final ALL370 plan/source audit PASS (`/tmp/hgt-li-infinite-formal-plan-audit.md`, SHA256 `2c7b96a61e79a405c074d09a25b649aa9974901d154fbccb7788383699221fd0`); pole also READ ALL370 allocation/normalization PASS. Root prepares only `/tmp/hgt-li-infinite-boundary-helper-*`: exact sequence perturbation, exponential cancellation in ratios and negative scaled-gap divergence from the already audited L5 proof. No extra tree leaf or source premise; later boundary owner must READ ALL and prove actual callers.

2026-09-30 09:51 UTC — Root boundary helper FINAL scratch92/5 proofs, SHA256 `ca4693d95524626120bd24326c9e262ba199181b61c9641e926ee8b714c17e82`: full compiler95221 exit0 EMPTY, all5 axioms39322 only foundational; independent producer ALL65+27 delta PASS (`/tmp/hgt-li-infinite-boundary-helper-independent-audit.md`). Later boundary owner must READ ALL before private reuse and supply actual callers. Root now owns only `/tmp/hgt-li-paired-harmonic-*` for the exact positive paired HasSum to log2 requested by tail owner; this is already paperT3, not an extra source or theorem claim. Focused prior search precedes scratch proof; tail tree ownership stays pole.

2026-09-30 11:55 UTC — Root READ ALL1210 source foundation PASS, SHA256 `2eb5015c5cf5f2c1ae39ae3b0c4d0cbacd2741534f6faaac9fe32883d21a33e3`; producer independent ALL1210/99public/56private PASS. Every M1–M8 target checked; all99 exact public headers match frozen source. Identical tree promotion released to current, followed by named build, direct Lean and all99 public axiom gates. Consumers still import only FINAL_READY. Root also READ ALL1296 standalone arithmetic/source proof PASS, SHA256 `7365b770fcc4428ecac3b222c59ae8d7b2260c46475e376e89dfab9e03f52862`; current independent ALL1296 PASS. Full interval sums, periodic correction and sharp lattice limits, actual exp Jacobians, retained-tail normalizer lower bound and exact rational certificate included. Canonical Tail wrappers and full Borel/Boundary consumers remain pending.

Paired harmonic helper resolved by reusing existing `GaloisForLFunctions.HTGeometry.hasSum_alternatingHarmonicPair`; exact9-line application compiler27061 exit0, foundational axioms only, SHA256 `0a92fb79b5af77c6b79444180200682921a3ee770fd8ce52dfa0205750dc6c48`. Complete source126 lines inspected. Documented direct research inspected all20 candidate/source-argument records; complete inventory63261/63261, freshness limitations recorded in `/tmp/hgt-li-root-consumer-core-audits.md`. No novelty claim. Root pure Borel111/79/101 reviews PASS; later combined core and actual adapters still need root review. These auxiliary proofs do not settle the compensation sign or RH.

Root complete combined Borel1059/67private core review now PASS, SHA256 `16523fd2488ab842d9bda5ec9e3217a564b30dacf05ea7101b4c7e4a15260d20`, independently matching current's ALL1059 review. Full raw integral/series exchanges, sharp growing-complex-disk envelope, both normalizer errors, compact convergence, geometric moment error, complex remainder and real asymptotics checked. Actual source adapters still require certified dependency imports, compilation and complete final audit.

2026-09-30 11:57 UTC — Measure M1–M8 FINAL_READY, wired in RHTower: exact audited1210/SHA256 `2eb5015c5cf5f2c1ae39ae3b0c4d0cbacd2741534f6faaac9fe32883d21a33e3`. Named90081 exit0 (own8.3s,12995jobs), exact direct58558 exit0/empty, ALL99 public axiom reports46220 exit0/foundational only, including both dotted instances. Root independently matched every report/header and exact tree bytes. Tail/Borel actual adapters now consume certified source. Current's complete Boundary L1–L7 implementation released in sole planned fourth leaf, preserving all spatialD1–D6/joint/uniform/iterated limits; Tail/Borel imports await their own FINAL_READY. Whole card stays Stage2 until every target is formalized and audited. No RH or compensation-sign conclusion.

Measure integration: index46764 exit0 (3 changed/0 removed); global lint84994 exit1 only11 unrelated unreachable modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, WeilLogSummableRigidity, ZetaZeroDensityPowerSaving. Every error inspected; no owned leaf/proof-debt error. Scoped diff check empty. Logs `/tmp/hgt-li-infinite-measure-{index,lint}.log`; no umbrella build.

2026-09-30 12:00 UTC — Borel actual-source scratch1528 compiler97509 exit0/empty; root full review PASS, SHA256 `d329eac873f03b3308d36ad95c737a252a9c0f4b61c63623bc0cb083d8bc2168`. Every466 actual-adapter line plus exact preserved1059 core covered; all36 complete public definitions/headers match source. Entire kernels, exact factorial reference moments, compact limits and both growing-complex-disk errors are instantiated. Tail B2/B4 and full final certification remain pending. Boundary78-line implementation ledger READ ALL/root PASS; all L1–L7 and D1–D6 preserved, sole planned leaf released with imports only after dependency FINAL_READY.

2026-09-30 12:06 UTC — Current independent ALL466 actual Borel adapter review PASS, completing independent coverage of frozen1528. Root opened separate [weighted complex quarter-window](li-clock-infinite-partition-quarter-window.md), with full author paper argument and documented prior search; independent audit subsequently PASS/Stage2 at12:12, no Lean released. It proves exponential-weighted complex estimates for c<1/4 and resulting real joint limits. This card's unweighted c<1/16 scope and all four formal targets remain unchanged.

2026-09-30 12:12 UTC — Tail complete canonical scratch1510 compiler41763 exit0/empty, root complete proof/API audit PASS; SHA256 `f490c3e186a0141e60b27dfa1cce037b8317412cd58e933d8d1dc3d7e607479f`,74public(6defs/68theorems),65private. Exact prior1296 body preserved except cubic log2 proof/import delta; all canonical density/H/normalizer/ratio/sharp-lattice/non-little-o and strict lambda certificates inspected. All74 complete headers source matched, including nested-let lattice statements. Current independent final-delta review pending, then identical promotion/named/direct/all74 gates released. Whole card remains Stage2.

2026-09-30 12:24 UTC — DensityTail T1–T7 FINAL/wired:1510 lines,74public(6defs/68theorems),65private; SHA256 `f490c3e186a0141e60b27dfa1cce037b8317412cd58e933d8d1dc3d7e607479f`. Root/current full proof audits PASS; named68986 exit0(own15s/12997jobs), exact direct38106 exit0/empty, ALL74 axioms50759 exit0/foundational only. Root matched exact tree/frozen bytes and every complete API/axiom report. Full arithmetic correction, sharp log-lattice/non-little-o behavior, density/normalizer bridges and strict lambda certificate retained. Unique umbrella import added. Index1045 PASS(6changed/0removed); authoritative global lint11319 reports14 unrelated unreachable modules, no owned/proof-debt errors; logs `/tmp/hgt-li-infinite-tail-{index,lint}.log`. Whole card stays Stage2 until Borel/Boundary ALL targets complete.

2026-09-30 12:24 UTC — Borel all B1–B8 scratch1680 compiler38645 exit0/empty, SHA256 `18571915742e701c47f915239e43dae5eb6e4e4f286e7a596274761a4e2ca649`: ROOT complete proof/API review PASS, all48 public blocks source-matched, exact prior1528 preserved plus one Tail import/new150 lines. Pole independent final150 audit pending; no tree promotion. Boundary core336 compiler16448 exit0/empty, SHA256 `ddef07a820335fe03533f21bb076b56a1b7c5a835da9d185242b9f1949666cee`: ROOT READ ALL336/9headers PASS; complete spatial/joint/iterated callers remain in progress.

2026-09-30 12:34 UTC — Borel1680/48 all B1–B8 now independently PASS (Pole final150 and exact prior mapping; additional Current final-delta confirmation), root full certificate read/source spotchecked. Before final promotion, released producer exactly4 narrow public wrappers after full root/Pole90-line mathematical interface audit: literal full reference raw-loss envelope, all-complex genuine integrability and actual/reference normalized-error caps retaining both normalizers. These reuse existing private factorial/Bochner proofs; original1680/48 bodies stay exact. Quarter consumer separate; original unweighted c<1/16 scope unchanged. Full52 source/delta/root/independent/named/direct/axiom gates required before FINAL.

2026-09-30 12:43 UTC — Complete Borel1877/52 scratch clean45834 exit0/empty, SHA256 `85af54c8ddc8f3d5d8ecf9d7cacd102eb276c9fe399d6e9b0a069a3fdc55e5d9`; root READ ALL197 final append PASS and all52 complete interfaces source-matched, original1680 byte-exact. Four raw-loss wrappers instantiate full signed difference/integrability and unrestricted-complex caps with each source's own two normalizers. Pole independent final197 review pending; identical promotion plus named/direct/ALL52 gates conditionally released after PASS. Full parent Boundary targets still ongoing; whole card remains Stage2.

2026-09-30 12:46 UTC — Boundary spatial scratch492 compiler60546 exit0/empty, SHA256 `0c8cb60ddd8ca8b6cf81fbf918278f53a571df56debace5936c632a59a641036`: ROOT READ ALL155 delta and exact preserved336/import PASS. Full sharpq density ratio, both normalization-error terms, uniform bulk error tending0, arbitrary joint spatial limits and explicit raw nested-order limits proved from FINAL source/tail. All17 public headers source-matched; independent full Boundary audit and remaining clock/iterated/fixedN callers await Borel FINAL. Whole target unchanged.

2026-09-30 12:47 UTC — Pole independent ALL197 final Borel reuse proof audit PASS; root READ ALL certificate `/tmp/li_pole_infinite_borel_reuse_delta_audit.md` and source claims checked. Entire1877/52 source now author/root/independent proof-PASS; identical sole-leaf promotion and named/direct/ALL52 foundational gates released. Boundary492 complete17-interface ledger including full definition body source-matched; producer assigned independent READ ALL492 during final compiler gates. No umbrella import until FINAL_READY.

2026-09-30 12:57 UTC — Producer independent READ ALL492/17-interface spatial audit PASS; root complete certificate `/tmp/hgt-li-boundary-spatial-independent-audit.md` read and source claims checked. Exact inclusive raw/strict ratio domains, full signedcompetition, both normalizers and arbitrary sequence/iterated quantifiers verified. Remainingclock189 and direct uniform-epsilon corollary are separate unfinalized delta. Borel named52487 exit0/success13000jobs/own157s and exactdirect57678 exit0/empty; ALL52 axiom gate56983 active.

2026-09-30 13:01 UTC — Borel B1–B8 plus4 raw-loss interfaces FINAL/wired:1877 lines,52public(9defs/43theorems),97private; SHA256 `85af54c8ddc8f3d5d8ecf9d7cacd102eb276c9fe399d6e9b0a069a3fdc55e5d9`. Named52487 exit0(own157s/13000jobs), exactdirect57678 exit0/empty, ALL52axioms56983 exit0/foundational only. Root read complete43-line certificate, independently matched exacttree/frozen bytes, all52 complete ledger blocks and source-order unique reports, checked emptydirect and namedolean. Unique umbrella import added; index38438 PASS(4changed/0removed), global lint6590 reports13 unrelated unreachable modules/no owned or proof-debt errors. Logs `/tmp/hgt-li-infinite-borel-{index,lint}.log`. Current complete Boundary702 scratch70180 compiling all original targets; Quarter consumer separately active. Whole parent remains Stage2 until all four leaves complete; actual compensation sign and RH remain OPEN.

2026-09-30 13:08 UTC — Complete Boundary702 scratch40939 exit0/empty, SHA256 `5c5cdde756c6a3b11e1c9c82e1a1b07a697203f7dcf6df5171945e7dfcece356`; root READ ALL209 final delta and full29-interface/targetmatrix PASS. Exact prior492 retained after one FINAL Borel import. Every L1–L7/D1–D6 target, explicit epsilon bulk claim, arbitrary qualified4limits, uniformclockgap, both nested orders, N1 equality and opposite escapes closed in scratch. Producer independent final209 audit pending, then identicalpromotion/named/direct/ALL29 gates released. Whole card remains Stage2 until FINAL artifact certified/wired.

2026-09-30 13:11 UTC — Producer independent complete final209 audit PASS; root READ ALL certificate/source claims checked. Combined prior492 and final209 prove all702/29 declarations and every L1–L7/D1–D6 target. Identical planned Boundary leaf promoted, SHA256 `5c5cdde756c6a3b11e1c9c82e1a1b07a697203f7dcf6df5171945e7dfcece356`; named77054 running, exact direct/ALL29 gates next. Parent remains Stage2 until artifact certification/root integration; RH and actual completion compensation remain OPEN.
