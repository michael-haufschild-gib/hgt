# WP01 — An actual negative-seed sector at growing aperture

8 October 2026. Paper proof and concrete selected-sector Lean formalization complete. Full PBAP
remains open. No numerical experiment or zero-side positivity enters this proof.

## Exact conjecture selected after the crossing audit

Let phi be a nonzero, nonnegative real C-infinity function with support in
[0,1]. Put B=int phi>0, m0=int phi^2>0, kappa=m0/B^2. For a prime p put

    L=log(p)/2, W=kappa*L*exp(-L/2), beta(u)=phi(u/W), m=W*m0,
    n=floor(exp L), a=log n-L, c=3*m*L/2.

Let e(T) be the literal full energy of the cosine/sine cluster pair used in
`jointPairFullEnergy`, and E0=e(0). The selected statement is: for all
sufficiently large primes p (threshold depending only on phi),

    E0 < 0,
    n is real-active,
    e(T)+c*cos(a*T) >= m*L/8                   for every real T.       (1)

Consequently every nonnegative finite correction satisfying the actual
aggregate real integer-null equations has

    full energy >= (L/16)*(actual physical mass).                     (2)

This class has unbounded support diameter. Its seed has negative FULL energy;
the positivity conclusion uses cancellation between actual tests. It extends
the earlier fixed-profile coercivity/minimum bridge: it constructs the profile,
coefficient and sign bound, uniformly at every modulation height. It does not
cover arbitrary profiles, widths or finite mixtures.

The previous proposed width-crossing construction is superseded by this
explicit width. No crossing existence or uniform-continuity premise is needed.
Initial verdict: SURVIVES PRELIMINARY ATTACK, scientific novelty unestablished.
The general tools are classical; the candidate research content is the actual
negative-seed family and its uniform integer-node certificate.

## Dependency-closed paper proof

All constants below may depend on the ONE fixed phi, never on L, T or p.
Every asymptotic statement is as L tends to positive infinity. Big-O statements
are consequences of the explicit integral bounds below, not numerical fits.

Write q(v)=int phi(u)*phi(u-v) du. Then q is even, smooth, nonnegative,
supported in [-1,1], q(0)=m0, int_0^1 q=B^2/2, and
0<=m0-q(v)<=C*v^2 on [0,1]. The last inequality follows from
m0-q(v)=int |phi(u)-phi(u-v)|^2 du/2 and translation plus Cauchy--Schwarz,
giving C=int |phi'|^2/2. In particular q is strictly positive near zero.
Changes of variable give beta's mass m=W*m0 and real autocorrelation W*q(y/W).

Let omega(y)=exp(-y/2)/(1-exp(-2*y)), y>0, and
cGamma=Re digamma(1/4)-log pi. The already formal physical identities give

    Gamma(beta)=cGamma*m+2*int_0^infinity omega(y)*(m-W*q(y/W))dy.

On (0,1], omega(y)<=C/y and |2*omega(y)-1/y|<=C. Indeed y*omega(y)
extends smoothly through zero with value 1/2, by factoring 1-exp(-2*y)
as y times a smooth positive function with value 2. For y>=1, omega is
bounded by C*exp(-y/2). Splitting the integral at W and 1, for 0<W<=1,

    Gamma(beta)/m = log(1/W)+O(1).                                    (3)

The integral on (0,W), after y=W*v, is bounded uniformly by
C*int_0^1 v dv, using the q estimate. The (W,1) integral equals
log(1/W)+O(1) because q(y/W)=0 there. The integral above 1 is bounded.
These statements give both an upper and a lower bound in (3).

For L>2W, the cluster correlation is
2*W*q(y/W)-W*q((y-L)/W)-W*q((y+L)/W). Its mass is 2m, and hence its
Gamma energy is 2*Gamma(beta) plus

    2*int_0^infinity omega(y)*W*q((y-L)/W)dy.

The other translate vanishes on the positive half-line. The displayed term
is nonnegative and at most C*exp(-(L-W)/2)*W^2*B^2, for L-W>=1.
Both pole terms together equal, EXACTLY,

    -8*(cosh(L/2)-1)*W^2*int_0^1 cosh(W*v/2)*q(v)dv.                  (4)

This is obtained by translating the full cosh pairing, then using evenness;
it agrees with the signed pole normalization in `testPole_eq_integral_cosh`.
The integral in (4) is B^2/2+O(W^2), with error at most
(cosh(W/2)-1)*B^2/2. Thus, with the selected kappa and W,

    E0/m = 2*log(1/W)-2*L+O(1)
          = -L-2*log L+O(1).                                        (5)

Here exp(L/2)*W=kappa*L, L*W^2 tends to zero, and
L*exp(-L/2) tends to zero. In particular, eventually

    -(9/8)*m*L <= E0 < 0.                                           (6)

The exact positive modulation kernel already formalized in
`jointPairFullEnergy_sub_zero` and `jointPairFullEnergy_zero_le` gives

    e(T)>=E0 for every real T.                                      (7)

Its sign restriction is proved here by nonnegativity of phi and q; no
energy sign is assumed. Eventually W<min(1,log 2) and 2W<L.

We next prove a uniform high-frequency estimate sharper than the existing
profile-dependent logarithmic-moment bound. Write H=abs(T)>=2,
D=int |phi''|, and let rho be `jointPairDensity beta L T`. Existing exact
Plancherel and low-frequency concentration identities give

    int rho=4*pi*m,
    int_{|xi|<=H/2} rho <= 64*D^2/(W^2*H^3).                         (8)

Endpoint changes have zero Lebesgue measure. The estimate for negative T
is identical: cosine is even in T, sine changes sign, and its square does
not change. It is not necessary to change the sign of either pole.

The corpus lower bound for gammaBracket is
log(2+abs(xi))-C0, C0=10+log 4. Use -C0 globally and
log(H/2)-C0 outside the middle interval in (8). Because log(H/2)>=0,

    Gamma(pair)/m >= 2*log(H/2)-2*C0
          - C*log(H/2)/(W*H)^3.                                    (9)

This estimate preserves the coefficient 2 of the ACTUAL mass. Using a
pointwise upper bound for the translated density to replace that mass
would lose the coefficient and would not prove (1).

The existing complex Fourier decay theorem `Zeta23.norm_paperFT_mul_sq_le`
gives |paperFT beta z|*|z|^2 <= exp(abs(Im z)*W)*int |beta''|.
Here int |beta''|=D/W by change of variables. Thus for v in {1/2,-1/2},
0<W<=1 and H=abs(T)>0, using |+/-T+i*v|^2>=H^2,

    |paperFT beta (+/-T+i*v)| <= C*W/(W*H)^2.                        (10)

The sign of v in the exponential is immaterial for this two-element set.
Cosine and sine transforms are half-sums/differences of these translates,
so satisfy the same bound. Translating by L multiplies the pole transform
by 1-exp(i*z*L). The absolute value of the pair's full pole contribution
is consequently at most

    C*(1+exp(L/2))*(1+exp(-L/2))*W^2/(W*H)^4.

After division by m, this is at most C*L/(W*H)^4 for the selected W and
large L. This controls BOTH poles and either sign of their real product.

Let H0=exp(7*L/8). Then W*H0=kappa*L*exp(3*L/8). For H>=H0, the error
in (9) tends uniformly to zero: log(H/2)/H^3 decreases for H>=2.
The pole error tends uniformly to zero as well. Therefore

    inf_{|T|>=H0} e(T)/m >= (7/4)*L-O(1)
                          >= (13/8)*L eventually.                  (11)

This is an all-height estimate, not continuity on a compact frequency band.

Now choose n=floor(exp L). For large prime p, 2<=n<p and exp L=sqrt p
is not an integer, so a is nonzero. Since n<=exp L<n+1 and n>=exp L/2,

    0<abs(a)=log(exp L/n)<=1/n<=2*exp(-L).

It follows that abs(a)/W tends to zero. Since q(0)>0 and q is continuous,
the actual real autocorrelation at a is positive, so n is real-active.
For |T|<=H0, abs(a*T)<=2*exp(-L/8). Hence cos(a*T)>=11/12 eventually,
uniformly on that entire band (use 1-cos x<=x^2/2). Combining (6)-(7),

    e(T)+c*cos(a*T)>=(-9/8+11/8)*m*L=m*L/4.

For |T|>=H0, use (11) and cos>=-1 to get

    e(T)+c*cos(a*T)>=(13/8-3/2)*m*L=m*L/8.

This proves (1). All thresholds above depend only on phi; taking their
maximum gives one threshold valid simultaneously for every sufficiently
large prime p and every real T.

Finally let w_j>=0 and t_j be ANY finite real-null correction of this
actual seed. At its active node n, the already established correlation
identity gives 1+sum_j w_j*cos(a*t_j)=0. With M=sum_j w_j,

    E0+sum_j w_j*e(t_j)
      = (E0+c)+sum_j w_j*(e(t_j)+c*cos(a*t_j))
      >= (m*L/8)*(1+M).

Its literal physical mass is 2*m*(1+M), proving (2). The family is nonempty:
the existing finite simultaneous shifted-log correction theorem constructs
positive corrections for every prescribed M>1 for these prime halves.
It cancels all relevant nodes, hence also the actual real-active subset.
Unbounded primes give unbounded cluster separation. The cluster support diameter
is at least L and at most L+W; equality with L+W requires full source support. No assumption of
RH, full PBAP, a positive producer, or a negative-seed crossing was used.

## Hostile audit and limits

- The coefficient c is constructed, not supplied by a separation premise.
- Its constant residual in (1) is used as a LOWER BOUND, not added to the
  cosine polynomial. The actual dual certificate is only -c*cos(a*T).
- The active integer node is proved active; no extra null equation is imposed.
- All heights and arbitrary correction mass are controlled. The old bound
  with a width-dependent Fourier logarithmic moment is insufficient for (11).
- This is not the previous narrow integer-centred packet class: the cluster
  separation is log(sqrt p), and W is much larger than the integer log mesh
  near sqrt p. Those packets used exact isolated multiplicative diagonals.
- `WeilWorkExposingRayCoherentCompletion` constructs one particular polar
  geometric-filter repair with positive total energy. It does not prove the
  bound for every correction of this negative full-energy seed.
- The zero-side smooth two-edge lower-bound theorem is RH-equivalent; it
  provides no unconditional input to this proof.
- Scientific novelty is not established by these comparisons or by absence
  of a search hit. No claim of full PBAP follows from (2).

External audit: the version-specific HTML for arXiv:2608.24827v2 (2 September
2026; displayed author Xuefeng Zhu, unlike the earlier v1 page) states a
fixed-support computational certificate and RH-conditional large-window
upper bounds. These have different quantifiers and are not used here.
https://arxiv.org/html/2608.24827v2 . Suzuki's localized Weil-form framework
https://arxiv.org/html/2606.09096v2 supplies no integer-node sign estimate.

## Next conjecture exposed by this proof

Replace kappa by alpha*m0/B^2. The same proof suggests an actual sector for
every 1/2<alpha<3/2, with E0/(m*L)->1-2*alpha and normalized null energy at
least eta*L for every eta<(3-2*alpha)/4. More sharply, along prime subsequences
where log(1/abs(a))/L tends to lambda in [1,2], the one-node threshold should
be alpha=lambda+1/2. Strictly below should admit certificates; strictly above
should not, by testing T=pi/abs(a). Equality is unpaid. This sharper
classification is a NEW conjecture, not part of the proved statement above;
it needs its own paper, novelty and upper-energy audits before Lean.

## Equivalent Fourier proof of the seed Gamma estimate

For Lean, (3) and its cluster counterpart can be obtained without a new
singular-kernel expansion. Write F=paperFT phi, r=abs(v)>0, 0<W<=1. The
already formal lower/upper Gamma-symbol bounds imply

    log r-C0 <= gammaBracket(v/W)-log(1/W) <= log(1+r)+4.

Indeed log(2+abs(v/W))=log(1/W)+log(2W+r), and the analogous upper
identity uses W+r. Thus the absolute difference is bounded by

    C0+4+abs(log r)+log(1+r).

Its product with |F(v)|^2 is integrable. Near zero, |F|<=int|phi| and
int_0^1 -log v dv=1. Outside [-1,1], abs(log r)<=log(2+r); the required
Fourier logarithmic moment is already formal in `joint_fourier_log_integrable`.
These bounds also prove all integrability needed when subtracting the mass
term. The point v=0 has zero Lebesgue measure.

For g=clusterDifference beta L, Fourier dilation gives
F_g(xi)=(1-exp(i*xi*L))*W*F(W*xi). Its squared multiplier is at most 4.
Subtract log(1/W)*testMass(g) from Gamma(g), change variable v=W*xi,
and use the integrable bound above. The absolute remainder is at most
C_phi*W, uniformly in L. For L>W, testMass(g)=2W*m0 exactly, so

    Gamma(g)/(W*m0)=2*log(1/W)+O_phi(1).

This is the exact seed estimate used in (5). It is a classical scaling
bridge for the selected research theorem, not a separate novelty claim.
The full signed pole asymptotic can equally use the exact transform factor
at +/-i/2: testPole(g)=-2*(cosh(L/2)-1)*testPole(beta). For nonnegative phi,
testPole(beta)=2W^2*(int phi(v)*exp(W*v/2)dv)*
(int phi(v)*exp(-W*v/2)dv)=2W^2*(B^2+O_phi(W)). This slightly weaker
O(W) remainder still gives O(LW)=o(1) after normalization, sufficient for (5).
No private folded-kernel lemma needs to be duplicated or exposed.

### Simpler uniform high-frequency remainder for Lean

The all-height estimate (11) needs no derivative test for log(H/2)/H^3.
For H>=2, `0<=log(H/2)<=H`, so the audited Gamma loss is at most
`(64/(2*pi))*D^2/(W^2*H^2)`. For L>=1 and H>=exp(7L/8), division by
`W*m0*L` and substitution W=kappa*L*exp(-L/2) bounds this by

    A*exp(-L/4),    A=64*D^2/(2*pi*kappa^3*m0).

Here the exact remaining denominator L^4 is at least one. Likewise W<=1,
L>=0 give `(1+exp(L/2))*(1+exp(-L/2))<=4*exp(L/2)` and
`exp(W/2)^2<=exp(1)`. The audited two-pole loss, divided by `W*m0*L`, is
at most

    B*exp(-3L/2),   B=16*exp(1)*D^2/(kappa^3*m0).

Thus the literal high-frequency lower bound implies

    e(T)/(m*L) >= 7/4 - 2*(log 2+10+log 4)/L
                        - A*exp(-L/4) - B*exp(-3L/2)

uniformly for abs(T)>=exp(7L/8), once the stated elementary size bounds hold.
Each error tends to zero. This proves the required eventual 13/8 lower bound
using only elementary exponential limits. This is a proof simplification of
(11), not a new conjecture or numerical estimate.


## Completed Lean capstone

Eight new leaves are wired and fully audited: JointHighFrequency, JointScale,
JointSeedGamma, JointSeedPole, JointSeedLimit, JointWidthHigh, JointWidthPhase,
and JointWidthSector, all with the `WeilWorkPBAP` prefix. Every final direct
`lake env lean <leaf>` audit has empty diagnostics; 66 named axiom checks use
only `propext`, `Classical.choice`, and `Quot.sound`. EVIDENCE records hashes.

The concrete source is `jointUnitBumpTest`, the corpus narrow bump at index
zero translated by 1/2. Support, positive mass, nonzero integral and
nonnegative real autocorrelation are proved. The unconditional capstones are:

- `eventually_jointUnitBump_negative_seed_certificate`: negative literal full
  seed, actual index >=2, positive real autocorrelation there, and the
  all-height cosine certificate.
- `eventually_jointUnitBump_null_energy`: EVERY nonnegative finite correction
  obeying actual aggregate real nullness has energy >=L/16 times physical mass.
- `exists_jointUnitBump_prime_sector`: at every sufficiently large prime half-
  logarithm and every prescribed M>1, such corrections exist with positive
  physical mass. No sign, active-node, crossing, or certificate premise.

These close the selected sector, not full PBAP. Scientific novelty remains
unestablished; no claim of priority follows from source-search coverage.

## Next boundary diagnostic — not yet proved

For any one-node certificate `-c*cos(a*T)<=e(T)`, testing T=0 and T=pi/abs(a)
forces `E0+e(pi/abs(a))>=0`. The earlier alpha/lambda conjecture should first
be attacked through this literal necessary inequality. The unproved sharper
candidate at `alpha(L)=1/2+log(1/abs(a))/L` predicts a negative `-2*m*log L`
remainder in that sum. Paying the actual high-frequency UPPER estimate is
mandatory before asserting this critical-boundary failure. The completed
positive sector is the existing survivor; no one-node or broader D2 route is
retired on this candidate diagnostic.
