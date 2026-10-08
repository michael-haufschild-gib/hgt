# Integer-grid pole quadrature: exact arithmetic defect

Cycle24. The kernel decomposition, coefficient bounds and weighted uniform
error are FORMALIZED in WeilWorkExposingRayGridDefect.lean. The actual-source
moment identity (4) and arbitrary matched-family identity are FORMALIZED in
WeilWorkExposingRayZetaMoment.lean. Universal WP02 remains OPEN.
The proposed uniform scalar gamma compensation is FALSE on paper. Its
large-value input is external and is not claimed as a Lean theorem.
Classification: BRIDGE / classical Euler-summation mechanism; significant
external novelty is not established. Universal WP02 remains OPEN.

## Exact conjecture attacked

For n>=1 define

    q_n = integral_(log n)^(log(n+1)) 2*cosh(y/2) dy
        = 2*(sqrt(n+1)-sqrt(n)) + 2*(1/sqrt(n)-1/sqrt(n+1)),
    D_K(t) = sum_(1<=n<=K) q_n*cos(t*log n)
             - integral_0^(log(K+1)) 2*cosh(y/2)*cos(t*y) dy.

The candidate was: there exist a>0, B and K0 such that, for every K>=K0
and every real t,

    archimedeanWeilSymbol(t/(2*pi)) >= a*D_K(t)-B.

This is one possible scalar certificate for the sampling error, not the
universal WP02 statement or the vanishing-mass-defect conjecture itself.
Rejecting it does not reject integrated, trace-dependent certificates.

## Positive survivor: exact decomposition with positive correction

Put delta_n=q_n-1/sqrt(n), a_n=sqrt(n), b_n=sqrt(n+1). Direct rationalization
using b_n^2-a_n^2=1 gives

    delta_n = (2*a_n+b_n)/(a_n*b_n*(a_n+b_n)^2) > 0,
    delta_n <= 3/(4*n^(3/2)).

For the upper bound use the equivalent expression
(1+a_n/(a_n+b_n))/(a_n*b_n*(a_n+b_n)): its numerator is <=3/2 and its
denominator is >=2*a_n^3. Thus sum delta_n converges, and

    C(t)=sum_(n>=1) delta_n*cos(t*log n)

converges absolutely and uniformly, with |C(t)|<=C(0).
It is a positive-definite real even kernel: every finite quadratic form
is a nonnegative sum of squared trigonometric amplitudes.

For every real t,

    lim_(K->infinity) D_K(t) = Re(zeta(1/2+i*t)) + C(t).          (1)

Proof: set s=1/2-i*t and L=log(K+1). Euler partial summation, already
formalized as RHTower.tendsto_sum_cpow_sub_pow, gives

    sum_(n<=K) n^(-s) - (K+1)^(1-s)/(1-s) -> zeta(s).

Replacing K by K+1 in the elementary endpoint changes it by O_t(K^-1/2).
The continuous pole integral is the real part of

    (exp((1/2+i*t)*L)-1)/(1/2+i*t)
    + (exp((-1/2+i*t)*L)-1)/(-1/2+i*t).

The constant terms have cancelling real parts. The second exponential
endpoint tends to zero. Split q_n=n^-1/2+delta_n and apply absolute
convergence to the latter sum. Conjugation of zeta identifies the real
parts at 1/2-i*t and 1/2+i*t. This proves (1).

Since D_K(0)=0 for every K by the exact cell integrals,

    C(0) = -zeta(1/2),
    |lim D_K(t)-Re(zeta(1/2+i*t))| <= -zeta(1/2).               (2)

No limit is asserted uniformly in t for D_K. Only C's series is uniformly
convergent. This distinction is essential for the next obstruction.

## Why the scalar conjecture fails

Fix t and pass K to infinity in the proposed bound. The actual digamma
growth bound in WeilDilationCriticalLineShift gives gamma(t)=O(log(2+|t|)).
Equations (1)-(2) would then imply

    Re(zeta(1/2+i*t)) <= O(log(2+|t|)).

Kalpokas--Korolev--Steuding, Corollary3 at angle phi=0, unconditionally
gives positive REAL zeta values up to height T of size at least a positive
constant times (log T)^(5/4). These heights escape every compact interval,
by continuity and unbounded values, and log(2+|t|)<=log(2+T). Contradiction.
Large absolute values alone would not prove this; the positive-real phase
in that corollary is the needed input. Its RH-dependent stronger estimate
is not used.

Primary source: https://arxiv.org/html/1109.2224 (Corollary3);
version record: https://arxiv.org/abs/1109.2224.

## Stronger survivor audit and task relevance

The exact correction has a sign at the coefficient level, not a pointwise
sign in t. It preserves every low integer cell and the growing support
endpoint. It explains why dense sampling plus a gamma-only error bound
does not automatically pay the pole cancellation: the missing kernel
contains the actual critical-line zeta function, not a small mesh remainder.

Nearest inspected corpus parent:
XiHeatCassiniWoldNaturalLogMeshContinuation uses
log((n+2)/(n+1))-1/(n+2) and a zeta-plus-holomorphic-remainder continuation.
ZetaPartialSumStrip already supplies the principal Euler limit. Neither
inspected source states this pole-cell kernel identity; search coverage is
not an absence proof. Formalize only the exact positive-coefficient survivor
and its literal kernel limit, not a new conditional RH receiver.

The stronger source identity and its interchange proof follow below.
No second zeta moment or higher pole-jet sign is claimed.

## Quantitative survivor and actual-source conservation

Write s=1/2+i*t, Q=K+1. The corpus's exact fractional-part remainder
(Sieve.ZetaTruncated.riemannZeta_eq_sum_add_tail and
norm_integral_Ioi_fract_cpow_le) gives

    |sum_(n<=Q) n^(-s)-Q^(1-s)/(1-s)-zeta(s)|
       <= 2*|s|/sqrt(Q).

The index shift from Q to K and the second pole endpoint together cost
at most (1+1/|s|)/sqrt(Q). Also the coefficient bound

    0<delta_n<=2*(1/sqrt(n)-1/sqrt(n+1))

telescopes, so sum_(n>K) delta_n<=2/sqrt(Q). Since
|s|<=1/2+|t| and |s|>=1/2, altogether

    |D_K(t)-Re(zeta(s))-C(t)| <= (6+2*|t|)/sqrt(K+1).           (3)

This is weighted uniform convergence; it is not unweighted uniform
convergence. It supplies the interchange missing from pointwise (1).

For an actual complex compact C2 polar test f, put rho(t)=|paperFT f(t)|^2,
M=integral rho and c(y)=Re(weilTest f f y). Fourier inversion gives
integral rho*cos(t*y)=2*pi*c(y), with c even, supported in [-2A,2A],
and atomCoeff(f,n)=2*c(log n). Both pole conditions give
integral_0^infinity 2*cosh(y/2)*c(y)dy=0. Compact C2 Fourier decay implies
integral rho*(1+|t|)<infinity. Thus (3), multiplied by rho and integrated,
proves convergence of the defect pairing. All finite lag interchanges
are absolutely integrable because their lag interval is compact.

For log(K+1)>2A, the continuous pole pairing vanishes exactly and

    integral rho*D_K = q_1*M + pi*sum_(n>=2) q_n*atomCoeff(f,n).

Absolute summability of delta and |cos|<=1 likewise justify

    integral rho*C = delta_1*M + pi*sum_(n>=2) delta_n*atomCoeff(f,n).

Both atom sums are finite by compact support. Subtracting, with
q_n-delta_n=n^-1/2, proves the unconditional actual-source identity

    integral rho(t)*Re(zeta(1/2+i*t))dt
       = M + pi*sum_(n>=2) atomCoeff(f,n)/sqrt(n).              (4)

For every actual finite matched family at cutoff N, summing (4) yields

    sum_i alpha_i integral rho_i(t)*Re(zeta(1/2+i*t))dt
       = sum_i alpha_i M_i + (t_ray/2)*sum_(2<=n<=N) w(n)/sqrt(n).

This includes integer-null families (t_ray=0). It is a conservation law,
not a gamma-energy sign. It rules out treating the scalar zeta peaks as
freely selectable without the matched moment constraint. Classical
co-Poisson ancestry remains; task-specific utility is the exact all-family
moment interface. Equation (3) is formalized as defect_error_le; equation
(4) as ExposingRayZetaMoment.moment_eq, with the finite-family conclusion
in matched_moment. Both are exact actual-source theorems.

Cycle25 implementation audit: use the finite principal defect

    P_K(t)=sum_(n<=K) cos(t*log n)/sqrt(n)
             -integral_0^(log(K+1)) 2*cosh(y/2)*cos(t*y)dy.

Since P_K=D_K minus the finite delta sum, (3) and the delta tail bound
give |P_K-Re(zeta)|<=(8+2|t|)/sqrt(K+1). For K=0, P_0=0, so the same
inequality supplies a global linear bound for Re(zeta). Consequently both
the zeta pairing and the error are integrable for compact C2 sources.
Pair P_K directly, using only finite sums and compact-lag Fubini. For
K beyond the autocorrelation support it equals the right side of (4),
independently of K; the error integral tends to zero. This proves exactly
(4) without an infinite correction-series interchange. All factors pi and
the n=1 Fourier-mass contribution are unchanged.

Finite-family quantifier audit: the moment identity is linear in the row
coefficients. Therefore its matched-family conclusion also holds for
arbitrary real alpha_i and arbitrary real ray scale, provided the literal
matching equations hold for every n>=2. Positivity is needed by the original
energy problem, not by this conservation law. The proof takes a common
finite cutoff above every row's support cutoff and N, interchanges two
finite sums, substitutes each matching equation, and removes the exactly
zero truncated-ray tail. Empty families and N<2 obey the same algebra.

## Verification obligations

1. Positive, summable literal cell correction and exact elementary identity.
2. Full pointwise pole-grid limit, with actual cosine normalization.
3. Weighted uniform error (3), then source pairing (4), without assuming
   an integral interchange as a new premise. Both formalized; the finite
   principal route below supplies every required integrability statement.
4. Final foreground leaf/axiom/lint audits and umbrella import.
5. Keep external large-value no-go labelled paper-only unless independently
   formalized. No computations, new axioms, or heartbeat changes.

Audit receipt: final installed leaf `lake --old env lean -o <owned-cache>
GaloisForLFunctions/RHTower/WeilWorkExposingRayGridDefect.lean` exits0,
no warnings. All15 public theorem axiom audits exit0 with only propext,
Classical.choice and Quot.sound. One RHTower import added. No full build.
Global lint exits1 on eight unrelated unreachable modules, no WP02 finding.

Cycle25 installed moment leaf: final `lake --old env lean -o <owned-cache>
GaloisForLFunctions/RHTower/WeilWorkExposingRayZetaMoment.lean` exits0 with
no warnings. One umbrella import added; no full build. Latest global lint
reports13 unrelated unreachable modules and no WP02 finding; exact list
in EVIDENCE. All12 public moment-leaf axiom audits exit0 using only
propext, Classical.choice and Quot.sound. Source and family identities
have no additional analytic or positivity premises.
