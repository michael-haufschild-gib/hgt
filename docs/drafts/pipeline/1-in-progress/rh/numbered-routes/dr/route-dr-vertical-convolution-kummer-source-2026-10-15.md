# DR: vertical-convolution realization of an arithmetic Kummer germ

Status: candidate fails on paper by an exact arithmetic obstruction.
Positive finite-interpolation survivor checked in the companion draft;
full finite-measure and Euler-germ identification closure still pending.
Do not retire the candidate before that closure. RH and DR remain active.

User scope correction: stop ancillary formalization and work directly on
the missing arithmetic Kummer continuation. This card is retained unfinished,
not promoted, not a half-strip certificate, and not the next work item.
Companion draft: `route-dr-vertical-convolution-coefficient-work-2026-10-15.lean`.
The exact draft passed direct Lean checking with no diagnostics before being
moved unchanged from `/tmp/hgt_dr_vertical_root_uniform_work.lean`.
It proves the prime/multiple-of-six logarithmic-frequency gap, coefficient
non-uniform-continuity, and exact finite exponential-sum interpolation.
It does not yet prove the finite-measure Fourier theorem, Euler-root identity,
or the stated escape corollary. No production module was added.

## Intended construction and exact conjecture

For d>=2 put alpha=1/d. Let D_alpha(n) be the multiplicative coefficient
of the normalized Euler germ zeta(s)^alpha on Re(s)>1:

    D_alpha(p^k) = alpha*(alpha+1)*...*(alpha+k-1)/k!,
    D_alpha(1)=1.

Proposed source: a finite complex Borel measure nu on the vertical
translation parameter t, with

    integral exp(-i*t*log(n)) dnu(t) = D_alpha(n),  n>=1.

Then on Re(s)>1, absolute convergence justifies

    integral zeta(s+i*t) dnu(t) = zeta(s)^alpha.

If nu were supported on t>=0 and had sufficient moments, the same integral
would be a candidate holomorphic source on Re(s)>1/2, Im(s)>0: translated
zeta poles remain outside that domain. Establishing the moment and
holomorphic-integrability requirements is part of the construction, never
an allowed continuation premise. In fact even the weaker finite-measure
moment problem above has no solution, without any support restriction.

This is a Kummer-source construction attempt, not a direct estimate on
zeta zeros. Exact source moments must be constructed; postulating analytic
continuation of the desired Euler root would be circular.

## Paper obstruction: nearby integer frequencies retain different arithmetic values

The Fourier transform phi(x)=integral exp(-i*t*x) dnu(t) of every finite
complex measure is uniformly continuous. Indeed

    |phi(x+h)-phi(x)| <= integral |exp(-i*t*h)-1| d|nu|(t),

independently of x. The right side tends to zero by dominated convergence,
with dominating function 2 and finite total variation.

For 0<alpha<1, every local coefficient b_alpha(k), k>=1, lies in (0,alpha].
This follows from b_alpha(1)=alpha and
b_alpha(k+1)/b_alpha(k)=(alpha+k)/(k+1)<1. Therefore

    D_alpha(p)=alpha for every prime p;
    0<D_alpha(m)<=alpha^2 for every positive multiple m of 6.

The latter bound uses the distinct factors 2 and 3 and multiplicativity;
all remaining prime-power factors are at most 1. For any prime p>6 choose
m=6*floor(p/6). Then 0<=p-m<6 and m>0. As p tends to infinity through
primes, log(p)-log(m) tends to zero, whereas

    |D_alpha(p)-D_alpha(m)| >= alpha-alpha^2 > 0.

Uniform continuity is impossible. Infinitude of primes suffices; no prime
number theorem, prime-gap estimate, numerical computation, RH assumption,
or zero-free-region premise enters.

Verdict for the exact finite-measure construction: FALSE. This is a
consequence of Fourier uniform continuity plus arithmetic factorization.
Scientific novelty/significance beyond those parent mechanisms is
unestablished. External literature searches are excluded by user instruction.

## Strong positive survivor: every finite moment problem has an exact solution

Given N and arbitrary complex targets a_1,...,a_N, choose delta>0 with
delta*log(N)<2*pi (for N=1 any positive delta works). The numbers
z_n=exp(-i*delta*log(n)), 1<=n<=N, are distinct. The Vandermonde matrix
(z_n^j)_(1<=n<=N,0<=j<N) is invertible. Solve for complex weights w_j
and set nu_N=sum_(j<N) w_j*delta_(j*delta). This finite complex atomic
measure is supported at nonnegative heights and interpolates all N
prescribed Fourier moments exactly. In particular it matches the first
N coefficients of every finite-level Kummer germ.

The obstruction is genuinely infinite. If the measures matching larger
and larger coefficient sets had uniformly bounded total variation and a
tight variation family, weak compactness would produce a forbidden finite
measure. Thus finite arithmetic matching alone cannot supply a convergent
root source.

When nu has a finite first absolute moment M, the same proof gives the
necessary resolution inequality

    M*|log(p)-log(m)| >= alpha-alpha^2

for every matched prime p>6 and its neighboring multiple m of 6. Hence
the first absolute moment must diverge along any exact finite-interpolation
family. This records escape in the vertical translation parameter; the
constant is not a target for optimization.

## Remaining proof and research work

1. Audit current Lean root-coefficient and Fourier/interpolation machinery.
2. Formalize the exact arithmetic non-uniform-continuity theorem and the
   finite-measure consequence, with no assumed root continuation.
3. Formalize the positive finite atomic interpolation statement, then the
   necessary escape statement with its exact hypotheses. Only then close
   the failed candidate.
4. Retain the hard arithmetic attachment problem. Non-finite distributional
   translation sources are not excluded. Their action on holomorphic zeta
   cannot be asserted from a bounded spectral multiplier alone: the integer
   frequencies log(n) coalesce, and local analytic continuation is precisely
   what still needs proof.

No half-strip is certified by this card. The main unconditional RH goal
is unchanged.
