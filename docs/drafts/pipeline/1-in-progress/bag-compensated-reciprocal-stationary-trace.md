# BAG: compensated reciprocal stationary trace

- **ID:** bag-compensated-reciprocal-stationary-trace-25az
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** bag-covered-global-defect-cancellation.md, continuation24az;
  its earlier continuations05az/06az/09az;
  bag-cubic-signed-zero-form.md, C28.56q/r.
- **Statement:** Estimate the complete signed denominator-dual action of the
  literal noncontracting prime cubic by o(N/log²N), retaining every divisor,
  dual frequency, contraction, physical factor and boundary remainder.

## Goal and present status

Route BAG. The complete continuous middle-coordinate cubic now vanishes
at the target normalization, by ChiCubicPrimeFullContinuousCancellation.
The unpaid problem is the full compensated arithmetic sampling error.
Growing moments/cofactors and deterministic common-height return remain
open after this cubic problem; this card is not an RH proof.

No new Lean estimate is claimed in this card. Fixed-denominator rational
row estimates and a scalar prime exponential-sum bound do not supply
the required joint saving. This revisits the denominator-dual attempt
from06az, now with the full continuous producer and fixed-radius prime
cancellation available. The square-root saddle and its growing modes
were already identified in06az; they are not new frontier results.

## Exact source basis

The literal smooth physical amplitude in
ChiPrimeGaussianCubicFourierLattice:104 has phase exp(2*pi*i*p*q/r),
physical factor1/r, V(p/N)V(q/N)conj(V(r/N)), the full W(p*q/(r*N)),
and the selected edge cutoffs. Sharp-to-smooth transfer is already
proved in ChiPrimeGaussianCubicSharpEdges; it is not an N-uniform
high-derivative assertion about those cutoffs.

ChiPrimeGaussianCubicPrimeOnlyVaughan:117 identifies its COMPLETE
signed coefficient pointwise with the prime logarithm. Applying that
pointwise identity in r is legitimate; expanding a Type-I squarefree
mask requires retaining all its divisor lattices. A Type-II prime
factor cannot be treated as an unrestricted integer long factor.
The old balanced Type-I expansion and its surviving large primitive
frequencies are recorded in continuation09az of the parent log.

## Reciprocal stationary calculation — paper only

Consider one unrestricted integer lattice r=d*m from that finite
expansion, with d>0. This is a single lattice contribution, not the
whole prime coefficient. Write e(t)=exp(2*pi*i*t). Poisson's mode
with Fourier index -h has phase

    phi(m)=p*q/(d*m)+h*m.

For p,q,m>0 a stationary point exists only when h>0. It is

    m0=sqrt(p*q/(d*h)),
    r0=sqrt(d*p*q/h),
    phi(m0)=2*sqrt((h/d)*p*q),
    phi''(m0)=2*h/m0.

If p,q,r0 lie in [N,2N], then 1/4<=h/d<=4. Thus the stationary
indices have h comparable to d. Large divisor lattices create
growing rational modes; dualizing the denominator does not turn
the complete action into a fixed finite list of modes.

The leading stationary size of the m-integral is proportional to
sqrt(m0/h). Since m0~N/d and h~d, this is sqrt(N)/d. The original
factor1/r0 and prime-log unweighting give a size proportional to
1/(d*sqrt(N)*log N), before the actual divisor coefficient and
the remaining two prime sums. This is a scale calculation, not a
uniform asymptotic or a proved aggregate remainder estimate.

The exact W argument at this saddle is

    p*q/(r0*N)=sqrt((h/d)*p*q)/N.

It remains coupled to both numerator primes and the dual ratio;
it must not be frozen or replaced by a constant.

## Test of a second independent stationary saving

For b=h/d>0 let Psi_b(p,q)=2*sqrt(b*p*q). Its Hessian has entries

    Psi_pp=-(sqrt(b)/2)*sqrt(q)*p^(-3/2),
    Psi_qq=-(sqrt(b)/2)*sqrt(p)*q^(-3/2),
    Psi_pq=sqrt(b)/(2*sqrt(p*q)).

Its determinant is identically zero: the phase is homogeneous of
degree one and its radial direction is null. Thus a nondegenerate
two-variable stationary theorem cannot provide a further independent
N^-1 factor. This rejects that proposed proof step, not cancellation
of the full signed source and not the BAG route.

Retaining rational numerator Fourier modes a,c instead gives

    Psi_b(p,q)-a*p-c*q.

Both stationary equations hold precisely when b=a*c, with
p/q=c/a, for positive a,c. These are the original cone incidences,
in another order of integration. Off-cone nonstationarity is useful
only with a bound uniform in the FULL growing rational source.
There is no permission to replace nonzero rational defects by a
fixed positive separation.

## Surviving local mechanism and next proof obligation

For the integer mode b=1, the following exact identities retain
the nonlinear gap rather than Taylor expanding it:

    2*sqrt(p*q)=p+q-(sqrt(p)-sqrt(q))^2,
    (sqrt(p)-sqrt(q))^2=(p-q)^2/(sqrt(p)+sqrt(q))^2.

Since p,q are integers, e(Psi_1)=e(-(sqrt(p)-sqrt(q))^2). At the
denominator saddle r0=sqrt(p*q),

    |(p-r0)*(q-r0)|/r0=(sqrt(p)-sqrt(q))^2.

Hence bounded quadratic-gap action in this mode is exactly bounded
hyperbolic phase at its saddle. The existing fixed-radius theorem
already concerns this physical region; merely rediscovering the
diagonal saddle does not move the frontier. No equality of a
restricted original packet with a restricted stationary expansion
is asserted without controlling the transition and remainder.

The next substantive conjecture is a signed bound for the ENTIRE
growing b=h/d family after all equal rational modes have been
assembled with their actual divisor coefficients. It must pay the
off-cone family jointly and keep the cone and contraction terms
until the original masks are recovered. A collection of individual
mode estimates, or a complete-source identity without a saving,
would leave the same open problem.

The equal-mode assembly can be done BEFORE a stationary approximation
for the unmasked smooth source. The two discrete contraction families
and their all-equal overlap must be subtracted separately using their
exact source identity. Changing a smooth function at the isolated
points r=p or r=q leaves its integral unchanged and does NOT remove
those lattice samples; it cannot implement the masks in Poisson.
In the balanced finite Type-I source from09az write the coefficient on
the lattice r=d*m as A_d*log(r)+B_d, and retain only d<=X=2N.
For a reduced rational b=h0/q, every contributing pair has d=k*q and
h=k*h0. Changing variable r=d*m in the exact mode integral gives

    (1/d)*integral F(r)*(A_d*log(r)+B_d)*e(p*q'/r+b*r) dr,

where q' denotes the physical second numerator prime, distinct from
the reduced denominator q. Thus the complete coefficient of that
same rational mode is exactly

    alpha_q*log(r)+beta_q,
    alpha_q=sum_(d<=X,q|d) A_d/d,
    beta_q =sum_(d<=X,q|d) B_d/d.

This is the SAME coefficient pair already exposed by09az's
middle-coordinate expansion, rather than a new source with better
signs. The semiprime primitive coefficient from09az still survives.
The useful change of representation is analytic: its test now has
the reciprocal integral and square-root saddle described above.
No decay of these coefficients or norm-saving interchange is inferred.

In particular, an attack on alpha_q or beta_q individually would
repeat09az's failed coefficientwise cancellation test. The next
estimate must couple DIFFERENT rational b values through their full
physical kernels, including the nonzero transverse defects. The
already closed positive-cone action can only be used after proving
its exact incidence with this complete assembled representation.

Required work remains: finite divisor expansion with both masks;
exact lattice Poisson with actual amplitudes; a uniform stationary
expansion including both edges and transition ranges; signed mode
aggregation with every divisor coefficient; restore the original
sharp cubic. No such analytic obligation is inserted as a Lean
premise. This is an active attempt, not a retired no-go card.

## Gates

- [x] 0 → 1: literal source and unconditional target identified.
- [ ] 1 → 2: signed growing-mode estimate and all remainders proved.
- [ ] 2 → 3: exact theorem formalized and direct leaf/axiom audits passed.
- [ ] 3 → 4: publication review.

## Log

- 2026-10-06,25az: source-based denominator-dual attempt opened.
  Stationary geometry exposes a growing rational-mode family and
  a rank-one, rather than nondegenerate, two-variable phase.
  These paper calculations have not produced a hard analytic saving.
