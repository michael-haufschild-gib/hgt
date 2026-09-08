# CCM-FU: a uniformly positive signed head moment

- **Stage:** 3-formalized; exact-file checks, new-declaration axiom audit and global lint passed. Lake packaging audit remains pending.
- **Parent:** [signed head moment and averaged remainder](../1-in-progress/ccm-fu-fixed-core-signed-head-moment.md).
- **Closed:** Literal continuous source, all-cutoff and all-rational sample identities, absolute moment integrability, exact Euler factorization, positive lower bound independent of the finite prime core.
- **Open:** Weighted distant-head average, correlation sign and size, reserve renewal, exhaustive selection, uniform signed Abel bound, RH.

## Exact theorem

Let b(n)=log(n)-tau(n)+2gamma and let G_empty be the real part of its existing
square-root summatory primitive. For a finite set P of primes, D=product(P),

`G_P(x)=sum_(d divides D) mu(d)*sqrt(d)*G_empty(x/d)`.

These are literal source values:

`G_P(M)=H_P(M)` and `G_P(M/r)=I_P(M,r)`

for every natural M and every positive natural r. No product threshold,
squarefree condition on r, disjointness condition on r, or omitted clip is
needed for these identities. The head is zero at and below one.

The inverse-cube integral is absolutely convergent and

`J_P=integral_1^infinity G_P(x)/x^3 dx`

`=J_empty*product_(p in P)(1-sqrt(p)/p²)`.

The two factor forms sqrt(p)/p²=p^(-3/2) are equal. The unit moment is

`J_empty=Re(LSeries(b,3/2))/6>0`.

For the finite convergent series S=sum_(n>=0) n^(-3/2),

`J_P >= exp(-2*S)*J_empty > 0`

uniformly over every finite prime core P. This is a positive integral of
the signed processed head; pointwise nonnegativity of G_P is not asserted.

## Dependency-closed paper proof

The logarithmic coefficient series and divisor-counting series converge
absolutely for Re(s)>1. Their exact difference with the constant 2gamma
proves absolute convergence of the literal coefficient b on that half-plane.
Its prefix is the existing divisor defect, bounded by 24*sqrt(N). Apply
the existing square-root summatory Mellin formula at s=2. Taking real parts
gives absolute integrability of G_empty(x)/x³ and the displayed L-series
value divided by six.

The existing primitive interpolation gives G_empty(M)=K_1(M), and between
k and k+1 gives K_1(k)+(sqrt(x)-sqrt(k))*D(k). All integer unit channels are
nonnegative, so exact square-root interpolation gives nonnegativity on the
whole ray. On (1,2) the value is (sqrt(x)-1)*D(1), strictly positive by the
existing analytic harmonic bounds for gamma. That interval has positive
measure, so the absolutely convergent unit moment is strictly positive.

The clipped channel homothety identifies sqrt(d)*G_empty(M/d)=K_d(M).
In the processed discrete head, nonsquarefree indices have zero Möbius
coefficient. All remaining indices have prime factors in P precisely when
they divide D. Divisors larger than the cutoff have zero channel. This
proves the finite divisor representation for every M, removing the old
product threshold. Applying the common clipped interpolation to each
divisor summand proves the full rational-sample identity.

For d>0, changing variables x=d*y in the inverse-cube moment of
G_empty(x/d) gives d^(-2)*J_empty. Multiplying by sqrt(d), summing the finite
signed dilation, and retaining absolute integrability gives the divisor
sum of mu(d)*sqrt(d)/d². This arithmetic function is multiplicative. Its
convolution with the constant-one arithmetic function gives the divisor
sum, whose value on D factors over P as product(1-sqrt(p)/p²).

For every prime p, u_p=sqrt(p)/p² lies in [0,1/2]. The existing analytic
logarithm inequality gives -log(1-u_p)<=u_p+2*u_p²<=2*u_p. The finite sum
of u_p is at most the convergent full natural p-series S. Summing logarithms
and exponentiating proves the uniform positive product floor.

## Lean implementation and validation

`DivisorContinuousUnitMoment.lean` contains the literal unit profile, its
integer and interval identities, the improved absolute-convergence range,
and its absolutely convergent strictly positive inverse-cube moment.

`MobiusDivisorContinuousHeadMoment.lean` contains all-cutoff finite Möbius
reassembly, the rational sample identity, absolute integrability, exact
Euler product, its uniform lower bound, and the integral from one to infinity.

Both leaves pass foreground scratch checks and exact-file checks using
`lake env lean`; only their two needed leaf oleans were emitted. Both are
wired into `RHTower.lean`. One external scratch audit covers only the 22
new public declarations (20 theorems and two definitions); it reports only
`propext`, `Classical.choice`, and `Quot.sound`. Global formal lint passes.
The declaration index is refreshed. No full or umbrella build was run;
the known Lake packaging audit remains pending to avoid its broad stale
prerequisite rebuild. No numerical experiment, numerical premise, added
axiom, or unfinished proof is used.

## Remaining mathematical obstacle

The source moment is the factor needed by a possible signed weak remainder
argument. The dilation average W_P(Y)=integral G_P(Y*x)*G_P(x)/x³ is not yet
controlled as Y grows. A pointwise constant limit for G_P after its leading
square-root term is not assumed. The existing complete correlation series
is already formalised, but its continuous integral identification and a
signed asymptotic estimate for W_P remain open. Neither the new moment law
nor the existing fixed-core energy limit supplies reserve renewal by itself.
