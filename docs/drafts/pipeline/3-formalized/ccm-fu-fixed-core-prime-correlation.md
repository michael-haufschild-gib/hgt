# CCM-FU: complete signed prime-release correlation

- **Stage:** 3-formalized; exact-file checks, new-declaration axiom audit and current global lint passed; Lake packaging pending.
- **Parent:** [fixed-core prime correlation](../1-in-progress/ccm-fu-fixed-core-prime-correlation.md).
- **Closed:** Exact all-cutoff paired-source identity, explicit mixed-block limits, absolute convergence over all quotient depths, exact reserve coefficient series, rigorous finite-prefix error.
- **Physical identification and orientation:** [The exact physical integral and strict distant-prime coefficient sign](ccm-fu-discrete-physical-prime-release.md) are proved.
- **Open:** Uniform reserve control through changing cores and cutoffs, exhaustive selection, uniform signed Abel bound, RH.

## Literal signed source

For p prime outside the finite processed prime core P, the full energy release is

`Q_P(M)-Q_(P+p)(M)=sum_r R_(P,p,M)(r)`,

`R_(P,p,M)(r)=2*sqrt(p)*r*I_P(M,r)*I_P(M,p*r)`.

The source contains every squarefree 1<=r<=M with primeFactors(r) disjoint
P+p. This identity holds at every cutoff, even before p is born. Both
clipped samples retain their signs. Their exact update is

`I_(P+p)(M,r)=I_P(M,r)-sqrt(p)*I_P(M,p*r)`.

The latter identity holds on every positive squarefree source avoiding P+p.

## Explicit complete coefficient

Write a_n,b_n for the existing processed-head slope and intercept in the
physical square-root clock. For n>=1 set q=floor(n/p) and

`Xi_(P,p,n)(t)=2*[a_n*a_q*t`

`+(2/3)*(sqrt(p)*a_n*b_q+b_n*a_q)*t*sqrt(t)`

`+sqrt(p)*b_n*b_q*t²/2]`.

Put c_(P,p,0)=0 and, for n>=1,

`c_(P,p,n)=rho_(P+p)*[Xi_(P,p,n)(1/n)-Xi_(P,p,n)(1/(n+1))]`.

The actual release source in quotient cell M/r=n, divided by M², tends to
c_(P,p,n). The complete series is absolutely convergent and

`kappa_P-kappa_(P+p)=sum_n c_(P,p,n)`.

This is an explicit signed series in the literal head values. Its exact
physical representation is 2*rho_(P+p)*p^(-3/2)*W_P(p). For every fixed
nonempty core, sufficiently distant unprocessed primes give strict sign
(-1)^(card(P)+1). No sign for every prime at every cutoff is asserted.

For C_P=(3/5)*2^(card(P)-1), with natural truncated subtraction,

`abs(kappa_P-kappa_(P+p)-sum_(n<T) c_(P,p,n)) <= 2*C_P²/T`

for every T>0. The stronger finite-source tail bound is

`sum_(source r, M/r>=T) abs(R_(P,p,M)(r)) <= (2*C_P²/T)*M²`.

Thus finite head data come with a proved error for the full signed
coefficient. The bound depends on processed cardinality; it does not renew
reserve through changing cores.

## Dependency-closed paper proof

The squarefree source splits exactly by p-divisibility. Multiplication by
p bijects its divisible class with squarefree cofactors avoiding P+p.
The prime-merger identity on the label primeFactors(r), the product
interpolation theorem and mu(p*r)=-mu(r) give the displayed sample update.
The original energy therefore splits into the two old sample squares.
Subtract the new sample square: the diagonal squares cancel and the
literal signed cross term remains. Samples at and beyond their birth
threshold vanish, so the child cutoff may be extended to the full source
without an omitted endpoint term.

On M/r=n, the exact nested quotient is M/(p*r)=floor(n/p). Apply both
existing affine head identities. The release term becomes

`2*M*(a_n+b_n*sqrt(r/M))*(a_q+sqrt(p)*b_q*sqrt(r/M))`.

Expand this product and apply the already proved source count, square-root
and linear moments at the exact cell endpoints 1/n and 1/(n+1). This gives
the stated signed block limit with density rho_(P+p).

The same release term equals -2*F_P(M,primeFactors(r))*
F_P(M,insert p primeFactors(r)). The existing source-amplitude ceiling
bounds its absolute value by 2*C_P²*M. There are at most floor(M/T) source
integers with M/r>=T. Summing gives the absolute tail bound at every cutoff.

The absolute values of every finite set of limiting block masses have sum
at most 2*C_P², by passing from the literal absolute source bound. Hence the
mass series is absolutely summable. Passing to the energy limits in the
finite-source remainder inequality gives the explicit finite-prefix error.
Letting T tend to infinity identifies the series with kappa_P-kappa_(P+p).
No positivity, numerical result or unknown analytic estimate is a premise.

## Lean validation

Seven new public theorems in `MobiusDivisorFixedCorePrimeCorrelation` and
`MobiusDivisorFixedCorePrimeCorrelationLimit` pass foreground scratch checks.
Both leaves are wired into `RHTower.lean`; only their needed leaf oleans
are emitted using `lake env lean <file> -o <leaf.olean>`. One external
scratch audit of these seven new declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`. The declaration index is refreshed.
No full or umbrella build is run. The known
Lake packaging audit remains pending to avoid its broad prerequisite rebuild.

The current global formal lint passes. The companion physical bridge
adds its own exact-file checks and new-declaration audits without
re-auditing these existing seven theorems.

Owned scratch files and validation logs are removed; no owned Lean process remains.
