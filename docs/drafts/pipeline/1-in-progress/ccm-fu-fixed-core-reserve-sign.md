# CCM-FU: fixed-core quadratic reserve signs

- **Stage:** 1-in-progress.
- **Type:** Derived source diagnostic, not a new primary conjecture.
- **Parent:** [exact successor extension](ccm-fu-exact-successor-extension.md).
- **Goal:** Produce reserve through changing signed fields, then the uniform signed Abel bound and RH. Goal remains open.

## Frozen question

The empty state releases quadratic energy when any fixed first prime is
processed. Does an already processed fixed prime core still release energy
on that scale, or do some actual small-prime mergers have persistent positive
quadratic gain? Separate changes in the head square from nonempty energy.
The cutoff-seven stepwise obstruction and cutoff-21 defect obstruction do
not decide the eventual fixed-core sign. The existing all-state transport
bound limits costs but supplies no negative gain.

Fix S={2,3,5,7,11,13}. For every P subset S and q in S minus P, inspect

`r_(P,q)(M)=(Q_P(M)-Q_(P+q)(M))/M^2`.

Record Q_P/B with B=Q_empty and the head contribution
`(H_P^2-H_(P+q)^2)/M^2`; subtract it to retain the nonempty contribution.
This is the literal complete source energy at each cutoff. Q_P<=B alone
is not full successor-envelope admission. This finite prime pool is not
claimed to contain all available source primes.

## Frozen experiment and decision rules

Use every cutoff M=2^k for k=9,...,18 and all 64 states/192 edges.
Derive divisor counts, signed Möbius coefficients, the exact unit Abel
prefix and clipped dilation channels. Group every nonzero source coefficient
by its unprocessed prime-factor product; retain all source indices and labels.
Use at most eight cutoff workers and one-thread numerical libraries.

Store every energy, head, normalized release, and nonempty release.
A persistently negative diagnostic means r<-1e-8 at each of the final
three cutoffs. Report these edges separately according to whether their
parent has Q_P<=B at those cutoffs. Also report whether every remaining
prime in the fixed pool has negative release at any such parent. Do not
reinterpret this as rejection of all available source primes.

If any persistent negative edge exists, select the one with the most
negative final normalized release among parents below B at all three tail
cutoffs; if that class is empty, select the most negative persistent edge
overall. Independently reconstruct its complete source at the largest cutoff
at 80 digits. Recompute divisor counts by prime-factor exponents rather than
the floating run's divisor sieve. Verify both energies and their signed
release. One high-precision representative is the predeclared audit; all
other float diagnostics remain unaudited numerical evidence.

A negative quadratic-scale diagnostic would direct the proof toward the
fixed-core energy coefficient and its signed arithmetic correlation, rather
than assuming every next small prime provides reserve. A positive screen
would motivate proving that coefficient's source positivity. Neither finite
outcome proves an eventual sign, reserve renewal, complete selection or RH.
Do not change the cutoffs, threshold or budget after seeing the results.

Run only on the supplied RunPod host, under a 60-second foreground deadline
for the complete screen and optional audit. Download and hash the script
and output in the computation ledger, then remove owned remote files and
workers. No repeat at larger cutoffs is scheduled. No computed value may
become a Lean premise.

## Current evidence and proof target

The frozen run completed in 6.565 seconds including its 80-digit audit.
[Artifacts and interpretation](../2-fully-proven/computations/ccm-fu-fixed-core-reserve-2026-09-08/README.md)
record 91 persistent negative-release diagnostics, all from parents below the
original budget. Fourteen parents have that sign for every remaining prime
in the fixed pool. P={2,3} is one such parent. The audited strongest edge
P={3,5,11,13}, q=7 has normalized release approximately -0.00012103224 at
M=262144, almost entirely from nonempty fibres.

No eventual sign or failure of full completion follows from this finite
evidence. The complete fixed-core coefficient now has a proved series formula.
Its [complete signed correlation series](../3-formalized/ccm-fu-fixed-core-prime-correlation.md)
is also formalised; the remaining target is a reserve-producing sign and size law. Empty-state quadratic reserve cannot
be assumed to persist through arbitrary processed cores. No route is retired.

## Formalised source reduction

[Eight source theorems](../3-formalized/ccm-fu-fixed-core-profile.md) now prove
the exact profile and energy representations below, fixed-head cancellation,
and a uniform quotient-tail energy estimate. Exact-file and new-declaration
axiom checks passed. The complete coefficient now has a proved convergent block-series formula; its reserve-sign problem remains open.

For a finite processed core P and a disjoint remaining prime label R, set
r=product(R). The exact identity is

`F_P(M,R)=mu(r)*sqrt(r)*[(1-w(M,r))*H_P(floor(M/r)) + w(M,r)*H_P(floor(M/r)+1)]`.

Here H_P(N)=F_P(N,empty), with P fixed at both child cutoffs, and w is the
existing physical square-root clipping weight. Reindex the source by n=r*d.
Terms with gcd(r,d)>1 vanish by the Möbius square exclusion. For coprime
terms the surviving label is exactly R iff primeFactors(d) is contained in
P. Apply the existing masked clipped channel identity and sum. No sign or
analytic premise is needed. Squaring and summing over active labels gives
the complete energy as product-weighted samples of this same fixed-core
head. The squarefree Möbius square is one.

For D=product(P) with P consisting of primes, every nonzero head coefficient
has index dividing D. The new all-cutoff reassembly gives, for every M,
`H_P(M)=sum_(d divides D) mu(d)*K_d(M)`.
The corpus's uniform quotient-tail mean gives K_d(M)/sqrt(M)->c for each
fixed positive d. Thus the head limit is c times sum_(d divides D) mu(d),
which is zero for every nonempty P. This proves actual head cancellation
without a numerical premise. Together with the complete product-scale
identity, it distinguishes a vanishing fixed-core head at infinity from
the many moving-scale head samples that carry the full energy.

The [continuous signed head and every clipped rational sample](../3-formalized/ccm-fu-fixed-core-signed-head-moment.md)
are now formalised. Its inverse-cube first moment is uniformly positive
over finite prime cores, with an exact Euler factorization. This does not
settle the signed cross correlation. The weighted squarefree integral
identification remains unproved; the intended identity is
`kappa_P=rho_P*integral_1^infinity G_P(x)^2/x^3 dx`.
For q outside P, the intended continuous update is
G_(P+q)(x)=G_P(x)-sqrt(q)*G_P(x/q); its formal proof remains open.
After the integral identification, the diagonal terms
cancel after the density factor q/(q+1), leaving the signed correlation
`kappa_P-kappa_(P+q)=2*rho_P*q*sqrt(q)/(q+1)*integral_1^infinity G_P(x)*G_P(x/q)/x^3 dx`.
The [density, moments and actual block limits](../3-formalized/ccm-fu-fixed-core-density-moments.md)
and the [complete coefficient series](../3-formalized/ccm-fu-fixed-core-energy-limit.md)
are now proved in Lean for every fixed prime core, including the empty core.
The [complete signed prime-correlation series](../3-formalized/ccm-fu-fixed-core-prime-correlation.md)
now gives the exact release coefficient and a rigorous finite-prefix error.
Integral identification is optional; signed reserve control remains open and
is not a conclusion from the finite experiment. The [energy-limit card](ccm-fu-fixed-core-energy-limit.md)
states the exact remaining analytic steps.
