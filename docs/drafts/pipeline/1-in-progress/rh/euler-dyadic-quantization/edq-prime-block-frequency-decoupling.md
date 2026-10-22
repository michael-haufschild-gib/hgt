# EDQ: prime blocks and rational-frequency decoupling

- **ID:** EDQ-PRIME-FREQUENCY-DECOUPLING
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Bound the complete signed physical covariance while retaining the prime-block drift and the actual rational-frequency coefficients.
- **Status:** No stronger arithmetic estimate. Paper transfer tests only; no new Lean theorem or closed no-go.

The proof chain remains Euler deletion → cofinal subpower source control
→ off-line exclusion → RH. This attempt tests two possible ways of
controlling the cross terms. Neither supplies the required estimate.

## Prime-block cancellation test

Write \(b_n(u)=(\{u/n\}-\{u\}/n)/u\), \(G_N=\sum_{n\le N}\mu(n)b_n\),
and \(D_pf(u)=f(u/p)/p\). Group each nonzero coefficient with n>1 by
its largest prime factor p. If \(P^+(1)=1\), the exact block is

\[
 B_{p,N}=-\sum_{\substack{m\le N/p\\P^+(m)<p}}\mu(m)b_{pm},
 \qquad G_N=\sum_{p\le N}B_{p,N}.
\]

The generator identity \(b_{pm}=D_pb_m+b_p/m\) gives
\[
 B_{p,N}
 =-D_p\!\sum_{\substack{m\le N/p\\P^+(m)<p}}\mu(m)b_m
   -b_p\!\sum_{\substack{m\le N/p\\P^+(m)<p}}\frac{\mu(m)}m .
\]
Unique prime factorization proves the grouping; substitution proves the
generator identity. The harmonic term remains at the same masked cutoff.

For N/2<p≤N, this block is exactly \(-b_p\). These blocks reinforce each
other in the physical measure. The corpus already proves the stronger
packet bound
\[
 \left\|\sum_{N/2<p\le N}b_p\right\|^2
 \ge \frac{\lfloor N/2\rfloor}{2}
       \left(\sum_{N/2<p\le N}\frac1p\right)^2
\]
in DeletionPrimePacket.packet_norm_sq_lower. It also proves cancellation
with the entire remaining source in relative norm. Thus prime grouping
does not create orthogonal increments or a new absolute bound.

EulerDeletionResidueMartingale already bounds the genuine innovations
by two in squared norm; its drift contains all squarefree composite
increments. The inspected fixed-source conditional-expectation theorems
do not bound that growing drift. Neither known result needs another
formalization or audit.

## Exact frequency coefficients retained by the next test

EulerDeletionFluxFourierTruncation retains the following finite primitive
at every divisor-channel time:
\[
 F_{N,Q}(x)=\frac1{2\pi^2}
 \sum_{e\le N}\mu(e)e\sum_{1\le m\le Q}
           \frac{\cos(2\pi mx/e)-1}{m^2}.
\]
Its all-time flux truncation error is logarithmic when Q=N+1.
Reducing the rational frequency m/e, put m=ar and e=br, with (a,b)=1,
and define
\[
 D_{a,b}=\min(\lfloor N/b\rfloor,\lfloor Q/a\rfloor),\qquad
 H_b(D)=\sum_{\substack{r\le D\\(r,b)=1}}\frac{\mu(r)}r .
\]
Finite regrouping gives the paper identity
\[
 F_{N,Q}(x)=\frac1{2\pi^2}
 \sum_{\substack{b\le N,\ a\le Q\\(a,b)=1}}
 \frac{b\mu(b)}{a^2}H_b(D_{a,b})
                  \bigl(\cos(2\pi ax/b)-1\bigr).             \tag{1}
\]
Indeed, \(\mu(br)=\mu(b)\mu(r)1_{(b,r)=1}\), including when either
side vanishes, and \(e/m^2=b/(a^2r)\). The two cutoffs and the constant
term are retained. Formula (1) is not the different reduced-denominator
complementary kernel head in EulerDeletionReducedDenominatorHead.

## Curved-frequency transfer test

A broad newest-first arXiv search for decoupling found Jiajun Wang's
[Sharp Bilinear Decoupling under Shell-Type Restrictions and Applications](https://arxiv.org/html/2608.19531v1)
(20 August 2026). Theorem 1.5 and the inspected cap–plate proof use
paraboloid extension phases \(x\cdot\xi+t|\xi|^2\). Nonzero interactions
must satisfy both a linear-frequency relation and a squared-frequency
relation. EDQ's sum in (1) has one physical time variable; it supplies
the linear phase only.

This distinction affects literal source terms. For a prime p>N/2 with
p≥11 and Q≥4, the rational coefficients in (1) at a/p, a=1,2,3,4,
are all nonzero: D=1 and the coefficient before \(1/(2\pi^2)\) is
\(-p/a^2\). The quartet
\[
  \frac1p+\frac4p=\frac2p+\frac3p,\qquad
  \frac{1^2+4^2-2^2-3^2}{p^2}=\frac4{p^2}\ne0
\]
is coherent in the physical variable. Adding and averaging a quadratic
phase changes this contribution. This is not a lower bound for the
complete signed flux or energy; all other terms remain.

The corpus's unconditional
integral_unitSquare_discreteParabola_norm_pow_six_subpower in
BourgainPlanarDiscreteDecoupling likewise integrates both variables.
A generic trace transfer with only subpower cost is unavailable even
for its elementary one-sign packet: at v=0 and
0≤u≤1/(6H), the real part of \(\sum_{n=1}^H e^{2\pi inu}\) is at
least H/2. Its sixth moment on the u interval is at least H^5/384.
The two-variable theorem bounds the full-square moment by
\(C_\epsilon H^{3+\epsilon}\). Thus the missing trace can cost a
positive power. This test does not rule out an arithmetic trace estimate
using the actual coefficients in (1); no such estimate is proved here.

The Gaussian exact-curve theorem inspected in
BourgainExactOsculatingGaussianDecoupling also retains a higher-dimensional
integral and an explicit perturbation condition. No identification with
the complete EDQ weighted time sum was found.

## Search coverage and remaining work

Three deep searches covered signed Gram/divisor/Schur methods, reverse
filtrations, and decoupling. The first two used OR matching; the last
used one word. Each used all retrieval views, no module cap, no refresh,
two rounds and a 120-second budget. All three returned 20 declarations,
20 candidate lemmas and 20 source arguments, all inspected. No proof
ideas were returned. The sole ingredient set concerned rational
exponent bookkeeping and was unverified.

The first two searches ended at the deadline with pending coverage,
generation 873347. The second also reported unavailable semantic
retrieval and malformed judging output. The last completed in 80 seconds
with only semantic-index incompleteness: its reported inventory covered
56,810 files, generation 873531, with most compiler states pending.
Candidate applicability was unchecked and compiler status source-only.
These searches do not certify absence of an applicable theorem.

Further inspected hits retain their own gaps: growing signed prime
batches omit middle primes, while monotone Möbius density positivity
uses inverse-square dilation weights. Neither supplies the covariance
estimate here. The cumulant arXiv page was unavailable; web searches
with dates returned older unrelated material.

The remaining work is an arithmetic estimate for the actual coefficients,
same-time cross terms, constant term and complete divisor-channel tail
in (1). A bound for a lifted average, selected prime pool, or innovation
component does not supply it. No computations, Lean builds, axiom
printing, frontier-map edits, or new route-independent claims were made.
