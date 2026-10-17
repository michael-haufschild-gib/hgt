# Critical Nyquist finite part and signed broad-source classification

## Scope and status

[PROVED HERE] Dependency-closed paper proof below; Lean implementation not started.
This is one connected candidate contribution, not yet counted. It continues
infinite-grid tail rigidity within independent BiScaleUncertainty. The field
guide `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` remains read-only.
The user cleared the research goal on 2026-10-18. This paper is retained at the
fully proven paper stage; it leaves no partial Lean source or pending import.

The preceding package establishes the exact Taylor-order threshold. At equality,
its positive residual has infinite mass and logarithmically divergent cell sums.
Here we construct its continuous counterterm and finite part, then classify the
effect of actual signed source cancellation on broad-source limits.

## 1. Actual producer, constants and statements

Fix an integer k>=1, put m=k-1 and beta=k. For n>=1 write

    a_n=log n, b_n=log(n+1), delta_n=b_n-a_n,
    p_n(x)=sum_(j=0..k-1) w^(j)(a_n)(x-a_n)^j/j!,
    w(x)=cosh(kx), e_n(x)=w(x)-p_n(x),
    alpha_n=integral_[a_n,b_n] e_n(x) dx,
    c=k^k/(2(k+1)!), D=c 2^k, Q=2c+D, M=8D+4c.

Let e(x)=e_n(x) on (a_n,b_n], and e(x)=0 for x<=0. Values at
the countably many endpoints do not affect any integral. These are the actual
Nyquist Taylor producer and residual of package 15, not abstract approximants.

**Theorem A (explicit finite part).** Define d_n=alpha_n-c delta_n. Then

    |d_n| <= D delta_n/n <= D/n^2.

Consequently B=sum_(n>=1) d_n exists absolutely, and |B|<=2D. More generally
the tail B_N=sum_(n>=N) d_n satisfies |B_N|<=2D/N. For T>=0,

    F(T)=integral_0^T e(x) dx-cT,
    |F(T)-B| <= 2(3D+2c) exp(-T).

Thus B is also the unique limit of this continuous primitive. At logarithmic
nodes the stronger bound |F(log N)-B|<=2D/N holds.

**Theorem B (signed broad-test expansion).** Let H: R->R be compactly supported
and Lipschitz with constant K>=0. For every L>0,

    |integral_0^infinity H(x/L)e(x) dx
       -c L integral_0^infinity H(t) dt-B H(0)| <= K M/L.

No sign condition on H occurs. The constant M depends only on the producer order;
there is no source support radius in the bound. K is the actual Lipschitz constant
of this fixed test, not an energy-derived uniform regularity assumption.

**Theorem C (actual-source classification).** Let f be a nonzero real compactly
supported C^2 function. Put

    h_f(x)=integral_R f(u)f(u+x) du, R=h_f(0)>0,
    A=integral_R |f|, mu=integral_R f, H=h_f/R,
    f_L(u)=f(u/L), L>0.

There exists a finite global Lipschitz constant K_f for f. Every such constant
gives K_H=K_f A/R for H, and

    |integral_0^infinity [h_(f_L)(x)/h_(f_L)(0)] e(x) dx
       -c L mu^2/(2R)-B| <= M K_f A/(R L).

For every fixed f, normalized Levy energy E(f_L) tends to zero, and the normalized
correlations tend locally uniformly to one. Nevertheless the critical residual
tends to B exactly when mu=0; when mu!=0 it tends to positive infinity, with
residual/L -> c mu^2/(2R). Both alternatives have explicit actual smooth sources.
No infinite-grid zeros, polar constraint or global uniform convergence is asserted.

## 2. Elementary cell estimates and proof of Theorem A

The logarithmic width satisfies 1/(n+1)<=delta_n<=1/n by integrating 1/u.
The exact kth derivative is

    J_k(x)=k^k [exp(kx)+(-1)^k exp(-kx)]/2.

It is nonnegative and increasing for x>=0, including at x=0. The Taylor integral
remainder (or the endpoint remainder bounds proved in package 15) gives

    J_k(a_n) delta_n^(k+1)/(k+1)! <= alpha_n
      <= J_k(b_n) delta_n^(k+1)/(k+1)!.

In particular e_n>=0 on the cell. Divide these bounds by c delta_n>0 and use
exp(k log n)=n^k. Dropping the sign of the second exponential gives

    (n delta_n)^k-(delta_n/n)^k <= alpha_n/(c delta_n)
      <= ((n+1)delta_n)^k+(delta_n/(n+1))^k.                 (1)

For 0<=t<=1 the elementary inequalities

    (1-t)^k >= 1-kt, (1+t)^k <= 1+(2^k-1)t,
    k+1 <= 2^k

follow by induction. For the second inequality, multiply the kth bound by 1+t
and use t^2<=t; for the first, multiply by 1-t>=0 and discard the nonnegative
k t^2. The third starts at k=1 and doubles its previous bound.

Now 1-1/n<=n delta_n<=1 and (n+1)delta_n<=1+1/n. Each of the two small
terms in (1) is at most n^(-2k)<=1/n. Therefore

    1-(k+1)/n <= alpha_n/(c delta_n) <= 1+2^k/n.

Use k+1<=2^k and multiply by c delta_n. This proves the displayed bound for
d_n for every n>=1, including the first cell and odd k where J_k(0)=0.

The decreasing integral comparison gives

    sum_(n>=N) n^-2 <= N^-2+integral_N^infinity t^-2 dt <= 2/N.

It proves absolute convergence and the B_N bound without conditional rearrangement.
Also, positivity of e_n and the relative discrepancy bound give

    integral_[a_n,b_n] |e_n-c|
      <= alpha_n+c delta_n <= (2c+D)delta_n=Q delta_n.       (2)

At T=log N the cell widths telescope, so F(T)=sum_(n<N)d_n and
F(T)-B=-B_N. For arbitrary T>=0 choose the unique n with a_n<=T<b_n.
Local integrability follows from finitely many continuous cell pieces on every
bounded interval. Add the partial cell to F(a_n). Equations (2) and delta_n<=1/n
give

    |F(T)-B| <= |B_n|+integral_[a_n,T]|e_n-c|
      <= (2D+Q)/n=(3D+2c)/n.

Since exp T<n+1<=2n, 1/n<=2 exp(-T). This proves the continuous bound.
In particular F-B is absolutely integrable and has an exponentially small tail.
The construction subtracts c times physical length; c delta_n telescopes exactly.

## 3. Signed broad-test estimate

Fix H and L as in Theorem B. Compact support and local integrability make the
actual weighted integral finite. Decompose it cell by cell, subtracting the
continuous counterterm c integral_0^infinity H(x/L) dx. On cell n the difference is

    H(a_n/L)d_n+r_n,
    r_n=integral_[a_n,b_n] [H(x/L)-H(a_n/L)](e_n(x)-c) dx.

Only finitely many cells contribute for this fixed H and L. Lipschitz continuity
and (2) give |r_n|<=K Q delta_n^2/L, and therefore

    sum |r_n| <= 2KQ/L.                                   (3)

For completeness, delta_n^2<=n^-2 and the preceding integral comparison at N=1
is at most two. Next,

    |sum H(a_n/L)d_n-B H(0)|
      <= (K/L) sum |d_n| log n.

The latter infinite series converges absolutely. Integrating u^-1<=u^-1/2
from one to n gives log n<=2(sqrt n-1)<=2 sqrt n. Hence

    sum |d_n| log n <= 2D sum n^(-3/2)
      <= 2D [1+integral_1^infinity t^(-3/2)dt]=6D.          (4)

The equality involving B is legitimate because sum |d_n| converges; the weighted
estimate follows from the absolutely summable majorant in (4). Combining (3)
and (4) gives K(6D+2Q)/L=KM/L. Finally x=Lt, with L>0, gives the leading
term c L integral_0^infinity H. This proves Theorem B for signed H.

## 4. Source regularity, Fubini and energy

A compactly supported C^2 function has bounded derivative: its derivative is
continuous and vanishes outside the compact support, so its absolute value attains
a finite bound K_f. The mean value theorem gives |f(u)-f(v)|<=K_f|u-v| globally.
Thus, for arbitrary x,y,

    |h_f(x)-h_f(y)|
      <= integral |f(u)| |f(u+x)-f(u+y)| du
      <= K_f A |x-y|.

All these integrals are finite by compact support. The normalized H is therefore
globally Lipschitz with the stated K_H, compactly supported, even and H(0)=1.
Evenness follows by translating u in h_f(-x). Positive mass follows because a
nonzero continuous f has f^2 positive on some open interval. Cauchy--Schwarz gives
|H|<=1; no pointwise nonnegativity is used.

Tonelli applied to |f(u)f(u+x)| gives total integral A^2<infinity by translating
x for each u. Fubini is consequently valid for the signed integrand and gives

    integral_R h_f(x) dx = integral_R f(u) [integral_R f(u+x) dx] du=mu^2.

Evenness and the null measure of {0} then imply

    integral_0^infinity H=mu^2/(2R).                        (5)

This is the usual convolution mass identity, not a new theorem of this package.
It also follows from the reflected convolution representation in
`SignedDyadicCollarPartition.lean` and Mathlib's `integral_convolution`.

Changing variables u=Lv proves h_(f_L)(x)=L h_f(x/L) and h_(f_L)(0)=LR.
Theorem B and (5) yield Theorem C's expansion. Its error tends to zero. If mu=0
the limit is B; if mu!=0 the strictly positive linear coefficient forces positive
infinite divergence. In both cases dividing by L gives the claimed slope.

Let W=integral_0^infinity x w_arch(x) dx. This is finite and nonnegative by the
already certified `archWeightFirstMoment` estimates. Positivity of the correlation
deficit and the Lipschitz bound give, directly in the actual normalized energy,

    0 <= E(f_L)
      =integral_0^infinity [1-H(x/L)] w_arch(x) dx
      <= K_H W/L.

Equivalently apply the package-15 theorem
`exists_sourceRescale_linear_energy_bound` with scale 1/L. No differentiability
budget is inferred from an energy ceiling. The bound |H(x/L)-1|<=K_H|x|/L also
proves local uniform convergence on every fixed bounded interval.

## 5. Explicit smooth witnesses

Use the actual nonnegative smooth bump p=`nyquistWideBump`, equal to one near
zero and supported in [-1,1]. Its integral is positive and R_p=integral p^2>0.
The family p(u/L) has nonzero-mean critical divergence and energy tending to zero.

For cancellation define the actual signed source g(u)=p(u)-p(u-4). The two
supports lie in [-1,1] and [3,5] and are disjoint. Translation invariance gives
integral g=0 and integral g^2=2R_p>0. It is smooth and compactly supported.
Expanding the four products in the autocorrelation gives

    h_g(x)=2h_p(x)-h_p(x-4)-h_p(x+4).

The correlation h_p vanishes for |x|>=2, so h_g(4)=-R_p and H_g(4)=-1/2.
Thus the cancellation witness has a genuinely signed autocorrelation, not merely
an abstract test of zero integral. For g(u/L), the critical residual tends to the
same B, energy tends to zero, and the negative value occurs at x=4L. This explains
why local convergence to one alone cannot determine the global critical residual.

## 6. Audit and novelty boundary

Every result above concerns actual signed integrals; absolute values are used only
to prove error estimates and justify summation. The nonnegative bump is a sharpness
witness, while Theorems B and C include arbitrary signed sources. Ordinary source
mean zero is not logarithmic grid blindness or polar orthogonality.

Endpoint tests: k=1 is included; n=1 is included; all L>0 are allowed; zero H is
allowed; f=0 is excluded exactly where normalization requires R>0. No sign of B
or closed form for B is claimed. The continuous primitive estimate does not claim
absolute integrability of e-c itself. Its cell oscillations need not vanish in
absolute mass. No renormalized Lebesgue integral of e-c over the whole half-line
is used: B is an absolutely convergent cell-discrepancy series and a primitive limit.

Internal searches: `/tmp/nyquist-critical-finite-part-deep.json`,
`/tmp/nyquist-critical-cell-discrepancy-deep.json`, and
`/tmp/nyquist-critical-source-mean-deep.json`, plus focused exhaustive text searches.
All three completed without partial/error flags; all 20 candidate statements and
20 source arguments from each were inspected. They supplied existing Taylor bounds
and ordinary convolution mechanisms, not this critical finite-part/source theorem.
Semantic coverage remained unmeasured and compiler metadata source-only; direct
Lean checks remain necessary. Broad searches often confused additive autocorrelation
with multiplicative dilation autocorrelation; those candidates were rejected.

The external query for logarithmic Taylor quadrature finite parts produced no
usable matching theorem. This is not evidence of global priority. Standard
convolution machinery is documented in
[Mathlib's convolution module](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convolution.html#MeasureTheory.integral_convolution).
The contribution claimed here is the explicit critical Nyquist finite part and
its quantitative signed broad-source classification, beyond package 15's prefix
asymptotic and positive divergence witness. Taylor remainder bounds, elementary
power comparisons, Fubini and the convolution mass identity are parent methods.

Paper dependency audit: Sections 2 and 3 prove every new analytic estimate; Section 4
derives actual source admission and identifies the coefficient; Section 5 constructs
both alternatives. Reused dependencies are exactly the certified package-15
Taylor remainder and first-moment energy estimates, whose arguments are described
above. No open arithmetic, spectral, summability or optimizer premise remains.
