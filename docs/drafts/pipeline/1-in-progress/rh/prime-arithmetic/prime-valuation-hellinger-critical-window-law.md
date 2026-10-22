# Prime-valuation Hellinger critical-window law

- **ID:** `prime-valuation-hellinger-critical-window-law`
- **Stage:** 1-in-progress
- **Type:** EXACT DOUBLE-SCALING LIMIT / UNIVERSAL CRITICAL PROFILE
- **Status:** `[CONJECTURE FROZEN] [PAPER PROOF IN DEVELOPMENT] [LEAN GATED]`
- **Parent:** `../4-publication-ready/riemann-divisor-prime-transfer-spectrum/main.tex`

## Scope correction

This card is the still-open **one-sided** scaling law comparing the critical state with
\(c_N=\tau/\log N\). It is not the symmetric reflected law. The symmetric comparison of
\(\pm c/\log N\), with profile
\[
4\int_0^1\frac{\sinh^2(cu)}u\,du,
\]
is proved and tracked in
`../../../3-formalized/prime-valuation-reflected-critical-window-reciprocity-law.md`.

## Frozen statement

Let
\[
 A_N(c)^2=
 \prod_{p<N}
 \frac{(1-p^{-1})(1-p^{-(1-2c)})}
      {(1-p^{-(1-c)})^2}
\]
and, for \(\tau\in\mathbb R\), put \(c_N=\tau/\log N\). Then
\[
 \boxed{\quad
 A_N(c_N)^2\longrightarrow
 \exp\!\left(
   -\int_0^1\frac{(e^{\tau u}-1)^2}{u}\,du
 \right).
 \quad}
\]
The integrand is continuously extended by value \(0\) at \(u=0\).

Define
\[
 J(\tau)=\int_0^1\frac{(e^{\tau u}-1)^2}{u}\,du.
\]
Then the fixed-\(c\) Hellinger--Rees phases are outer regimes of one universal profile:

- \(J(\tau)=\tau^2/2+O(\tau^3)\) at the critical tangent;
- \(e^{-J(-T)}\sim 2e^{-\gamma}/T\) as \(T\to+\infty\), matching the
  half-normal Wold face;
- \(J(T)\sim e^{2T}/(2T)\) as \(T\to+\infty\), matching the
  all-orders-flat face.

## Proof spine

Write \(L=\log N\), \(u_p=\log p/L\), and \(a_p=e^{\tau u_p}\). Exact local logarithms give
\[
 \log A_N(c_N)^2
 =
 \sum_{p<N}
 \left[
 \log(1-p^{-1})+\log(1-a_p^2p^{-1})
 -2\log(1-a_pp^{-1})
 \right].
\]
Uniform Taylor control on the compact \(a_p\)-range gives
\[
 \log A_N(c_N)^2
 =
 -\sum_{p<N}\frac{(a_p-1)^2}{p}+o(1).
\]
The error is dominated by \(C_\tau p^{-2}\) and tends pointwise to zero, so dominated
convergence over primes applies.

For \(f_\tau(u)=(e^{\tau u}-1)^2=u\,g_\tau(u)\), with continuous \(g_\tau(0)=0\),
\[
 \sum_{p<N}\frac{f_\tau(u_p)}p
 =
 \frac1{\log N}\sum_{p<N}\frac{\log p}{p}g_\tau(u_p).
\]
The prime number theorem and Abel summation imply weak convergence
\[
 \frac1{\log N}\sum_{p<N}\frac{\log p}{p}
 \delta_{\log p/\log N}
 \Longrightarrow
 1_{[0,1]}(u)\,du.
\]
This proves the profile limit.

## Antagonist gates

- Formalize actual-prime weak convergence, not an assumed equidistribution wrapper.
- Formalize uniform logarithm remainder and dominated prime-square error.
- Audit whether this double-scaling profile or equivalent generalized Mertens formula is
  already in probability, mod-Poisson, or arithmetic statistical-mechanics literature.
- Do not add to publication manuscript before paper proof and Lean proof both close.
- Do not market profile as zero exclusion. Its significance is unification of all three
  Hellinger--Rees phases and identification of the noncommuting thermodynamic/tangent limit.
