# Theta-cusp prime--archimedean first Hankel level

- **ID:** theta-cusp-prime-arch-first-hankel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[BRIDGE]`
- **Statement:** The zeroth Taylor moment of the normalized continued prime--Gamma trace is strictly positive; consequently every constant-polynomial source Hankel test is nonnegative, and every nonzero constant test is strictly positive.

## Theorem

Let
\[
\Phi(x)=\sum_{n\ge0}e^{x/2}\,
  2\pi\bigl(2\pi(n e^x)^4-3(n e^x)^2\bigr)e^{-\pi(n e^x)^2}
\]
be the full theta-cusp source. Lean proves
\[
\Phi(x)>0\qquad(x>0),
\]
and
\[
\Xi(t)=2\int_0^\infty \Phi(x)\cos(tx)\,dx.
\]
The Schwartz bounds justify two differentiations under the integral, giving
\[
\Xi(0)=2\int_0^\infty\Phi(x)\,dx>0,
\qquad
\Xi''(0)=-2\int_0^\infty x^2\Phi(x)\,dx<0.
\]
For the normalized continued prime--Gamma trace germ `G`, its first coefficient is therefore
\[
M_0=G(0)=-\frac{\Xi''(0)}{\Xi(0)}>0.
\]
Hence, for every real constant `c`,
\[
Q_{\mathrm{source}}(c)=c^2M_0\ge0,
\]
with strict inequality when `c\ne0`.

## Top-down chain advanced

\[
\Phi>0
\Longrightarrow
\Xi(0)>0\ \text{and}\ \Xi''(0)<0
\Longrightarrow
M_0>0
\Longrightarrow
Q_{\mathrm{source}}(c)\ge0
\quad(c\in\mathbb R).
\]

This discharges the degree-zero slice of `PrimeArchSourceTraceHankelIntNonnegative` without using Xi zeros or assuming RH.

## Positive open core

The remaining moments are logarithmic cumulants, not raw moments of the positive density. Write
\[
r_{2j}=\frac{2\int_0^\infty x^{2j}\Phi(x)\,dx}{\Xi(0)}.
\]
Formal power-series algebra gives
\[
M_0=r_2,
\qquad
M_1=\frac{r_2^2}{2}-\frac{r_4}{6},
\qquad
M_2=\frac{r_6}{120}-\frac{r_2r_4}{8}+\frac{r_2^3}{4}.
\]
Thus the first nonconstant two-by-two Hankel condition is the explicit theta-source inequality
\[
M_0M_2-M_1^2
=\frac{r_2r_6}{120}+\frac{r_2^2r_4}{24}-\frac{r_4^2}{36}\ge0,
\]
equivalently
\[
3r_2r_6+15r_2^2r_4-10r_4^2\ge0.
\]

`[OPEN CORE]` Prove this inequality from the exact theta-cusp density, then determine whether its mechanism extends to all Hankel minors. Positivity of an arbitrary density does not imply this cumulant inequality, so the next step requires genuine source shape information.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstMoment.lean`.

Principal declarations:

- `thetaCuspFullSource_pos_of_pos`
- `integral_Ioi_thetaCuspSecondMoment_pos`
- `XiC_ofReal_eq_two_mul_thetaCuspCosine`
- `Xi_secondDeriv_zero_neg`
- `analyticTraceMoments_normalizedPrimeArchSource_zero_pos`
- `primeArchSourceTraceHankel_C_re_nonneg`
- `primeArchSourceTraceHankel_C_re_pos`

## Gates

- [x] Source-side statement contains no Xi zero data
- [x] Positive theta source and weighted integrability proved
- [x] Exact completed Fourier/cosine identification proved
- [x] Center value and second derivative signs proved
- [x] Constant-polynomial source Hankel positivity formalized
- [ ] First two-by-two cumulant Hankel determinant
- [ ] Full countable source Hankel cone
