# The exterior Hedenmalm current has a complete positive Gaussian Hankel tower

- **ID:** `hedenmalm-exterior-complete-gaussian-hankel-phase-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent:** Sondow--Dumitrescu horizontal monotonicity, here reproved directly from the centered
  Xi divisor and transferred to the complete Gaussian moment cone
- **Lean:** `formal/GaloisForLFunctions/RHTower/HedenmalmExteriorGaussianHankel.lean`

## The law

Let

\[
 J_a(b)=\partial_a\left|\xi\!\left(\frac12+a+ib\right)\right|^2
       =\Re\widehat{\mathcal A_a'}\!\left(\frac{b}{2\pi}\right),
\]

where \(\mathcal A_a'\) is the canonical Hedenmalm horizontal-autocorrelation tangent.  For
\(\tau>0\), put

\[
 m_n(\tau,a)=\int_{\mathbb R} b^n e^{-\tau b^2}J_a(b)\,db.
\]

Then, unconditionally,

\[
 \boxed{
   \frac12\le a<1
   \quad\Longrightarrow\quad
   J_a(b)\ge0\quad(b\in\mathbb R)
   \quad\Longrightarrow\quad
   \sum_{i,j=0}^{N}c_ic_jm_{i+j}(\tau,a)\ge0
 }
\]

for every \(N\), every \(c_0,\ldots,c_N\in\mathbb R\), and every \(\tau>0\).  Thus every
exterior aperture \(1/2\le a<1\) carries a complete positive Gaussian Hankel tower.  In
particular, \(a=1/2\) gives one canonical complete tower without assuming RH.

The boundary is exact for the present route:

\[
 \left[
   J_a(b)\ge0\text{ for every }0<a<\frac12\text{ and every }b
 \right]
 \Longleftrightarrow \mathrm{RH}.
\]

The theorem therefore proves the whole exterior phase, not the RH-bearing interior phase.

## Proof

Write

\[
 X(z)=\Xi_C(z)=\xi\!\left(\frac12+iz\right),
 \qquad z=b-ai.
\]

The centered divisor points \(\alpha\) of \(X\) satisfy

\[
 -\frac12<\Im\alpha<\frac12.
\]

For the canonical relative-resolvent atom

\[
 r_\alpha(z)=\alpha^{-1}-(\alpha-z)^{-1},
\]

pair \(\alpha\) with its critical-line conjugate \(\overline\alpha\).  Direct algebra gives

\[
 \Im\bigl(r_\alpha(z)+r_{\overline\alpha}(z)\bigr)
 =\frac{-2\Im z\left((\Re z-\Re\alpha)^2+(\Im z)^2-(\Im\alpha)^2\right)}
 {\left((\Re z-\Re\alpha)^2+(\Im z-\Im\alpha)^2\right)
  \left((\Re z-\Re\alpha)^2+(\Im z+\Im\alpha)^2\right)}.
\]

If \(a\ge1/2\), then \(\Im z=-a\le-1/2\).  Hence

\[
 (\Im z)^2>(\Im\alpha)^2,
\]

the two denominator factors are strictly positive, and \(-2\Im z\ge0\).  Every paired atom is
therefore nonnegative.  The relative-resolvent series is absolutely summable away from the Xi
divisor, while the closed exterior \(|\Im z|\ge1/2\) is zero-free.  Pairing and summing give

\[
 \Im\frac{X'(z)}{X(z)}
 =\Im\sum_\alpha r_\alpha(z)\ge0.
\]

The actual Hedenmalm current satisfies

\[
 \begin{aligned}
 J_a(b)
 &=2\Re\!\left(\overline{X(z)}(-iX'(z))\right)\\
 &=2|X(z)|^2\Im\frac{X'(z)}{X(z)}\ge0.
 \end{aligned}
\]

This proves the global pointwise sign with no frequency restriction.

Finally, the Gaussian measure \(e^{-\tau b^2}db\) has full support and finite exponential moments.
The complete weighted-moment cone theorem identifies

\[
 \bigl[m_{i+j}(\tau,a)\bigr]_{i,j\ge0}\succeq0
 \quad\Longleftrightarrow\quad
 J_a(b)\ge0\quad\text{for all }b.
\]

Applying the pointwise-to-moment direction gives every Hankel section simultaneously.  This is a
complete tower theorem; no fixed or finite collection of sections is used.

## Scope and novelty audit

The exterior horizontal monotonicity of \(|\xi|\) is classical, notably in Sondow--Dumitrescu.
The present card's role is foundational: it supplies a dependency-closed proof in the exact
Hedenmalm current normalization and transports it to the complete Gaussian Hankel tower.  It is
not claimed as new scientific knowledge and does not establish the interior sign or RH.

## Formal theorem surface

- `xiRelativeResolventTerm_lineConj_pair_im_nonneg_lowerExterior`
- `xiRelativeResolventTrace_im_nonneg_lowerExterior`
- `kreinCurrent_eq_normSq_mul_logDeriv_im`
- `thetaXiHankelOrbit_kreinForm_nonneg_of_half_le`
- `thetaCuspCenterMixedFourierCurrent_nonneg_of_half_le`
- `hedenmalmGaussianHankelCone_exterior`
- `hedenmalmGaussianHankelCone_boundary`

## Reference

Jonathan Sondow and Cristian Dumitrescu, *A monotonicity property of Riemann's xi function and a
reformulation of the Riemann Hypothesis*, Periodica Mathematica Hungarica 60 (2010), 37--40,
<https://arxiv.org/abs/1005.1104>.
