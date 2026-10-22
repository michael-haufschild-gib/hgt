# Hedenmalm central-band complete Gaussian Hankel law

- **ID:** `hedenmalm-central-band-complete-gaussian-hankel-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT AN RH PROOF]`

## Statement

Let `R>=0` satisfy

\[
 C\left(\left(R+\frac12\right)^2+1\right)<4,
 \qquad C=2+\gamma_E-\log(4\pi).
\]

Let

\[
 J_a(b)=\partial_a\left|\Xi(b-ia)\right|^2
\]

be the Hedenmalm Fourier current, with `0<a<1`, and let `tau>0`.  Then

\[
 J_a(b)\ge 0\qquad (|b|\le R).
\]

Consequently, for the restricted Gaussian moments

\[
 m_n^{[-R,R]}(\tau,a)
 =\int_{-R}^{R}b^n e^{-\tau b^2}J_a(b)\,db,
\]

the complete Hankel tower is positive semidefinite:

\[
 \sum_{i,j=0}^{N-1}v_i v_j m_{i+j}^{[-R,R]}(\tau,a)\ge0
\]

for every `N` and every real vector `v`.  The exact corpus certificate makes
`R=218/25` admissible.  In particular this holds at every critical aperture `0<a<1/2`.  This is
an all-order statement, not positivity of a fixed finite Hankel section.

## Proof

Put `z_+=b+ia` and `z_-=b-ia`.  Exact quartet admissibility implies that every off-line centered
Xi divisor point is separated from `[-R,R]` by more than the full transverse half-width.
Pairing each centered divisor point with its critical-line conjugate in the relative-resolvent
trace therefore gives

\[
 \operatorname{Im}T(z_+)\le0\qquad (a>0,\ |b|\le R).
\]

This is the already proved exact quartet-band resolvent theorem.  Centered Schwarz symmetry
gives

\[
 T(z_+)=\overline{T(z_-)},
\]

and hence `Im T(z_-)>=0`.  The same quartet bound makes `Xi(z_-)` nonzero.  The canonical product
identity `Xi'/Xi=T` and the aperture-current identity now yield

\[
 J_a(b)
 =2|\Xi(z_-)|^2\operatorname{Im}T(z_-)
 \ge0.
\]

For a vector `v=(v_0,...,v_{N-1})`, let

\[
 p_v(b)=\sum_{j=0}^{N-1}v_jb^j.
\]

Finite summation and the definition of the moments give the exact identity

\[
 \sum_{i,j=0}^{N-1}v_iv_jm_{i+j}^{[-R,R]}(\tau,a)
 =\int_{-R}^{R}p_v(b)^2e^{-\tau b^2}J_a(b)\,db.
\]

Every factor in the integrand is nonnegative, proving the complete tower simultaneously at all
orders.

## Exact progress and remaining core

The theorem discharges the compact central frequency region for every critical aperture.  By the
evenness of the current, the global Hedenmalm condition is reduced to

\[
 J_a(b)\ge0\qquad \left(b>\frac{218}{25},\ 0<a<1/2\right).
\]

The existing source theorem identifies this positive-frequency tail with the remaining RH-bearing
orientation problem.  No finite-height certificate, finite Hankel section, or compact-frequency
argument can close that tail by itself.

## Lean realization

The unconditional formalization is

```text
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCentralBandGaussianHankel.lean
```

Its capstones are

```text
xiRelativeResolventTrace_im_nonneg_lower_exactOffLineQuartetBand
thetaCuspCenterMixedFourierCurrent_nonneg_exactOffLineQuartetBand
thetaCuspCenterMixedFourierCurrent_nonneg_twoHundredEighteen_twentyFifths
hedenmalmCentralGaussianHankelCone_exactOffLineQuartetBand
hedenmalmCentralGaussianHankelCone_twoHundredEighteen_twentyFifths
```

The direct file check and exact-module build pass.  The capstones depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Parent boundary

The resolvent-pair sign and polynomial-square moment identity are existing corpus mechanisms.  The
present theorem is their exact Hedenmalm-coordinate composition and is classified as a bridge, not
as new scientific knowledge.
