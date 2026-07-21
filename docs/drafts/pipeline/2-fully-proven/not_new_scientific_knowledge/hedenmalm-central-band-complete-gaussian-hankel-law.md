# Hedenmalm central-band complete Gaussian Hankel law

- **ID:** `hedenmalm-central-band-complete-gaussian-hankel-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT AN RH PROOF]`

## Statement

Let

\[
 J_a(b)=\partial_a\left|\Xi(b-ia)\right|^2
\]

be the Hedenmalm Fourier current, with `0<a<1`, and let `tau>0`.  Then

\[
 J_a(b)\ge 0\qquad (|b|\le4).
\]

Consequently, for the restricted Gaussian moments

\[
 m_n^{[-4,4]}(\tau,a)
 =\int_{-4}^{4}b^n e^{-\tau b^2}J_a(b)\,db,
\]

the complete Hankel tower is positive semidefinite:

\[
 \sum_{i,j=0}^{N-1}v_i v_j m_{i+j}^{[-4,4]}(\tau,a)\ge0
\]

for every `N` and every real vector `v`.  In particular this holds at every critical aperture
`0<a<1/2`.  This is an all-order statement, not positivity of a fixed finite Hankel section.

## Proof

Put `z_+=b+ia` and `z_-=b-ia`.  The unconditional Xi height gap through `9/2` implies that every
centered Xi divisor point whose frequency lies in `[-4,4]` is on the critical line, while every
remaining divisor point is separated from that band by more than the full transverse half-width.
Pairing each centered divisor point with its critical-line conjugate in the relative-resolvent
trace therefore gives

\[
 \operatorname{Im}T(z_+)\le0\qquad (a>0,\ |b|\le4).
\]

This is the already proved source-pure central-band resolvent theorem.  Centered Schwarz symmetry
gives

\[
 T(z_+)=\overline{T(z_-)},
\]

and hence `Im T(z_-)>=0`.  The same height gap makes `Xi(z_-)` nonzero.  The canonical product
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
 \sum_{i,j=0}^{N-1}v_iv_jm_{i+j}^{[-4,4]}(\tau,a)
 =\int_{-4}^{4}p_v(b)^2e^{-\tau b^2}J_a(b)\,db.
\]

Every factor in the integrand is nonnegative, proving the complete tower simultaneously at all
orders.

## Exact progress and remaining core

The theorem discharges the compact central frequency region for every critical aperture.  By the
evenness of the current, the global Hedenmalm condition is reduced to

\[
 J_a(b)\ge0\qquad (b>4,\ 0<a<1/2).
\]

The existing source theorem identifies this positive-frequency tail with the remaining RH-bearing
orientation problem.  No finite-height certificate, finite Hankel section, or compact-frequency
argument can close that tail by itself.

## Parent boundary

The resolvent-pair sign and polynomial-square moment identity are existing corpus mechanisms.  The
present theorem is their exact Hedenmalm-coordinate composition and is classified as a bridge, not
as new scientific knowledge.

