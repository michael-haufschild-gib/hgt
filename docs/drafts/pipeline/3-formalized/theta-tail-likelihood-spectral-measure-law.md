# Theta-tail likelihood spectral-measure law

## Status

- Stage: `3-formalized`
- Label: `[FORMALIZED NEW THEOREM CANDIDATE]`
- Route: Riemann theta source / Hedenmalm / Connes source geometry
- Paper proof: complete
- Lean: complete and unconditionally checked in `ThetaCuspLikelihoodSpectralMeasure.lean`

## The law

Let
\[
  A(x)=\pi e^{2x},\qquad B(x)=A(x)-\frac32,qquad d_n=n^2-1,
\]
and let
\[
  R(x)=\frac{k(x)-\phi_1(x)}{\phi_1(x)}
\]
be the higher-to-first-atom likelihood ratio of the Riemann theta-cusp source.  For `x>0`, define
the positive Borel measure
\[
 d\nu(t)=\sum_{n\ge2}e^{-3d_n/2}
 \left(n^4\,\delta_{d_n}(dt)
 +\frac32 n^2d_n\,\mathbf 1_{(d_n,\infty)}(t)\,dt\right).
\]
Then
\[
 \boxed{R(x)=\int_0^\infty e^{-B(x)t}\,d\nu(t).}
\]
Equivalently, the exact atom ratio is
\[
 \frac{\phi_n(x)}{\phi_1(x)}
 =e^{-3d_n/2}\left(n^4e^{-d_nB(x)}
 +\frac32n^2d_n\frac{e^{-d_nB(x)}}{B(x)}\right).
\]

For every `B>0`, tilt the fixed measure by `e^{-Bt}` and write its moments as
\[
 M_m(B)=\int_0^\infty t^m e^{-Bt}\,d\nu(t).
\]
For every finite order `q`, the entire moment-Hankel block is strictly positive definite:
\[
 \left[M_{i+j}(B)\right]_{0\le i,j\le q}\succ0.
\]
Indeed its quadratic form is the exact Gram integral
\[
 \sum_{i,j=0}^q c_ic_jM_{i+j}(B)
 =\int_0^\infty\left(\sum_{i=0}^q c_it^i\right)^2e^{-Bt}\,d\nu(t),
\]
and the infinitely many positive atoms at the distinct points `d_n` make this integral strictly
positive for every nonzero coefficient vector.

## Why this is a law rather than an estimate

There is no cutoff, fitted constant, numerical certificate, or asymptotic inequality.  The theorem
identifies the exact spectral measure of the complete normalized higher theta tail and derives its
full all-order tilted-moment positivity hierarchy.  Low-order moment and finite Hankel positivity
are consequences of one representation.

## Proof core

For `A=\pi e^{2x}` the exact source quotient is
\[
 \frac{\phi_n(x)}{\phi_1(x)}
 =n^2\frac{2An^2-3}{2A-3}e^{-A(n^2-1)}.
\]
Writing `A=B+3/2` gives
\[
 n^2\frac{2An^2-3}{2A-3}
 =n^4+\frac32\frac{n^2(n^2-1)}B,
\]
while
\[
 e^{-A d_n}=e^{-3d_n/2}e^{-Bd_n}.
\]
Finally
\[
 \frac{e^{-Bd}}B=\int_d^\infty e^{-Bt}\,dt
 \qquad(B>0),
\]
which produces the displayed mixed measure term by term.  Gaussian decay in `n` gives all
exponentially tilted moments and justifies the countable measure and integral identities.

## RH relevance and exact open core

The law supplies a canonical positive spectral carrier already inside the actual Riemann theta
source.  It upgrades first-order likelihood order to an infinite strict Gram hierarchy and gives a
source-side Hilbert realization without selecting an artificial finite approximation.

It does **not** by itself prove RH.  The remaining RH-bearing problem is to prove that this exact
positive source carrier couples, under the relevant Fourier/Mellin/reflection transform, to the
global divisor with a zero-selecting incidence law.  The theorem materially narrows that problem:
the higher theta tail is no longer an unknown perturbation; its complete normalized contribution is
an explicit positive spectral measure.

## Anti-theatre and novelty audit

- The theorem is not an RH-equivalent restatement.
- It is not a numerical strengthening of a known inequality.
- Bernstein--Widder theory is parent machinery, not the new content.
- The new content is the exact mixed pure-point/ray representing measure forced by the Riemann
  theta atoms and the resulting strict all-order tilted-moment Hankel law.
- Repository search found the atomwise likelihood equation, antitonicity, and low-order theta
  curvature, but not this representation or all-order hierarchy.
- A primary-source search found general complete-monotonicity and theta-kernel literature, but no
  statement identifying this normalized theta-tail measure.  Novelty remains subject to a final
  specialist literature audit after the proof is dependency-closed.

## Lean plan

1. Formalize the exact `B`-coordinate atom quotient.
2. Define the mixed spectral measure as a countable sum of a Dirac mass and a restricted Lebesgue
   ray for every `n>=2`.
3. Prove the exact Laplace representation and all tilted moment integrability. **Complete.**
4. Prove that the tilted measure retains infinite support at every positive coordinate. **Complete.**
5. Apply the existing infinite-support moment-Hankel theorem to obtain strict positive definiteness
   and positive determinants at every finite order. **Complete.**
6. Expose one master theorem bundling factorization, measure representation, moment law, and strict
   Hankel hierarchy. **Complete.**

## Formal theorem surface

The unconditionally checked module
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspLikelihoodSpectralMeasure.lean` contains:

- `thetaCuspAtomLikelihoodRatio_eq_spectralTerm` — exact atomwise transformed quotient;
- `integral_exp_neg_mul_thetaCuspAtomLikelihoodSpectralMeasure` — one-atom measure identity;
- `integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure` — complete fixed-measure law;
- `thetaCuspHigherLikelihoodSpectralResponse_coordinate` — identification with the actual theta
  likelihood ratio;
- `thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral` — exact source factorization;
- `integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure` — all tilted moments exist;
- `thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef` — all-order strict Hankel law;
- `det_thetaCuspHigherLikelihoodSpectralMoment_hankel_pos` — determinant form;
- `thetaCuspHigherLikelihoodSpectralMasterLaw` — the bundled universal law.
