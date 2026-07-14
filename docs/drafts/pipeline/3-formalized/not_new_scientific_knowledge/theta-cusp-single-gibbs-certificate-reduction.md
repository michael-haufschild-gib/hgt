# Theta-cusp single-Gibbs certificate reduction

- **ID:** `theta-cusp-single-gibbs-certificate-reduction`
- **Stage:** 3-formalized
- **Type:** exact source reduction law
- **Scientific status:** source-specific bridge; novelty not claimed
- **Lean source:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaSingleGibbsCertificateReduction.lean`
- **Statement:** Both live first-atom estimate obligations are exactly finite rational
  inequalities in one positive Liouville Gibbs moment sequence.

## Positive carrier theorem

Let

\[
b(x)=e^{5x/2}e^{-\pi e^{2x}},\qquad
L_m=\int_0^\infty x^m b(x)\,dx,
\]

and let `chi_1` be the first Born--Witten amplitude.  The exact Ward identity is

\[
\chi_1(x)^2=-b(x)-2b'(x),\qquad x\ge0.
\]

After integration by parts, every radial Born--Witten moment is therefore

\[
R_m=\int_0^\infty x^{m+2}\chi_1(x)^2\,dx
   =2(m+2)L_{m+1}-L_{m+2}.                    \tag{1}
\]

Thus the auxiliary Born--Witten density carries no independent scalar information in the two
remaining low-degree estimates: its complete contribution is the Ward image of the single
positive Gibbs density `b`.

## Morse--Fisher certificate

Put

\[
A=\frac{3/2}{\pi-3/2}.
\]

The quadratic-envelope upper energy is exactly

\[
\begin{aligned}
U_G={}&3L_1+\frac{21}{4}L_2+
  \left(-\frac{25}{8}+6A\right)L_4
  -\left(\frac{15}{4}+18A\right)L_5\\
&+\left(\frac{39}{16}+\frac{51}{2}A\right)L_6
  -15AL_7+3AL_8.                              \tag{2}
\end{aligned}
\]

Consequently the Morse--Fisher source certificate is equivalent to the single inequality

\[
\left(14\left(\frac{3005}{2997}\right)^2-9\right)
(8L_3-L_4)^2U_G
\le
9(4L_1-L_2)
\left(8L_3-6L_4+\frac12L_5\right)^2.          \tag{3}
\]

## Relaxed certificate

The independent relaxed fourth-moment obligation is exactly

\[
16\left(\frac{3005}{2997}\right)^2
(2e^{-\pi}-L_0)(8L_3-L_4)
\le45(4L_1-L_2)^2.                            \tag{4}
\]

Equations `(3)` and `(4)` together imply nonnegativity of every real linear-polynomial
prime--archimedean trace-Hankel test.

This is a positive carrier law: a successful low-degree estimate proof must certify one finite
moment fiber of the fixed positive density `b`.  Separate Morse, Witten, radial, Ward, and Fisher
channels are coordinate descriptions of that one fiber, not independent obligations.

## Remaining estimate

High-precision pre-certification gives strict positive margins for `(3)` and `(4)`, but numerical
evaluation is not used as proof.  The open analytic task is to produce rational enclosures for
`e^{-pi}` and `L_0,...,L_8` tight enough to discharge both inequalities.  Once those enclosures
are proved, the complete linear trace-Hankel block follows without any further physics input.

## Formal theorem surface

- `thetaCuspFirstAtomBornWittenDensity_eq_gibbsWard`
- `thetaCuspBornWittenRadialPowerMoment_eq_singleGibbs`
- `thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue_eq_singleGibbs`
- `thetaCuspFirstRadialQuadraticSteinCoupling_eq_singleGibbs`
- `thetaCuspFirstAtomSingleGibbsMorseCertificate_iff`
- `thetaCuspBornWittenRadialRawMoment_zero_eq_firstAtomWardMoment`
- `thetaCuspFirstAtomSingleGibbsRelaxedCertificate_iff`
- `thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_iff`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_singleGibbsLowDegreeCertificate`
- `thetaCuspFirstAtomSingleGibbsCertificateMaster`

The module contains no project axioms or placeholders.
