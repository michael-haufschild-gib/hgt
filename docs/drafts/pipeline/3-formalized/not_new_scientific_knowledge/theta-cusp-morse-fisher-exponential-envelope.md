# Theta-cusp Morse--Fisher exponential envelope

- **ID:** `theta-cusp-morse-fisher-exponential-envelope`
- **Stage:** 3-formalized
- **Type:** source-specific estimate law
- **Scientific status:** literature bridge pending novelty audit
- **Lean source:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaMorseFisherExponentialEnvelope.lean`
- **Statement:** The first-atom Morse Fisher quotient retains an exact exponentially decaying
  endpoint excess, yielding an unconditional upper bound strictly stronger than the constant
  endpoint envelope and a polynomial quadratic proxy that feeds the existing Stein--Robertson
  and linear trace-Hankel consumers.

## The estimate

Let

\[
t(x)=\pi e^{2x},\qquad q(x)=t(x)-\frac32,
\qquad A=\frac{\frac32}{\pi-\frac32}.
\]

For every `x>=0`,

\[
q(x)\ge \left(\pi-\frac32\right)e^{2x},
\]

and therefore

\[
\frac{t(x)}{q(x)}
 =1+\frac{3}{2q(x)}
 \le 1+A e^{-2x}
 \le 1+A(1-2x+2x^2).                         \tag{1}
\]

The second inequality is the global Taylor bound

\[
e^{-u}\le1-u+\frac{u^2}{2},\qquad u\ge0.       \tag{2}
\]

Its proof is exact: the positive exponential series gives
`1+u+u^2/2 <= exp u`, inversion reverses the inequality, and

\[
\left(1-u+\frac{u^2}{2}\right)
\left(1+u+\frac{u^2}{2}\right)-1=\frac{u^4}{4}.
\]

## Fisher residual

Write

\[
F(x)=x^4-x^5+\frac{x^6}{4}\ge0,
\qquad b(x)=e^{5x/2}e^{-\pi e^{2x}},
\]

and let

\[
R_F=\int_0^\infty F(x)\frac{t(x)}{q(x)}b(x)\,dx.
\]

Then `(1)` gives the unconditional chain

\[
R_F
\le \int_0^\infty F(x)(1+Ae^{-2x})b(x)\,dx
\le (1+A)\int_0^\infty F(x)b(x)\,dx,           \tag{3}
\]

as well as the finite polynomial-moment proxy

\[
R_F
\le \int_0^\infty F(x)
  \bigl(1+A(1-2x+2x^2)\bigr)b(x)\,dx.          \tag{4}
\]

Thus `(3)` strictly retains the decay discarded by the old endpoint estimate, while `(4)`
replaces the rational Fisher insertion by Gibbs moments only through order eight.

More precisely, write

\[
R_m=\int_0^\infty x^m\chi_{1,1}(x)^2\,dx,
\qquad
L_m=\int_0^\infty x^m b(x)\,dx.
\]

The sharpened upper energy is exactly the finite value

\[
\begin{aligned}
U_{\rm quad}={}&
 \frac34R_0+R_1-\frac78R_2-\frac12R_3+\frac5{16}R_4+8L_3\\
&+(1+6A)L_4-(8+18A)L_5
 +\left(\frac{11}{4}+\frac{51}{2}A\right)L_6
 -15AL_7+3AL_8.                                      \tag{5}
\end{aligned}
\]

This equality, not only the integral upper bound, is formalized unconditionally.

## Route consequence

The exact quadratic Stein energy is bounded above by the new polynomial-envelope energy.
Consequently the source-specific scalar condition

\[
\left(14\left(\frac{3005}{2997}\right)^2-9\right)J_1^2U_{\rm quad}
\le9J_0C^2                                            \tag{6}
\]

implies the buffered adjacent-ratio inequality

\[
14\left(\frac{3005}{2997}J_1\right)^2\le9J_0J_2,
\]

and, together with the already isolated relaxed fourth-moment inequality, every real
linear-polynomial prime--archimedean trace-Hankel test is nonnegative.

High-precision pre-certification gives a positive margin for `(6)`.  This computation selects the
certificate but is not part of the proof.  The remaining open task is a rigorous rational
enclosure of the finite Gibbs and radial moments occurring in `(5)` and in the relaxed
fourth-moment condition.  No RH conclusion is claimed here.

## Formal theorem surface

- `thetaCuspFirstAtom_morseWeight_exponential_floor`
- `thetaCuspFirstAtom_morseScale_div_weight_le_exponential`
- `thetaCuspFirstAtom_morseScale_div_weight_le_quadratic`
- `thetaCuspFirstRadialQuadraticMorseFisherResidual_le_exponentialEnvelope`
- `integral_morseFisherExponentialEnvelope_le_endpoint`
- `thetaCuspFirstRadialQuadraticMorseFisherResidual_le_quadraticEnvelope`
- `thetaCuspFirstRadialQuadraticVirialEnergy_le_morseQuadraticEnvelopeUpperEnergy`
- `integral_morseQuadraticEnvelopeUpperGibbs_eq_gibbsMoments`
- `thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy_eq_finiteMoments`
- `thetaCusp_firstRadial_upper_of_morseQuadraticEnvelope`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_morseQuadraticEnvelope`

The module has no project axioms or placeholders.
