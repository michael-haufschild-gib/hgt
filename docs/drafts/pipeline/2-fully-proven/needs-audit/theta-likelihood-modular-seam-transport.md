# Theta likelihood modular-seam transport

- **ID:** `theta-likelihood-modular-seam-transport`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PAPER-PROVED] [LEAN PARTIAL] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`
- **Statement:** The fixed positive likelihood measure of the higher theta tail extends across the modular seam, where reflection becomes an exact two-ended Laplace balance, a reciprocal Möbius scattering law, a strict monotone-likelihood-ratio transport, and an all-order odd score-orthogonality hierarchy.

## Definitions

Put

\[
 B(x)=\pi e^{2x}-\frac32,
 \qquad h(x)=\operatorname{thetaCuspSourceTerm}(x,1),
\]

and let `nu` be the positive higher-tail likelihood measure already constructed in
`ThetaCuspLikelihoodSpectralMeasure.lean`:

\[
 d\nu(t)=\sum_{n\ge2}e^{-3(n^2-1)/2}
 \left(n^4\delta_{n^2-1}(dt)
 +\frac32n^2(n^2-1)\mathbf 1_{(n^2-1,\infty)}(t)\,dt\right).
\]

Write

\[
 L(q)=\int_0^\infty e^{-qt}\,d\nu(t),
 \qquad d\mu=\delta_0+d\nu,
 \qquad C_x(t)=h(x)e^{-B(x)t}.
\]

The modular-seam window is

\[
 \mathcal I=\{x>0:B(-x)>0\}.
\]

No numerical endpoint is used.

## Theorem

For every real `x` with `B(x)>0`, the existing one-sided likelihood law extends to

\[
 k(x)=h(x)(1+L(B(x)))=\int C_x(t)\,d\mu(t),                 \tag{1}
\]

where `k=thetaCuspFullSource`. Consequently, for every `x in I`,

\[
 \int C_x(t)\,d\mu(t)=\int C_{-x}(t)\,d\mu(t),             \tag{2}
\]

and this common value is `k(x)=k(-x)`.

The two normalized channel measures

\[
 dP_x(t)=\frac{C_x(t)}{k(x)}d\mu(t),
 \qquad
 dP_{-x}(t)=\frac{C_{-x}(t)}{k(x)}d\mu(t)                  \tag{3}
\]

are probability measures. Moreover,

\[
 B(x)>B(-x)>0,
 \qquad h(x)>h(-x)>0.                                     \tag{4}
\]

Define the positive crossing location

\[
 \tau(x)=\frac{\log(h(x)/h(-x))}{B(x)-B(-x)}>0.            \tag{5}
\]

Then the Radon--Nikodym ratio is the exact decreasing exponential

\[
 \frac{dP_x}{dP_{-x}}(t)
 =\exp((B(x)-B(-x))(\tau(x)-t)).                           \tag{6}
\]

Thus `C_x-C_{-x}` has exactly one sign change: positive below `tau(x)`, zero at
`tau(x)`, and negative above it. In particular `P_x` is below `P_{-x}` in monotone
likelihood-ratio order and hence in first stochastic order:

\[
 \int \varphi\,dP_x\le\int\varphi\,dP_{-x}                \tag{7}
\]

for every nondecreasing observable for which both integrals exist.

At the seam, put `B_0=pi-3/2` and let `P_0` be the probability measure proportional to
`e^{-B_0t}dmu(t)`. For every odd integer `m`, define the channel score polynomial

\[
 Q_m(t)=\left.
 \frac{\partial_x^m C_x(t)}{C_0(t)}\right|_{x=0}.
\]

Then `Q_m` is a real polynomial of degree `m`, with leading coefficient `(-2pi)^m`, and

\[
 \int Q_m(t)\,dP_0(t)=0.                                  \tag{8}
\]

The first member is explicit. With

\[
 \ell_1=\frac92-2\pi+\frac6{2\pi-3}>0,
\]

one has

\[
 Q_1(t)=\ell_1-2\pi t,
 \qquad
 \mathbb E_{P_0}[t]=\frac{\ell_1}{2\pi}.                  \tag{9}
\]

Since `nu` is supported on `[3,infinity)`, if `p_0=P_0((0,infinity))` is the normalized
higher-tail mass at the seam, then

\[
 3p_0\le\mathbb E_{P_0}[t]=\frac{\ell_1}{2\pi},
 \qquad p_0\le\frac{\ell_1}{6\pi}.                        \tag{10}
\]

Equivalently, for the existing spectral moments,

\[
 2\pi M_1(B_0)=\ell_1(1+M_0(B_0)).                        \tag{11}
\]

### Nonperturbative modular scattering corollary

Let

\[
 \iota(B)=\frac{\pi^2}{B+3/2}-\frac32,
 \qquad Z(B)=1+L(B),
 \qquad S(x)=\frac{h(-x)}{h(x)}.
\]

Then source reflection is exactly the order-reversing fractional-linear temperature map

\[
 B(-x)=\iota(B(x)),\qquad \iota(\iota(B))=B.              \tag{12}
\]

In the modular-seam window, the positive partition obeys the exact scattering law

\[
 Z(B(x))=S(x)Z(B(-x)),\qquad
 0<S(x)<1,\qquad S(x)S(-x)=1.                             \tag{13}
\]

The crossing is therefore not an endpoint approximation. It is the negative divided slope of
the log partition along one complete modular orbit:

\[
 \tau(x)=\frac{\log Z(B(-x))-\log Z(B(x))}{B(x)-B(-x)}.   \tag{14}
\]

Write

\[
 m(B)=-\frac{d}{dB}\log Z(B)
     =\frac{M_1(B)}{1+M_0(B)}.
\]

Log-convexity of every positive Laplace partition, strict here because the carrier has mass at
both `0` and `3`, gives the exact thermodynamic bracket

\[
 m(B(x))<\tau(x)<m(B(-x)).                                \tag{15}
\]

Equivalently, if `P_x` and `P_{-x}` are the normalized channel laws in (3), their directed
relative entropies are

\[
 D(P_x\Vert P_{-x})
   =(B(x)-B(-x))(\tau(x)-m(B(x))),
\]

\[
 D(P_{-x}\Vert P_x)
   =(B(x)-B(-x))(m(B(-x))-\tau(x)).                       \tag{16}
\]

Both are strictly positive. Their sum is the exact Jeffreys flux

\[
 (B(x)-B(-x))(m(B(-x))-m(B(x))).
\]

Thus modular reflection is a passive, reciprocal exponential-family scattering process in the
latent coordinate. The seam limit of (14)--(15) recovers (9):
`tau(x) -> m(B_0)=ell_1/(2*pi)`.

## Dependency-closed proof

For one theta atom, set `A=pi*exp(2x)` and `d_n=n^2-1`. Direct division by the first
atom gives

\[
 \frac{\phi_n(x)}{\phi_1(x)}
 =n^2\frac{2An^2-3}{2A-3}e^{-Ad_n}.
\]

The only denominator is `2A-3=2B(x)`, so the formula and the existing summable atom
decomposition hold whenever `B(x)>0`, not only when `x>0`. Writing `A=B+3/2` and using
`e^{-Bd}/B=int_d^infinity e^{-Bt}dt` proves (1) term by term; Gaussian decay justifies
the countable sum exactly as in the existing one-sided theorem.

Apply (1) at `x` and `-x`. Theta modular reflection gives `k(-x)=k(x)`, proving (2).
The channel is positive because `B(plus_or_minus x)>0`, so (3) defines probabilities.
For `x>0`, strict monotonicity of the exponential gives `B(x)>B(-x)`. The measure `nu`
has positive mass at `t=3`, hence `L` is strictly decreasing on the positive half-line.
Equation (2) therefore gives

\[
 \frac{h(x)}{h(-x)}=\frac{1+L(B(-x))}{1+L(B(x))}>1,
\]

which proves (4)--(5). Dividing the two densities gives (6), and its sign relative to one
gives the single-crossing assertion. Because the signed density in (2) has total mass zero,

\[
 \int\varphi(dP_x-dP_{-x})
 =\int(\varphi(t)-\varphi(\tau(x)))(dP_x-dP_{-x})\le0,
\]

proving (7).

For (8), differentiate (1) in a fixed neighborhood of zero on which `B` stays positive.
Every `m`th channel derivative is `C_x(t)` times a degree-`m` polynomial in `t`; on a
smaller neighborhood it is dominated by a constant times
`(1+t^m)exp(-beta*t)` for some `beta>0`. All such tilted moments of `mu` are finite by
the existing spectral-measure theorem, so differentiation under the integral is valid at every
order. The source `k` is even, hence every odd derivative at zero vanishes, proving (8).
The leading term comes from differentiating the exponential `m` times and is
`(-B'(0)t)^m=(-2pi*t)^m`.

Finally,

\[
 Q_1(t)=\frac{h'(0)}{h(0)}-B'(0)t=\ell_1-2\pi t.
\]

The existing exact first-atom boundary theorem gives `h'(0)/h(0)=ell_1>0`, so (9) follows
from (8). The support of `nu` starts at `2^2-1=3`, giving (10); rewriting (9) before
normalization gives (11).

For (12), add `3/2` to `B(x)` and use
`(B(x)+3/2)(B(-x)+3/2)=pi^2`; applying the identity twice proves involutivity. Equation
(13) is (2) divided by the positive first-atom factor, and reciprocity follows by reflecting
again. Strict contraction is (4). Taking logarithms of (13) gives (14).

The normalized fixed-carrier law at temperature `B` has density `e^{-Bt}/Z(B)` with respect to
`mu`. Differentiation under the integral gives `(log Z)'=-m` and
`(log Z)''=Var_B(t)>0`; variance is strict because `mu` has the atom at zero and positive mass at
three. Strict secant inequalities for a strictly convex function give (15). Finally, logarithm
of (6) is `(B(x)-B(-x))(tau(x)-t)`; integrating it first against `P_x` and then its negative
against `P_{-x}` proves (16) and the Jeffreys identity.

## Hostile audit

Verdict: `SURVIVES PRELIMINARY ATTACK` as source structure; `BRIDGE` as an RH mechanism.

What is wrong first: (2) and (8) are modular evenness expressed through the new likelihood
factorization. Neither implies translation positive definiteness or the Hedenmalm current sign.
Complete monotonicity in `B`, strict likelihood-ratio order in `t`, and every odd seam
cancellation can coexist without a theorem controlling Fourier phase. Presenting this law as a
sign producer would repeat the coordinate-substitution error already ruled out in the parent card.

What is new and useful: the two reflected source ends now live on one fixed positive measure and
are related by the explicit one-crossing likelihood ratio (6). The seam cancellation is no longer
only a formal statement that odd source jets vanish: (8) identifies the exact positive carrier
against which every odd channel-score polynomial is orthogonal. Equation (9) fixes its first
barycenter exactly. Equations (12)--(16) additionally identify modular reflection as a reciprocal
Möbius scattering process whose phase is a log-partition secant and whose dissipation is exact
relative-entropy flux. The higher tail can therefore be small in normalized seam mass while
remaining responsible for all algebraic cusp cancellation and the surviving oscillatory
orientation.

## External parent audit

- Sondow--Dumitrescu horizontal modulus monotonicity is the parent RH equivalence, not a source
  producer.
- Dimitrov--Xu correlation kernels connect Fourier/Laplace Wronskians to positivity and give an RH
  density criterion, but do not identify this normalized higher-tail measure or its reflected MLR
  transport.
- Romik's balanced-theta Laplace/Fourier constructions exploit modular reciprocity and derive
  explicit transforms of the classical theta weight, but do not state (2), (6), or (8) for the
  higher-to-first likelihood measure.
- Search of current theta-kernel log-concavity and total-positivity work found no exact normalized
  measure law with this two-sided seam transport. Priority remains unverified pending specialist
  review.

## Exact open core

`[OPEN CORE]` Convert the stochastic order (7) into Fourier-phase orientation. Concretely, express
the unresolved two-ended resolvent phase current as an integral of an observable which is monotone
in the latent likelihood coordinate `t`, or prove an appropriate two-parameter total-positivity
law for the channel resolvent kernel. Without that connector, the law is not RH progress by itself.

## Lean plan

Verified exact theorem surface `[LEAN-PROVED]`:

- `thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos`;
- `integral_thetaCuspLikelihoodSeamChannel_reflection`;
- `iteratedDeriv_integral_thetaCuspLikelihoodSeamChannel_zero_of_odd`;
- `thetaCuspLikelihoodSeamChannel_reflection_lt_iff`;
- `thetaCuspLikelihoodCoordinate_neg_eq_modularInvolution`;
- `thetaCuspLikelihoodModularInvolution_involution`;
- `thetaCuspLikelihoodPartition_modular_scattering`;
- `thetaCuspLikelihoodSeamScattering_mul_reflection`;
- `thetaCuspLikelihoodSeamScattering_mem_Ioo`;
- `thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant`;
- `hasDerivAt_log_thetaCuspLikelihoodPartition`;
- `thetaCuspHigherLikelihoodSpectralMoment_seam_barycenter`.

The scratch axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for every
listed capstone. Targeted
`lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodModularSeam` and
`scripts/formal_tools.py lint --check-generated` pass. Remaining Lean gaps are the explicit
score-polynomial expansion in (8) and strict convexity/KL consequences (15)--(16).

1. [x] Extend the atom spectral identity and full source factorization from `x>0` to `B(x)>0`.
2. [x] Formalize reflected integral balance and strict first-atom asymmetry on the seam window.
3. [x] Formalize the exact likelihood-ratio identity and single-crossing sign law.
4. [x] Formalize all odd jets of the integrated fixed-measure channel and the first barycenter
   identity.
5. [x] Formalize Möbius reflection, reciprocal scattering, contraction, secant phase, and the
   log-partition derivative.
6. [ ] Expand every odd integrated channel jet as the explicit score-polynomial integral in (8).
7. [ ] Formalize strict log-partition convexity and the relative-entropy identities (15)--(16).
8. [x] Complete axiom/module audit for exact verified theorem surface. Keep card at Stage 2 until
   paper-only claims (8), (15), and (16) are formalized.

Current Lean module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodModularSeam.lean`.
