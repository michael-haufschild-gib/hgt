# The critical trace and the logarithmic translation boundary

- **ID:** xi-theta-critical-log-translation-seam
- **Stage:** 2-fully-proven
- **Type:** THEOREM / TRANSFORM ADJUDICATION / NATIVE BOUNDARY OBSTRUCTION, [PROVED HERE]
- **Date:** 2026-07-10
- **Lean modules:** XiThetaCriticalTrace.lean, XiThetaLogTranslationSeam.lean
- **Parent:** xi-theta-source-seam.md

## Question

The positive theta half-source is lower-supported. Which coefficient coordinate is actually visible
from the completed critical trace, and does the square-rate Blaschke reader act on that coordinate?

Three candidate moves were attacked:

1. [FALSIFIED] Treat the completed trace as a Laplace resolvent in the square rates pi m^2.
2. [SURVIVES AS BRIDGE] Identify the completed trace as a Fourier/cosine transform in log x.
3. [SURVIVES AS NATIVE SEAM] Rewrite square-rate atoms as log-translates and calculate the failure
   of positive truncation to commute with those translations.

## Theorem A [PROVED]: exact critical trace

Let

h(u)=exp(u/4) F(exp u),

where F is the modified even theta kernel. For real t,

completedRiemannZeta₀(1/2+it)
  = Fourier(h)(t/(4 pi))/2.                                (1)

### Proof

Mathlib's Mellin/Fourier change of variables gives

mellin(F,s)=Fourier(u -> exp(-Re(s)u)F(exp(-u)))(Im(s)/(2 pi)).

At s=(1/2+it)/2, the pullback is

exp(-u/4)F(exp(-u))=h(-u)=h(u)

by the theta reflection law already proved in the parent card. The frequency is t/(4 pi), and the
definition of completedRiemannZeta₀ contributes the factor 1/2.

## Theorem B [PROVED]: all source integrability hypotheses discharge

The functions h, h_+, and h_-(u)=h_+(-u) are integrable on the real line.

### Proof

The strong functional-equation pair proves Mellin convergence of F at every complex point, in
particular at 1/4. The logarithmic change of variables converts that precise Mellin convergence
statement into integrability of u -> exp(-u/4)F(exp(-u)), which equals h. Indicators and
measure-preserving reflection give integrability of the two halves.

No new analytic Prop is assumed.

## Theorem C [PROVED]: the completed trace is the positive cosine trace

For every real frequency w,

Fourier(h)(w)=Fourier(h_+)(w)+Fourier(h_+)(-w).              (2)

The positive source is real-valued, so

Fourier(h_+)(-w)=conj(Fourier(h_+)(w)).

Consequently

completedRiemannZeta₀(1/2+it)
  = Re(Fourier(h_+)(t/(4 pi))).                              (3)

Equation (3) is an exact theorem, not a transform hypothesis.

## Attack on the apparent information loss

Taking a real part does not by itself destroy the positive source. A real function supported on a
half-line may be determined by its cosine transform. Thus (3) is not a non-injectivity theorem.

The actual failure of the Blaschke route is a variable mismatch. Its reader interpolates
exponentials exp(-pi m^2 x) in the additive heat variable x. Equation (3) supplies the Fourier
transform after x=exp u. Individual atoms are

a_m(u)=2 exp(u/4-pi m^2 exp u),

not exponentials in u.

## Theorem D [PROVED]: exact log-translation coordinates

Define the mother profile

psi(u)=2 exp(u/4-pi exp u).

For every positive integer m,

a_m(u)=m^(-1/2) psi(u+2 log m).                              (4)

Thus the square spectrum becomes a translation lattice with shifts 2 log m in logarithmic
coordinates. Fourier diagonalizes these translations, but its common mother multiplier is the
archimedean profile.

## Theorem E [PROVED NEW]: exact truncation/translation commutator

For a>0, let P_+ be strict positive-half truncation and let

Boundary_a(f)(u)=1_(-a,0](u) f(u+a).

Then pointwise,

P_+(f(.+a))(u)+Boundary_a(f)(u)=P_+(f)(u+a).                 (5)

Hence P_+ does not commute with the translations that diagonalize the theta atoms. The entire
commutator is located on the interval swept across the reflection boundary.

Combining (4) and (5), for m>1,

P_+(a_m)(u)
 + m^(-1/2) Boundary_(2 log m)(psi)(u)
 = m^(-1/2) P_+(psi)(u+2 log m).                            (6)

The boundary interval has exact length 2 log m.

## Theorem F [PROVED]: exact Fourier boundary coordinate

Let

Window_a(f)(v)=1_(0,a](v) f(v).

The swept boundary is a translate of this finite window:

Boundary_a(f)(u)=Window_a(f)(u+a).

Therefore, with the project's Fourier convention,

Fourier(Boundary_a(f))(w)
  = fourierChar(a w) Fourier(Window_a(f))(w).                (7)

For the m-th theta atom, the unresolved source correction is consequently an explicit phase times
the Fourier transform of the mother profile on the finite interval (0,2 log m]. This closes the
first transform calculation of the moving boundary; no boundary-pairing hypothesis remains.

## What fails before what works

- [FALSIFIED] The completed-Mellin trace directly supplies the half-plane Laplace resolvent consumed
  by the square-rate Blaschke reader.
- [FALSIFIED] Real-part symmetrization alone proves loss of the one-sided source.
- [PROVED] The completed trace is the positive cosine trace.
- [PROVED] Square heat atoms are weighted translates in log coordinates.
- [PROVED NATIVE OBSTRUCTION] The lower-support truncation and the coefficient-diagonalizing
  translations fail to commute by the explicit moving boundary charge (6).
- [PROVED] The Fourier image of that charge is the finite-window expression (7).

## Novelty and significance gate

- **Parent theory:** Mellin/Fourier change of variables, theta heat atoms, and indicator algebra are
  individually classical.
- **Novel composition:** equation (6) identifies the exact project-native obstruction after the
  actual completed source, its lower-support interface, and its square atoms are put in one
  coordinate system. The obstruction is neither reciprocal Gamma nor Blaschke conditioning: it is
  an index-dependent boundary commutator.
- **Significance:** this replaces a false transform bridge by a precise source-side charge that a
  future coefficient theorem must carry. It locates the obstruction rather than packaging it in a
  new Prop.

## Open core

The first stability test is now settled negatively in
xi-theta-reader-superexponential-conditioning.md. The m-th positive atom has L1 norm and uniform
critical Fourier amplitude at most exp(-pi m squared), so every normalized L1-continuous reader and
every finite critical-sample reader costs at least exp(pi m squared).

The surviving question is whether the completed carrier supplies a stronger intrinsic topology
that offsets this decay while still controlling the balanced Perron seam. Equation (7) makes every
individual boundary coordinate explicit; the remaining issue is a non-artificial topology for
simultaneous inversion. No RH consequence is asserted here.

## Gates

- [x] 0 -> 1: transform candidates generated and strongest candidate attacked.
- [x] 1 -> 2: equations (1)-(6) proved without open hypotheses.
- [x] 2 -> 3: formalized in the two named Lean modules.
- [ ] 3 -> 4: requires a coefficient theorem for the moving-boundary family and composition with
  the balanced Perron charge.
