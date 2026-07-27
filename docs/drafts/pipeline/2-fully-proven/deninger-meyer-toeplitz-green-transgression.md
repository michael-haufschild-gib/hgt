# Meyer Toeplitz--Green transgression

- **ID:** `deninger-meyer-toeplitz-green-transgression`
- **Stage:** 2-fully-proven
- **Type:** PUBLISHED SOURCE THEOREM / GREEN IDENTIFICATION
- **Label:** `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** Meyer's nuclear trace computation is a
  cutoff-independent Green transgression on the multiplicative
  Schwartz algebra; its zeta and Fourier correction terms are the
  exact source of non-diagonal arithmetic boundary coupling.

## Multiplicative Green cocycle

Let
\[
 \mathcal A=C_c^\infty(\mathbb R_{>0})
\]
with multiplicative convolution, let
\[
 \tau(F)=F(1),\qquad
 (\partial F)(x)=F(x)\log x,
\]
and choose a smooth cutoff \(\phi\) equal to \(0\) near \(0\) and
\(1\) near infinity.  Write \(\lambda(F)\) for convolution and
\(M_\phi\) for multiplication by \(\phi\).

Meyer proves that
\[
 \lambda(F)[M_\phi,\lambda(G)]
\]
is nuclear on every weighted multiplicative Schwartz/Sobolev
realization and
\[
 \operatorname{Tr}\bigl(
   \lambda(F)[M_\phi,\lambda(G)]
 \bigr)
 =
 \tau(F*\partial G).                                           \tag{1}
\]

`[PROVED: MEYER] [DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION]`

Define
\[
 \omega_{\mathrm{mult}}(F,G)=\tau(F*\partial G).               \tag{2}
\]
Then
\[
 \omega_{\mathrm{mult}}(F,G)
 =
 -\omega_{\mathrm{mult}}(G,F),                                \tag{3}
\]
and `(1)` is independent of the interior shape of \(\phi\).

### Proof of antisymmetry

The operator \(\partial\) is a derivation of convolution and
\(\tau(\partial H)=0\).  Since convolution on
\(\mathbb R_{>0}\) is commutative,
\[
\begin{aligned}
 0
 &=\tau(\partial(F*G))\\
 &=\tau((\partial F)*G)+\tau(F*\partial G)\\
 &=\omega_{\mathrm{mult}}(G,F)
   +\omega_{\mathrm{mult}}(F,G).
\end{aligned}
\]
This proves `(3)`.

For two admissible cutoffs \(\phi,\phi'\), their difference is compactly
supported.  Cyclicity of the nuclear trace gives
\[
 \operatorname{Tr}\lambda(F)
 [M_{\phi-\phi'},\lambda(G)]=0,
\]
so `(1)` depends only on the two ends.  Equivalently, Meyer's direct
kernel proof replaces \(\phi\) by the half-line characteristic
function and obtains the logarithmic boundary jump.

## Reflection law

For
\[
 (\mathcal JF)(x)=x^{-1}F(x^{-1}),
\]
one has
\[
 \partial\mathcal J=-\mathcal J\partial.                       \tag{4}
\]
Thus multiplicative inversion reverses the Green orientation.  This
is the one-dimensional source analogue of the exchange of the two
extended cusp boundary values and of the two Calderón Hardy
polarizations.

## Zeta/Fourier correction

Let
\[
 Z=\sum_{n\ge1}\lambda_{n^{-1}}
\]
on Meyer's right-decaying source space.  In the same proof, the
operators
\[
 M_\phi-ZM_\phi Z^{-1},\qquad
 M_\phi-\mathcal F\mathcal J M_\phi\mathcal J\mathcal F        \tag{5}
\]
become nuclear after convolution by an admissible test packet.
Their traces give respectively:

1. the finite-prime Euler logarithmic derivative, through
   \(Z\,\partial(Z^{-1})\);
2. the archimedean Fourier boundary term.

Together `(5)` yields Meyer's complete prime-plus-real Weil character
on the source quotient.  Therefore the global arithmetic Green form
cannot be an orthogonal sum of independent Kummer rays.  Its required
cross-ray terms are already forced by conjugating one common cutoff by
the full Poisson operator \(Z\) and by Fourier reflection.

## Consequence for arithmetic cohomology

`DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN` provides the local
Dirichlet Green form.  Formula `(1)` identifies the universal
one-dimensional boundary transgression that its smooth suspension
must produce.  Formula `(5)` identifies the missing global incidence
correction before any spectral decomposition.

What remains is not discovery of a trace formula.  It is construction
of a global Calderón/Hardy polarization relation whose nuclear
relative trace realizes Paugam's alternating pairing, followed by a
positive completion on which that relation becomes an exact orthogonal
splitting.

## Hostile audit

- `(1)` is a trace identity on the source test algebra, not a positive
  form on \(M_\zeta\).
- The correction operators `(5)` are essential; the raw local cocycle
  `(2)` need not vanish on \(Z(H_\cap)\).
- Nuclearity and trace cyclicity are used only in Meyer's proved
  bornological/Fréchet setting.
- Paugam's upper/lower projector and Hodge positivity are not supplied
  by this theorem.
- No zeta zero, RH premise, CCM object, or numerical computation
  enters.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277, the Toeplitz trace lemma and the
  proof of the geometric character formula.
- `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS`.
- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.

## Log

- 2026-07-27 — Extracted Meyer's Toeplitz trace as the canonical
  multiplicative Green cocycle and identified his \(Z\)/Fourier
  conjugations as the required cross-ray arithmetic incidence terms.
