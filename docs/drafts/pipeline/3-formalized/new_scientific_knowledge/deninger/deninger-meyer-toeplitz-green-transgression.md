# Meyer Toeplitz--Green transgression

- **ID:** `deninger-meyer-toeplitz-green-transgression`
- **Stage:** 3-formalized
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

What remains is not discovery of the full trace formula.  It is
construction of a global Calderón/Hardy polarization relation and a
source-derived reflection orientation.  The complete Meyer character
cannot itself realize Paugam's alternating pairing: on the integrand

\[
 \widehat F(\rho)\widehat G(1-\rho)
 -\widehat G(\rho)\widehat F(1-\rho)
\]

the two reflection mates cancel.  Positive completion must first turn
the source relation into an exact orthogonal splitting; only its
oriented half-trace can be compared with Paugam.

## Hostile audit

- `(1)` is a trace identity on the source test algebra, not a positive
  form on \(M_\zeta\).
- The correction operators `(5)` are essential; the raw local cocycle
  `(2)` need not vanish on \(Z(H_\cap)\).
- Nuclearity and trace cyclicity are used only in Meyer's proved
  bornological/Fréchet setting.
- Paugam's upper/lower projector and Hodge positivity are not supplied
  by this theorem.
- The full character supplied here annihilates the reflection-odd
  Paugam wedge; treating `(5)` as the missing scalar cup is impossible,
  not merely unproved.
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

## Lean status

### The source-proved content landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerMultiplicativeGreenTransgression.lean`.  Axiom audit
for all 9 declarations: `propext, Classical.choice, Quot.sound` or less.

Meyer's trace identity `(1)` and the nuclearity of `(5)` are the imported analytic theorems; what
is proved here is everything the card itself proves.

- `deningerGreenForm`, `deningerGreenForm_antisymm` — **`(2)`--`(3)`**: on any commutative algebra
  with a derivation `D` and a trace `τ` killing derivations, the Green form `τ(F ⋆ DG)` is
  antisymmetric.  The proof is the card's: expand `τ(D(F ⋆ G))` by the Leibniz rule, use
  commutativity, and use `τ ∘ D = 0`.
- `deningerLogWeight`, `deningerMultTrace`, `deningerMultTrace_logWeight` — the concrete data of the
  multiplicative Schwartz algebra: the derivation is multiplication by `log`, the trace is
  evaluation at the unit, and the second hypothesis of the antisymmetry theorem is *proved* there,
  because `log 1 = 0`.
- `deningerLogWeight_convolution_leibniz` — the first hypothesis in the additive model: the
  splitting `x = t + (x - t)` under the integral is exactly the Leibniz rule for multiplication by
  the coordinate, i.e. for multiplication by `log` in multiplicative coordinates.  The integrability
  of the two pieces is a hypothesis, as it must be for the integral to split.
- `deningerMultInversion`, `deningerLogWeight_reflection` — **`(4)`**: multiplicative inversion
  anticommutes with the derivation, so it reverses the Green orientation.  This is the
  one-dimensional source analogue of the exchange of the two extended cusp boundary values.
- `deningerGreenTransgression_cutoff_independent` — **cutoff independence**: a commutator is
  additive in its first slot, so once the trace kills the commutator built from the difference of
  two admissible cutoffs — which is Meyer's cyclicity statement for a compactly supported
  difference — the two cutoffs give the same transgression.

### Remaining

Nothing the card proves.  Meyer's Toeplitz trace lemma `(1)`, nuclearity of the two correction
operators `(5)`, and resulting prime-plus-real Weil character are published analytic inputs;
mathlib has no bornological or nuclear Fréchet framework in which to restate them.  Global
Calderón/Hardy relation, faithful positive completion, source orientation, and comparison of its
oriented half-trace with Paugam stay open.  Full relative trace from `(5)` cannot substitute: it
cancels Paugam's reflection-odd wedge.
