# Meyer Poisson nuclear polarization pair

- **ID:** `deninger-meyer-poisson-nuclear-polarization-pair`
- **Stage:** 3-formalized
- **Type:** PUBLISHED SOURCE THEOREM / TOPOLOGICAL GUARDRAIL
- **Label:** `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** Meyer's source trace uses one exact and one
  almost-complemented Poisson polarization; convolution makes their
  defects nuclear, so no exact continuous Hardy projector on the
  nuclear source is required or presently justified.

## Ambient Poisson pair

Use Meyer's notation
\[
 \mathcal W=\mathcal S_>\oplus\mathcal S_<.
\]
The two closed source embeddings are
\[
\begin{aligned}
 \iota_+f&=(Zf,\mathcal JZ\mathcal Ff),\\
 \iota_-g&=(g,g).
\end{aligned}                                                    \tag{1}
\]
For a cutoff \(M_\phi\), Meyer constructs continuous maps
\[
 \pi_+:\mathcal W\to H_+,\qquad
 \pi_-:\mathcal W\to H_-                                       \tag{2}
\]
with
\[
 \pi_-\iota_-=1.                                                \tag{3}
\]
Hence
\[
 P_-=\iota_-\pi_-
\]
is an actual continuous projection onto \(\iota_-H_-\).

For the positive/Poisson leg,
\[
 \pi_+\iota_+
 =
 M_\phi+\mathcal F M_\phi\mathcal F
 =
 1+M_\phi-\mathcal F\mathcal J
                 M_\phi\mathcal J\mathcal F                   \tag{4}
\]
in Meyer's conventions.  Meyer states that he does not know whether
\(\iota_+H_+\) admits an honest continuous section in \(\mathcal W\).
Thus
\[
 P_+=\iota_+\pi_+
\]
must not be silently treated as an idempotent.

## Nuclear replacement

`[PROVED: MEYER] [DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR]`

For every admissible convolution test packet \(F\),
\[
 \lambda(F)(P_--P_+)                                          \tag{5}
\]
is nuclear on \(\mathcal W\), and
\[
 \lambda(F)(1-\pi_+\iota_+)                                   \tag{6}
\]
is nuclear on \(H_+\).  The same assertions hold uniformly for
bounded sets of test packets.

Meyer's hereditary nuclear trace theorem then computes the virtual
source character from `(5)` and `(6)` without complementing
\(\iota_+H_+\).  The result is the complete prime-plus-real Weil
distribution.

## Arithmetic interpretation

Equations `(1)`--`(6)` are the analytic model of a global Calderón
polarization **relation**, not a pair of strict nuclear projectors.
The correct arithmetic construction has three levels:

1. exact complementary Hardy projectors on every finite local
   Calderón packet;
2. a closed global source relation whose cutoff representatives are
   idempotent only modulo the nuclear trace ideal;
3. exact orthogonal Hardy projectors on the completed positive Hodge
   Hilbert space.

Level 2 suffices for Meyer's virtual-character trace and for a
relative trace-class representative because nuclear trace is
hereditary and cyclic.  It does **not** supply Paugam's scalar cup:
the reflection-complete character cancels Paugam's antisymmetrized
wedge, whereas his nondegenerate form retains one oriented spectral
half.  Level 3, plus comparison of its source orientation with that
spectral half, is required for scalar cup comparison, Hodge
positivity, and skew-adjointness.  It must be constructed from source
Dirichlet energy, not assumed on Meyer's Fréchet quotient.

## Hostile audit

- Closed range of \(\iota_+\) does not imply complemented range.
- \(P_+\) is not an idempotent in the proved source theorem.
- Calling `(5)` a difference of exact projectors would strengthen
  Meyer without proof.
- An exact projector may exist after Hodge Hilbert completion; that is
  a separate arithmetic theorem.
- Nuclear almost-complementation gives traceability, not positivity.
- Meyer's (H_+) source embedding is not Paugam's upper-imaginary
  discrete spectral sector; the shared plus notation must not be
  used as an identification.
- No zeta zero, RH premise, CCM object, or numerical computation
  enters.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277, the almost-sections corollary and
  summable-character proposition.
- `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION`.
- `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

## Log

- 2026-07-27 — Replaced an unjustified strict source Hardy projector
  by Meyer's exact analytic structure: closed Poisson embeddings and
  an almost-projector whose convolution defects are nuclear.
- 2026-08-02 — Formalized the guardrail: the exact leg is a projection, the
  almost-leg is idempotent exactly modulo its transported defect, and exact
  idempotence would itself produce the complement Meyer does not claim.

## Lean status

### The guardrail landed

`formal/GaloisForLFunctions/RHTower/DeningerPolarizationAlmostProjection.lean`.  Axiom audit for
all 12 declarations: `propext, Classical.choice, Quot.sound` or less.

The nuclearity statements `(5)` and `(6)` are Meyer's published analytic theorems and enter as
named hypotheses; what is proved here is the algebra that the card's hostile audit is about.

- `deningerLeg` — the leg operator `ι ∘ π` of a polarization leg `(ι, π)`.
- `deningerExactLeg_isIdempotent`, `deningerExactLeg_range`, `deningerExactLeg_isCompl` — **the
  negative leg**: from `π₋ι₋ = 1` of `(3)`, `P₋ = ι₋π₋` is an honest idempotent, its range is
  `ι₋H₋`, and the ambient space splits as `ker P₋ ⊕ ι₋H₋`.
- `deningerAlmostLeg_defect` — **the positive leg**: for any `(ι, π)` the idempotence defect is the
  transported retraction defect, `P² - P = ι ∘ (πι - 1) ∘ π`.  This is the precise sense in which
  `(4)` controls how far `P₊` is from a projection.
- `deningerAlmostLeg_isIdempotent_iff` — `P₊` is idempotent exactly when that transported defect
  vanishes; so it must not be silently treated as an idempotent.
- `deningerAlmostLeg_defect_mem` — **idempotence modulo a two-sided class**: if the retraction
  defect lies in a class of operators closed under composition with `ι` and `π` — a trace ideal, in
  particular the nuclear ideal of `(6)` — then so does the idempotence defect of the leg.  This is
  level 2 of the card's arithmetic interpretation, stated exactly.
- `deningerAlmostLeg_defect_of_cutoff` — the shape of `(4)`: if `πι = 1 + cutoff - conjugate` and
  the class contains both and is closed under differences, the retraction defect is in the class.
- `deningerAlmostLeg_isCompl_of_isIdempotent` — **the guardrail itself**: if the almost-leg were an
  exact idempotent and `π₊ι₊` were onto, then `ι₊H₊` would be complemented, with `ker P₊` as its
  complement.  Assuming exact idempotence is therefore a complementation claim, which is precisely
  what Meyer states he does not know; calling `(5)` a difference of exact projectors would
  strengthen him without proof.
- `deningerScalarLeg_defect`, `deningerScalarLeg_isIdempotent_iff` — the hypothesis class is not
  vacuous: scalar legs realize every defect, and are idempotent exactly for idempotent scalars.

### Remaining

Nothing in the theorem.  Meyer's nuclearity of `(5)` and `(6)`, and the uniformity over bounded
test sets, are imported analytic results; the levels 1 and 3 of the arithmetic interpretation —
exact local Calderón Hardy projectors and exact orthogonal Hardy projectors after the positive
Hodge completion — are separate constructions and remain open.
