# A pure-spinor square is not an actuality law

- **ID:** `pure-spinor-square-actuality-route`
- **Stage:** 5-failed
- **Type:** FALSIFIED ROUTE / CATEGORY ERROR / EXACT ALGEBRAIC SURVIVOR
- **Parent:** `../1-in-progress/quantum-incompatibility-spacetime-law.md`
- **Statement:** A nonzero spinor square is not, by itself, a physical event that creates
  spacetime translation.

## Goal

Test the proposed shortcut:

```text
square-zero pure spinor = unrealized quantum possibility
nonzero spinor square = actualization
spinor square landing in a vector = creation of spacetime translation.
```

The target was a direct physical bridge from the Cartan pure-spinor boundary already present in
the exceptional corpus to emergent spacetime.

## Hostile audit

The same quadratic equation occurs in three distinct categories which the shortcut conflates:

1. in the ten-dimensional supersymmetry algebra, \(Q\) is an odd supercharge and
   \(\frac12\{Q,Q\}\) lies in the already supplied even translation module;
2. after parity reversal, the coefficients \(\lambda^\alpha\) are commuting coordinates on the
   nilpotence variety of square-zero supercharges; and
3. in the Berkovits formalism, \(\lambda^\alpha\) is a bosonic pure-spinor ghost and
   \(Q_{\mathrm{BRST}}=\oint\lambda^\alpha d_\alpha\) is required to be nilpotent.

None of these objects is a quantum measurement outcome, a primitive physical actuality, or an
operational event. A nonzero \(\lambda\Gamma^\mu\lambda\) violates the pure-spinor constraint and
destroys the stated BRST nilpotence; the literature does not interpret it as actualization.

The construction also presupposes the object it was supposed to derive. In the super-Poincare
algebra the vector representation \(V\) is already the translation ideal. Modern pure-spinor
superfield treatments define spacetime as a torsor for this supplied translation space and define
supermultiplets as vector bundles over that spacetime. The odd bracket closes onto translations;
it does not derive the existence, real form, dimension, Lorentzian signature, time orientation, or
dynamics of spacetime.

The closest exceptional example strengthens the warning. For the \(E_6\) generalized
supertranslation whose pure-spinor variety is the cone over the complex Cayley plane, Cederwall,
Jonsson, Palmkvist, and Saberi find cohomology in the wrong ghost degree, call the resulting
physical-state interpretation pathological, and state that the nonlinear structure lacks a known
physical interpretation. Exceptional incidence geometry alone is not an event law.

## Exact algebraic survivor

Let \(B:S\times S\to V\) be the symmetric bilinear odd bracket after parity reversal and write
\[
\operatorname{sq}(q)=B(q,q).
\]
If \(\operatorname{sq}(q)=\operatorname{sq}(r)=0\), then
\[
\operatorname{sq}(q+r)=B(q,r)+B(r,q)=2B(q,r).
\]

Thus the sum of two individually square-zero directions fails to be square-zero exactly by their
polarized cross bracket. Geometrically, this cross term is the quadratic normal obstruction to a
secant line remaining inside the nilpotence cone. In ten-dimensional minimal supersymmetry the
nilpotence cone is the Cartan pure-spinor cone.

Combined with the already formalized exceptional splitting, the corpus has the sharper coordinate
selection statement:

> The \(B\)-normal part of the polarized Cartan obstruction is sourced only by a color direction
> paired with a mixed color-weak direction; color-color, mixed-mixed, and every pair containing the
> weak scalar contribute zero.

This is a precise compatibility-defect bridge. It does not say that either argument is a physical
possibility, that the defect is an event, or that the target vector is spacetime.

## No-go closure

- **Exact killing theorem/mechanism:** supercharges, parity-reversed nilpotence coordinates, and
  BRST ghosts are not physical actualizations; their bracket lands in a translation module already
  built into the super-Poincare algebra. Nonzero pure-spinor square is loss of nilpotence, not a
  derived event law.
- **Strongest positive survivor:** the polarized cross bracket exactly measures incompatibility of
  two square-zero directions, and its exceptional \(3+2\) split obeys the formalized
  color-cancellation/normal-selection law.
- **New insight:** pure-spinor geometry may test a future, independently defined physical
  joint-possibility relation. It cannot define that relation by relabelling. The open core moves
  from `SPINOR SQUARE AS ACTUALITY` to `PHYSICAL JOINT-POSSIBILITY RELATION`.
- **Status:** polarization identity is paper-proved and implemented unconditionally in
  `HTGeometry/SquareZeroCompatibilityDefect.lean`; Cartan quadrics and the stronger exceptional
  normal-selection theorem are already unconditional in
  `HTGeometry/PureSpinorColorNormalSelection.lean`. No new physics is claimed.

## Primary sources

- N. Berkovits, *Super-Poincare Covariant Quantization of the Superstring*,
  <https://arxiv.org/abs/hep-th/0001035>.
- R. Eager, I. Saberi, and J. Walcher, *Nilpotence Varieties*,
  <https://arxiv.org/abs/1807.03766>.
- R. Eager, F. Hahner, I. Saberi, and B. R. Williams, *Perspectives on the Pure Spinor
  Superfield Formalism*, <https://arxiv.org/abs/2111.01162>.
- M. Cederwall, S. Jonsson, J. Palmkvist, and I. Saberi, *Canonical Supermultiplets and Their
  Koszul Duals*, <https://arxiv.org/abs/2304.01258>.
- F. Hahner, S. Noja, I. Saberi, and J. Walcher, *Six-dimensional Supermultiplets from Bundles on
  Projective Spaces*, <https://arxiv.org/abs/2206.08388>.

## Gates

- [x] proposed physical identification stated
- [x] source categories separated
- [x] circular spacetime input exposed
- [x] exceptional physical-interpretation warning audited
- [x] strongest exact positive survivor extracted
- [x] polarization survivor formalized in Lean
- [x] physical route retired after formal audit

## Log

- 2026-07-29 — rejected before conjecture freeze. Retained only the exact polarized
  square-zero-compatibility defect as a standard algebraic bridge.
