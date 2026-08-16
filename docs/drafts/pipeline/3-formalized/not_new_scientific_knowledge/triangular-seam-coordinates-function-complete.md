# Triangular Seam Coordinates Are Function-Complete

- **ID:** triangular-seam-coordinates-function-complete
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / coordinate guardrail
- **Source:** `all-order-seam-jet-function-complete.md`;
  `seam-log-hankel-rh-equivalence.md`;
  `shifted-reciprocal-moments-determine-divisor.md`
- **Statement:** Any full all-order coordinate system that is triangularly
  invertible over the seam-log coefficients determines the completed even
  function up to scalar. Such a coordinate is a recoding of the object, not a
  softer source landscape.

## Setup

Let `F(w)` be an even entire function with `F(0) != 0`, and write

`F(w)=Phi(w^2)`.

Define

`L(z)=log(Phi(z)/Phi(0))=sum_{n>=1} ell_n z^n`

as a germ at `0`.

Let `(c_n)_{n>=1}` be another all-order coordinate sequence satisfying, for
each `n>=1`,

`c_n = a_n ell_n + P_n(ell_1,...,ell_{n-1})`,

where `a_n != 0` and `P_n` is a polynomial, rational expression, or locally
defined analytic expression in the previous coefficients only.

The rational/analytic case is understood on the nondegenerate locus where all
denominators or local coordinate charts used in the definition are defined.

## Theorem

The full sequence `(c_n)_{n>=1}` determines the full seam-log sequence
`(ell_n)_{n>=1}` recursively. Consequently, `(c_n)_{n>=1}` determines `F` up to
multiplication by a nonzero scalar and therefore determines its zero divisor
with multiplicity.

## Proof

At `n=1`,

`c_1=a_1 ell_1+P_1`,

where `P_1` is a constant. Since `a_1 != 0`, `ell_1` is determined by `c_1`.

Assume `ell_1,...,ell_{n-1}` have already been recovered. Then

`P_n(ell_1,...,ell_{n-1})`

is known. The defining relation gives

`ell_n = (c_n-P_n(ell_1,...,ell_{n-1}))/a_n`.

Thus induction recovers every `ell_n`.

By `all-order-seam-jet-function-complete.md`, the recovered seam-log jet
determines `Phi/Phi(0)` by formal exponentiation and then determines the entire
function `F` up to scalar by the identity theorem. Scalar multiplication does
not change the zero divisor.

## Consequence For The RH Landscape Route

This theorem catches a broad coordinate failure mode. If a proposed source
coordinate is a full all-order triangular recoding of the seam-log jet or of the
shifted tower, then receiving that coordinate is still receiving a
function-complete object.

This applies, on their nondegenerate invertible loci, to any proposed use of
full continued-fraction parameters, Jacobi/orthogonal-polynomial recurrence
coefficients, cumulant-to-moment coordinates, Hankel-ratio coordinates, or
Pade-style tables when the coordinate map reconstructs the underlying germ or
moment sequence.

Such coordinates can be excellent gauges for analysis. They do not by
themselves produce a non-mirror proof. A non-mirror proof must show that
Euler/Gamma/functional-equation data force the coordinate to satisfy a
positivity, index, or rigidity condition before the coordinate is inverted back
to the completed function or zero divisor.

## Split With Finite Prefixes

Finite prefixes of these coordinate systems are weak: existing finite-prefix
cards show that finite seam jets, finite linear probes, finite Markov prefixes,
and fixed-rank Hankel tests cannot select RH.

The full infinite coordinate string is the opposite danger: it is strong enough
to reconstruct the object. Therefore it is not a gentler landscape source unless
its defining constraints are independently produced from source structure.

## Novelty Status

The mathematical mechanism is elementary recursive inversion plus the identity
theorem. This card does not claim a new analytic theorem.

Its significance is route hygiene. It prevents a coordinate change from being
mistaken for new information merely because the new coordinate is sharper,
sparser, more stable, or more natural for computation.

## Theatre Test

For any proof using an all-order transformed coordinate:

1. Can the full coordinate sequence recursively recover the seam-log jet or the
   shifted reciprocal tower?
2. Does the proof receive that full coordinate before proving the source
   positivity/index theorem?
3. If yes, the proof has received function-complete data.
4. What source theorem, independent of zero localization and equivalent
   positivity predicates, forces the required sign or rigidity in this
   coordinate?

## Gates

- [x] 0 -> 1 in-progress: triangular all-order coordinate risk isolated.
- [x] 1 -> 2 fully-proven: recursive inversion and function-completeness proof
  written.
- [x] 2 -> 3 formalized: `RHTower/SeamJetFunctionComplete.lean`.

## Log

- 2026-06-24 -- Codex: created under the active RH continuation. Entropy draw:
  seed `2368594852583575042`, method `split`, analogies `lens-grinding` and
  `error-correcting-codes`. The split is finite-prefix weakness versus
  all-order function-completeness; the coordinate string is a lens, not an
  independent correcting code.

## 2026-08-16 Lean closure

`RHTower/SeamJetFunctionComplete.lean` proves the card unconditionally.

`seamLogCoeff L n = (n!)^(-1) * iteratedDeriv n L 0` is the coefficient `ell_n` of the seam-log
germ.

- `triangular_determines` is the card's recursion lemma in full generality: if
  `c_n = a_n ell_n + P_n(ell_1, ..., ell_(n-1))` with `a_n != 0` and `P_n` an arbitrary function of
  the strictly earlier coefficients, then the sequence `(c_n)` determines `(ell_n)`.  The proof is
  strong induction: the `P_n` terms agree by the induction hypothesis, and `a_n != 0` cancels.
  `P_n` is an arbitrary function `(Fin n -> C) -> C`, which covers the card's polynomial, rational
  and locally analytic cases at once, with no nondegeneracy caveat needed.
- `triangularSeam_function_complete`: consequently the sequence `(c_n)` determines the function up
  to its central scalar, `Phi_1 = (Phi_1(0)/Phi_2(0)) Phi_2`, and
  `triangularSeam_zero_set_eq` gives the zero divisor.

The reference to formal power series exponentiation is replaced by the analytic route already used
for the all-order seam jet: equal coefficients give equal germs
(`eventuallyEq_of_iteratedDeriv_eq`), and `exp L_1 = exp L_2` near the origin plus the identity
theorem give the proportionality.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
