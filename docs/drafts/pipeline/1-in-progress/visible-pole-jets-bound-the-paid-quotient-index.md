# Visible pole jets bound the paid quotient index

- **ID:** visible-pole-jets-bound-the-paid-quotient-index
- **Stage:** 1-in-progress
- **Type:** LEAN VERIFICATION (canonical import checks pending)
- **Parent:** [Q-III](q-iii-escape-state-classification.md)
- **Statement:** The actual paid-ideal quotient has rank at least the sum of
  visible translated zero orders over any finite set of distinct interior
  points, with critical-boundary visible points contributing at least one.

## Corpus inputs

The verified strict-interior order theorem makes every paid kernel's jets
vanish below the visible translated order. Existing
`TheMoebiusReceiverCountsItsOffLineZeros` gives the corresponding distinct
point count without multiplicity. `DeningerJetInterpolation` and
`DeningerArithmeticFiniteJetInterpolation` supply polynomial finite-Hermite
mechanisms. No existing paid-Wiener finite-jet index theorem surfaced.

## Interpolation mechanism

Joint jet evaluation onto the finite jet target is constructed from the full
critical Wiener algebra; surjectivity is not a theorem hypothesis.
A proposed finite-polynomial route chooses a Dirichlet polynomial a(s) separating all
selected points with a'(s) nonzero at each, avoiding finitely many linear
conditions on coefficients. Polynomial Hermite interpolation in a(s) then
recovers arbitrary jets by its invertible triangular chain-rule matrix.
A single integer base can also work if its exponentials separate the points;
that separation must be constructed, not assumed. Finite-polynomial witnesses
were a proposed refinement, not an established finding. The exact construction
below proves full-Wiener interpolation, which suffices for the paid-index bound.

The paid ideal lies in the evaluation kernel, so quotient rank bounds follow.
The arithmetic vanishing inputs are the checked order and endpoint theorems.

## Scope

This is the paid ideal P, not the actual limiting-module annihilator I.
P subset I does not transfer a lower index bound to W/I. Do not identify
these quotient multiplicities or infer occurrence of every visible zero
in every actual cofactor module. Unit-orbit invariance transfers any proved
paid-index bound to Liouville and finite Euler-factor variants.

## Lean implementation route and endpoint value count

The inspected `DeningerJetInterpolation` suggests a direct mask construction,
without a single global separating coordinate. For each target i, choose
pairwise separating Wiener factors vanishing at each other point j but not
i, and raise them to the required orders m_j. Their product is nonzero at i.
Multiply by successive powers of the local factor delta_2 minus its value
at i; that factor has a simple zero at i. Analytic-order calculus makes the
resulting local jet matrix triangular with nonzero diagonal, while every
other target jet vanishes. `deningerTriangular_solvable` then supplies all
coefficients.

Additional value selectors are multiplied by masks vanishing to every
interior order. Normalizing each selector at its own point corrects the
additional values without changing any interior jet. No boundary derivative
is required. The resulting surjective linear map descends through the paid
ideal. Its finite target has dimension equal to the sum of interior orders
plus the number of boundary points. Equality of paid ideals on Wiener unit
orbits transports this bound, including the Möbius–Liouville case.

## Canonical verification

`InteriorWienerJets` passed final source-only audit `84720` with standard
axioms. The complete application check finished without errors; all fourteen
axiom reports in `/tmp/qiii-visible-mixed-jet-index-third.log` contain only
`propext`, `Classical.choice`, `Quot.sound`.

Six application modules are installed and umbrella-wired:

- `VisiblePolesImposeIndependentPaidConditions`: separated half-plane
  characters, closed-half-plane obstruction and finite visible-point count.
- `FiniteWienerJetsCanBePrescribed`:
  `exists_wiener_with_prescribed_finite_jets` and its surjectivity theorem.
- `VisiblePoleJetsBoundThePaidIndex`:
  `sum_visible_orders_le_rank_quotient_paidIdeal_moebius`.
- `InteriorJetsAndBoundaryValuesCanBePrescribed`:
  `exists_wiener_with_mixed_finite_data`.
- `VisibleInteriorAndBoundaryPolesBoundThePaidIndex`:
  `sum_visible_orders_add_boundary_card_le_paid_index`.
- `VisibleJetIndexBoundsPersistOnWienerUnitOrbits`: the corresponding
  unit-orbit and Liouville paid-index bounds.

Individual canonical import-boundary checks remain in
[the completion ledger](q-iii-existing-findings-lean-completion.md).
