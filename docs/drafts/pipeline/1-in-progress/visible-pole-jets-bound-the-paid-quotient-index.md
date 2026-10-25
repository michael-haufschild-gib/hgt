# Visible pole jets bound the paid quotient index

- **ID:** visible-pole-jets-bound-the-paid-quotient-index
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
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

## Missing bridge

Prove joint jet evaluation onto the finite jet target from the full critical
Wiener algebra. Do not add surjectivity as a theorem hypothesis.
A proposed finite-polynomial route chooses a Dirichlet polynomial a(s) separating all
selected points with a'(s) nonzero at each, avoiding finitely many linear
conditions on coefficients. Polynomial Hermite interpolation in a(s) then
recovers arbitrary jets by its invertible triangular chain-rule matrix.
A single integer base can also work if its exponentials separate the points;
that separation must be constructed, not assumed. Finite-polynomial witnesses
were a proposed refinement, not an established finding. The exact construction
below proves full-Wiener interpolation, which suffices for the paid-index bound.

After surjectivity, the paid ideal lies in the evaluation kernel and quotient
rank bounds follow. All arithmetic vanishing inputs are proved by the new
order/endpoint theorems, but the interpolation bridge remains open.

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
coefficients. This route still needs exact Lean implementation and audit.

The endpoint distinct-value consequence is drafted in
`/tmp/qiii_visible_pole_point_count_body.lean` and included in
`/tmp/qiii-visible-mixed-jet-index-check.lean`. It proves closed-half-plane
character separation, unifies strict-interior and boundary visible pole
obstructions, and bounds the paid quotient rank by their finite point count.
UNVERIFIED. This is only the value count; the multiplicity-weighted claim
above remains open until the full masked jet interpolation passes.

## Exact masked interpolation draft

The local analytic bridge and the full strict-interior masked interpolation
now have Lean drafts: `/tmp/qiii-wiener-jet-evaluation-check.lean` and
`/tmp/qiii_wiener_masked_interpolation_body.lean`. The former constructs
linear jet functionals on the full Wiener algebra and proves local product
and power order laws. The latter constructs a simple dyadic local parameter,
pairwise separation masks, triangular jet matrices, and joint surjectivity.
Both are UNVERIFIED. The base check is
`/tmp/qiii-wiener-jet-evaluation-check.lean`; the full application is
`/tmp/qiii-visible-mixed-jet-index-check.lean`. All pole dependency oleans and
their canonical audits are complete. The base jets, interpolation and index
applications still require direct Lean checks. No paper claim is complete.

The strict-interior quotient application is now drafted in
`/tmp/qiii_visible_jet_quotient_index_body.lean`. It descends the proved-to-be
surjective jet map through an arbitrary ideal imposing the jet conditions,
then applies the actual paid-kernel visible-order theorem. Its exact target
is the sum of any finite lower multiplicities of the visible orders, with
no assumed interpolation or rank bound. It is included in the unverified
`/tmp/qiii-visible-mixed-jet-index-check.lean`.

The mixed endpoint claim also has a complete draft.
`/tmp/qiii_wiener_mixed_interpolation_body.lean` constructs masks vanishing to
the interior orders while avoiding a selected additional half-plane point.
Separated boundary value interpolation then corrects values without changing
any interior jet. `/tmp/qiii_visible_mixed_jet_index_body.lean` descends that
surjection and gives the sum of visible interior multiplicities plus the
number of distinct critical-boundary poles as a paid quotient lower bound.
The complete scratch is `/tmp/qiii-visible-mixed-jet-index-check.lean`; all
new claims are UNVERIFIED, not completed by these drafts.

The exact unit-orbit and Liouville corollaries are drafted in
`/tmp/qiii_visible_jet_index_unit_orbit_body.lean` and included in the mixed
index scratch. They rewrite the already established equality of paid
ideals; no new arithmetic premise is introduced. These corollaries remain
UNVERIFIED with their interpolation and quotient-index dependencies.
