# Exact radial/logarithmic Jacobian for Hecke Mellin unfolding

- **ID:** hecke-radial-logarithmic-jacobian
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke theta Mellin unfolding](hecke-theta-mellin-continuation-and-unit-unfolding.md)
- **Statement:** Identify the exact Haar-measure change from the radial logarithm and weighted unit-log coordinates to independent archimedean logarithms.

Let `m_v` be the actual archimedean multiplicities, `n=Σ_v m_v=[K:ℚ]`,
and `P` the proved weighted-zero profile completion. The map is
`(q,l) ↦ (q-P(l)_v)_v`. Its absolute Jacobian should be
`n/(∏_v m_v)=n/2^r₂`. Consequently `dt/t dl`, with `q=log(t)/2`, becomes
`2^(r₂+1)/n` times independent archimedean logarithmic measure.

## Existing source and direct matrix route

Mathlib's `NormLeOne.completeBasis` has absolute determinant
`n*regulator`; its `expMapBasis` derivative and nonnegative change-of-variables
theorem are source-inspected. They provide an alternative through actual
fundamental-unit coordinates, but require a further basis-coordinate measure
change to cancel the regulator.

A direct map on the full place-coordinate space may be shorter. Store `q`
at the distinguished place and the weighted unit-log coordinates elsewhere.
The inverse of the displayed map sends `z` to
`q=(Σ_v m_v z_v)/n`, and, off the distinguished place,
`l_v=m_v*(q-z_v)`. After factoring the diagonal multiplicity matrix, its
matrix is a diagonal matrix with distinguished entry zero and other entries
`-1`, plus a rank-one matrix. Its determinant is
`(-1)^(#places-1)*(∏_v m_v)/n`. This is a proposed calculation, not yet a
Lean result. Search the corpus first for the diagonal/rank-one determinant
formula, then Mathlib. Do not reprove a general determinant lemma if available.

The final proof must also identify the product measure from splitting off
the distinguished coordinate, prove the actual map's inverse, and combine
this linear change with `t=exp(2q)`. The degree and multiplicities are actual
number-field data, not free analytic hypotheses. No Lean source yet.

## Exact corpus determinant input found

`HTGeometry/BorisovGabberVasiuDeterminant.lean` is source-inspected and
contains exactly the required singular diagonal/rank-one formula:

`bgv_det_diagonal_add_vecMulVec a u v`:
`det(diagonal a + vecMulVec u v) = (∏ i,a_i) +
 Σ i,u_i*v_i*(∏ j≠i,a_j)`.

It imports only Mathlib matrix adjugates and multilinear algebra, and its
proof expands the alternating determinant and eliminates every term using
two proportional rows. Reuse this declaration directly. The broad
archimedean determinant framework and the heavier finite monomial-chart
file are unnecessary for this direct calculation. The future consumer must
audit its transitive dependencies together with the specialized Jacobian.

Further corpus source leads:

- `numberFieldWeightedPlaceMean` already exists in
  `NumberFieldDetOneUnitWeightBalancing.lean`, as weighted sum divided by
  total place multiplicity. `NumberFieldArchimedeanBalancedMean.lean` proves
  its additive, scalar, and constant-profile identities. Avoid introducing a
  second named weighted-mean definition.
- `PauliCommutatorFullEnsembleLowerTail.lean` splits arbitrary finite
  coordinate families using `MeasurableEquiv.piCongrLeft` and
  `MeasurableEquiv.sumPiEquivProdPi`; its measure-preserving proof uses
  `measurePreserving_piCongrLeft` and
  `measurePreserving_sumPiEquivProdPi`. Those general Mathlib mechanisms
  apply to Lebesgue measures as well as its Gaussian measures. A direct
  distinguished-coordinate splitting theorem is being searched first.

Mathlib source checks found `Equiv.piSplitAt` (explicit distinguished
coordinate and complement), `Homeomorph.piSplitAt`, and
`volume_preserving_piEquivPiSubtypeProd`. The latter splits by the predicate
`v=w₀`; collapse its singleton-coordinate factor using the standard
one-coordinate product equivalence. `MeasureTheory/Constructions/Pi.lean`
also contains the general coordinate-reindexing measure-preserving theorem.
No direct `measurePreserving_piSplitAt` declaration was found in the searches.

## Gamma convention checked

Mathlib `Analysis/SpecialFunctions/Gamma/Deligne.lean` defines
`Gammaℂ(s)=2*(2*pi)^(-s)*Gamma(s)` and
`Gammaℝ(s)=pi^(-s/2)*Gamma(s/2)`. Thus, using Mathlib's standard factors, the
proposed full unfolding scalar is
`torsionOrder K / ([K:ℚ] * 2^(Units.rank K))`.
Equivalently it is `torsionOrder * 2^(1-r₁-r₂)/[K:ℚ]`.
The earlier `torsionOrder * 2^(1-r₁)/[K:ℚ]` applies only to the convention
that omits the factor two at each complex place. This scalar remains a
formalization target; the source check fixes its intended convention.

## Linear-map implementation plan

Work first on the full place-coordinate space to use `LinearMap.det` for an
endomorphism. For an input `x`, put `q=x(w₀)` and
`l=(x(v))_{v≠w₀}`, and define `E(x)=q-P(l)`. The inverse is the mean/weighted
difference map above. A short completion lemma suffices for the inverse:
if `Σ_v m_v*y_v=0`, then `P((m_v*y_v)_{v≠w₀})=y`. At retained places this
is cancellation by `m_v≠0`; at the omitted place split the weighted-zero sum.
Apply it to the negative centered profile. The weighted mean of `P(l)` is
zero, so the opposite inverse identity is direct.

The inverse matrix can be written without a matrix product:
`diagonal d + vecMulVec u m`, where
`d(w₀)=0`, `d(v)=-m_v` otherwise,
`u(w₀)=1/n`, and `u(v)=m_v/n` otherwise.
The diagonal product vanishes. In the rank-one determinant sum every term
except `w₀` contains the zero distinguished diagonal entry. The surviving
term is `(m_w₀/n)*∏_{v≠w₀}(-m_v)`, giving
`(-1)^rank * (∏_v m_v)/n`. This specializes the existing corpus determinant
lemma directly and avoids a new generic determinant proof.

## Active formalization

`/tmp/HeckeRadialLogJacobianScratch.lean` now constructs the full-place
linear equivalence and its inverse, specializes the existing diagonal plus
rank-one determinant formula, and targets the exact measure pushforward
factor `2^r₂/[K:ℚ]`. This is still a scratch construction, not a certified
result. The first check exposed expensive elaboration of the forward
linear-map laws; that map is now built directly from coordinate projections,
linear subtraction, and the existing profile-completion linear map.
No proof limit was raised.

The exact product identity for multiplicities follows from Mathlib's
`InfinitePlace.prod_eq_prod_mul_prod`, `mult_isReal`, and `mult_isComplex`.
The coordinate split can use `Homeomorph.funSplitAt` plus the already
source-checked `volume_preserving_piEquivPiSubtypeProd` and
`volume_preserving_funUnique` to prove its measure-preserving property.

The linear equivalence, inverse matrix, exact absolute determinant, and
full-place Lebesgue pushforward now pass Lean with standard-only transitive
axioms. The remaining check concerns the distinguished-coordinate product
split and its integral/integrability corollaries. Introducing a `Unique`
instance for the distinguished singleton changes the inferred `Fintype`
instance inside product measures, so that instance is now fixed before the
singleton equivalence is used. No measure equality is assumed.

A corpus lookup found `numberFieldInfinitePlaceWeight_eq_finrank` already in
`NumberFieldArchimedeanCanonicalDeterminant.lean`. Its existing theorem is
now imported and reused; the duplicate scratch declaration was removed.
The next Gamma calculation has its own active card:
`hecke-archimedean-mellin-integrals.md`.
