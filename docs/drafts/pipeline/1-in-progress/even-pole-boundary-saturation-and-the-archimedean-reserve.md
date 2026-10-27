# Even-pole boundary saturation and the archimedean reserve

- **ID:** even-pole-boundary-saturation-and-the-archimedean-reserve
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-2610/hard-obstacles-summary.md, B3.18
- **Statement:** A completed positive system of positive archimedean degree cannot spend its entire pole budget on nonreal boundary zeros.

## Exact conjecture

For every `CompletedPositiveSystem κ d F Λ` and every finite set Z of positive
real heights, conjecture

`2 * Σ(t ∈ Z) ord_(1+it)(Λ) < κ`.

The pole budget is positive by the existing `5*d < 9*κ` law and `d ≥ 1`.
At odd κ this has the same integral capacity as the proved weak inequality;
at even κ it excludes saturation. This concerns the exact boundary, not a
uniform finite-height collar. No improved collar width is conjectured here.

A structural resolution would identify the reserve required by the positive
archimedean degree, or construct and classify genuine equality examples.
No significance credit is assigned to an isolated numerical improvement.
Accepted significant contributions remain 0 / 250.

## Established sources and exact scope

- `SBWF.SharpHalfPoleCollar.two_mul_sum_order_collar_zeros_le_poleOrder`
  proves the weak bound, with a finite-height collar.
- `SBWF.CollectivePoleRepulsion.exists_completedPositiveSystem_boundary_zeros_at_half_pole`
  constructs r prescribed boundary zeros with κ=2r+1 and d=1.
  Its actual statement does not construct κ=2r equality examples.
- `BGG.TheBoundaryCapacityOfDeformationsOfPowersOfZeta`
  proves capacity `(κ-d)/2` for positive Laplace deformations of ζ^d and for
  arithmetic members whose deficit has abscissa below 1. This is another
  thread's theorem. Its extra hypotheses are not available for the general
  completed positive system and will not be inserted into the conjecture.
- `SBWF.TheSimplePoleClassIsZeta` uses degree restriction and positive-measure
  functional-equation rigidity to classify κ=1. The completion has pure
  Γ_R(s)^d and conductor one; general conductor factors cannot be ignored.

## Current attack and unresolved input

The limiting boundary divisor is a positive-definite function with central
mass κ and negative masses at the boundary-zero ordinates. At equality its
finite-frequency model is a graph Laplacian. Thus positivity of this boundary
limit alone supplies no strictness. A proof must retain more of the original
positive Laplace measure or the Gamma functional equation.

Investigate whether the completion forces a nonzero positive reserve after
boundary extraction. Dividing by the canonical boundary factors does NOT
come with a proved positivity theorem; this is a gap, not an allowed premise.
The rational deformation class is already covered by BGG and is not a new
contribution. No dependency-closed paper proof exists yet.

## External novelty audit

Burnol, *Deux extensions de Théorèmes de Hamburger*,
https://arxiv.org/html/1106.4749v2, was read for the distributional functional-
equation mechanism. Its rigidity theorems require discrete Dirichlet support
(or finitely many lattice translates); they do not directly establish this
continuous positive-measure conjecture. No external result has been imported
as an axiom or claimed as a new theorem.

## Gates

- [x] Well-posed statement and exact existing boundary checked in Lean sources.
- [ ] General reserve mechanism, without an added comparison hypothesis.
- [ ] Complete paper proof, or counterexample with positive structural survivor.
- [ ] Exact Lean theorem, individual source check, axiom audit, umbrella import.
