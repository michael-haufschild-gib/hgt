# Prime Euler--Hadamard nodal scalar-unit universality law

- **ID:** prime-euler-hadamard-nodal-scalar-unit-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Whole-corpus theorem-generated closure of `TailHadamardReducedProduct`,
  `PrimeEulerOrientationNorm`, and `PrimeEulerNodalPhaseBarrierLaw`
- **Statement:** For two Boolean prime orientations, same-sheet finite Euler gauge is exactly
  Hadamard product `1`, opposite-sheet Euler norm complementarity is exactly Hadamard product
  `-1`, and every continuous positive-weight residue deformation has infinite nodal support when
  its endpoint product is neither scalar unit.

## Goal

Identify nonlinear Euler lifting modes intrinsically inside coefficient-tail algebra, then express
nodal phase separation as escape from its complete two-point scalar-unit locus. This is a
cross-folder closure: HTGeometry supplies reduced-product algebra and projective nodal rigidity;
RHTower supplies exact Euler lift classification.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4  publication-ready: post-proof collision audit found no exact literature match

## Approach

Write each orientation as its Boolean sign stream in the Hadamard reduced product. Product
equality with a constant stream is equality outside a finite coordinate set.

## Paper proof

**[PROVED HERE]** Let `q_epsilon` and `q_delta` be the two reduced-product sign classes. By
compatibility of quotient multiplication with coordinatewise multiplication,
`q_epsilon q_delta` is represented by
`p ↦ sign(epsilon p) sign(delta p)`.

At every coordinate, Boolean case analysis gives

`sign(epsilon p) sign(delta p) = 1` iff `epsilon p = delta p`,

and

`sign(epsilon p) sign(delta p) = -1` iff `epsilon p ≠ delta p`.

Equality in the reduced product is equality away from a finite set. Hence `q_epsilon q_delta = 1`
iff the orientations are eventually equal, which the existing exact Euler theorem identifies with
same-sheet finite-gauge equivalence. Likewise `q_epsilon q_delta = -1` iff they are eventually
opposite, exactly the cyclotomic-norm-complementary Euler mode.

If the product is neither `1` nor `-1`, neither Euler mode holds by the two equivalences. Existing
prime Euler nodal phase-barrier law then makes nodal support infinite for every continuous
positive-weight residue deformation joining the endpoints. This proves completeness of the two
scalar units and its nodal consequence. ∎

## Strict gain over corpus endpoints

The Hadamard endpoint proved only one-orientation involution and positivity. The Euler endpoint
classified two lift modes through eventual equality/opposition. The nodal endpoint used absence of
those modes as a hypothesis. Their closure supplies one intrinsic algebraic observable—the endpoint
Hadamard product—whose complete scalar spectrum both classifies the Euler modes and triggers the
nodal barrier.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PrimeEulerHadamardNodalScalarUnitUniversalityLaw`
- Main theorem:
  `primeEulerHadamardNodal_completeScalarUnitUniversality`
- Supporting exact classifiers:
  `primeOrientationHadamardTail_mul_eq_one_iff_eulerGauge` and
  `primeOrientationHadamardTail_mul_eq_neg_one_iff_eulerNorm`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/PrimeEulerHadamardNodalScalarUnitUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for Boolean prime orientations, Euler tail gauge, Hadamard reduced products, cyclotomic norm
complementarity, and infinite nodal deformation found no exact collision. Closest inspected primary
sources cover separate mechanisms:

- M. Righetti, *Zeros of combinations of Euler products for sigma > 1*,
  <https://arxiv.org/abs/1412.6331>, proves analytic zero theorems for polynomial combinations of
  orthogonal Euler products and uses unimodular prime twists; it does not classify finite-defect
  Boolean orientation products in a Hadamard quotient or connect them to coordinatewise nodal
  deformation.
- A. Logunov and E. Malinnikova, *Nodal sets of Laplace eigenfunctions: estimates of the Hausdorff
  measure in dimension two and three*, <https://arxiv.org/abs/1605.02595>, concerns geometric nodal
  measure of eigenfunctions, not tail orientation phase changes or Euler lifting modes.
- A 2025 manuscript on Witt--Hadamard Euler-product calculus,
  <https://arxiv.org/abs/2509.25038>, is withdrawn and explicitly reports errors in major results;
  its abstract concerns Dold congruences and norm descent, not the scalar-unit/nodal classifier here.

## Log

- 2026-07-23 — generated from exact shared symbol `primeDirichletRealSign`; corpus search found
  separate Hadamard involution, Euler two-mode, and nodal barrier theorems but no scalar-product
  classifier joining them.
- 2026-07-23 — dependency-closed paper proof completed.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
