# Degree-five Gaussian eventual strictness law

- **ID:** degree-five-gaussian-eventual-strict-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), hostile literature audit passed with close flat-kernel prior art
- **Source:** Bottom-up closure of Gaussian Fock positivity, unisolvent coefficient congruence,
  inverse degree scaling, and degree-five collision determinant survival
- **Statement:** Every degree-five collision value matrix is PSD; an unisolvent dimension-sixteen
  packet is eventually positive definite, with positive determinant, at small nonzero scale in
  both raw Gaussian and singularly normalized degree coordinates.

## Goal

Join two previously separate HilbertMetric mechanisms.  The collision-curvature module proves
eventual determinant nonvanishing but does not order the matrix; generic Gaussian Fock theory
orders the same matrix but is not connected to the collision coordinates.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes scratch `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `hilbertExponentialInnerMatrix_posSemidef` gives universal exponential Fock-Gram PSD.
2. `degreeFiveGaussianValueMatrix` is the Fock Gram of the explicit collision points at bandwidth
   `1/2`.
3. `eventually_ne_degreeFiveSixteen_gaussianValueMatrix_det` gives determinant survival from the
   unisolvent degree-five normalized limit.
4. `degreeFiveRecombinedValueMatrix_eq_congr` and
   `degreeFiveNormalizedValueMatrix_eq_scale_recombined` identify recombination and nonzero degree
   scaling as two further Gram congruences.

## Paper proof

For every scale `e`, write the collision point packet as vectors `x_i` in the finite Euclidean
space indexed by lower and top degree features.  Its value matrix has entries
`exp(⟨x_i,x_j⟩)`, the exponential Fock kernel at bandwidth `1/2`; hence it is positive
semidefinite.  The degree-five unisolvent limit theorem independently proves that its determinant
is nonzero throughout a punctured neighborhood of `e=0`.  On that neighborhood PSD plus
nonsingularity gives positive definiteness, and its determinant is strictly positive.
Arbitrary coefficient recombination preserves PSD.  At every nonzero scale, inverse degree scaling
is a second congruence, so the normalized matrix is PSD as well.  Its independently proved
eventual nonzero determinant therefore upgrades the normalized coordinates to the same eventual
positive-definite and positive-determinant conclusion.
`[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/HilbertMetric/DegreeFiveGaussianEventualStrictLaw.lean`
- Capstone: `eventually_degreeFiveSixteen_gaussianValueMatrix_posDef`
- Determinant: `eventually_det_degreeFiveSixteen_gaussianValueMatrix_pos`
- Normalized capstone: `eventually_degreeFiveSixteen_normalizedValueMatrix_posDef`
- Normalized determinant: `eventually_det_degreeFiveSixteen_normalizedValueMatrix_pos`

## Hostile literature audit

Searches on 2026-07-21 included `"degree-five" Gaussian collision Gram positive definite
curvature`, `graded monomial unisolvent Gaussian collision determinant curvature`, `exponential
inner product kernel collision scale positive definite Gram`, and `Gaussian Gram degree five
collision log determinant curvature`.  Nearest result is materially close but not identical:

- [Karvonen--Särkkä, *Worst-case optimal approximation with increasingly flat Gaussian
  kernels*](https://arxiv.org/abs/1906.02096) proves convergence toward polynomial methods for
  fixed unisolvent points in the flat Gaussian limit.  It does not use the moving graded collision
  packet, degree-five normalization, balanced top-degree amplitude, or the dimension-sixteen
  collision determinant proved here.
- [Guella--Menegatto, *Strictly positive definite kernels on a product of
  spheres*](https://arxiv.org/abs/1505.03695) studies general strict kernel positivity in a
  different geometry.
- [Jorgensen--Tian, *Positive Definite Kernels, Algorithms, Frames, and
  Approximations*](https://arxiv.org/abs/2104.11807) treats broad RKHS factorization and finite
  approximations, not graded collision asymptotics.

Generic exponential/Gaussian Fock positivity and flat-kernel unisolvence are prior art.  No source
found the exact law joining the corpus's moving degree-five collision construction and its
unisolvent determinant survival to strict positivity on a punctured scale neighborhood.  Verdict:
`NO EXACT COLLISION FOUND`, with the flat-Gaussian paper recorded as closest adjacent result.
`[NOVELTY AUDIT PASSED]`

## Log

- 2026-07-21 — Found by cross-family search for eventual determinant survival lacking PSD closure.
- 2026-07-21 — Scratch proof passed exactly with `lake env lean`.
- 2026-07-21 — Direct tree check passed exactly:
  `lake env lean GaloisForLFunctions/HilbertMetric/DegreeFiveGaussianEventualStrictLaw.lean`.
- 2026-07-21 — Hostile audit found close flat-Gaussian/unisolvent prior art but no degree-five
  moving-collision strictness theorem.
- 2026-07-21 — Post-law HilbertMetric rescan closed the maximal coordinate statement: coefficient
  recombination and inverse degree scaling preserve PSD, so eventual strictness also holds for the
  normalized matrix. Direct tree check passed after the extension.
