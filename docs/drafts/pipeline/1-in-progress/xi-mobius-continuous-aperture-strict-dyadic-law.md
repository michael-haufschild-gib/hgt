# Xi Möbius continuous-aperture strict dyadic law

- **ID:** xi-mobius-continuous-aperture-strict-dyadic-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), hostile literature audit passed
- **Source:** Bottom-up closure of explicit dyadic innovation features and true-aperture
  Vandermonde separation
- **Statement:** Every positive dyadic mesh refinement has a completed all-prime innovation Gram
  that is positive definite, with positive determinant, on finite distinct positive apertures.

## Goal

Upgrade the existing positive-semidefinite Loewner increment.  The explicit innovation features
are geometric depth sequences.  Their first `N` coordinates form a weighted Vandermonde at any one
prime, so no nonzero finite aperture combination can vanish in the full direct-sum feature space.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact strictness hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes scratch `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `xiMobiusPrimeContinuousApertureDyadicInnovationFeature` is an explicit nonzero weight times
   powers of a squared disk node.
2. `xiMobiusContinuousApertureDiskNode_injective`, positivity, and the `<1` bound separate distinct
   positive aperture nodes.
3. `xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero` exposes the neighboring weighted
   Vandermonde mechanism; the new proof performs the exact squared-node innovation factorization.
4. The one-prime and all-prime inner-product identities identify the closed innovation kernels
   with genuine `ell²` Gram matrices.

## Paper proof

For prime `p`, put `r_j=exp(-(h/2)a_j log p)`.  The innovation feature at depth `e` is
`d_j(r_j²)^e`, where `d_j=(q/(1+q))(1-r_j)²` is nonzero.  Positive `h,a_j` give
`0<r_j<1`; injective apertures give distinct `r_j²`.  The first `N` feature coordinates therefore
form `V(r_j²)^T diag(d_j)`, an invertible matrix.  Hence the one-prime `ell²` feature packet is
linearly independent and its Gram is positive definite.  Restriction of the all-prime direct sum
to `p=2` preserves that independence, so the completed innovation Gram is also positive definite
and has positive determinant. `[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/RHTower/XiMobiusContinuousApertureStrictDyadicLaw.lean`
- Capstone: `xiMobiusContinuousApertureDyadicInnovationGram_posDef`
- Determinant: `det_xiMobiusContinuousApertureDyadicInnovationGram_pos`

## Hostile literature audit

Searches on 2026-07-21 used both structural and exact-project language:
`"dyadic innovation" Szegő kernel positive definite Gram`,
`Szegő kernel Loewner increment strict positive definite refinement`,
`geometric sequence features weighted Vandermonde positive definite kernel`,
`"continuous aperture" Möbius prime kernel`, and
`"dyadic innovation Gram"`.  Nearest results cover the separate classical ingredients:

- [Bai, *A Class of Weighted Low Rank Approximation of the Positive Semidefinite Hankel
  Matrix*](https://doi.org/10.1155/2015/937573) uses Vandermonde representations of PSD Hankel
  matrices.
- [Guella--Menegatto, *Strictly positive definite kernels on a product of
  spheres*](https://arxiv.org/abs/1505.03695) characterizes strict kernel positivity in a different
  geometric setting.
- [Bolotnikov--Heinig, *Confluent Cauchy and Cauchy--Vandermonde
  matrices*](https://doi.org/10.1016/S0024-3795(96)00200-5) treats the classical structured-matrix
  mechanism.

No source found the conjunction proved here: the Möbius prime continuous-aperture kernel, its
positive dyadic Loewner innovation, the explicit squared disk-node feature factorization, and
strict all-prime Gram positivity obtained by restriction to one prime.  Search hits for the phrase
“continuous aperture” concerned antenna systems and were mathematically unrelated.  Verdict:
`NO COLLISION FOUND`; standard Vandermonde strictness is prior art, project-specific universal law
is not. `[NOVELTY AUDIT PASSED]`

## Log

- 2026-07-21 — Found in complete audit of PSD-specific RHTower closures.
- 2026-07-21 — Scratch proof passed exactly.
- 2026-07-21 — Direct tree check passed exactly:
  `lake env lean GaloisForLFunctions/RHTower/XiMobiusContinuousApertureStrictDyadicLaw.lean`.
- 2026-07-21 — Hostile literature audit found standard component mechanisms but no exact law.
