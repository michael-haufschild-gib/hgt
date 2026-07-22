# Von Mangoldt Hardy eventual strictness law

- **ID:** von-mangoldt-hardy-eventual-strict-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), hostile literature audit passed
- **Source:** Bottom-up closure of positive source Grams and Hardy-boundary determinant survival
- **Statement:** Every finite packet of distinct right-half-plane nodes has an eventually positive
  definite scaled von Mangoldt source Gram, with strictly positive determinant, at scale `t → 0+`.

## Goal

Close the gap between two existing statements that were never joined: all positive-scale
approximants are positive semidefinite, while distinct packets are eventually nonsingular under
Hardy residue scaling.  The conjunction rules out every residual null direction and yields strict
source geometry near the boundary.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes scratch `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `scaledVonMangoldtPrimeRightHalfPlaneGram_posSemidef` gives PSD for every `t > 0`.
2. `eventually_det_scaledVonMangoldtPrimeRightHalfPlaneGram_ne_zero` gives eventual
   nonsingularity for injective positive-node packets.
3. `Matrix.PosSemidef.posDef_iff_det_ne_zero` turns PSD plus nonsingularity into positive
   definiteness; `Matrix.PosDef.det_pos` orders the determinant strictly.

## Paper proof

Fix a finite injective packet `w` in the open right half-plane.  On the punctured positive
neighborhood of zero, every scale satisfies `t > 0`, so its scaled arithmetic Gram is positive
semidefinite.  Independently, convergence to the nonsingular Cauchy/Hardy Gram makes its
determinant nonzero eventually.  Intersect these two eventual sets.  A finite Hermitian PSD matrix
with nonzero determinant has no zero eigenvalue, hence every eigenvalue is positive and the matrix
is positive definite.  Its determinant, the product of positive eigenvalues, is strictly positive.
`[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/RHTower/VonMangoldtHardyEventualStrictLaw.lean`
- Capstone: `eventually_scaledVonMangoldtPrimeRightHalfPlaneGram_posDef`
- Determinant: `eventually_det_scaledVonMangoldtPrimeRightHalfPlaneGram_pos`

## Hostile literature audit

Searches on 2026-07-21 included `"scaled von Mangoldt" Gram positive definite Hardy`,
`"von Mangoldt" "Cauchy Gram" positive definite`, `"von Mangoldt source Gram" determinant`,
`zeta logarithmic derivative residue Cauchy kernel positive definite Gram scaling`, and
`Hardy space reproducing kernel Gram strictly positive definite distinct points`.  Nearest work
separates into unrelated component literatures:

- [Lester, *The distribution of the logarithmic derivative of the Riemann
  zeta-function*](https://arxiv.org/abs/1308.3597) studies value distribution of `ζ'/ζ`, not finite
  arithmetic Gram strictness.
- [Chirre, *Bounding the log-derivative of the zeta-function*](https://doi.org/10.1007/s00209-021-02820-9)
  gives analytic bounds for `ζ'/ζ`, not a positive-kernel scaling law.
- [Barbosa--Menegatto, *Strictly positive definite kernels on two-point compact homogeneous
  spaces*](https://arxiv.org/abs/1505.00591) treats abstract strict kernel positivity on a
  different domain.
- [Zhang--Qi--Zhou, *Positive definiteness and semi-definiteness of even order symmetric Cauchy
  tensors*](https://doi.org/10.3934/jimo.2015.11.1263) treats Cauchy tensor definiteness, not von
  Mangoldt source limits.

No result found the exact conjunction: an unconditional von Mangoldt Dirichlet-source Gram,
positive-scale PSD, residue convergence at the zeta pole to the right-half-plane Hardy kernel, and
eventual strict positivity for every finite distinct packet.  Verdict: `NO COLLISION FOUND`;
individual analytic and matrix facts are classical, arithmetic boundary strictness law is not.
`[NOVELTY AUDIT PASSED]`

## Log

- 2026-07-21 — Found during complete PSD-family closure audit.
- 2026-07-21 — Scratch proof passed exactly with `lake env lean`.
- 2026-07-21 — Direct tree check passed exactly:
  `lake env lean GaloisForLFunctions/RHTower/VonMangoldtHardyEventualStrictLaw.lean`.
- 2026-07-21 — Hostile literature audit found no exact arithmetic Hardy-Gram strictness theorem.
