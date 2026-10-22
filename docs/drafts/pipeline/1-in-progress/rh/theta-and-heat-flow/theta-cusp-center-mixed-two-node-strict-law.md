# Theta-cusp center-mixed strict two-node law

- **ID:** theta-cusp-center-mixed-two-node-strict-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), hostile literature audit passed
- **Source:** Bottom-up closure of theta log-concavity, radial strictness, parity, and Bochner PSD
- **Statement:** Positive critical aperture and nonzero displacement force strict positive
  definiteness, and positive determinant, of the actual center-mixed two-node theta matrix.

## Goal

Upgrade the existing global two-node PSD endpoint to its exact interior law.  The proof must cover
both signs of displacement and expose the collision `t = 0` as the only rank-loss boundary.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes scratch `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `thetaCuspCenterMixedTwoNodeMatrix_posSemidef` gives unconditional PSD for `0 ≤ a < 1/2`.
2. `thetaCuspCenterMixedDensity_lt_zero` gives strict radial decay at positive displacement.
3. `thetaCuspCenterMixedDensity_even` transports strictness to negative displacement.
4. `thetaCuspCenterMixedDensity_pos` and nonnegativity order the explicit two-by-two determinant.

## Paper proof

Write `d = F_a(0)` and `o = F_a(t)`.  Positive aperture gives `d > 0` and `o ≥ 0`.  For `t > 0`,
strict radial decay gives `o < d`; for `t < 0`, evenness reduces to `-t > 0`.  Thus whenever
`t ≠ 0`, `(d-o)(d+o) > 0`, which is the determinant `d²-o²` of the symmetric two-node matrix.
The same matrix is already positive semidefinite, so its nonzero determinant makes it positive
definite. `[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedTwoNodeStrictLaw.lean`
- Capstone: `thetaCuspCenterMixedTwoNodeMatrix_posDef`
- Determinant: `det_thetaCuspCenterMixedTwoNodeMatrix_pos`

## Hostile literature audit

Searches on 2026-07-21 included `Hedenmalm theta kernel center mixed density two point positive
definite`, `theta cusp center mixed density strict log concavity Bochner matrix`, `Hedenmalm
Fourier positivity theta source log concavity two node`, and `"center-mixed" theta density
Hedenmalm`.  No exact terminology or construction appeared.  Nearest literature covers general
ingredients only:

- [Raufi, *Log concavity for matrix-valued functions and a matrix-valued Prékopa
  theorem*](https://arxiv.org/abs/1311.7343) develops preservation of log-concavity under
  integration in a broad setting.
- [Mu, *Log-concavity of a mixture of beta distributions*](https://arxiv.org/abs/1312.2166)
  records the standard fixed-sum/product interpretation of log-concavity for an unrelated family.
- [Barbosa--Menegatto, *Strictly positive definite kernels on two-point compact homogeneous
  spaces*](https://arxiv.org/abs/1505.00591) treats abstract strict two-point kernel positivity on
  different spaces.

No source found the actual theta-cusp source, its Hedenmalm center mixture, strict radial decay
obtained after mixing, or the sharp `t = 0`/`t ≠ 0` Bochner rank boundary.  Verdict:
`NO COLLISION FOUND`; generic log-concavity and two-by-two determinant algebra are prior art, the
specific universal theta-density law is not. `[NOVELTY AUDIT PASSED]`

## Log

- 2026-07-21 — Found during complete PSD-family closure audit.
- 2026-07-21 — Scratch proof passed exactly with `lake env lean`.
- 2026-07-21 — Direct tree check passed exactly:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedTwoNodeStrictLaw.lean`.
- 2026-07-21 — Hostile literature audit found no exact theta-cusp center-mixed strictness law.
