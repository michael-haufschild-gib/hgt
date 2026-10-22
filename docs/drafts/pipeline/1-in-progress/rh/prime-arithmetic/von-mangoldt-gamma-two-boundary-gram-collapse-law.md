# Von Mangoldt--Gamma two-boundary Gram collapse law

- **ID:** von-mangoldt-gamma-two-boundary-gram-collapse-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), hostile literature audit passed; no priority claim
- **Source:** Bottom-up closure across projection, affine, jet, and cofinal boundary balances
- **Statement:** Every supported balance mechanism annihilates the full canonical
  `(+1/2,-1/2)` Gram exactly; total collapse persists in the cofinal von Mangoldt limit.

## Goal

Extract the common rank law hidden behind four separately formalized two-boundary constructions.
The maximal statement must identify the entire two-node matrix as zero and carry the result through
the infinite source limit, rather than record only zero determinant.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes scratch `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. Orthogonal boundary compression kills source vectors at both `+1/2` and `-1/2`.
2. Affine two-boundary residuals kill both characters while preserving cutoff compatibility.
3. Every positive boundary-jet order kills both characters; order growing with depth inherits this.
4. Finite order-growing Grams converge entrywise to the genuine cofinal kernel.

## Paper proof

Evaluate each construction on the two-node packet `w=(+1/2,-1/2)`.  In every finite balancing
model both feature vectors are exactly zero, so all four inner products forming the two-by-two Gram
vanish.  This proves zero matrices for orthogonal, affine, fixed positive-jet, and order-growing
balance at arbitrary source cutoff and Gamma depth.  Every entry of the finite order-growing Gram
is therefore the constant zero sequence in the cutoff.  Its independently proved cofinal limit is
unique, so every entry of the infinite Gram is also zero. `[PROVED HERE]`

## Hostile literature audit

Exact searches for combinations of `von Mangoldt`, `Gamma`, `Cauchy kernel`, `boundary jet`,
`two-boundary balance`, and `Gram matrix` found no paper stating this simultaneous five-model
collapse or its cofinal persistence.  Searches also deliberately included the broader phrases
`Mellin boundary +1/2 -1/2 Cauchy Gram` and `balanced Cauchy Gram boundary jets`.  Returned work
concerned the Riemann--von Mangoldt counting formula, generic Cauchy/Gram kernels, unrelated
holomorphic boundary jets, or speculative explicit-formula Gram constructions; none contained the
canonical balanced packet, the four finite mechanisms, or the order-growing cofinal endpoint.

The result still uses classical ingredients—Gram matrices, the Cauchy kernel, and uniqueness of
limits—and therefore carries no priority claim.  Novelty status is limited to the exact corpus-level
assembly formalized here. `[HOSTILE AUDIT PASSED; NO PRIORITY CLAIM]`

## Formalization

- Module: `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaTwoBoundaryGramCollapseLaw.lean`
- Capstone: `vonMangoldtAllDepthTwoBoundaryGramCollapseLaw`
- Cofinal endpoint: `infiniteVonMangoldtAllDepthOrderGrowingCauchyGram_twoBoundary_eq_zero`

## Log

- 2026-07-21 — Found during complete PSD and exact-boundary nullspace audit.
- 2026-07-21 — Scratch proof passed exactly with `lake env lean`.
- 2026-07-21 — Direct tree check passed exactly:
  `lake env lean GaloisForLFunctions/RHTower/VonMangoldtGammaTwoBoundaryGramCollapseLaw.lean`.
- 2026-07-21 — Hostile exact-phrase and component-literature searches found no collision with the
  simultaneous four-finite-plus-cofinal zero-matrix law; audit passed without a priority claim.
