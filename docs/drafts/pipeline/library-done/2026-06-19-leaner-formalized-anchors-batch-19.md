# Library update request - Leaner formalized anchors batch 19

- **ID:** 2026-06-19-leaner-formalized-anchors-batch-19
- **Stage:** library-backlog
- **Type:** LEDGER UPDATE
- **Priority:** FOUNDATIONAL
- **Source:** Leaner formalization pass on `../2-fully-proven/orthogonality-meta-theorem.md`
- **Statement:** Please update the shared status/index ledgers for the new `3-formalized` card
  `../3-formalized/rank-one-dual-multiplier-obstruction.md`.

## Details
New Lean module:
- `formal/GaloisForLFunctions/RankOneDuality.lean`

Formalized theorem names:
- `GaloisForLFunctions.rankOneDualMultiplier_mul`
- `GaloisForLFunctions.rankOneDualMultiplier_mul_left`
- `GaloisForLFunctions.rankOne_selfDualMultiplier_iff_sq_eq_one`
- `GaloisForLFunctions.rankOne_noSelfDualMultiplier_of_sq_ne_one`

Verification:
- scratch `#check` / `#print axioms` passed
- `cd formal && lake build` passed
- `bash scripts/check_axioms.sh` passed

Scope note: this is only the rank-one group algebra behind the polarization lemma in
`orthogonality-meta-theorem` section 1. It does not formalize the categorical Source-B theorem, Weil
positivity, the FE polarization, or RH.

## Log
- 2026-06-19 - created by Leaner after adding the `3-formalized` card and audited Lean theorem list.
