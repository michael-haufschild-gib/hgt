# Library update request — additional formalized analytic-anchor cards

- **Date:** 2026-06-19
- **From:** Leaner
- **Requested ledger action:** add/update formalization ledger entries for four new `3-formalized` analytic-anchor cards.

## New formalized cards
- `docs/drafts/pipeline/3-formalized/log-zeta-prime-coefficient-identities.md`
  - Lean file: `formal/GaloisForLFunctions/C5JensenPrimeKernel.lean`
  - Theorems: `logZetaPrimeCoeff_prime`, `logZetaPrimeCoeff_primePower`
  - Split from `c5-jensen-prime-kernel.md`.
- `docs/drafts/pipeline/3-formalized/function-field-local-factor-fe-algebra.md`
  - Lean file: `formal/GaloisForLFunctions/FunctionFieldFE.lean`
  - Theorems: `multiset_esymm_map_mul`, `functionField_esymm_FE`, `functionField_localFactor_FE`
  - Split from the function-field/C6 border material.
- `docs/drafts/pipeline/3-formalized/stieltjes-pairing-cauchy-product.md`
  - Lean file: `formal/GaloisForLFunctions/StieltjesWeld.lean`
  - Theorem: `stieltjes_pairing_cauchy_j`
  - Split from `stieltjes-log-weld.md`.
- `docs/drafts/pipeline/3-formalized/friable-dirichlet-derivative-at-one.md`
  - Lean file: `formal/GaloisForLFunctions/FriableAuxiliary.lean`
  - Theorem: `iteratedDeriv_friableExponentDirichletExp_at_one`
  - Split from `friable-dirichlet-auxiliary.md`.

## Note
The parent cards remain in `2-fully-proven`; these new cards cover exact subclaims whose whole stated content is now Lean-formalized and axiom-audited.
