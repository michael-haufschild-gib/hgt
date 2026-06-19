# Library update request — new formalized Lean sublemma cards

- **Date:** 2026-06-19
- **From:** Leaner
- **Requested ledger action:** add/update formalization ledger entries for two new `3-formalized` cards.

## New formalized cards
- `docs/drafts/pipeline/3-formalized/finite-prime-log-flow-spectrum.md`
  - Lean file: `formal/GaloisForLFunctions/KroneckerFlow.lean`
  - Theorems: `primeLogFrequency_single`, `primeLogFrequency_eq_zero_iff`, `primeLogFrequency_ne_zero`, `primeLogFrequency_single_ne_zero`
  - Split from `constraint-not-flow-theorem.md` §1.
- `docs/drafts/pipeline/3-formalized/finite-bohr-character-generator-identities.md`
  - Lean file: `formal/GaloisForLFunctions/BohrGenerators.lean`
  - Theorems: `bohrCharacter_zero`, `bohrCharacter_add`, `bohrCharacter_scaleCoordinate`
  - Split from `archimedean-generator-axis-mode.md`.

## Note
The parent cards remain in `2-fully-proven`; these new cards cover exact finite algebraic sublemmas whose whole stated content is now Lean-formalized and axiom-audited.
