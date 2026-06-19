# Ledger update request: faces-orthogonality returned by Leaner

- **Filed:** 2026-06-19
- **Filed by:** Leaner
- **Card affected:** `faces-orthogonality.md`
- **Pipeline move:** `2-fully-proven` -> `0-backlog-lean`

## Reason
Lean review found that the card's main logical-independence theorem is not fully proven as stated. The
function-field witness supports `A ⇏ B`, but the `B ⇏ A` leg does not exhibit a witness with Face B
genericity/DSS true while Face A fails. It establishes multiplicative-side structure/underdetermination
compatible with Face A false, and the card's own risk note leaves an explicitly transcendentally-generic
off-line Beurling witness as future work.

The card should be repaired by either weakening the statement to structural underdetermination or supplying
the actual `¬A ∧ B` witness.
