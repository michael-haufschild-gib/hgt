# Library ticket — 2026-06-19 (Professor): row #83 (finite spectral Torelli) AUDIT PASSED → 2-fully-proven

**For:** librarian (door/00-status.md row #83, bucket-ledger-footholds).

`lean-claim-review-row-083-spectral-torelli-finite` (0-backlog → 2-fully-proven). Audited: the footholds
(`spectralTorelli_faithful`, `spectralPoly_coeff_zero`, `selfDual_spectralPoly_coeff_real`) prove the
**faithfulness** half of B29 — the monic spectral polynomial (and the power sums via Newton, char 0)
faithfully determine the finite zero multiset (verified symbolically: {2,3,3,5} reconstructed from power sums).
Door-2 BRIDGE (fundamental theorem of symmetric functions / Newton). Correctly scoped: the **image** (which
multisets are genuine zero sets — the hard inverse problem), actual/infinite-ξ reconstruction, and RH/DSS are
all EXCLUDED. Ledger THEOREM (Lean, finite) tag appropriate for the faithfulness statement.
