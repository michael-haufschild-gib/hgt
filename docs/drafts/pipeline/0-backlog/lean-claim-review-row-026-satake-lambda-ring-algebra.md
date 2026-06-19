# Lean claim review row #26 — Satake lambda-ring algebra

- **ID:** lean-claim-review-row-026-satake-lambda-ring-algebra
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #26; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** Satake lambda-ring algebra: tensor, isobaric sum, Adams operations, plethysm, and e-h duality.

## Goal
Audit the claim from scratch. Researchers must decide whether this broad row is one theorem, a bundle of independent finite algebra statements, or should be split before Leaner verifies formalization.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/AdamsOperations.lean`
- `formal/GaloisForLFunctions/SymPowerPlethysm.lean`
- `formal/GaloisForLFunctions/EHKoszulDuality.lean`
- Candidate names include `adamsPowerSum_tensor`, `adamsPowerSum_isobaricSum`, `adamsPowerSum_comp`, `adamsPowerSum_one`, `chebyshevU_eval_plethysm`, `eh_koszul_duality`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; component statements enumerated; old ledger claim treated as unverified
- [ ] 1 -> 2 fully-proven: researchers confirm complete paper proofs for every component retained under the row
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate, or split tickets if the bundle is too broad

## Approach
Decompose the row into the algebraic operations it names, then check each one independently in finite Satake-parameter language before accepting the row as a single audited claim.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
