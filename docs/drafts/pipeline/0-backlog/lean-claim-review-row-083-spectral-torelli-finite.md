# Lean claim review row #83 — finite spectral Torelli

- **ID:** lean-claim-review-row-083-spectral-torelli-finite
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #83; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean, finite)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** Spectral Torelli: `{s_m}` determine `xi`, in the finite sense claimed by the ledger.

## Goal
Audit the claim from scratch. Researchers must pin down the finite statement precisely and separate it from any infinite or actual-`xi` reconstruction claim. Leaner checks formalization after that scope review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/SpectralTorelli.lean`
- Candidate names: `spectralTorelli_faithful`, `spectralPoly_coeff_zero`, `selfDual_spectralPoly_coeff_real`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; finite Torelli statement restated without overclaiming actual `xi`
- [ ] 1 -> 2 fully-proven: researchers confirm a complete paper proof from scratch
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Review finite multiset reconstruction from power sums/Newton identities and decide exactly what "determine `xi`" means in this finite ledger row.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean, finite)` ledger row.
