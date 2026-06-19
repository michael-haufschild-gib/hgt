# Lean claim review row #58 — finite `kappa_-` and elementary-symmetric layers

- **ID:** lean-claim-review-row-058-finite-layers-kappa-esymm
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #58; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** both finite layers are ledgered: exact `kappa_-` and elementary-symmetric algebraic independence.

## Goal
Audit the claim from scratch. Researchers must decide whether this compound row is a legitimate combined theorem or simply references two separate finite Lean footholds. Leaner verifies formalization only after the row is scoped.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/CarrierCauchy.lean`
- `formal/GaloisForLFunctions/SpectrumGenericity.lean`
- Candidate names: `multiPair_carrier_exact_neg_inertia`, `spectrum_esymm_algIndep`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; decide whether to split into row #32 plus finite DSS-face review
- [ ] 1 -> 2 fully-proven: researchers confirm the complete paper proof or replace this with separate precise statements
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate, or split tickets if needed

## Approach
Review the RH finite layer (`kappa_-`) and the DSS finite layer (`esymm` algebraic independence) independently, then determine whether the A1/A2-unification row asserts anything beyond their conjunction.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
