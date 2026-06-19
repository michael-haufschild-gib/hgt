# Lean claim review row #49 — sigma-parity and FE-parity weld

- **ID:** lean-claim-review-row-049-sigma-parity-fe-parity-weld
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #49; ../../door/bucket-ledger-footholds.md; sigma-parity-fe-weld.md; ../3-formalized/sigma-parity-fe-weld.md
- **Claimed ledger status:** `THEOREM (Lean)`; a `../3-formalized/sigma-parity-fe-weld.md` card exists, but this review ticket requires researchers to re-check the claim from scratch before relying on it.
- **Statement:** sigma-parity equals FE-parity weld, as a candidate native theorem.

## Goal
Audit the claim from scratch. Researchers must determine the exact theorem being asserted and whether it is a native weld theorem or only a finite bookkeeping package. Leaner checks formalization after that determination.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/FunctionalEquationParity.lean`
- `formal/GaloisForLFunctions/ExteriorParity.lean`
- Candidate names: `fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`, `exteriorPower_map_neg_id`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; exact statement and Door-2/native status fixed from scratch
- [ ] 1 -> 2 fully-proven: researchers confirm a complete paper proof and decide whether the row is a bridge, native theorem, or smaller finite formal package
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Separate functional-equation moment parity from exterior-power sign parity. Then check whether the proposed weld proves an equality of structures or only parallel finite identities.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
