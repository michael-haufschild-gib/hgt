# Lean claim review row #49 — sigma-parity and FE-parity weld

- **ID:** lean-claim-review-row-049-sigma-parity-fe-parity-weld
- **Stage:** 0-backlog-lean (review reopened; authoritative card returned from `../3-formalized/sigma-parity-fe-weld.md`)
- **Type:** THEOREM (Lean) — grade **BRIDGE (substrate)**; not C5
- **Source:** ../../door/00-status.md · 00-status row #49; ../../door/bucket-ledger-footholds.md; sigma-parity-fe-weld.md; ../3-formalized/sigma-parity-fe-weld.md
- **Reviewed ledger status:** `THEOREM (Lean), BRIDGE (substrate)`; the authoritative card is
  `../3-formalized/sigma-parity-fe-weld.md`.
- **Statement:** sigma-parity equals FE-parity weld, as a candidate native theorem.

## Goal
Audit the claim from scratch. Researchers must determine the exact theorem being asserted and whether it is a native weld theorem or only a finite bookkeeping package. Leaner checks formalization after that determination.

## Resolution
Review complete. DeWitt resolved the Door-2/D-axis verdict: C-axis Door-2 fails because the stripped
statement is the sign representation `(−1)^k` on exterior powers; D-axis D2 is met because the weld ties
the difference-Galois `σ`-cohomology grading to analytic FE-parity. Leaner kept the authoritative card in
`3-formalized/sigma-parity-fe-weld.md` and removed the duplicate `2-fully-proven` copy. The verified Lean
constants are `fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`, and `exteriorPower_map_neg_id`.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/RHTower/FunctionalEquationParity.lean`
- `formal/GaloisForLFunctions/RHTower/ExteriorParity.lean`
- Candidate names: `fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`, `exteriorPower_map_neg_id`

These names are leads, not certification.

## Gates
- [x] 0 -> 1 in-progress: researcher assigned; exact statement and Door-2/native status fixed from scratch
- [x] 1 -> 2 fully-proven: researchers confirm a complete paper proof and decide whether the row is a bridge, native theorem, or smaller finite formal package
- [x] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file; authoritative formalized card is `../3-formalized/sigma-parity-fe-weld.md`
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate, tracked by the authoritative card

## Approach
Separate functional-equation moment parity from exterior-power sign parity. Then check whether the proposed weld proves an equality of structures or only parallel finite identities.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
- 2026-06-19 — review closed after DeWitt/Leaner resolution: row #49 is `THEOREM (Lean), BRIDGE (substrate)`;
  the active theorem card remains `../3-formalized/sigma-parity-fe-weld.md`.

## Lean-formalizer return note (2026-06-19, Leaner)
Review reopened. The authoritative `sigma-parity-fe-weld.md` card was returned from `3-formalized` because its named Lean constants prove separate parity lemmas but not the claimed weld/equivalence between the difference-Galois `sigma` grading and analytic FE parity. This review card should not be closed as formalized until that bridge theorem is stated and proved, or until the claim is narrowed to the already formalized separate parity facts.
