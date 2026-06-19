# Library update request — sigma parity duplicate resolved

- **Date:** 2026-06-19
- **From:** Leaner
- **Ticket:** `sigma-parity-fe-weld.md`
- **Requested ledger action:** keep the authoritative card in `3-formalized`; remove any `2-fully-proven` duplicate from ledgers.

## Change
Merged DeWitt's Door-2/D-axis verdict into `docs/drafts/pipeline/3-formalized/sigma-parity-fe-weld.md` and removed the duplicate `docs/drafts/pipeline/2-fully-proven/sigma-parity-fe-weld.md`.

## Reason
The duplicate `2-fully-proven` copy stated that the `2 -> 3` gate was already complete via `fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`, and `exteriorPower_map_neg_id`. The existing `3-formalized` card is therefore the correct pipeline home; the new Door-2/D-axis verdict is metadata for that formalized card, not a reason to demote it.
