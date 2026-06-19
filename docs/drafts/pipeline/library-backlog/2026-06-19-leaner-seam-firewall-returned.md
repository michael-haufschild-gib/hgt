# Ledger update request — seam-firewall returned to Lean backlog

- **Date:** 2026-06-19
- **Filed by:** Leaner
- **Card:** `docs/drafts/pipeline/0-backlog-lean/seam-firewall.md`
- **Requested ledger action:** do not ledger `seam-firewall` as an unconditional `2-fully-proven` theorem yet.

## Reason
The card's 1→2 gate says the proof is assembled from `#131/#132/#133/#27(cond.)/#118/#54`, and §2 includes
the class `ω` among the cross-obstructions for which the prime block contributes null. But the same card says
the `ω` computation remains open and the positivity residual `ω=0` is handed to G5.

That mixes proven generator-level facts with a conditional/open `ω` component. A restored theorem card should
either remove `ω` from the unconditional firewall claim, mark the firewall explicitly conditional on `#27`, or
add a proof that the generator-level statement does not depend on `ω`.
