# Ledger update request — C5 Jensen perturbation returned to Lean backlog

- **Date:** 2026-06-19
- **Filed by:** Leaner
- **Card:** `docs/drafts/pipeline/0-backlog-lean/c5-jensen-perturbation-lemma.md`
- **Requested ledger action:** reflect that the card is not currently in `2-fully-proven`; it has been returned
  to Lean backlog for a fourth formalizer obstruction.

## Reason
The §1‴ endpoint/no-inflection repair makes the window data total, but the perturbation statement still uses
`x_i'` as a root of `F'` in the open interval `(x_i-ε_i, x_i+ε_i)` with
`ε_i := sup_{window}|D'| / m_i`. If `sup_{window}|D'| = 0`, then `ε_i = 0` and the open interval is empty;
the natural witness is `x_i`, but the stated open-interval witness is undefined.

## Needed repair
Restate the local critical-point witness using a closed interval, or split off the zero-slope case with an
explicit witness convention, before the card can be treated as Lean-ready.
