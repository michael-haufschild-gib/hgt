# Signed prime–polar transport and Chebyshev coupling

- **ID:** signed-prime-polar-transport
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Scope:** Independent BiScaleUncertainty; 100 substantial contributions requested.
- **Ledger:** `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`

## Current mathematical target

For every actual compact continuous real source, construct a differentiable
annular collar average of its autocorrelation. Express its finite-window signed
von Mangoldt–polar pairing exactly through the classical error ψ(exp x)−exp x.
Control the difference from the original signed pairing by the local Krein
transport cost, retaining both endpoints and the negative-exponential polar term.
No zero-grid, source derivative, arithmetic cancellation, or energy premise.

## Proof plan and verification

- [x] Read field motivation and Pillars XIV–XV; inspect existing corpus.
- [x] Identify missing actual arithmetic coupling and rough-source admission.
- [x] Prove the collar average differentiable, with explicit derivative and local Lévy penalty.
- [ ] Prove exact finite-window Chebyshev identity with all boundary terms.
- [ ] Combine uniform Krein averaging error with actual signed prime–polar pairing.
- [x] Write dependency-closed paper proof and precise contribution boundary.
- [ ] Audit new leaves using `lake --old env lean`, check axioms in `/tmp`, wire umbrella.
- [ ] Run formal lint and regenerate indexes; preserve concurrent edits.

## Research discipline

Count theorem packages resolving distinct mathematical issues, never helper lemmas.
Search found local collar transport and kernel-specific Chebyshev identities;
no retrieved result supplies this rough-source coupling. Search partial=false,
errors=[], semantic coverage unmeasured, so no external novelty claim follows.
The 100-contribution goal remains active after any individual package.

## State

First goal turn; no prior goal-turn progress classification is applicable.
`update_plan` is unavailable; this card carries the executable plan.
Serena cannot extract Lean symbols (active language Python); use precise patches.
