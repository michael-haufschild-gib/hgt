# Local Inverse-Branch Collar Off Other Filled Julia Set

- **ID:** local-inverse-branch-collar-off-other
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../../logs/grok-bottcher-routes-worklog.md · Route B
- **Statement:** [CONJECTURE] If `z0 ∈ filledJulia c1 \ filledJulia c2`, then a sufficiently deep itinerary inverse branch for `f_c1^[n]` pulls a far-field annular slit sector back to a `K_c2`-free local collar on which `explicitBranch c1 n` is one-sheeted.

## Goal
Produce the missing local domain input for the disconnected Böttcher deck route: an open/preconnected `A_n ⊆ explicitDomain c1 n ∩ (filledJulia c2)^c` near the depth-`n` cylinder of `z0`, with enough strip control to feed `CylinderUnivalence.exp_comp_injOn` and enough deck structure to feed the existing `DeckAnnulus` machinery.

## Gates
- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `exists_local_inverseBranch_collar_offOther`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Use `z0 ∉ filledJulia c2` and compactness/closedness of `filledJulia c2` to choose `epsilon > 0` with `Metric.ball z0 epsilon ⊆ (filledJulia c2)^c`. Pull back a fixed far-field annular slit sector `E ⊆ escapeOpen c1 ∩ Complex.slitPlane` along the inverse branch determined by the itinerary of `z0`. The key analytic/topological estimate is that the selected collar diameter tends to zero as `n → ∞`, so eventually its closure lies in `Metric.ball z0 epsilon`.

Once `A_n` is localized, use the existing facts:
- `ExplicitBranch.analyticOnNhd_explicitBranch` for analyticity on `explicitDomain`.
- injectivity of `f_c1^[n]` on the selected inverse-branch collar.
- strip control for `2^-n * bottcherLog c1 ∘ f_c1^[n]`.
- `CylinderUnivalence.exp_comp_injOn` to make `explicitBranch c1 n` injective.
- `CylinderUnivalence.rotation_fixes_monomial_comp` / `DeckAnnulus` to keep functions of `t^(2^n)` deck-fixed.

First falsifier: the itinerary inverse-branch collars may fail to shrink up to the Julia boundary while preserving a deck loop. If shrinkage holds only for point neighborhoods but not for annular slit collars, this route must be replaced by the finite sausage-pruning route.

## Log
- 2026-06-29 — created in 0-backlog from high-temperature Grok route mutation; repaired into a local inverse-branch collar claim.
