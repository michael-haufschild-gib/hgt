# Local Inverse-Branch Collar Off Other Filled Julia Set

- **ID:** local-inverse-branch-collar-off-other
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../logs/grok-bottcher-routes-worklog.md · Route B
- **Statement:** [CONJECTURE] If `z0 ∈ filledJulia c1 \ filledJulia c2`, then a sufficiently deep itinerary inverse branch for `f_c1^[n]` pulls a far-field annular slit sector back to a `K_c2`-free local collar on which `explicitBranch c1 n` is one-sheeted.

## Goal
Produce the missing local domain input for the disconnected Böttcher deck route: an open/preconnected `A_n ⊆ explicitDomain c1 n ∩ (filledJulia c2)^c` near the depth-`n` cylinder of `z0`, with enough strip control to feed `CylinderUnivalence.exp_comp_injOn` and enough deck structure to feed the existing `DeckAnnulus` machinery.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
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

Formal bridge now available in `formal/GaloisForLFunctions/Bottcher/LocalCollar.lean`:
- `explicitBranchLift` packages the logarithmic lift of `explicitBranch`.
- `explicitBranchLift_injOn_of_iterate_bottcherLog_injOn` reduces lift injectivity to iterate injectivity plus injectivity of the selected `bottcherLog` sheet on the forward image.
- `explicitBranch_injOn_of_lift_injOn_strip` reduces the local one-sheet branch claim to lift injectivity plus horizontal strip control.
- `explicitBranch_injOn_of_iterate_bottcherLog_injOn_strip` combines these into the exact formal endpoint the collar geometry should feed.
- `LocalCollarData c1 c2 n A y0` is the current formal interface for the conjectural collar: `A` must be open, preconnected, nonempty, inside `explicitDomain c1 n`, off `filledJulia c2`, injective for `f_c1^[n]`, injective for the selected `bottcherLog` sheet on the forward image, and contained in one horizontal strip.
- `LocalCollarData.analyticOnNhd_explicitBranch` and `LocalCollarData.explicitBranch_injOn` are verified consumers of that interface.
- `ForwardCollarData c1 c2 n A E y0` is the corrected forward-sector bridge extracted from Grok's pullback-sector suggestion: produce a forward sector `E` with `f_c1^[n] '' A ⊆ E`, `E ⊆ escapeOpen c1 ∩ Complex.slitPlane`, `bottcherLog c1` injective on `E`, and the scaled strip bound for `2^-n * bottcherLog c1` on `E`. Then `ForwardCollarData.toLocalCollarData` transports the data back to `A`.
- `ForwardCollarData.analyticOnNhd_explicitBranch` and `ForwardCollarData.explicitBranch_injOn` are verified consumers.
- `ForwardCollarData.of_stepwise_injOn` and `ForwardCollarData.of_stepwise_antipodalFree` reduce the iterate-injectivity part to the already-proven `CylinderUnivalence.quadratic_iterate_injOn` / `quadratic_injOn` engine. The geometric obligation is now lobe-shaped: for each `j < n`, show `f_c1^[j] '' A` is antipodal-free.
- `bottcherLog_injOn_far_subset` and `ForwardCollarData.of_stepwise_antipodalFree_far` discharge the `bottcherLog` injectivity part from the existing `FarFieldUnivalence.bottcherCoord_injOn_far`. The forward sector now only needs to be far-field, slit-plane, scaled-strip controlled, and have antipodal-free intermediate images.
- `scaled_strip_sector_of_bottcherLog_im_bounds` and `ForwardCollarData.of_stepwise_antipodalFree_far_im_bounds` move strip control into the unscaled coordinate `im (bottcherLog c1 w)`. This is the right target for estimates using `bottcherLog c z = Complex.log z + ∑ k, bottcherLogTerm c z k`.

First falsifier: the itinerary inverse-branch collars may fail to shrink up to the Julia boundary while preserving a deck loop. If shrinkage holds only for point neighborhoods but not for annular slit collars, this route must be replaced by the finite sausage-pruning route.

## Log
- 2026-06-29 — created in 0-backlog from high-temperature Grok route mutation; repaired into a local inverse-branch collar claim.
- 2026-06-29 — moved to 1-in-progress; added and checked `LocalCollar.lean` (`lake env lean GaloisForLFunctions/Bottcher/LocalCollar.lean`).
- 2026-06-29 — strengthened `LocalCollar.lean` with `LocalCollarData`; `lake build GaloisForLFunctions.Bottcher.LocalCollar` and `lake env lean GaloisForLFunctions/Bottcher.lean` pass.
- 2026-06-29 — asked Grok for the post-`LocalCollarData` bridge; corrected its unscaled-log mistake and formalized `ForwardCollarData`; `lake build GaloisForLFunctions.Bottcher.LocalCollar` and `lake env lean GaloisForLFunctions/Bottcher.lean` pass.
- 2026-06-29 — added stepwise/antipodal constructors for `ForwardCollarData`; same targeted checks pass.
- 2026-06-29 — wired far-field Böttcher univalence into the collar route (`bottcherLog_injOn_far_subset`, `ForwardCollarData.of_stepwise_antipodalFree_far`); `lake build GaloisForLFunctions.Bottcher.LocalCollar` and `lake env lean GaloisForLFunctions/Bottcher.lean` pass without warnings.
- 2026-06-29 — asked Grok about scaled-strip control; formalized the pure rescaling bridge from unscaled `im bottcherLog` bounds; same targeted checks pass.
- 2026-06-29 — asked Grok for post-log-error mutations. Extracted the angular-pruning mechanism and formalized two gates: `bottcherLog_im_bounds_of_log_im_bounds_error` / `ForwardCollarData.of_stepwise_antipodalFree_far_log_im_bounds_error` reduce strip control to principal-log sector bounds plus the known Böttcher-log error, and `ForwardCollarData.of_forward_halfplane_far_log_im_bounds_error` lets finite forward half-plane containment replace raw stepwise antipodal-freeness. `lake build GaloisForLFunctions.Bottcher.LocalCollar` passes.
- 2026-06-29 — added `bottcherLog_log_error_le_on_far` and `ForwardCollarData.of_forward_halfplane_far_log_im_bounds`, so the Grok angular-pruning route now needs only a far-field forward sector, forward half-plane containment through depth `n`, off-`K(c2)` containment, and principal-log strip margins. The Böttcher-log error is discharged internally from `norm_bottcherLog_sub_log_le`. `lake build GaloisForLFunctions.Bottcher.LocalCollar` passes.

## Current reduced obstruction
After the Grok angular-pruning mutation, the Lean endpoint no longer requires a raw inverse-branch proof first. It is enough to construct `A,E,a,R,y0,n` such that `A` is open/preconnected/nonempty and off `filledJulia c2`, `f_c1^[n] '' A ⊆ E`, `E` is far-field and in the slit plane, every intermediate image `f_c1^[j] '' A` lies in the open half-plane `{w | 0 < (a j * w).re}`, and the principal-log imaginary part on `E` lies in the widened interval with margin `2 * ‖c1‖ / R^2`. The theorem `ForwardCollarData.of_forward_halfplane_far_log_im_bounds` then supplies the one-sheeted explicit branch.
