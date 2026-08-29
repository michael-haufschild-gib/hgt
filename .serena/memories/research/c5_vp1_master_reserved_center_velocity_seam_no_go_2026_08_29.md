# C5-VP1 master-reserved center-velocity seam no-go (2026-08-29)

Formalized module: `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityMasterReservedSeamNoGo`.

Branch killed: `∀ t > 0, 0 ≤ thetaCuspCenterFifthRootVelocityMasterReservedCore t` is false. Route-kill theorem: `not_forall_thetaCuspCenterFifthRootVelocityMasterReservedCore_nonneg`.

Core construction: define smooth proxy `M = literalActionCore + 10*r*t^2*(G3+6*G2)`. On positive ray, `M = masterReservedCore`. Literal action core is odd and vanishes through order 4 at seam. With `r''(0)=k>0`, generic Leibniz classification gives `M^(4)(0)=120*k*(G3(0)+6*G2(0))`. Strict cooling `6G2 < -G3` makes it negative. Taylor mean remainder yields punctured-right negativity.

Sharp survivor: `thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_seamJetClassification`. Uniform six-curvature reserve preserves cubic cancellation but injects first uncancelled negative fourth jet. Viable C5-VP1 proof must retain literal third likelihood channel through fourth order or supply exact opposite correction.

New infrastructure: generalized derivatives of likelihood source jets 6 and 7 under positive likelihood coordinate, enabling two-sided `ContDiffAt` across modular seam.

Audit: direct Lean PASS; targeted lake build PASS; axioms only `[propext, Classical.choice, Quot.sound]`; wired into RHTower umbrella. Global lint fails only unrelated pre-existing unreachable modules.

Docs: `docs/drafts/pipeline/3-formalized/theta-cusp-c5-master-reserved-center-velocity-seam-no-go.md` and live C5 card updated. Frontier map was not edited.