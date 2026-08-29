# C5 master-reserved seam no-go (2026-08-29)

Formalized `GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5MasterReservedSeamNoGo` and wired it into `RHTower.lean`.

Killed chain: universal positivity of `c5CompletedMasterReservedCompensationMargin` -> literal direct-J orientation -> compact/far-tail C5 assembly -> rank-four/Ptolemy wall -> CLG/TTF or Weil -> RH.

Core theorem: adaptive master curvature is strictly greater than six times reflected adverse master curvature on `0 <= t <= u`, because both endpoint likelihood curvatures are positive and both first-atom scales exceed 3. Therefore adaptive-reserved margin strictly dominates master-reserved margin. Existing adaptive seam negativity implies `eventually_c5CompletedMasterReservedCompensationMargin_neg` at every positive centre and `not_forall_c5CompletedMasterReservedCompensationMargin_nonneg`.

Strong separation: at any centre with positive exact seam orientation, literal completed compensation is positive while master-reserved surrogate is negative throughout a common punctured seam neighbourhood.

Positive survivor: `c5CompletedMasterResidualReserve_eq_scaleGap_add_adaptiveResidual` splits full discarded reserve into strict adaptive scale-gap surplus plus exact third-likelihood-channel residual; `c5CompletedMasterResidualReserve_pos` on structural tail. Surviving C5 work must retain exact third-channel transport or prove normalized sixth-invariant monotonicity directly.

Verification: direct Lean PASS; targeted lake build PASS; axioms only propext, Classical.choice, Quot.sound. Global lint red only from pre-existing unrelated unreachable modules. Docs: failed card `docs/drafts/pipeline/5-failed/theta-cusp-c5-master-reserve-seam-no-go.md`; survivor card `docs/drafts/pipeline/3-formalized/theta-cusp-c5-master-residual-decomposition.md`.