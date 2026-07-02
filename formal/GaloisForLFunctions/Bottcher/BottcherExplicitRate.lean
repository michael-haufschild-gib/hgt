/-
# Explicit closeness radius for the Böttcher coordinate (mixed-pair wiring, step B1)

The quantitative far-field rate `‖φ_c(z) − z‖ ≤ 4‖c‖/‖z‖` is already in the tree
(`norm_bottcherCoord_sub_id_le`, `PolyAsymptotic`).  This file adds the effective closeness
radius the mixed-pair anchor arguments consume: beyond `max (4‖c‖) 3` the coordinate is
within `1` of the identity — the explicit substitute for the anchor's non-effective
tendsto-threshold `M₁`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.PolyAsymptotic

open Complex Set

namespace Bottcher

/-- **Explicit closeness radius**: beyond `max (4‖c‖) 3` the Böttcher coordinate is within
`1` of the identity. -/
theorem norm_bottcherCoord_sub_id_lt_one {c z : ℂ} (hz : max (4 * ‖c‖) 3 < ‖z‖) :
    ‖bottcherCoord c z - z‖ < 1 := by
  have h3 : (3:ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
  have h4c : 4 * ‖c‖ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hc : ‖c‖ ≤ ‖z‖ := by nlinarith [norm_nonneg c]
  have h := norm_bottcherCoord_sub_id_le hc (by linarith)
  have h1 : 4 * ‖c‖ / ‖z‖ < 1 := by
    rw [div_lt_one (by linarith)]
    exact h4c
  linarith

end Bottcher
