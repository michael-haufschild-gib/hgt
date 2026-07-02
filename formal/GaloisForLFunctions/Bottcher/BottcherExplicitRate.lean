/-
# Explicit far-field rate for the Böttcher coordinate (mixed-pair wiring, step B1)

`tendsto_bottcherCoord_sub_id` gives `φ_c − id → 0` only as a filter limit, so every consumer
(the tower anchor's closeness radius `M₁`, hence the anchor radius `Ra`) inherits a
non-effective `c`-dependence.  This file extracts the QUANTITATIVE inequality its proof
already contains: `‖φ_c(z) − z‖ ≤ 4‖c‖/‖z‖` on the crude escape set — making every anchor
threshold explicit in `‖c‖`.  This is the root enabling bound of the mixed-pair tower
(patch localization at level `4h` needs the far identity zone to start at an
explicitly-bounded radius).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord

open Complex Set

namespace Bottcher

/-- **Explicit normalization rate** `‖φ_c(z) − z‖ ≤ 4‖c‖/‖z‖` on the escape set: the
quantitative form of `tendsto_bottcherCoord_sub_id`. -/
theorem norm_bottcherCoord_sub_id_le {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ‖bottcherCoord c z - z‖ ≤ 4 * ‖c‖ / ‖z‖ := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzpos
    linarith
  set S := ∑' k, bottcherLogTerm c z k with hSdef
  have hSbd : ‖S‖ ≤ 2 * ‖c‖ / ‖z‖ ^ 2 := by
    have h := norm_bottcherLog_sub_log_le hc hz
    rw [bottcherLog, add_sub_cancel_left] at h
    rw [hSdef]
    exact h
  have hSle1 : ‖S‖ ≤ 1 := by
    have h2 : 2 * ‖c‖ / ‖z‖ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [norm_nonneg z]
    linarith
  rw [bottcherCoord_eq_mul_exp hzne, ← hSdef,
    show z * Complex.exp S - z = z * (Complex.exp S - 1) by ring, norm_mul]
  calc ‖z‖ * ‖Complex.exp S - 1‖
      ≤ ‖z‖ * (2 * ‖S‖) := by
        gcongr
        exact Complex.norm_exp_sub_one_le hSle1
    _ ≤ ‖z‖ * (2 * (2 * ‖c‖ / ‖z‖ ^ 2)) := by gcongr
    _ = 4 * ‖c‖ / ‖z‖ := by
        field_simp
        ring

/-- **Explicit closeness radius**: beyond `max (4‖c‖) 3` the Böttcher coordinate is within
`1` of the identity — the effective substitute for the anchor's non-effective `M₁`. -/
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
