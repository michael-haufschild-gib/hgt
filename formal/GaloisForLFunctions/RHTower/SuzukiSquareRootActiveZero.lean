import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The square-root active-zero floor

A ridge certificate whose regularized defect is below `1/16` is within `1/4` of the unit source, so
its own norm is below `5/4` while its mass on the two endpoint strips stays above `5/8`.  The
`L²` Nikolskii inequality bounds that endpoint mass by the strip length times the number of active
frequencies times the global `L²` norm over the full aperture, and comparing the two bounds leaves
`√a < π m √L`: the number of distinct active ordinates grows at least like the square root of the
aperture.

Nothing here depends on the internal spacing of the ordinates — the Nikolskii bound is
separation-free, which is why the conclusion is uniform over all zero clusters.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **`(386)`: a small defect keeps the certificate near the source.** -/
theorem norm_certificate_lt {E : Type*} [NormedAddCommGroup E] {h p : E}
    (hh : ‖h‖ = 1) (hdist : ‖h - p‖ < 1 / 4) : ‖p‖ < 5 / 4 := by
  have hsplit : ‖p‖ ≤ ‖h‖ + ‖h - p‖ := by
    calc ‖p‖ = ‖h - (h - p)‖ := by congr 1; abel
      _ ≤ ‖h‖ + ‖h - p‖ := norm_sub_le _ _
  rw [hh] at hsplit
  linarith

/-- **`(388)`: the Nikolskii comparison forces a square-root active-zero floor.** -/
theorem sqrt_aperture_lt_of_nikolskii {E : Type*} [NormedAddCommGroup E] {h p : E}
    {hB pB L a m : ℝ} (hL : 0 < L) (ha : 0 < a) (hm : 0 ≤ m)
    (hh : ‖h‖ = 1) (hdist : ‖h - p‖ < 1 / 4)
    (hhB : 7 / 8 < hB) (htriB : hB - ‖h - p‖ ≤ pB)
    (hnik : pB ≤ Real.sqrt (2 * L) * (Real.pi * m / 2) * ‖p‖ / Real.sqrt (2 * a)) :
    Real.sqrt a < Real.pi * m * Real.sqrt L := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpnorm : ‖p‖ < 5 / 4 := norm_certificate_lt hh hdist
  have hpB : 5 / 8 < pB := by linarith
  have h2L : Real.sqrt (2 * L) = Real.sqrt 2 * Real.sqrt L :=
    Real.sqrt_mul (by norm_num) L
  have h2a : Real.sqrt (2 * a) = Real.sqrt 2 * Real.sqrt a :=
    Real.sqrt_mul (by norm_num) a
  have hX : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt L * (Real.pi * m / 2) := by positivity
  have hdenpos : 0 < Real.sqrt 2 * Real.sqrt a := by positivity
  have hstep : pB * (Real.sqrt 2 * Real.sqrt a)
      ≤ Real.sqrt 2 * Real.sqrt L * (Real.pi * m / 2) * ‖p‖ := by
    rw [h2L, h2a] at hnik
    rw [le_div_iff₀ hdenpos] at hnik
    exact hnik
  have hkey : 5 / 8 * (Real.sqrt 2 * Real.sqrt a)
      < Real.sqrt 2 * Real.sqrt L * (Real.pi * m / 2) * ‖p‖ := by
    nlinarith [hstep, hpB, hdenpos]
  have hnorm : Real.sqrt 2 * Real.sqrt L * (Real.pi * m / 2) * ‖p‖
      ≤ Real.sqrt 2 * Real.sqrt L * (Real.pi * m / 2) * (5 / 4) :=
    mul_le_mul_of_nonneg_left hpnorm.le hX
  have hfinal : 5 / 8 * (Real.sqrt 2 * Real.sqrt a)
      < Real.sqrt 2 * Real.sqrt L * (Real.pi * m / 2) * (5 / 4) := lt_of_lt_of_le hkey hnorm
  have hcancel : (Real.sqrt 2 * (5 / 8)) * Real.sqrt a
      < (Real.sqrt 2 * (5 / 8)) * (Real.pi * m * Real.sqrt L) := by nlinarith [hfinal, hs2]
  have hpos : 0 < Real.sqrt 2 * (5 / 8) := by positivity
  exact lt_of_mul_lt_mul_left hcancel hpos.le

/-- **`(384)`: a counting bound transfers the floor to the zero height.** -/
theorem height_floor_of_count {G m C c : ℝ} (hC : 0 < C)
    (hcount : m ≤ C * (G * Real.log (G + 2))) (hm : c ≤ m) :
    c / C ≤ G * Real.log (G + 2) := by
  rw [div_le_iff₀ hC]
  nlinarith [hcount, hm]

end GaloisForLFunctions.RHTower
