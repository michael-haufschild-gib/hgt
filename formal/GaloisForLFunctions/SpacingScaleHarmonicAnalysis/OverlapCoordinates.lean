import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Length, height, overlap, and aperture

For polynomial length `X` and spectral height `T`, overlap is `X/T` and bandwidth is
`log X / log T`. A fixed overlap greater than one still has limiting bandwidth one.
The coordinate identities retain the logarithmic loss `-log c` when height is `X/c`.
The aperture `log X / 2` corresponds to prime cutoff `X`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight

/-- The reciprocal width of atoms with length `X` and overlap `c`. -/
def height (X c : ℝ) : ℝ := X / c

/-- Length divided by spectral height. -/
def overlap (X T : ℝ) : ℝ := X / T

/-- Logarithmic polynomial length relative to height. -/
def bandwidth (X T : ℝ) : ℝ := Real.log X / Real.log T

/-- Symmetric aperture whose autocorrelation has prime cutoff `X`. -/
def aperture (X : ℝ) : ℝ := Real.log X / 2

theorem inv_height (X c : ℝ) : (height X c)⁻¹ = c / X := by
  simp only [height, inv_div]

theorem overlap_height {X : ℝ} (hX : X ≠ 0) (c : ℝ) :
    overlap X (height X c) = c := by
  exact div_div_cancel₀ hX

theorem height_overlap {X : ℝ} (hX : X ≠ 0) (T : ℝ) :
    height X (overlap X T) = T := by
  exact div_div_cancel₀ hX

theorem length_eq_height_mul_overlap {T : ℝ} (hT : T ≠ 0) (X : ℝ) :
    X = T * overlap X T := by
  dsimp [overlap]
  field_simp

/-- The bandwidth excess records the logarithm of the overlap, including its sign. -/
theorem bandwidth_eq_one_add_log_overlap {X T : ℝ} (hX : 0 < X) (hT : 1 < T) :
    bandwidth X T = 1 + Real.log (overlap X T) / Real.log T := by
  rw [overlap, Real.log_div hX.ne' (zero_lt_one.trans hT).ne']
  dsimp [bandwidth]
  field_simp [(Real.log_pos hT).ne']
  ring

theorem overlap_le_one_iff {T : ℝ} (hT : 0 < T) (X : ℝ) :
    overlap X T ≤ 1 ↔ X ≤ T := by
  simpa only [overlap, one_mul] using (div_le_iff₀ hT : X / T ≤ 1 ↔ X ≤ 1 * T)

theorem one_lt_overlap_iff {T : ℝ} (hT : 0 < T) (X : ℝ) :
    1 < overlap X T ↔ T < X := by
  simpa only [overlap, one_mul] using (lt_div_iff₀ hT : 1 < X / T ↔ 1 * T < X)

theorem bandwidth_le_one_iff {X T : ℝ} (hX : 0 < X) (hT : 1 < T) :
    bandwidth X T ≤ 1 ↔ X ≤ T := by
  rw [bandwidth, div_le_iff₀ (Real.log_pos hT), one_mul]
  exact Real.log_le_log_iff hX (zero_lt_one.trans hT)

theorem bandwidth_le_one_iff_overlap_le_one {X T : ℝ} (hX : 0 < X) (hT : 1 < T) :
    bandwidth X T ≤ 1 ↔ overlap X T ≤ 1 :=
  (bandwidth_le_one_iff hX hT).trans (overlap_le_one_iff (zero_lt_one.trans hT) X).symm

theorem bandwidth_rpow {T : ℝ} (hT : 1 < T) (α : ℝ) :
    bandwidth (T ^ α) T = α := by
  rw [bandwidth, Real.log_rpow (zero_lt_one.trans hT)]
  exact mul_div_cancel_right₀ α (Real.log_pos hT).ne'

/-- Fixed excess bandwidth means power-growing overlap, not fixed overlap. -/
theorem overlap_rpow {T : ℝ} (hT : 0 < T) (α : ℝ) :
    overlap (T ^ α) T = T ^ (α - 1) := by
  rw [overlap, Real.rpow_sub hT, Real.rpow_one]

theorem four_thirds_overlap {T : ℝ} (hT : 0 < T) :
    overlap (T ^ (4 / 3 : ℝ)) T = T ^ (1 / 3 : ℝ) := by
  rw [overlap_rpow hT]
  congr 1
  ring

theorem exp_two_aperture {X : ℝ} (hX : 0 < X) :
    Real.exp (2 * aperture X) = X := by
  rw [aperture, show 2 * (Real.log X / 2) = Real.log X by ring, Real.exp_log hX]

/-- Subtracting the prime counterterm from the height logarithm leaves `-log c`. -/
theorem log_height_sub_log_length {X c : ℝ} (hX : 0 < X) (hc : 0 < c) :
    Real.log (height X c) - Real.log X = -Real.log c := by
  rw [height, Real.log_div hX.ne' hc.ne']
  ring

theorem two_aperture_sub_log_height {X T : ℝ} (hX : 0 < X) (hT : 0 < T) :
    2 * aperture X - Real.log T = Real.log (overlap X T) := by
  rw [aperture, overlap, Real.log_div hX.ne' hT.ne']
  ring

/-- A convenient exact formula for comparing overlap schedules at the same length. -/
theorem bandwidth_height_eq {X c : ℝ} (hX : 1 < X) (hc : 0 < c) :
    bandwidth X (height X c) = 1 / (1 - Real.log c / Real.log X) := by
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have heq : 1 - Real.log c / Real.log X = (Real.log X - Real.log c) / Real.log X := by
    rw [sub_div, div_self hlog]
  rw [bandwidth, height, Real.log_div (zero_lt_one.trans hX).ne' hc.ne', heq,
    one_div, inv_div]

/-- Every fixed positive overlap has limiting bandwidth one, on either side of touching. -/
theorem tendsto_bandwidth_fixed_overlap {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ => bandwidth X (height X c)) atTop (𝓝 1) := by
  have hr : Tendsto (fun X : ℝ => Real.log c / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h : Tendsto (fun X : ℝ => 1 / (1 - Real.log c / Real.log X)) atTop
      (𝓝 (1 / (1 - 0) : ℝ)) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub hr)
      (show (1 : ℝ) - 0 ≠ 0 by norm_num)
  simp only [sub_zero, div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  exact (bandwidth_height_eq hX hc).symm

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight
