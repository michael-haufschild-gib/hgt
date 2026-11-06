import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffBands

/-!
# Pointwise tails of the Hausdorff saddle

The strip modulus estimate preserves Gaussian decay near the real saddle
and power decay beyond four saddle heights. All constants are uniform in
the two integer orders.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

theorem saddle_width_le_height {s w : ℝ} {p : ℕ} (hs : 0 < s) (hw : 0 ≤ w)
    (hp : 1 ≤ p) (hwidth : (p : ℝ) * w ^ 2 = s ^ 2) : w ≤ s := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h := mul_le_mul_of_nonneg_right hpR (sq_nonneg w)
  exact (sq_le_sq₀ hw hs.le).mp (by nlinarith only [h, hwidth])

theorem sixteen_width_le_height {s w : ℝ} {p : ℕ} (hs : 0 < s) (hw : 0 ≤ w)
    (hp : 256 ≤ p) (hwidth : (p : ℝ) * w ^ 2 = s ^ 2) : 16 * w ≤ s := by
  have hpR : (256 : ℝ) ≤ p := by exact_mod_cast hp
  have h := mul_le_mul_of_nonneg_right hpR (sq_nonneg w)
  exact (sq_le_sq₀ (by positivity) hs.le).mp (by nlinarith only [h, hwidth])

theorem height_le_order_mul_width {s w : ℝ} {p : ℕ} (hs : 0 < s) (hw : 0 ≤ w)
    (hp : 1 ≤ p) (hwidth : (p : ℝ) * w ^ 2 = s ^ 2) : s ≤ (p : ℝ) * w := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h := mul_le_mul_of_nonneg_right hpR (show 0 ≤ (p : ℝ) * w ^ 2 by positivity)
  exact (sq_le_sq₀ hs.le (by positivity)).mp (by nlinarith only [h, hwidth])

/-- A width of at least 32 absorbs the transverse modulus cost into `exp 1`. -/
theorem norm_kernel_le_exp_mul_realKernel {R s w x : ℝ} {p r : ℕ} (hR : 0 < R)
    (hs : 0 < s) (hp : 0 < p) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * (p : ℝ) ≤ r) (hwidth : (p : ℝ) * w ^ 2 = s ^ 2)
    (hw : 32 ≤ w) (hxs : s / 4 ≤ x) {y : ℝ} (hy : |y| ≤ 1 / 2) :
    ‖kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 * realKernel R p r x := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity : 0 < s / 4) hxs
  have hRx := saddle_radius_mul_sq_ge hR hs hp hbalance hpr hxs
  have hA : 0 ≤ R - x⁻¹ ^ 2 := by
    linarith only [half_radius_le_complement hx hRx, hR]
  have hM : 0 ≤ realKernel R p r x := by unfold realKernel; positivity
  have hw2 : 1024 ≤ w ^ 2 := by nlinarith only [hw]
  have hcost : 1024 * (p : ℝ) / s ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hs)]
    have h := mul_le_mul_of_nonneg_left hw2 (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    nlinarith only [h, hwidth]
  calc
    _ ≤ realKernel R p r x * Real.exp (1024 * (p : ℝ) / s ^ 2) :=
      norm_kernel_le_realKernel_saddle_exp hR hs hp hbalance hpr hxs hy
    _ ≤ realKernel R p r x * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost) hM
    _ = _ := mul_comm _ _

/-- Gaussian tail in the actual ordinate coordinate. -/
theorem norm_kernel_le_saddle_gaussian {R s w x : ℝ} {p r : ℕ} (hR : 0 < R)
    (hs : 0 < s) (hp : 0 < p) (hr : 0 < r)
    (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r) (hpr : 200 * (p : ℝ) ≤ r)
    (hwidth : (p : ℝ) * w ^ 2 = s ^ 2) (hw : 32 ≤ w)
    (hxs : s / 4 ≤ x) (hxs4 : x ≤ 4 * s) {y : ℝ} (hy : |y| ≤ 1 / 2) :
    ‖kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 * realKernel R p r s * Real.exp (-((x - s) / w) ^ 2 / 16) := by
  have hw0 : 0 < w := by linarith only [hw]
  have ht : 1 / 4 ≤ x / s := (le_div_iff₀ hs).mpr (by linarith only [hxs])
  have ht4 : x / s ≤ 4 := (div_le_iff₀ hs).mpr hxs4
  have hprofile := realKernel_mul_le_saddle_gaussian hs hp hr hbalance hpr ht ht4
  rw [mul_div_cancel₀ x hs.ne'] at hprofile
  have heq : -(p : ℝ) * (x / s - 1) ^ 2 / 16 = -((x - s) / w) ^ 2 / 16 := by
    field_simp [hs.ne', hw0.ne']
    nlinarith only [mul_congr hwidth (show (x - s) ^ 2 = (x - s) ^ 2 from rfl)]
  rw [heq] at hprofile
  calc
    _ ≤ Real.exp 1 * realKernel R p r x :=
      norm_kernel_le_exp_mul_realKernel hR hs hp hbalance hpr hwidth hw hxs hy
    _ ≤ Real.exp 1 * (realKernel R p r s * Real.exp (-((x - s) / w) ^ 2 / 16)) :=
      mul_le_mul_of_nonneg_left hprofile (Real.exp_pos 1).le
    _ = _ := by ring

/-- Power decay beyond four saddle heights. -/
theorem norm_kernel_le_saddle_power {R s w x : ℝ} {p r : ℕ} (hR : 0 < R)
    (hs : 0 < s) (hp : 0 < p) (hr : 0 < r)
    (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r) (hpr : 200 * (p : ℝ) ≤ r)
    (hwidth : (p : ℝ) * w ^ 2 = s ^ 2) (hw : 32 ≤ w)
    (hxs : 4 * s ≤ x) {y : ℝ} (hy : |y| ≤ 1 / 2) :
    ‖kernel R p r ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 * realKernel R p r s * (x / s)⁻¹ ^ p := by
  have ht : 4 ≤ x / s := (le_div_iff₀ hs).mpr hxs
  have hprofile := realKernel_mul_le_saddle_inv_pow hs hp hr hbalance hpr ht
  rw [mul_div_cancel₀ x hs.ne'] at hprofile
  calc
    _ ≤ Real.exp 1 * realKernel R p r x :=
      norm_kernel_le_exp_mul_realKernel hR hs hp hbalance hpr hwidth hw
        (by linarith only [hxs, hs]) hy
    _ ≤ Real.exp 1 * (realKernel R p r s * (x / s)⁻¹ ^ p) :=
      mul_le_mul_of_nonneg_left hprofile (Real.exp_pos 1).le
    _ = _ := by ring

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
