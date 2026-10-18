import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel

/-!
# Signed phase cancellation for Hausdorff powers

The two factors of a Hausdorff atom rotate in opposite directions. Their
signed linear phase, together with the cubic arctangent remainder, controls
the real part without paying the sum of the two absolute phases. This is the
local mechanism behind quadratic-order saddle bands in the actual Xi source.
-/

open Complex

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The linear phase retains its sign; only the cubic remainder is absolute. -/
def signedPowerPhaseBudget (n r : ℕ) (τ σ : ℝ) : ℝ :=
  |(n : ℝ) * τ - (r : ℝ) * σ| +
    ((n : ℝ) * |τ| ^ 3 + (r : ℝ) * |σ| ^ 3) / 3

theorem signedPowerPhaseBudget_nonneg (n r : ℕ) (τ σ : ℝ) :
    0 ≤ signedPowerPhaseBudget n r τ σ := by
  unfold signedPowerPhaseBudget
  positivity

/-- The unreduced phase is controlled even when the two absolute phases are large. -/
theorem abs_arctan_power_phase_le (n r : ℕ) (τ σ : ℝ) :
    |(n : ℝ) * Real.arctan τ - (r : ℝ) * Real.arctan σ| ≤
      signedPowerPhaseBudget n r τ σ := by
  have hτ := HTGeometry.abs_arctan_sub_self_le_cube τ
  have hσ := HTGeometry.abs_arctan_sub_self_le_cube σ
  have hid : (n : ℝ) * Real.arctan τ - (r : ℝ) * Real.arctan σ =
      ((n : ℝ) * τ - (r : ℝ) * σ) +
        ((n : ℝ) * (Real.arctan τ - τ) + -((r : ℝ) * (Real.arctan σ - σ))) := by
    ring
  rw [hid]
  calc
    _ ≤ |(n : ℝ) * τ - (r : ℝ) * σ| +
        (|(n : ℝ) * (Real.arctan τ - τ)| +
          |-((r : ℝ) * (Real.arctan σ - σ))|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ = |(n : ℝ) * τ - (r : ℝ) * σ| +
        ((n : ℝ) * |Real.arctan τ - τ| + (r : ℝ) * |Real.arctan σ - σ|) := by
      simp only [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) r)]
    _ ≤ |(n : ℝ) * τ - (r : ℝ) * σ| +
        ((n : ℝ) * (|τ| ^ 3 / 3) + (r : ℝ) * (|σ| ^ 3 / 3)) := by
      gcongr
    _ = signedPowerPhaseBudget n r τ σ := by
      unfold signedPowerPhaseBudget
      ring

/-- Exact real-part formula for a pair of oppositely rotating powers. -/
theorem re_compensated_power_eq (n r : ℕ) (τ σ : ℝ) :
    ((1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r).re =
      ‖(1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r‖ *
        Real.cos ((n : ℝ) * Real.arctan τ - (r : ℝ) * Real.arctan σ) := by
  let u : ℂ := 1 + (τ : ℂ) * I
  let v : ℂ := 1 - (σ : ℂ) * I
  have hu : u.re = 1 := by simp [u]
  have hv : v.re = 1 := by simp [v]
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hargu : u.arg = Real.arctan τ := by
    rw [HTGeometry.complexArg_eq_arctan_of_re_pos (by rw [hu]; norm_num)]
    simp [u]
  have hargv : v.arg = -Real.arctan σ := by
    rw [HTGeometry.complexArg_eq_arctan_of_re_pos (by rw [hv]; norm_num)]
    simp [v, Real.arctan_neg]
  let Z : ℂ := (n : ℂ) * Complex.log u + (r : ℂ) * Complex.log v
  have hexp : Complex.exp Z = u ^ n * v ^ r := by
    dsimp only [Z]
    rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul,
      Complex.exp_log hu0, Complex.exp_log hv0]
  have hphase : Z.im = (n : ℝ) * Real.arctan τ - (r : ℝ) * Real.arctan σ := by
    simp [Z, Complex.mul_im, Complex.log_im, hargu, hargv, sub_eq_add_neg]
  change (u ^ n * v ^ r).re = ‖u ^ n * v ^ r‖ * _
  rw [← hexp, Complex.exp_re, Complex.norm_exp, hphase]

/-- A global lower bound: no phase-budget smallness is needed for this inequality. -/
theorem re_compensated_power_ge (n r : ℕ) (τ σ : ℝ) :
    (1 - signedPowerPhaseBudget n r τ σ ^ 2 / 2) *
        ‖(1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r‖ ≤
      ((1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r).re := by
  have hphase := abs_arctan_power_phase_le n r τ σ
  have hsquare : ((n : ℝ) * Real.arctan τ - (r : ℝ) * Real.arctan σ) ^ 2 ≤
      signedPowerPhaseBudget n r τ σ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hphase 2
    simpa only [sq_abs] using this
  have hcos := Real.one_sub_sq_div_two_le_cos
    (x := (n : ℝ) * Real.arctan τ - (r : ℝ) * Real.arctan σ)
  rw [re_compensated_power_eq]
  have hlower : 1 - signedPowerPhaseBudget n r τ σ ^ 2 / 2 ≤
      Real.cos ((n : ℝ) * Real.arctan τ - (r : ℝ) * Real.arctan σ) := by linarith
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlower (norm_nonneg _)

/-- Signed cancellation retains half the absolute mass when its budget is at most one. -/
theorem half_norm_le_re_compensated_power (n r : ℕ) {τ σ : ℝ}
    (hbudget : signedPowerPhaseBudget n r τ σ ≤ 1) :
    1 / 2 * ‖(1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r‖ ≤
      ((1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r).re := by
  have h0 := signedPowerPhaseBudget_nonneg n r τ σ
  have hsquare : signedPowerPhaseBudget n r τ σ ^ 2 ≤ 1 := by nlinarith
  exact (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)).trans
    (re_compensated_power_ge n r τ σ)

end

end GaloisForLFunctions.BiScaleUncertainty
