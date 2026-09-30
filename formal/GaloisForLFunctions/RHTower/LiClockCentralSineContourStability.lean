import GaloisForLFunctions.RHTower.LiClockCentralSineContour

/-!
# Stability of the literal central trace sine contour

A uniform error on one source circle controls every complex clock by the exact
odd-factorial majorant `sinh`. The normalization includes the negative trace sign;
no parity, source positivity, or hypothesis about zeta zeros is needed.
-/

open Complex Set Metric Filter Topology MeasureTheory
namespace RHTower
noncomputable section


private theorem sine_norm_le_sinh_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := by
  have hs := Complex.hasSum_sin z
  calc
    ‖Complex.sin z‖ = ‖∑' j : ℕ, (-1 : ℂ)^j*z^(2*j+1)/((2*j+1).factorial : ℂ)‖ := by
      rw [hs.tsum_eq]
    _ ≤ ∑' j : ℕ, ‖(-1 : ℂ)^j*z^(2*j+1)/((2*j+1).factorial : ℂ)‖ :=
      norm_tsum_le_tsum_norm hs.summable.norm
    _ = Real.sinh ‖z‖ := by
      rw [← (Real.hasSum_sinh ‖z‖).tsum_eq]
      apply tsum_congr
      intro j
      simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, Complex.norm_natCast]

/-- The normalized odd-trace sine functional, including its literal negative sign. -/
def liClockCentralTraceSineContour (T : ℂ → ℂ) (r : ℝ) (t : ℂ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (∮ z in C(0,r), T z * Complex.sin (t/z) / z)

/-- A uniform source error controls every complex clock with the sharp odd-factorial envelope. -/
theorem norm_liClockCentralTraceSineContour_sub_le {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    {T U : ℂ → ℂ} (hT : ContinuousOn T (sphere 0 r)) (hU : ContinuousOn U (sphere 0 r))
    (hbound : ∀ z ∈ sphere (0 : ℂ) r, ‖T z-U z‖ ≤ M) (t : ℂ) :
    ‖liClockCentralTraceSineContour T r t-liClockCentralTraceSineContour U r t‖ ≤
      M * Real.sinh (‖t‖/r) := by
  have hnz (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : z ≠ 0 := by
    intro hz0
    subst z
    simp at hz
    linarith
  have hsine : ContinuousOn (fun z : ℂ => Complex.sin (t/z)) (sphere 0 r) :=
    Complex.continuous_sin.comp_continuousOn
      (continuousOn_const.div continuousOn_id hnz)
  have hTi : CircleIntegrable (fun z : ℂ => T z * Complex.sin (t/z) / z) 0 r :=
    ((hT.mul hsine).div continuousOn_id hnz).circleIntegrable hr.le
  have hUi : CircleIntegrable (fun z : ℂ => U z * Complex.sin (t/z) / z) 0 r :=
    ((hU.mul hsine).div continuousOn_id hnz).circleIntegrable hr.le
  have hsub : (∮ z in C(0,r), (T z-U z)*Complex.sin (t/z)/z) =
      (∮ z in C(0,r), T z*Complex.sin (t/z)/z) -
      (∮ z in C(0,r), U z*Complex.sin (t/z)/z) := by
    rw [← circleIntegral.integral_sub hTi hUi]
    apply circleIntegral.integral_congr hr.le
    intro z _
    dsimp only
    ring
  have heq : liClockCentralTraceSineContour T r t-liClockCentralTraceSineContour U r t =
      -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C(0,r), (T z-U z)*Complex.sin (t/z)/z) := by
    rw [hsub]
    unfold liClockCentralTraceSineContour
    ring
  have hpoint : ∀ z ∈ sphere (0 : ℂ) r,
      ‖(T z-U z)*Complex.sin (t/z)/z‖ ≤ M/r*Real.sinh (‖t‖/r) := by
    intro z hz
    have hzNorm : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hsin := sine_norm_le_sinh_norm (t/z)
    rw [norm_div, hzNorm] at hsin
    rw [norm_div, norm_mul, hzNorm]
    calc
      _ ≤ M * Real.sinh (‖t‖/r)/r := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul (hbound z hz) hsin (norm_nonneg _) hM) hr.le
      _ = _ := by ring
  have hi := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hpoint
  rw [heq]
  simpa only [neg_mul, norm_neg, smul_eq_mul,
    show r*(M/r*Real.sinh (‖t‖/r))=M*Real.sinh (‖t‖/r) by field_simp] using hi

end
end RHTower
