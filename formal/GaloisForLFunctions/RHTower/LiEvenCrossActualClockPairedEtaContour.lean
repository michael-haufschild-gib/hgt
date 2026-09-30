import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimeGammaContour
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPairedEtaSource
import GaloisForLFunctions.RHTower.LiClockPairedEtaCentralDisk
import GaloisForLFunctions.RHTower.LiClockCentralSineContourStability
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation

/-!
# The complete complex clock from literal paired eta arithmetic

The response retains all normalized actual moments and converges absolutely at
every complex clock. On a full central disk the completed paired-eta quotient
reconstructs the inverse-tilted prime--Gamma trace. One radius inside that disk
and the actual analytic germ gives the exact negative trace sine contour, with
no zero-location or global sign premise.
-/

open Complex Set Metric Filter Topology MeasureTheory
namespace RHTower
noncomputable section


/-- The literal complexification of one odd clock coefficient. -/
def liEvenCrossActualComplexClockResponseTerm (t : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ)^j * (normalizedPrimeArchMoment j : ℂ) * t^(2*j+1) /
    ((2*j+1).factorial : ℂ)

/-- The complete complex-clock response, with every actual moment retained. -/
def liEvenCrossActualComplexClockResponse (t : ℂ) : ℂ :=
  ∑' j : ℕ, liEvenCrossActualComplexClockResponseTerm t j

private theorem trace_zero : inverseTiltedPrimeGammaSourceTrace 0 = 0 :=
  inverseTiltedPrimeGammaSourceTrace_eventuallyEq_continuedPrimeArchSourceRelativeTrace.eq_of_nhds.trans
    continuedPrimeArchSourceRelativeTrace_zero

private theorem trace_eq_germ (z : ℂ) : inverseTiltedPrimeGammaSourceTrace z =
    -z * normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z := by
  simpa only [oddTracePreimage] using
    (congrFun (oddTracePreimage_normalizedTraceMomentGerm_eq
      inverseTiltedPrimeGammaSourceTrace trace_zero) z).symm

private theorem exists_germ_radius : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
    DiffContOnCl ℂ (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace)
      (ball (0 : ℂ) r) := by
  have hG := analyticAt_normalizedTraceMomentGerm analyticAt_inverseTiltedPrimeGammaSourceTrace
  obtain ⟨s, hs, hA⟩ := hG.exists_mem_nhds_analyticOnNhd
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r₀, hr₀, fun r _hr hrr₀ => ?_⟩
  exact hA.differentiableOn.diffContOnCl_ball
    ((closedBall_subset_ball hrr₀).trans hball)

private theorem contourTerm_eq (t : ℂ) (j : ℕ) :
    liClockCentralSineContourTerm (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace)
      t j = liEvenCrossActualComplexClockResponseTerm t j := by
  unfold liClockCentralSineContourTerm liEvenCrossActualComplexClockResponseTerm
  rw [normalizedTraceMomentGerm_inverseTiltedPrimeGammaSource_eventuallyEq.iteratedDeriv_eq (2*j)]
  rw [show iteratedDeriv (2*j) normalizedPrimeArchMomentGerm 0 =
      ((2*j).factorial : ℂ) * (normalizedPrimeArchMoment j : ℂ) by
    simpa only [normalizedPrimeArchMoment] using iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul j]
  have heven : ((2*j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*j)
  have hodd : ((2*j+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*j+1)
  field_simp

/-- Absolute convergence holds at every complex clock without a zero-location premise. -/
theorem summable_norm_liEvenCrossActualComplexClockResponseTerm (t : ℂ) :
    Summable (fun j : ℕ => ‖liEvenCrossActualComplexClockResponseTerm t j‖) := by
  obtain ⟨r₀, hr₀, hG⟩ := exists_germ_radius
  have hs := summable_norm_liClockCentralSineContourTerm
    (by linarith : 0 < r₀/2) (hG (r₀/2) (by linarith) (by linarith)) t
  exact hs.congr (fun j => congrArg norm (contourTerm_eq t j))

/-- The literal complete complex clock series is summable. -/
theorem summable_liEvenCrossActualComplexClockResponseTerm (t : ℂ) :
    Summable (liEvenCrossActualComplexClockResponseTerm t) :=
  (summable_norm_liEvenCrossActualComplexClockResponseTerm t).of_norm

/-- Restriction to real clocks is the already fixed actual clock response. -/
theorem liEvenCrossActualComplexClockResponse_ofReal (t : ℝ) :
    liEvenCrossActualComplexClockResponse (t : ℂ) = (liEvenCrossActualClockResponse t : ℂ) := by
  rw [liEvenCrossActualClockResponse_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro j
  simp only [liEvenCrossActualComplexClockResponseTerm, liEvenCrossActualClockResponseTerm,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_natCast]

/-- The closed arithmetic disk reconstructs the actual complete trace at every point. -/
theorem liEvenCrossActualClockPairedEtaSourceTrace_eq_of_norm_le {z : ℂ}
    (hz : ‖z‖ ≤ 1/128) :
    liEvenCrossActualClockPairedEtaSourceTrace z = inverseTiltedPrimeGammaSourceTrace z := by
  have hs : ‖(1/2 + z*I) - ((1/2 : ℝ) : ℂ)‖ ≤ 1/128 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      add_sub_cancel_left, norm_mul, norm_I, mul_one] using hz
  have hi := Complex.abs_im_le_norm z
  have hilo := (abs_le.mp (hi.trans hz))
  apply liEvenCrossActualClockPairedEtaSourceTrace_eq_inverseTiltedPrimeGammaSourceTrace
  · simp only [Complex.add_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith [hilo.2]
  · simp only [Complex.add_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith [hilo.1]
  · exact liClockPairedEtaCore_ne_zero_of_norm_sub_half_le hs


private theorem traceContour_eq_complexResponse {r : ℝ} (hr : 0 < r)
    (hG : DiffContOnCl ℂ (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace)
      (ball (0 : ℂ) r)) (t : ℂ) :
    liClockCentralTraceSineContour inverseTiltedPrimeGammaSourceTrace r t =
      liEvenCrossActualComplexClockResponse t := by
  have hcircle : (∮ z in C(0,r), inverseTiltedPrimeGammaSourceTrace z *
      Complex.sin (t/z) / z) =
      -(∮ z in C(0,r), normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z *
        Complex.sin (t/z)) := by
    calc
      _ = ∮ z in C(0,r), (-1 : ℂ) *
          (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z * Complex.sin (t/z)) := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        have hnz : z ≠ 0 := by
          intro hz0
          subst z
          simp at hz
          linarith
        dsimp only
        rw [trace_eq_germ z]
        field_simp
      _ = _ := by
        rw [circleIntegral.integral_const_mul]
        ring
  have hraw := liClockCentralSineContour_eq_tsum hr hG t
  have hsum : (∑' j : ℕ, liClockCentralSineContourTerm
      (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace) t j) =
      liEvenCrossActualComplexClockResponse t := by
    exact tsum_congr (contourTerm_eq t)
  rw [hsum] at hraw
  unfold liClockCentralTraceSineContour
  rw [hcircle, hraw]
  calc
    _ = ((2 * (Real.pi : ℂ) * I)⁻¹ * (2 * (Real.pi : ℂ) * I)) *
        liEvenCrossActualComplexClockResponse t := by ring
    _ = _ := by rw [inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- One full central arithmetic disk gives the exact completed eta contour at every complex clock.
Its radius is also chosen inside the actual analytic germ radius. -/
theorem exists_liEvenCrossActualClockPairedEtaContour_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ContinuousOn liEvenCrossActualClockPairedEtaSourceTrace (sphere (0 : ℂ) r) ∧
      ∀ t : ℂ, liClockCentralTraceSineContour liEvenCrossActualClockPairedEtaSourceTrace r t =
        liEvenCrossActualComplexClockResponse t := by
  obtain ⟨r₀, hr₀, hG⟩ := exists_germ_radius
  refine ⟨min r₀ (1/128), lt_min hr₀ (by norm_num), min_le_right _ _, fun r hr hrr₀ => ?_⟩
  have hGr := hG r hr (hrr₀.trans_le (min_le_left _ _))
  have hrsmall : r ≤ 1/128 := hrr₀.le.trans (min_le_right _ _)
  have hGc : ContinuousOn (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace)
      (sphere (0 : ℂ) r) := hGr.continuousOn_ball.mono sphere_subset_closedBall
  have hT : ContinuousOn inverseTiltedPrimeGammaSourceTrace (sphere (0 : ℂ) r) := by
    apply (continuousOn_id.neg.mul hGc).congr
    intro z _hz
    exact trace_eq_germ z
  have heq (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) :
      liEvenCrossActualClockPairedEtaSourceTrace z = inverseTiltedPrimeGammaSourceTrace z := by
    apply liEvenCrossActualClockPairedEtaSourceTrace_eq_of_norm_le
    have hzNorm : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    exact hzNorm.le.trans hrsmall
  refine ⟨hT.congr heq, fun t => ?_⟩
  rw [← traceContour_eq_complexResponse hr hGr t]
  unfold liClockCentralTraceSineContour
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  dsimp only
  rw [heq z hz]

end
end RHTower
