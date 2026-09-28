import GaloisForLFunctions.RHTower.CCMExponentialRampCenteredAge

/-!
# Terminal entropy in the signed arithmetic balance

The oriented terminal current is nonnegative in both orientations. Its exact
integral is an exponential entropy of the quantile-boundary mismatch. Together
with the nonpositive centered bulk remainder, this retains the source and
dissipation signs before any absolute-value estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace RHTower

def ccmExponentialRampTerminalEntropyKernel (d : ℝ) : ℝ :=
  1+(d-1)*Real.exp d

theorem ccmExponentialRampTerminalEntropyKernel_nonneg (d : ℝ) :
    0 ≤ ccmExponentialRampTerminalEntropyKernel d := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-d)) (Real.exp_pos d).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  unfold ccmExponentialRampTerminalEntropyKernel
  nlinarith only [h]

@[simp] theorem ccmExponentialRampTerminalEntropyKernel_zero :
    ccmExponentialRampTerminalEntropyKernel 0 = 0 := by
  simp [ccmExponentialRampTerminalEntropyKernel]

theorem hasDerivAt_ccmExponentialRampTerminalEntropyKernel (d : ℝ) :
    HasDerivAt ccmExponentialRampTerminalEntropyKernel (d*Real.exp d) d := by
  convert! (((hasDerivAt_id d).sub_const 1).mul (Real.hasDerivAt_exp d)).const_add 1 using 1
  simp only [id_eq]
  ring

theorem ccmExponentialRampTerminalEntropyKernel_le (d : ℝ) :
    ccmExponentialRampTerminalEntropyKernel d ≤ d^2*Real.exp |d| := by
  have hb (s : ℝ) (hs : s ∈ Icc (-|d|) |d|) :
      ‖s*Real.exp s‖ ≤ |d| * Real.exp |d| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (abs_le.mpr hs) (Real.exp_le_exp.mpr hs.2)
      (Real.exp_pos _).le (abs_nonneg d)
  have h := (convex_Icc (-|d|) |d|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hasDerivAt_ccmExponentialRampTerminalEntropyKernel s).hasDerivWithinAt) hb
    (show (0 : ℝ) ∈ Icc (-|d|) |d| from ⟨neg_nonpos.mpr (abs_nonneg d), abs_nonneg d⟩)
    (show d ∈ Icc (-|d|) |d| from ⟨neg_abs_le d, le_abs_self d⟩)
  calc
    _ ≤ (|d| * Real.exp |d|)*|d| := by
      simpa only [ccmExponentialRampTerminalEntropyKernel_zero, sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (ccmExponentialRampTerminalEntropyKernel_nonneg d)] using h
    _ = _ := by rw [← sq_abs d]; ring

def ccmExponentialRampTerminalEntropyDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmExponentialRampDerivativeWeight r*ccmActualHeadQuantileTerminalDisplacementDensity T N r

theorem ccmExponentialRampTerminalEntropyDensity_nonneg (T : ℝ) (N : ℕ) (r : ℝ) :
    0 ≤ ccmExponentialRampTerminalEntropyDensity T N r := by
  unfold ccmExponentialRampTerminalEntropyDensity ccmExponentialRampDerivativeWeight
    ccmActualHeadQuantileTerminalDisplacementDensity
  by_cases hb : ccmOutgoingPrimeQuantileBoundary N ≤ T
  · rw [if_pos hb]
    by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary N-T) 0
    · rw [indicator_of_mem hr]
      exact mul_nonneg (mul_nonneg (neg_nonneg.mpr hr.2) (Real.exp_pos _).le) (Real.exp_pos _).le
    · rw [indicator_of_notMem hr, mul_zero]
  · rw [if_neg hb]
    by_cases hr : r ∈ Ioc 0 (ccmOutgoingPrimeQuantileBoundary N-T)
    · rw [indicator_of_mem hr]
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.1.le) (Real.exp_pos _).le)
        (neg_nonpos.mpr (Real.exp_pos _).le)
    · simp only [indicator_of_notMem hr, neg_zero, mul_zero, le_refl]

theorem integrable_ccmExponentialRampTerminalEntropyDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmExponentialRampTerminalEntropyDensity T N) := by
  have h := integrable_ccmActualHeadQuantileTerminalDensity_continuousTest T N
    ⟨ccmExponentialRampDerivativeWeight, by unfold ccmExponentialRampDerivativeWeight; fun_prop⟩
  simpa only [ccmExponentialRampTerminalEntropyDensity, ContinuousMap.coe_mk, mul_comm] using h

def ccmExponentialRampTerminalEntropy (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, ccmExponentialRampTerminalEntropyDensity T N r

theorem ccmExponentialRampTerminalEntropy_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmExponentialRampTerminalEntropy T N :=
  integral_nonneg (ccmExponentialRampTerminalEntropyDensity_nonneg T N)

/-- The terminal entropy is exact, including heads whose boundary overshoots physical time. -/
theorem ccmExponentialRampTerminalEntropy_eq_boundaryMismatch (T : ℝ) (N : ℕ) :
    ccmExponentialRampTerminalEntropy T N = Real.exp (T/2)*
      ccmExponentialRampTerminalEntropyKernel (ccmOutgoingPrimeQuantileBoundary N-T) := by
  have he (h : ℝ) : Real.exp (h/2)*ccmExponentialRampDerivativeWeight (h-T) =
      Real.exp (-T/2)*(Real.exp h*(T-h)) := by
    have hx : Real.exp (h/2)*Real.exp ((h-T)/2) = Real.exp (-T/2)*Real.exp h := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    unfold ccmExponentialRampDerivativeWeight
    calc
      _ = (Real.exp (h/2)*Real.exp ((h-T)/2))*(T-h) := by ring
      _ = _ := by rw [hx]; ring
  have hd (h : ℝ) : HasDerivAt (fun u : ℝ => Real.exp u*(T-u+1))
      (Real.exp h*(T-h)) h := by
    convert! (Real.hasDerivAt_exp h).mul (((hasDerivAt_id h).const_sub T).add_const 1) using 1
    simp only [id_eq]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun h _ => hd h)
    ((by fun_prop : Continuous (fun h : ℝ => Real.exp h*(T-h))).intervalIntegrable
      (ccmOutgoingPrimeQuantileBoundary N) T)
  unfold ccmExponentialRampTerminalEntropy ccmExponentialRampTerminalEntropyDensity
  simp_rw [mul_comm (ccmExponentialRampDerivativeWeight _)]
  rw [integral_ccmActualHeadQuantileTerminalDensity_mul]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, hi]
  have hx : Real.exp (-T/2)*Real.exp T = Real.exp (T/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hy : Real.exp (-T/2)*Real.exp (ccmOutgoingPrimeQuantileBoundary N) =
      Real.exp (T/2)*Real.exp (ccmOutgoingPrimeQuantileBoundary N-T) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold ccmExponentialRampTerminalEntropyKernel
  linear_combination hx+(ccmOutgoingPrimeQuantileBoundary N-T-1)*hy

theorem ccmExponentialRampTerminalEntropy_le_quadraticMismatch (T : ℝ) (N : ℕ) :
    ccmExponentialRampTerminalEntropy T N ≤ Real.exp (T/2)*
      ((ccmOutgoingPrimeQuantileBoundary N-T)^2*Real.exp |ccmOutgoingPrimeQuantileBoundary N-T|) := by
  rw [ccmExponentialRampTerminalEntropy_eq_boundaryMismatch]
  exact mul_le_mul_of_nonneg_left (ccmExponentialRampTerminalEntropyKernel_le _) (Real.exp_pos _).le

end RHTower
