import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedResolvent
import GaloisForLFunctions.RHTower.LiClockSineImaginaryEnvelope
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integrated actual Xi clock

The literal interval primitive of the actual response equals the complete
reciprocal-frequency cosine defect, retaining every divisor multiplicity.
A squared-frequency compact majorant admits the entire complex sum before
restricting to real clocks. The sharp quadratic envelope and RH-conditional
nonnegativity do not supply an unconditional sign or an RH converse.
-/

open Complex Set MeasureTheory Filter
open scoped BigOperators

namespace RHTower
noncomputable section

/-- The literal oriented interval primitive of the complete actual response. -/
def liEvenCrossActualClockPrimitive (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, liEvenCrossActualClockResponse s

/-- The cosine defect of one actual analytic multiplicity copy. -/
def liEvenCrossActualClockCosineAtom (t : ℝ) (q : XiZeroCopy) : ℂ :=
  1 - Complex.cos ((t:ℂ) * (xiSpectralPoint q)⁻¹)

private theorem primitive_cosine_deriv (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1-Complex.cos ((s:ℂ)*w))
      (w*Complex.sin ((t:ℂ)*w)) t := by
  convert! (((Complex.hasDerivAt_cos ((t:ℂ)*w)).comp t
    ((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const w)).const_sub 1) using 1
  simp [mul_comm]

private theorem primitive_cosine_integral (w : ℂ) (t : ℝ) :
    (∫ s in (0:ℝ)..t, w*Complex.sin ((s:ℂ)*w)) =
      1-Complex.cos ((t:ℂ)*w) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => primitive_cosine_deriv w s)
    ((show Continuous (fun s : ℝ => w*Complex.sin ((s:ℂ)*w)) by fun_prop).intervalIntegrable 0 t)
  simpa using h

private theorem primitive_cosine_bound_nonneg {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    ‖1-Complex.cos ((t:ℂ)*w)‖ ≤ t^2/2*‖w‖^2*Real.exp (t*|w.im|) := by
  rw [← primitive_cosine_integral w t]
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) ht
    (g:=fun s : ℝ => s*‖w‖^2*Real.exp (t*|w.im|))
    (Filter.Eventually.of_forall (fun s hs => by
      refine (liClock_norm_mul_sin_le_imaginary_exp hs.1.le w).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)))
        (mul_nonneg hs.1.le (sq_nonneg _))))
    ((show Continuous (fun s : ℝ => s*‖w‖^2*Real.exp (t*|w.im|)) by fun_prop).intervalIntegrable 0 t)
  simpa only [intervalIntegral.integral_mul_const, integral_id,
    zero_pow (by omega : (2:ℕ) ≠ 0), sub_zero] using h

/-- Integrating the sine envelope retains the sharp quadratic factor at every real clock. -/
theorem liClock_norm_one_sub_cos_le_imaginary_exp (t : ℝ) (w : ℂ) :
    ‖1-Complex.cos ((t:ℂ)*w)‖ ≤ t^2/2*‖w‖^2*Real.exp (|t| * |w.im|) := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using primitive_cosine_bound_nonneg ht w
  · have h := primitive_cosine_bound_nonneg (neg_nonneg.mpr (le_of_not_ge ht)) w
    simpa only [Complex.ofReal_neg, neg_mul, Complex.cos_neg, neg_sq,
      abs_of_neg (lt_of_not_ge ht)] using h

private def primitiveFrequency (q : XiZeroCopy) : ℂ := (xiSpectralPoint q)⁻¹

private theorem primitive_mass_summable :
    Summable (fun q : XiZeroCopy => ‖primitiveFrequency q‖^2) := by
  simpa only [primitiveFrequency, norm_inv, one_div, inv_pow] using xiSpectralPoint_inv_sq_summable

private theorem primitive_frequency_norm_le_one (q : XiZeroCopy) : ‖primitiveFrequency q‖ ≤ 1 := by
  have h := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
  have heq : ‖xiZeroCopyReciprocalSquare q‖ = ‖primitiveFrequency q‖^2 := by
    simp [xiZeroCopyReciprocalSquare, primitiveFrequency, norm_pow]
  rw [heq] at h
  nlinarith [norm_nonneg (primitiveFrequency q)]

private def primitiveComplex (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, (1 - Complex.cos (z*primitiveFrequency q))

private theorem primitive_complex_bound (z : ℂ) :
    ‖1-Complex.cos z‖ ≤ ‖z‖^2/2*Real.exp |z.im| := by
  simpa only [Complex.ofReal_one, one_mul, one_pow, abs_one, div_mul_eq_mul_div]
    using liClock_norm_one_sub_cos_le_imaginary_exp 1 z

private theorem primitive_complex_majorant {R : ℝ} (_hR : 0 ≤ R)
    (q : XiZeroCopy) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖1-Complex.cos (z*primitiveFrequency q)‖ ≤
      ‖primitiveFrequency q‖^2*(R^2/2*Real.exp R) := by
  have hn : ‖z*primitiveFrequency q‖ ≤ R := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (primitive_frequency_norm_le_one q) (norm_nonneg z)).trans
      (by simpa using hz)
  have hi : |(z*primitiveFrequency q).im| ≤ R :=
    (Complex.abs_im_le_norm _).trans hn
  have h := primitive_complex_bound (z*primitiveFrequency q)
  rw [norm_mul, mul_pow] at h
  calc
    _ ≤ ‖z‖^2*‖primitiveFrequency q‖^2/2*Real.exp |(z*primitiveFrequency q).im| := h
    _ ≤ R^2*‖primitiveFrequency q‖^2/2*Real.exp R := by gcongr
    _ = _ := by ring

private theorem primitive_complex_summable (z : ℂ) :
    Summable (fun q : XiZeroCopy => ‖1-Complex.cos (z*primitiveFrequency q)‖) := by
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q =>
    primitive_complex_majorant (norm_nonneg z) q le_rfl)
    (primitive_mass_summable.mul_right (‖z‖^2/2*Real.exp ‖z‖))

/-- The full cosine-defect trace is absolutely summable without a zero-location premise. -/
theorem summable_norm_liEvenCrossActualClockCosineAtom (t : ℝ) :
    Summable (fun q : XiZeroCopy => ‖liEvenCrossActualClockCosineAtom t q‖) := by
  exact primitive_complex_summable (t:ℂ)

private theorem primitive_complex_hasDerivAt (z : ℂ) :
    HasDerivAt primitiveComplex (∑' q : XiZeroCopy,
      primitiveFrequency q*Complex.sin (z*primitiveFrequency q)) z := by
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsum := primitive_mass_summable.mul_right (R^2/2*Real.exp R)
  have hd (q : XiZeroCopy) (y : ℂ) : HasDerivAt
      (fun y : ℂ => 1-Complex.cos (y*primitiveFrequency q))
      (primitiveFrequency q*Complex.sin (y*primitiveFrequency q)) y := by
    convert! (((Complex.hasDerivAt_cos (y*primitiveFrequency q)).comp y
      ((hasDerivAt_id y).mul_const _)).const_sub 1) using 1
    simp [mul_comm]
  have hb q y (hy : y∈Metric.ball (0:ℂ) R) :=
    primitive_complex_majorant hR q ((by simpa using hy : ‖y‖<R).le)
  have hdiff : DifferentiableOn ℂ primitiveComplex (Metric.ball 0 R) :=
    Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun q y _ => (hd q y).differentiableAt.differentiableWithinAt)
      Metric.isOpen_ball hb
  have hs := Complex.hasSum_deriv_of_summable_norm (U:=Metric.ball (0:ℂ) R) hsum
    (fun q y _ => (hd q y).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball hb (z:=z) (by simp [R])
  simp_rw [(hd _ _).deriv] at hs
  rw [hs.tsum_eq]
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))).hasDerivAt

private theorem primitive_complex_real_deriv (t : ℝ) :
    HasDerivAt (fun s : ℝ => primitiveComplex (s:ℂ))
      (liEvenCrossActualClockResponse t:ℂ) t := by
  have h := (primitive_complex_hasDerivAt (t:ℂ)).comp_ofReal
  rw [liEvenCrossActualClockResponse_ofReal_eq_tsum_sine]
  exact h

/-- The literal primitive is the complete complex trace, including its real-axis reality. -/
theorem liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine (t : ℝ) :
    (liEvenCrossActualClockPrimitive t:ℂ) =
      ∑' q : XiZeroCopy, liEvenCrossActualClockCosineAtom t q := by
  have hz : primitiveComplex 0 = 0 := by simp [primitiveComplex]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => primitive_complex_real_deriv s)
    ((Complex.continuous_ofReal.comp continuous_liEvenCrossActualClockResponse).intervalIntegrable 0 t)
  simp only [Complex.ofReal_zero, hz, sub_zero] at h
  simpa [intervalIntegral.integral_ofReal, liEvenCrossActualClockPrimitive, primitiveComplex, primitiveFrequency,
    liEvenCrossActualClockCosineAtom] using h

/-- Endpoint FTC gives the actual response as the primitive's genuine derivative. -/
theorem hasDerivAt_liEvenCrossActualClockPrimitive (t : ℝ) :
    HasDerivAt liEvenCrossActualClockPrimitive (liEvenCrossActualClockResponse t) t :=
  (continuous_liEvenCrossActualClockResponse.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The complete entire complex trace makes its literal real primitive smooth. -/
theorem contDiff_liEvenCrossActualClockPrimitive :
    ContDiff ℝ (⊤:ℕ∞) liEvenCrossActualClockPrimitive := by
  have heq : liEvenCrossActualClockPrimitive = fun t : ℝ => (primitiveComplex (t:ℂ)).re := by
    funext t
    exact congrArg Complex.re (liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine t)
  rw [heq]
  exact (show Differentiable ℂ primitiveComplex from
    fun z => (primitive_complex_hasDerivAt z).differentiableAt).contDiff.real_of_complex

/-- The primitive vanishes at the origin and is even on the whole real line. -/
theorem liEvenCrossActualClockPrimitive_origin_even :
    liEvenCrossActualClockPrimitive 0 = 0 ∧
      ∀ t : ℝ, liEvenCrossActualClockPrimitive (-t) = liEvenCrossActualClockPrimitive t := by
  constructor
  · simp [liEvenCrossActualClockPrimitive]
  · intro t
    apply Complex.ofReal_injective
    rw [liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine,
      liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine]
    apply tsum_congr
    intro q
    simp [liEvenCrossActualClockCosineAtom]

private theorem primitive_mass_eq : (∑' q : XiZeroCopy, ‖primitiveFrequency q‖^2) =
    xiShiftAbsoluteMass 0 := by
  simp [xiShiftAbsoluteMass, primitiveFrequency, xiZeroCopyReciprocalSquare, norm_pow]

/-- Complete square-frequency mass and the actual strip give the quadratic exponential bound. -/
theorem abs_liEvenCrossActualClockPrimitive_le (t : ℝ) :
    |liEvenCrossActualClockPrimitive t| ≤
      xiShiftAbsoluteMass 0*t^2/2*Real.exp (|t|/300) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine]
  have hb (q : XiZeroCopy) : ‖liEvenCrossActualClockCosineAtom t q‖ ≤
      ‖primitiveFrequency q‖^2*(t^2/2*Real.exp (|t|/300)) := by
    have h := liClock_norm_one_sub_cos_le_imaginary_exp t (primitiveFrequency q)
    have he : Real.exp (|t| * |(primitiveFrequency q).im|) ≤ Real.exp (|t|/300) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left
        (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q).le (abs_nonneg t)
      simpa only [primitiveFrequency, div_eq_mul_inv, one_div, one_mul] using this
    exact h.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  calc
    _ ≤ ∑' q : XiZeroCopy, ‖liEvenCrossActualClockCosineAtom t q‖ :=
      norm_tsum_le_tsum_norm (summable_norm_liEvenCrossActualClockCosineAtom t)
    _ ≤ ∑' q : XiZeroCopy, ‖primitiveFrequency q‖^2*(t^2/2*Real.exp (|t|/300)) :=
      (summable_norm_liEvenCrossActualClockCosineAtom t).tsum_le_tsum hb
        (primitive_mass_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right, primitive_mass_eq]; ring

/-- Under RH every real-frequency cosine defect is nonnegative, including the full sum. -/
theorem liEvenCrossActualClockPrimitive_nonneg_of_rh (hRH : RiemannHypothesis) (t : ℝ) :
    0 ≤ liEvenCrossActualClockPrimitive t := by
  have h := congrArg Complex.re (liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine t)
  rw [Complex.re_tsum (summable_norm_liEvenCrossActualClockCosineAtom t).of_norm] at h
  rw [show liEvenCrossActualClockPrimitive t =
    ∑' q : XiZeroCopy, (liEvenCrossActualClockCosineAtom t q).re from h]
  apply tsum_nonneg
  intro q
  obtain ⟨a,ha⟩ := xiSpectralPoint_real_of_rh hRH q
  have hc := Real.cos_le_one (t*a⁻¹)
  simp only [liEvenCrossActualClockCosineAtom, ha, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re]
  linarith

end
end RHTower
