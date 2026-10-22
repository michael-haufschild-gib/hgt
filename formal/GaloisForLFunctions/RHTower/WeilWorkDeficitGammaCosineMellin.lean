import GaloisForLFunctions.RHTower.WeilWorkDeficitGammaKernelMellin
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCosineMellin
import GaloisForLFunctions.RHTower.Suzuki.SuzukiMellinConvolution

/-!
# Absolute Mellin transform of the actual reciprocal-Gamma cosine kernel

The rational kernel has zero total mass. Subtracting one from the cosine
therefore preserves its transform and permits absolute Mellin convolution
on the strip `-2 < re s < 0`. The corpus's cosine-difference Euler integral
then gives the exact transform, including its physical `2π` frequency scale.

The inverse-square moment records that normalization explicitly. Positive-strip
continuation, the actual Xi-density contour shift, and the spectral-deficit
producer remain separate obligations.
-/

noncomputable section
open Complex MeasureTheory Set
namespace RHTower.WeilWorkDeficitGamma

/-- The actual rational kernel's cosine transform, in frequency `2πx`. -/
def cosineKernel (N : ℕ) (x : ℝ) : ℂ :=
  ∫ u in Ioi (0:ℝ), kernel N u * (Real.cos (2*Real.pi*x*u) : ℂ)

private def rawCosine (N : ℕ) (x : ℝ) : ℂ :=
  ∫ u in Ioi (0:ℝ), kernel N u * (Real.cos (x*u) : ℂ)

private def cosineDifference (x : ℝ) : ℂ := 1-(Real.cos x : ℂ)

private def inverseKernel (N : ℕ) (y : ℝ) : ℂ := kernel N y⁻¹ / (y:ℂ)

private theorem raw_integrable (N : ℕ) (x : ℝ) :
    IntegrableOn (fun u : ℝ => kernel N u*(Real.cos (x*u):ℂ)) (Ioi 0) := by
  apply (integrable_kernel N).norm.mono' (by
    exact ((continuous_kernel N).mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with u
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

private theorem inverse_admission (N : ℕ) (s : {s : ℂ // -2<s.re ∧ s.re<0}) :
    MellinConvergent (inverseKernel N) s := by
  have h0 : MellinConvergent (kernel N) (1-(s:ℂ)) := by
    simpa only [MellinConvergent, smul_eq_mul, sub_sub_cancel_left] using
      integrable_kernel_strip N ⟨s, s.property.1, lt_trans s.property.2 (by norm_num)⟩
  have hi : MellinConvergent (fun y : ℝ => kernel N y⁻¹) ((s:ℂ)-1) := by
    have h := (MellinConvergent.comp_rpow (f := kernel N) (s := (s:ℂ)-1)
      (a := -1) (by norm_num)).mpr
        (show MellinConvergent (kernel N) (((s:ℂ)-1)/(-1:ℝ)) by
          convert h0 using 1; push_cast; ring)
    simpa only [Real.rpow_neg_one] using h
  have h := (MellinConvergent.cpow_smul
    (f := fun y : ℝ => kernel N y⁻¹) (s := (s:ℂ)) (a := -1)).mpr
      (by simpa only [sub_eq_add_neg] using hi)
  change MellinConvergent (fun y : ℝ => kernel N y⁻¹/(y:ℂ)) s
  simpa only [Complex.cpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

private theorem inverse_mellin (N : ℕ) (s : {s : ℂ // -2<s.re ∧ s.re<0}) :
    mellin (inverseKernel N) s = (s:ℂ)*((s:ℂ)-1)/clearingProduct (N+3) s := by
  have hf : inverseKernel N = fun y : ℝ => (y:ℂ)^(-1:ℂ) • kernel N y⁻¹ := by
    funext y
    simp only [inverseKernel, Complex.cpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hf, mellin_cpow_smul, mellin_comp_inv]
  simp only [mellin, smul_eq_mul]
  have he : -((s:ℂ)+ -1)-1 = -(s:ℂ) := by ring
  rw [he]
  exact kernel_mellin_strip N ⟨s, s.property.1, lt_trans s.property.2 (by norm_num)⟩

private theorem difference_admission (s : {s : ℂ // -2<s.re ∧ s.re<0}) :
    MellinConvergent cosineDifference s := by
  have h := RHTower.WeilHigherDenominator.integrable_cosineFractionalKernel
    (α := -(s:ℂ)) (by simpa using neg_pos.mpr s.property.2)
      (by simp only [Complex.neg_re]; linarith [s.property.1])
  have he : -1-(-(s:ℂ)) = (s:ℂ)-1 := by ring
  change IntegrableOn (fun x : ℝ => (1-(Real.cos x:ℂ))*(x:ℂ)^(-1-(-(s:ℂ))))
    (Ioi 0) at h
  simpa only [MellinConvergent, smul_eq_mul, cosineDifference, he, mul_comm] using h

private theorem difference_mellin (s : {s : ℂ // -2<s.re ∧ s.re<0}) :
    mellin cosineDifference s = (Real.pi:ℂ)/
      (2*Complex.Gamma (1-(s:ℂ))*Complex.sin (-(Real.pi:ℂ)*(s:ℂ)/2)) := by
  have h := RHTower.WeilHigherDenominator.integral_cosineFractionalKernel
    (α := -(s:ℂ)) (by simpa using neg_pos.mpr s.property.2)
      (by simp only [Complex.neg_re]; linarith [s.property.1])
  have he : -1-(-(s:ℂ)) = (s:ℂ)-1 := by ring
  have he' : -(s:ℂ)+1 = 1-(s:ℂ) := by ring
  have he'' : (Real.pi:ℂ)*(-(s:ℂ)/2) = -(Real.pi:ℂ)*(s:ℂ)/2 := by ring
  simpa only [mellin, smul_eq_mul, cosineDifference,
    RHTower.WeilHigherDenominator.cosineFractionalKernel, he, he', he'', mul_comm] using h

private theorem convolution_eq_neg (N : ℕ) (x : ℝ) :
    RHTower.positiveMellinConvolution (inverseKernel N) cosineDifference x =
      -rawCosine N x := by
  let H : ℝ → ℂ := fun u => kernel N u*cosineDifference (x*u)
  have hi := mellin_comp_inv H (-1)
  have he : (-1:ℂ)-1 = ((-2:ℤ):ℂ) := by norm_num
  simp only [mellin, neg_neg, sub_self, Complex.cpow_zero,
    he, Complex.cpow_intCast, smul_eq_mul, one_mul] at hi
  calc
    _ = ∫ y in Ioi (0:ℝ), (y:ℂ)^(-2:ℤ)*H y⁻¹ := by
      unfold RHTower.positiveMellinConvolution
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      simp only [inverseKernel, H, div_eq_mul_inv, zpow_neg, zpow_ofNat,
        pow_two]
      ring
    _ = ∫ u in Ioi (0:ℝ), H u := hi
    _ = (∫ u in Ioi (0:ℝ), kernel N u)-rawCosine N x := by
      rw [rawCosine, ← integral_sub (integrable_kernel N) (raw_integrable N x)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp [H, cosineDifference]
      ring
    _ = _ := by rw [integral_kernel_zero, zero_sub]

private theorem raw_hasMellin (N : ℕ) (s : {s : ℂ // -2<s.re ∧ s.re<0}) :
    HasMellin (rawCosine N) s
      (-((s:ℂ)*((s:ℂ)-1)/clearingProduct (N+3) s)*
        ((Real.pi:ℂ)/(2*Complex.Gamma (1-(s:ℂ))*
          Complex.sin (-(Real.pi:ℂ)*(s:ℂ)/2)))) := by
  have hf : Measurable (inverseKernel N) := by
    exact ((continuous_kernel N).measurable.comp measurable_inv).div Complex.continuous_ofReal.measurable
  have hg : Measurable cosineDifference := by unfold cosineDifference; fun_prop
  have h := RHTower.hasMellin_positiveMellinConvolution hf hg
    (inverse_admission N s) (difference_admission s)
  have he : RHTower.positiveMellinConvolution (inverseKernel N) cosineDifference =
      fun x => -rawCosine N x := funext (convolution_eq_neg N)
  rw [he, inverse_mellin, difference_mellin] at h
  constructor
  · have hn := h.1.neg
    change IntegrableOn (fun t : ℝ => -((t:ℂ)^((s:ℂ)-1) • (-rawCosine N t)))
      (Ioi 0) at hn
    simpa only [MellinConvergent, smul_neg, neg_neg] using hn
  · have hv := h.2
    simp only [mellin, smul_neg, integral_neg] at hv
    change mellin (rawCosine N) s = _
    change -mellin (rawCosine N) s = _ at hv
    rw [neg_eq_iff_eq_neg] at hv
    rw [hv]
    ring

/-- Absolute negative-strip Mellin identity for the actual cosine transform. -/
theorem hasMellin_cosineKernel (N : ℕ) (s : {s : ℂ // -2<s.re ∧ s.re<0}) :
    HasMellin (cosineKernel N) s
      (-(2*(Real.pi:ℂ))^(-(s:ℂ))*
        ((s:ℂ)*((s:ℂ)-1)/clearingProduct (N+3) s)*
        ((Real.pi:ℂ)/(2*Complex.Gamma (1-(s:ℂ))*
          Complex.sin (-(Real.pi:ℂ)*(s:ℂ)/2)))) := by
  have he : cosineKernel N = fun x => rawCosine N ((2*Real.pi)*x) := by
    funext x
    rfl
  have h := raw_hasMellin N s
  constructor
  · rw [he]
    exact (MellinConvergent.comp_mul_left (by positivity : 0<2*Real.pi)).mpr h.1
  · rw [he, mellin_comp_mul_left _ _ (by positivity : 0<2*Real.pi), h.2]
    simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring

/-- Exact inverse-square moment, with the physical frequency normalization retained. -/
theorem integral_cosineKernel_inv_sq (N : ℕ) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(-2:ℤ)*cosineKernel N x) =
      -2*(Real.pi:ℂ)^2/clearingProduct (N+3) (-1) := by
  have h := (hasMellin_cosineKernel N ⟨-1, by norm_num⟩).2
  have hG : Complex.Gamma (2:ℂ) = 1 := by norm_num
  have he : (-1:ℂ)-1 = ((-2:ℤ):ℂ) := by norm_num
  simp only [mellin, smul_eq_mul, he, Complex.cpow_intCast] at h
  norm_num only [neg_neg, Complex.cpow_one, neg_mul_neg, one_mul,
    sub_neg_eq_add, show (1:ℂ)+1 = 2 by norm_num, hG,
    Complex.sin_pi_div_two, mul_one, neg_mul, mul_neg] at h
  rw [h]
  ring

end RHTower.WeilWorkDeficitGamma
