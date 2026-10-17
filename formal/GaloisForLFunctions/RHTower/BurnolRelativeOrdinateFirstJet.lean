import GaloisForLFunctions.RHTower.BurnolBaseFirstJetNoncompact

/-!
# The ordinate-independent essential part of the native Burnol first jet

Changing each prime-depth ordinate by a bounded real amount changes the literal native
first-jet columns by a square-summable family. Thus every bounded ordinate family has a
bounded, noncompact first-jet synthesis, and any two such syntheses differ by a
Hilbert–Schmidt operator. The original amplitudes and all mixed Gram entries are retained.

This concerns ordinate clocks. Gaussian coefficient damping is a different operation.
-/

open Complex ContinuousLinearMap
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem inner_routePPrimitiveBurnolWindowFeatureLp
    (pe tau : RoutePPrimitiveIndex) (kappa nu : ℝ) :
    ⟪routePPrimitiveBurnolWindowFeatureLp pe kappa,
      routePPrimitiveBurnolWindowFeatureLp tau nu⟫_ℂ =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        routePBaseCauchyCubicKernel 1 (xiGammaEulerPrimitiveLogFrequency pe)
          (xiGammaEulerPrimitiveLogFrequency tau) (nu - kappa) *
        star (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat tau)) := by
  unfold routePPrimitiveBurnolWindowFeatureLp routePBurnolHalfLineL2Of
  rw [inner_toLp_routePBurnolHalfLine_eq_pairing]
  exact integral_star_routePPrimitiveBurnolWindowFeature_mul pe tau kappa nu

theorem norm_sq_burnolWindowFeatureLp_eq_base (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    ‖routePPrimitiveBurnolWindowFeatureLp pe kappa‖ ^ 2 =
      ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 := by
  have h : ⟪routePPrimitiveBurnolWindowFeatureLp pe kappa,
      routePPrimitiveBurnolWindowFeatureLp pe kappa⟫_ℂ =
      ⟪routePPrimitiveBurnolBaseField pe, routePPrimitiveBurnolBaseField pe⟫_ℂ := by
    rw [inner_routePPrimitiveBurnolWindowFeatureLp, inner_routePPrimitiveBurnolBaseField,
      sub_self]
  have hr := congrArg Complex.re h
  change (inner ℂ (routePPrimitiveBurnolWindowFeatureLp pe kappa)
    (routePPrimitiveBurnolWindowFeatureLp pe kappa)).re =
    (inner ℂ (routePPrimitiveBurnolBaseField pe) (routePPrimitiveBurnolBaseField pe)).re at hr
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans
    (hr.trans (inner_self_eq_norm_sq (𝕜 := ℂ) _))

private theorem reciprocal_cubic_re (t : ℝ) :
    ((1 : ℂ) / (1 + I * (t : ℂ)) ^ 3).re =
      (1 - 3 * t ^ 2) / (1 + t ^ 2) ^ 3 := by
  rw [one_div, ← inv_pow]
  simp only [pow_succ, pow_zero, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  field_simp
  ring

private theorem reciprocal_cubic_loss_le (t : ℝ) :
    1 - ((1 : ℂ) / (1 + I * (t : ℂ)) ^ 3).re ≤ 6 * t ^ 2 := by
  rw [reciprocal_cubic_re]
  have hd : 0 < 1 + t ^ 2 := by positivity
  have he : 1 - (1 - 3 * t ^ 2) / (1 + t ^ 2) ^ 3 =
      ((1 + t ^ 2) ^ 3 - (1 - 3 * t ^ 2)) / (1 + t ^ 2) ^ 3 := by
    field_simp
  rw [he]
  apply (div_le_iff₀ (pow_pos hd 3)).2
  nlinarith [sq_nonneg (t ^ 2), sq_nonneg (t ^ 3), sq_nonneg (t ^ 4)]

private theorem base_cubic_clock_rescaling {a : ℝ} (ha : 0 < a) (kappa : ℝ) :
    routePBaseCauchyCubicKernel 1 a a kappa =
      routePBaseCauchyCubicKernel 1 a a 0 *
        ((1 : ℂ) / (1 + I * ((kappa / (2 * a) : ℝ) : ℂ)) ^ 3) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hz : (1 : ℂ) + I * ((kappa / (2 * a) : ℝ) : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.zero_re,
      zero_mul, mul_zero, sub_zero, add_zero] at this
  have hw : (a : ℂ) + a + I * (kappa : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold routePBaseCauchyCubicKernel routePCollisionPairFrequency
  push_cast
  simp only [one_pow, mul_one, one_mul]
  field_simp [ha', hz, hw]
  ring

theorem inner_burnolWindowFeatureLp_base_rescaling (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    ⟪routePPrimitiveBurnolBaseField pe, routePPrimitiveBurnolWindowFeatureLp pe kappa⟫_ℂ =
      ((‖routePPrimitiveBurnolBaseField pe‖ ^ 2 : ℝ) : ℂ) *
        ((1 : ℂ) / (1 + I *
          ((kappa / (2 * xiGammaEulerPrimitiveLogFrequency pe) : ℝ) : ℂ)) ^ 3) := by
  change ⟪routePPrimitiveBurnolWindowFeatureLp pe 0,
    routePPrimitiveBurnolWindowFeatureLp pe kappa⟫_ℂ = _
  rw [inner_routePPrimitiveBurnolWindowFeatureLp, sub_zero,
    base_cubic_clock_rescaling (xiGammaEulerPrimitiveLogFrequency_pos pe)]
  have h := inner_routePPrimitiveBurnolBaseField pe pe
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖routePPrimitiveBurnolBaseField pe‖ ^ 2 : ℝ) : ℂ) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        routePBaseCauchyCubicKernel 1 (xiGammaEulerPrimitiveLogFrequency pe)
          (xiGammaEulerPrimitiveLogFrequency pe) 0 *
        star (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe)) := by
    simpa only [Complex.ofReal_pow] using! h
  rw [h']
  ring

/-- The phase difference supplies the spatial factor missing from the absolute first jet. -/
theorem norm_sq_burnolOrdinateDifference_mul_clock_le
    (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    (xiGammaEulerPrimitiveLogFrequency pe) ^ 2 *
      ‖routePPrimitiveBurnolWindowFeatureLp pe kappa - routePPrimitiveBurnolBaseField pe‖ ^ 2 ≤
      3 * kappa ^ 2 * ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 := by
  let t := kappa / (2 * xiGammaEulerPrimitiveLogFrequency pe)
  have hnorm :
      ‖routePPrimitiveBurnolWindowFeatureLp pe kappa - routePPrimitiveBurnolBaseField pe‖ ^ 2 ≤
        12 * t ^ 2 * ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 := by
    rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ), norm_sq_burnolWindowFeatureLp_eq_base,
      inner_burnolWindowFeatureLp_base_rescaling]
    change ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 -
      2 * (((‖routePPrimitiveBurnolBaseField pe‖ ^ 2 : ℝ) : ℂ) *
        ((1 : ℂ) / (1 + I * (t : ℂ)) ^ 3)).re +
      ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 ≤ _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h := mul_le_mul_of_nonneg_right (reciprocal_cubic_loss_le t)
      (sq_nonneg ‖routePPrimitiveBurnolBaseField pe‖)
    dsimp only [t] at h ⊢
    nlinarith
  have hlam := xiGammaEulerPrimitiveLogFrequency_pos pe
  calc
    _ ≤ (xiGammaEulerPrimitiveLogFrequency pe) ^ 2 *
        (12 * t ^ 2 * ‖routePPrimitiveBurnolBaseField pe‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
    _ = _ := by dsimp only [t]; field_simp; ring

/-- Native derivative column at the indicated ordinate. -/
def burnolOrdinateFirstJetField (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    routePBurnolHalfLineL2 :=
  ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)) •
    routePPrimitiveBurnolWindowFeatureLp pe kappa

def burnolRelativeOrdinateFirstJetField (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    routePBurnolHalfLineL2 :=
  burnolOrdinateFirstJetField pe kappa - burnolBaseFirstJetField pe

theorem norm_sq_burnolRelativeOrdinateFirstJetField_le
    (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    ‖burnolRelativeOrdinateFirstJetField pe kappa‖ ^ 2 ≤
      8 * kappa ^ 2 * ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 := by
  let u := (xiGammaEulerPrimitiveLogFrequency pe : ℂ) •
    (routePPrimitiveBurnolWindowFeatureLp pe kappa - routePPrimitiveBurnolBaseField pe)
  let v := (I * (kappa : ℂ)) • routePPrimitiveBurnolWindowFeatureLp pe kappa
  have heq : burnolRelativeOrdinateFirstJetField pe kappa = u + v := by
    dsimp [burnolRelativeOrdinateFirstJetField, burnolOrdinateFirstJetField,
      burnolBaseFirstJetField, u, v]
    module
  have hu : ‖u‖ ^ 2 ≤ 3 * kappa ^ 2 * ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 := by
    simpa only [u, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      norm_sq_burnolOrdinateDifference_mul_clock_le pe kappa
  have hv : ‖v‖ ^ 2 = kappa ^ 2 * ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 := by
    simp only [v, norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, norm_sq_burnolWindowFeatureLp_eq_base]
  rw [heq]
  have hn := norm_add_le u v
  have hn2 := sq_nonneg (‖u‖ - ‖v‖)
  nlinarith [norm_nonneg (u + v), norm_nonneg u, norm_nonneg v]

theorem summable_norm_sq_burnolRelativeOrdinateFirstJetField
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) :
    Summable fun pe => ‖burnolRelativeOrdinateFirstJetField pe (kappa pe)‖ ^ 2 := by
  obtain ⟨M, hM⟩ := hkappa
  refine (summable_norm_sq_routePPrimitiveBurnolBaseField.mul_left (8 * M ^ 2)).of_nonneg_of_le
    (fun pe => sq_nonneg _) (fun pe => ?_)
  have hs : (kappa pe) ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (kappa pe)) (hM pe) 2
  exact (norm_sq_burnolRelativeOrdinateFirstJetField_le pe (kappa pe)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (sq_nonneg _))

private abbrev Source := lp (fun _ : RoutePPrimitiveIndex => ℂ) 2

/-- The Hilbert–Schmidt correction to the base first jet. -/
def burnolRelativeOrdinateFirstJetSynthesis (kappa : RoutePPrimitiveIndex → ℝ)
    (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) : Source →L[ℂ] routePBurnolHalfLineL2 :=
  (besselAnalysis (fun pe => burnolRelativeOrdinateFirstJetField pe (kappa pe))
    (isBesselFamily_of_summable_sq
      (summable_norm_sq_burnolRelativeOrdinateFirstJetField kappa hkappa))).adjoint

theorem burnolRelativeOrdinateFirstJetSynthesis_single (kappa : RoutePPrimitiveIndex → ℝ)
    (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) (pe : RoutePPrimitiveIndex) (z : ℂ) :
    burnolRelativeOrdinateFirstJetSynthesis kappa hkappa (lp.single 2 pe z) =
      z • burnolRelativeOrdinateFirstJetField pe (kappa pe) :=
  besselSynthesis_single _ pe z

theorem isHilbertSchmidt_burnolRelativeOrdinateFirstJetSynthesis
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) :
    IsHilbertSchmidt (burnolRelativeOrdinateFirstJetSynthesis kappa hkappa) := by
  refine isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis RoutePPrimitiveIndex) ?_
  simpa only [HilbertSchmidt.lpBasis_apply, burnolRelativeOrdinateFirstJetSynthesis_single,
    one_smul] using summable_norm_sq_burnolRelativeOrdinateFirstJetField kappa hkappa

/-- Complete native first-jet synthesis for any bounded family of ordinate clocks. -/
def burnolOrdinateFirstJetSynthesis (kappa : RoutePPrimitiveIndex → ℝ)
    (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) : Source →L[ℂ] routePBurnolHalfLineL2 :=
  burnolBaseFirstJetSynthesis + burnolRelativeOrdinateFirstJetSynthesis kappa hkappa

theorem burnolOrdinateFirstJetSynthesis_single (kappa : RoutePPrimitiveIndex → ℝ)
    (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) (pe : RoutePPrimitiveIndex) (z : ℂ) :
    burnolOrdinateFirstJetSynthesis kappa hkappa (lp.single 2 pe z) =
      z • burnolOrdinateFirstJetField pe (kappa pe) := by
  simp only [burnolOrdinateFirstJetSynthesis, add_apply,
    burnolBaseFirstJetSynthesis_single, burnolRelativeOrdinateFirstJetSynthesis_single,
    burnolRelativeOrdinateFirstJetField]
  module

/-- All mixed entries are the literal differentiated Burnol Gram. -/
theorem inner_burnolOrdinateFirstJetField
    (pe tau : RoutePPrimitiveIndex) (kappa nu : ℝ) :
    ⟪burnolOrdinateFirstJetField pe kappa, burnolOrdinateFirstJetField tau nu⟫_ℂ =
      star ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)) *
        ((xiGammaEulerPrimitiveLogFrequency tau : ℂ) + I * (nu : ℂ)) *
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        routePBaseCauchyCubicKernel 1 (xiGammaEulerPrimitiveLogFrequency pe)
          (xiGammaEulerPrimitiveLogFrequency tau) (nu - kappa) *
        star (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat tau)) := by
  rw [burnolOrdinateFirstJetField, burnolOrdinateFirstJetField,
    inner_smul_left, inner_smul_right, inner_routePPrimitiveBurnolWindowFeatureLp]
  simp only [starRingEnd_apply]
  ring

/-- The essential first jet is independent of every bounded choice of source ordinates. -/
theorem isHilbertSchmidt_burnolOrdinateFirstJetSynthesis_sub
    (kappa nu : RoutePPrimitiveIndex → ℝ)
    (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) (hnu : ∃ M : ℝ, ∀ pe, |nu pe| ≤ M) :
    IsHilbertSchmidt
      (burnolOrdinateFirstJetSynthesis kappa hkappa - burnolOrdinateFirstJetSynthesis nu hnu) := by
  have heq : burnolOrdinateFirstJetSynthesis kappa hkappa -
      burnolOrdinateFirstJetSynthesis nu hnu =
      burnolRelativeOrdinateFirstJetSynthesis kappa hkappa -
        burnolRelativeOrdinateFirstJetSynthesis nu hnu := by
    unfold burnolOrdinateFirstJetSynthesis
    abel
  rw [heq]
  exact (isHilbertSchmidt_burnolRelativeOrdinateFirstJetSynthesis kappa hkappa).sub
    (isHilbertSchmidt_burnolRelativeOrdinateFirstJetSynthesis nu hnu)

theorem not_isCompactOperator_burnolOrdinateFirstJetSynthesis
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) :
    ¬ IsCompactOperator (burnolOrdinateFirstJetSynthesis kappa hkappa) := by
  intro h
  have hc := h.sub
    (isHilbertSchmidt_burnolRelativeOrdinateFirstJetSynthesis kappa hkappa).isCompactOperator
  apply not_isCompactOperator_burnolBaseFirstJetSynthesis
  change IsCompactOperator (fun x : Source =>
    (burnolBaseFirstJetSynthesis x + burnolRelativeOrdinateFirstJetSynthesis kappa hkappa x) -
      burnolRelativeOrdinateFirstJetSynthesis kappa hkappa x) at hc
  simpa only [add_sub_cancel_right] using hc

end

end RHTower
