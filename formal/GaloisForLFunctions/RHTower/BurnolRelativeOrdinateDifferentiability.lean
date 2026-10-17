import GaloisForLFunctions.RHTower.BurnolRelativeOrdinateFirstJet
import GaloisForLFunctions.RHTower.BurnolBaseNativeGenerator
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hilbert–Schmidt differentiation of the relative native Burnol orbit

For any bounded ordinate family, let `R` be the complete synthesis of the literal column
differences `f_i(kappa_i) - f_i(0)`, and let `H` be the relative first jet. Then
`(S_c R - R)/c` tends to `-H` in Hilbert–Schmidt norm as `c` tends to zero from the right.

The proof differentiates each actual semigroup eigenfeature. Contractivity bounds its
relative difference quotient by the relative first-jet column. The square-summable
correction from `BurnolRelativeOrdinateFirstJet` then supplies dominated convergence.
-/

open Complex ContinuousLinearMap Filter Set
open scoped BigOperators InnerProductSpace Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Source := lp (fun _ : RoutePPrimitiveIndex => ℂ) 2

def burnolRelativeOrdinateSourceField (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    routePBurnolHalfLineL2 :=
  routePPrimitiveBurnolWindowFeatureLp pe kappa - routePPrimitiveBurnolBaseField pe

theorem summable_norm_sq_burnolRelativeOrdinateSourceField (kappa : RoutePPrimitiveIndex → ℝ) :
    Summable fun pe => ‖burnolRelativeOrdinateSourceField pe (kappa pe)‖ ^ 2 := by
  refine (summable_norm_sq_routePPrimitiveBurnolBaseField.mul_left 4).of_nonneg_of_le
    (fun pe => sq_nonneg _) (fun pe => ?_)
  dsimp only [burnolRelativeOrdinateSourceField]
  have hn := norm_sub_le (routePPrimitiveBurnolWindowFeatureLp pe (kappa pe))
    (routePPrimitiveBurnolBaseField pe)
  have hs := norm_sq_burnolWindowFeatureLp_eq_base pe (kappa pe)
  nlinarith [norm_nonneg (routePPrimitiveBurnolWindowFeatureLp pe (kappa pe)),
    norm_nonneg (routePPrimitiveBurnolBaseField pe),
    norm_nonneg (routePPrimitiveBurnolWindowFeatureLp pe (kappa pe) -
      routePPrimitiveBurnolBaseField pe),
    sq_nonneg (‖routePPrimitiveBurnolWindowFeatureLp pe (kappa pe)‖ -
      ‖routePPrimitiveBurnolBaseField pe‖)]

def burnolRelativeOrdinateSource (kappa : RoutePPrimitiveIndex → ℝ) :
    Source →L[ℂ] routePBurnolHalfLineL2 :=
  (besselAnalysis (fun pe => burnolRelativeOrdinateSourceField pe (kappa pe))
    (isBesselFamily_of_summable_sq
      (summable_norm_sq_burnolRelativeOrdinateSourceField kappa))).adjoint

theorem burnolRelativeOrdinateSource_single (kappa : RoutePPrimitiveIndex → ℝ)
    (pe : RoutePPrimitiveIndex) (z : ℂ) :
    burnolRelativeOrdinateSource kappa (lp.single 2 pe z) =
      z • burnolRelativeOrdinateSourceField pe (kappa pe) :=
  besselSynthesis_single _ pe z

theorem isHilbertSchmidt_burnolRelativeOrdinateSource (kappa : RoutePPrimitiveIndex → ℝ) :
    IsHilbertSchmidt (burnolRelativeOrdinateSource kappa) := by
  refine isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis RoutePPrimitiveIndex) ?_
  simpa only [HilbertSchmidt.lpBasis_apply, burnolRelativeOrdinateSource_single, one_smul]
    using summable_norm_sq_burnolRelativeOrdinateSourceField kappa

private def ordinateColumnFlow (pe : RoutePPrimitiveIndex) (kappa t : ℝ) :
    routePBurnolHalfLineL2 :=
  Complex.exp (-(t : ℂ) *
    ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ))) •
      routePPrimitiveBurnolWindowFeatureLp pe kappa

private theorem ordinateColumnFlow_eq_shift (pe : RoutePPrimitiveIndex) (kappa : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ordinateColumnFlow pe kappa t =
      burnolWeightedShift t.toNNReal (routePPrimitiveBurnolWindowFeatureLp pe kappa) := by
  rw [burnolWeightedShift_windowFeatureLp, Real.coe_toNNReal t ht]
  simp only [ordinateColumnFlow, neg_mul]

private theorem ordinateColumnFlow_zero (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    ordinateColumnFlow pe kappa 0 = routePPrimitiveBurnolWindowFeatureLp pe kappa := by
  simp [ordinateColumnFlow]

private theorem hasDerivAt_ordinateColumnFlow (pe : RoutePPrimitiveIndex) (kappa t : ℝ) :
    HasDerivAt (ordinateColumnFlow pe kappa)
      (-(Complex.exp (-(t : ℂ) *
          ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ))) •
        burnolOrdinateFirstJetField pe kappa)) t := by
  let gamma := (xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)
  have hl : HasDerivAt (fun s : ℝ => -(s : ℂ) * gamma) (-gamma) t := by
    simpa only [Pi.neg_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, neg_mul, one_mul] using!
      (Complex.ofRealCLM.hasDerivAt (x := t)).neg.mul_const gamma
  have heq : -(Complex.exp (-(t : ℂ) * gamma) • burnolOrdinateFirstJetField pe kappa) =
      (Complex.exp (-(t : ℂ) * gamma) * (-gamma)) •
        routePPrimitiveBurnolWindowFeatureLp pe kappa := by
    dsimp only [burnolOrdinateFirstJetField, gamma]
    module
  dsimp only [gamma] at heq
  rw [heq]
  simpa only [ordinateColumnFlow, gamma] using!
    hl.cexp.smul_const (routePPrimitiveBurnolWindowFeatureLp pe kappa)

private theorem hasDerivAt_relativeColumnFlow (pe : RoutePPrimitiveIndex) (kappa : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => ordinateColumnFlow pe kappa s - ordinateColumnFlow pe 0 s)
      (-(burnolWeightedShift t.toNNReal (burnolRelativeOrdinateFirstJetField pe kappa))) t := by
  have heq : -(burnolWeightedShift t.toNNReal (burnolRelativeOrdinateFirstJetField pe kappa)) =
      -(Complex.exp (-(t : ℂ) *
          ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ))) •
        burnolOrdinateFirstJetField pe kappa) -
      -(Complex.exp (-(t : ℂ) *
          ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (0 : ℂ))) •
        burnolOrdinateFirstJetField pe 0) := by
    simp only [burnolRelativeOrdinateFirstJetField, burnolOrdinateFirstJetField,
      burnolBaseFirstJetField, routePPrimitiveBurnolBaseField, map_sub, map_smul,
      burnolWeightedShift_windowFeatureLp, Real.coe_toNNReal t ht,
      Complex.ofReal_zero, mul_zero, add_zero, neg_mul]
    module
  rw [heq]
  exact (hasDerivAt_ordinateColumnFlow pe kappa t).sub (hasDerivAt_ordinateColumnFlow pe 0 t)

private def relativeColumnQuotient (pe : RoutePPrimitiveIndex) (kappa c : ℝ) :
    routePBurnolHalfLineL2 :=
  c⁻¹ • (burnolWeightedShift c.toNNReal (burnolRelativeOrdinateSourceField pe kappa) -
    burnolRelativeOrdinateSourceField pe kappa)

private theorem relativeColumnQuotient_eq_slope (pe : RoutePPrimitiveIndex) (kappa : ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    relativeColumnQuotient pe kappa c =
      c⁻¹ • ((ordinateColumnFlow pe kappa c - ordinateColumnFlow pe 0 c) -
        (ordinateColumnFlow pe kappa 0 - ordinateColumnFlow pe 0 0)) := by
  simp only [relativeColumnQuotient, burnolRelativeOrdinateSourceField,
    routePPrimitiveBurnolBaseField, map_sub,
    ← ordinateColumnFlow_eq_shift pe kappa hc, ← ordinateColumnFlow_eq_shift pe 0 hc,
    ordinateColumnFlow_zero]

private theorem tendsto_relativeColumnQuotient (pe : RoutePPrimitiveIndex) (kappa : ℝ) :
    Tendsto (relativeColumnQuotient pe kappa) (𝓝[>] (0 : ℝ))
      (𝓝 (-burnolRelativeOrdinateFirstJetField pe kappa)) := by
  have hd := (hasDerivAt_relativeColumnFlow pe kappa (t := 0) (le_refl 0)).tendsto_slope_zero_right
  simp only [Real.toNNReal_zero, burnolWeightedShift_zero] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  simpa only [zero_add] using (relativeColumnQuotient_eq_slope pe kappa hc.le).symm

private theorem norm_relativeColumnQuotient_le (pe : RoutePPrimitiveIndex) (kappa : ℝ)
    {c : ℝ} (hc : 0 < c) :
    ‖relativeColumnQuotient pe kappa c‖ ≤ ‖burnolRelativeOrdinateFirstJetField pe kappa‖ := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 c) :=
    (hasDerivAt_relativeColumnFlow pe kappa ht.1).hasDerivWithinAt (s := Icc 0 c)
  have hb (t : ℝ) (_ht : t ∈ Ico 0 c) :
      ‖-(burnolWeightedShift t.toNNReal (burnolRelativeOrdinateFirstJetField pe kappa))‖ ≤
        ‖burnolRelativeOrdinateFirstJetField pe kappa‖ := by
    rw [norm_neg]
    calc
      _ ≤ ‖burnolWeightedShift t.toNNReal‖ * ‖burnolRelativeOrdinateFirstJetField pe kappa‖ :=
        (burnolWeightedShift t.toNNReal).le_opNorm _
      _ ≤ 1 * ‖burnolRelativeOrdinateFirstJetField pe kappa‖ :=
        mul_le_mul_of_nonneg_right (norm_burnolWeightedShift_le t.toNNReal) (norm_nonneg _)
      _ = _ := one_mul _
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb c (show c ∈ Icc 0 c from ⟨hc.le, le_rfl⟩)
  rw [relativeColumnQuotient_eq_slope pe kappa hc.le, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hc]
  simp only [sub_zero] at hm
  calc
    _ ≤ c⁻¹ * (‖burnolRelativeOrdinateFirstJetField pe kappa‖ * c) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hc.le)
    _ = _ := by field_simp

def burnolRelativeOrdinateDifferenceQuotient (kappa : RoutePPrimitiveIndex → ℝ) (c : ℝ) :
    Source →L[ℂ] routePBurnolHalfLineL2 :=
  c⁻¹ • (burnolWeightedShift c.toNNReal ∘L burnolRelativeOrdinateSource kappa -
    burnolRelativeOrdinateSource kappa)

private theorem relativeDifferenceQuotient_single (kappa : RoutePPrimitiveIndex → ℝ)
    (c : ℝ) (pe : RoutePPrimitiveIndex) :
    burnolRelativeOrdinateDifferenceQuotient kappa c (lp.single 2 pe 1) =
      relativeColumnQuotient pe (kappa pe) c := by
  simp only [burnolRelativeOrdinateDifferenceQuotient, smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply, burnolRelativeOrdinateSource_single, one_smul,
    relativeColumnQuotient]

theorem isHilbertSchmidt_burnolRelativeOrdinateDifferenceQuotient
    (kappa : RoutePPrimitiveIndex → ℝ) (c : ℝ) :
    IsHilbertSchmidt (burnolRelativeOrdinateDifferenceQuotient kappa c) := by
  have hs := isHilbertSchmidt_burnolRelativeOrdinateSource kappa
  have hdiff := (hs.comp_left (burnolWeightedShift c.toNNReal)).sub hs
  refine isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis RoutePPrimitiveIndex) ?_
  simpa only [burnolRelativeOrdinateDifferenceQuotient, smul_apply, norm_smul, mul_pow]
    using (hdiff.summable (HilbertSchmidt.lpBasis RoutePPrimitiveIndex)).mul_left (‖c⁻¹‖ ^ 2)

/-- Relative ordinate anchoring restores a native right derivative in Hilbert–Schmidt norm. -/
theorem tendsto_hsNormSq_burnolRelativeOrdinateDifferenceQuotient
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) :
    Tendsto (fun c => hsNormSq (burnolRelativeOrdinateDifferenceQuotient kappa c +
      burnolRelativeOrdinateFirstJetSynthesis kappa hkappa)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let f (c : ℝ) (pe : RoutePPrimitiveIndex) : ℝ :=
    ‖relativeColumnQuotient pe (kappa pe) c + burnolRelativeOrdinateFirstJetField pe (kappa pe)‖ ^ 2
  have hsum : Summable fun pe => 4 * ‖burnolRelativeOrdinateFirstJetField pe (kappa pe)‖ ^ 2 :=
    (summable_norm_sq_burnolRelativeOrdinateFirstJetField kappa hkappa).mul_left 4
  have hpoint (pe : RoutePPrimitiveIndex) :
      Tendsto (fun c => f c pe) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => burnolRelativeOrdinateFirstJetField pe (kappa pe))
        (𝓝[>] (0 : ℝ)) (𝓝 (burnolRelativeOrdinateFirstJetField pe (kappa pe))) :=
      tendsto_const_nhds
    simpa only [f, neg_add_cancel, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((tendsto_relativeColumnQuotient pe (kappa pe)).add hc).norm.pow 2
  have hbound : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ pe,
      ‖f c pe‖ ≤ 4 * ‖burnolRelativeOrdinateFirstJetField pe (kappa pe)‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with c hc pe
    have hq := norm_relativeColumnQuotient_le pe (kappa pe) hc
    have hn := norm_add_le (relativeColumnQuotient pe (kappa pe) c)
      (burnolRelativeOrdinateFirstJetField pe (kappa pe))
    simp only [f, Real.norm_eq_abs, abs_sq]
    nlinarith [norm_nonneg (relativeColumnQuotient pe (kappa pe) c +
      burnolRelativeOrdinateFirstJetField pe (kappa pe)),
      norm_nonneg (relativeColumnQuotient pe (kappa pe) c),
      norm_nonneg (burnolRelativeOrdinateFirstJetField pe (kappa pe))]
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have heq (c : ℝ) : hsNormSq (burnolRelativeOrdinateDifferenceQuotient kappa c +
      burnolRelativeOrdinateFirstJetSynthesis kappa hkappa) = ∑' pe, f c pe := by
    rw [hsNormSq_eq ((isHilbertSchmidt_burnolRelativeOrdinateDifferenceQuotient kappa c).add
      (isHilbertSchmidt_burnolRelativeOrdinateFirstJetSynthesis kappa hkappa))
        (HilbertSchmidt.lpBasis RoutePPrimitiveIndex)]
    simp only [HilbertSchmidt.lpBasis_apply, add_apply, relativeDifferenceQuotient_single,
      burnolRelativeOrdinateFirstJetSynthesis_single, one_smul, f]
  simpa only [← heq, tsum_zero] using hlim

theorem tendsto_hsNorm_burnolRelativeOrdinateDifferenceQuotient
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) :
    Tendsto (fun c => hsNorm (burnolRelativeOrdinateDifferenceQuotient kappa c +
      burnolRelativeOrdinateFirstJetSynthesis kappa hkappa)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [ContinuousLinearMap.hsNorm, Function.comp_apply, Real.sqrt_zero] using!
    (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_hsNormSq_burnolRelativeOrdinateDifferenceQuotient kappa hkappa)

end

end RHTower
