import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OriginDegreeDoesNotDescendThroughPoissonBoundaries
import GaloisForLFunctions.RHTower.FrankensteinMeyerHalfDensityL2KoszulDescent
import GaloisForLFunctions.HTGeometry.L2TranslationCyclicity
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# Genuine Poisson boundaries are dense for origin square mass

The canonical half-density map identifies origin square mass with the ordinary
L2 norm. The Xi-cap boundary has a Fourier transform nonzero almost everywhere,
so its centered-flow orbit is cyclic. Genuine boundaries are therefore dense in
this Hilbert completion, although their all-weight source quotient is nontrivial.
-/

noncomputable section
open Complex MeasureTheory Set RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private def criticalFourierPoint (t : ℝ) : ℂ :=
  1 / 2 - ((2 * Real.pi * t : ℝ) : ℂ) * I

private theorem criticalFourierPoint_injective : Function.Injective criticalFourierPoint := by
  intro a b hab
  have hmul : ((2 * Real.pi * a : ℝ) : ℂ) * I = ((2 * Real.pi * b : ℝ) : ℂ) * I := by
    simpa only [criticalFourierPoint, sub_right_inj] using hab
  have hreal := Complex.ofReal_injective (mul_right_cancel₀ I_ne_zero hmul)
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hreal

private theorem ae_xi_criticalFourierPoint_ne_zero :
    ∀ᵐ t : ℝ, xi (criticalFourierPoint t) ≠ 0 := by
  have hc := (_root_.HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd
    xi_analyticOnNhd_univ ⟨1, by rw [xi_one]; norm_num⟩).preimage criticalFourierPoint_injective
  have hz : volume {t : ℝ | xi (criticalFourierPoint t) = 0} = 0 := hc.measure_zero volume
  rw [ae_iff]
  simpa only [not_not] using hz

/-- The canonical half-density source has the exact critical-line Mellin Fourier profile. -/
theorem meyerHalfDensityFunction_fourier (g : DeningerMeyerStrongLogTarget) (w : ℝ) :
    𝓕 (deningerMeyerHalfDensityL2Function g) w =
      deningerMeyerStrongLogMellin g (1 / 2 - ((2 * Real.pi * w : ℝ) : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, deningerMeyerStrongLogMellin]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [deningerMeyerHalfDensityL2Function, deningerMeyerStrongLogMellinJet,
    pow_zero, one_mul, smul_eq_mul, Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The completed Fourier transform retains the same source formula almost everywhere. -/
theorem meyerHalfDensityL2_fourier_ae (g : DeningerMeyerStrongLogTarget) :
    (𝓕 (deningerMeyerHalfDensityL2LM g) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun w : ℝ => deningerMeyerStrongLogMellin g
        (1 / 2 - ((2 * Real.pi * w : ℝ) : ℂ) * I) := by
  have hcoe : (deningerMeyerHalfDensityL2LM g : ℝ → ℂ) =ᵐ[volume]
      deningerMeyerHalfDensityL2Function g := deningerMeyerHalfDensityL2_coeFn g
  have hi : Integrable (deningerMeyerHalfDensityL2LM g : ℝ → ℂ) :=
    (integrable_deningerMeyerHalfDensityL2Function g).congr hcoe.symm
  have hf := GaloisForLFunctions.HTGeometry.fourierL2_coeFn_ae_eq_fourier
    (deningerMeyerHalfDensityL2LM g) hi
  have hclassic (w : ℝ) :
      𝓕 (deningerMeyerHalfDensityL2LM g : ℝ → ℂ) w =
        𝓕 (deningerMeyerHalfDensityL2Function g) w := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards [hcoe] with t ht
    exact congrArg
      (fun z : ℂ => Complex.exp (((-2 * Real.pi * t * w : ℝ) : ℂ) * I) • z) ht
  filter_upwards [hf] with w hw
  change (GaloisForLFunctions.HTGeometry.fourierL2 ℝ (deningerMeyerHalfDensityL2LM g)) w = _
  rw [hw, hclassic, meyerHalfDensityFunction_fourier]

/-- Origin square degree is exactly the squared norm of the existing half-density embedding. -/
theorem meyerHalfDensityL2_norm_sq (g : DeningerMeyerStrongLogTarget) :
    ‖deningerMeyerHalfDensityL2LM g‖ ^ 2 =
      (meyerOriginDegree (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))).re := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq, meyerOriginDegree_sharp_square, Complex.ofReal_re]
  apply integral_congr_ae
  filter_upwards [deningerMeyerHalfDensityL2_coeFn g] with t ht
  change ‖(deningerMeyerHalfDensityL2 g : ℝ → ℂ) t‖ ^ 2 = _
  rw [ht, deningerMeyerHalfDensityL2Function, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← Complex.normSq_eq_norm_sq]
  have he : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]

/-- All real translates of the actual Xi-cap boundary form a cyclic L2 family. -/
theorem meyerXiBoundary_halfDensity_translation_cyclic :
    IsCyclicFamily (𝕜 := ℂ) (fun a : ℝ => MellinL2.additiveTranslationUnitary a
      (deningerMeyerHalfDensityL2LM (deningerMeyerStrongLogSumLM deningerMeyerXiCapSource))) := by
  apply GaloisForLFunctions.HTGeometry.isCyclicFamily_translation_of_fourier_ae_ne_zero
  filter_upwards [meyerHalfDensityL2_fourier_ae
    (deningerMeyerStrongLogSumLM deningerMeyerXiCapSource), ae_xi_criticalFourierPoint_ne_zero]
    with w hw hxi
  rw [hw]
  change deningerMeyerBoundaryMellin deningerMeyerXiCapSource (criticalFourierPoint w) ≠ 0
  rw [deningerMeyerXiCapSource_mellin]
  exact hxi

/-- Genuine Poisson boundaries already have dense image in the origin-mass Hilbert space. -/
theorem meyerPoissonBoundary_halfDensity_dense :
    DenseRange (fun f : DeningerMeyerCap =>
      deningerMeyerHalfDensityL2LM (deningerMeyerStrongLogSumLM f)) := by
  let B := deningerMeyerHalfDensityL2LM.comp deningerMeyerStrongLogSumLM
  have hspan : Submodule.span ℂ (Set.range (fun a : ℝ => MellinL2.additiveTranslationUnitary a
      (deningerMeyerHalfDensityL2LM (deningerMeyerStrongLogSumLM deningerMeyerXiCapSource)))) ≤
        LinearMap.range B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let f := Complex.exp (-((-a : ℝ) : ℂ) / 2) •
      deningerMeyerCapFlow (-a) deningerMeyerXiCapSource
    have hflow : deningerMeyerStrongLogCenteredFlow (-a)
        (deningerMeyerStrongLogSumLM deningerMeyerXiCapSource) =
          deningerMeyerStrongLogSumLM f := by
      dsimp only [f]
      rw [deningerMeyerStrongLogCenteredFlow, LinearMap.smul_apply,
        deningerMeyerStrongLogFlow_boundary, map_smul]
    refine ⟨f, ?_⟩
    change deningerMeyerHalfDensityL2LM (deningerMeyerStrongLogSumLM f) = _
    rw [← hflow, deningerMeyerHalfDensityL2LM_centeredFlow, neg_neg]
  exact meyerXiBoundary_halfDensity_translation_cyclic.mono hspan

/-- Each genuine source class has representatives with arbitrarily small half-density norm. -/
theorem exists_meyer_representative_small_halfDensity_norm
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : DeningerMeyerStrongLogTarget,
      (Submodule.Quotient.mk h : DeningerMeyerStrongLogCohomology) = Submodule.Quotient.mk g ∧
      ‖deningerMeyerHalfDensityL2LM h‖ < ε := by
  obtain ⟨u, ⟨f, rfl⟩, hf⟩ := Metric.mem_closure_iff.mp
    (meyerPoissonBoundary_halfDensity_dense (deningerMeyerHalfDensityL2LM g)) ε hε
  refine ⟨g - deningerMeyerStrongLogSumLM f, ?_, ?_⟩
  · change (LinearMap.range deningerMeyerStrongLogSumLM).mkQ
      (g - deningerMeyerStrongLogSumLM f) = _
    rw [map_sub, show (LinearMap.range deningerMeyerStrongLogSumLM).mkQ
        (deningerMeyerStrongLogSumLM f) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨f, rfl⟩, sub_zero]
    rfl
  · rw [map_sub]
    simpa only [dist_eq_norm] using hf

/-- The quotient infimum of positive origin square mass vanishes on every genuine class. -/
theorem exists_meyer_representative_small_origin_square
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : DeningerMeyerStrongLogTarget,
      (Submodule.Quotient.mk h : DeningerMeyerStrongLogCohomology) = Submodule.Quotient.mk g ∧
      (meyerOriginDegree (deningerMeyerSourceConvolution h (deningerMeyerSourceSharp h))).re < ε := by
  obtain ⟨h, heq, hn⟩ := exists_meyer_representative_small_halfDensity_norm g (Real.sqrt_pos.mpr hε)
  refine ⟨h, heq, ?_⟩
  rw [← meyerHalfDensityL2_norm_sq]
  nlinarith only [hn, norm_nonneg (deningerMeyerHalfDensityL2LM h), Real.sq_sqrt hε.le]

/-- Every genuine class has exactly the nonpositive numbers as lower bounds for its origin mass. -/
theorem meyerOriginSquareMass_class_lower_bound_iff
    (u : DeningerMeyerStrongLogCohomology) (b : ℝ) :
    (∀ g : DeningerMeyerStrongLogTarget,
      (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = u →
        b ≤ (meyerOriginDegree
          (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))).re) ↔ b ≤ 0 := by
  constructor
  · intro hb
    by_contra hnot
    have hpos : 0 < b := lt_of_not_ge hnot
    obtain ⟨g, hg⟩ := (LinearMap.range deningerMeyerStrongLogSumLM).mkQ_surjective u
    obtain ⟨h, he, hm⟩ := exists_meyer_representative_small_origin_square g hpos
    have hclass : (Submodule.Quotient.mk h : DeningerMeyerStrongLogCohomology) = u :=
      he.trans hg
    exact (not_lt_of_ge (hb h hclass)) hm
  · intro hb g _
    rw [← meyerHalfDensityL2_norm_sq]
    exact hb.trans (sq_nonneg _)

/-- Every continuous linear reporter killing genuine boundaries vanishes on the whole completion. -/
theorem meyerHalfDensity_continuous_boundary_reporter_zero
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [T2Space Y]
    (L : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Y)
    (hL : ∀ f : DeningerMeyerCap,
      L (deningerMeyerHalfDensityL2LM (deningerMeyerStrongLogSumLM f)) = 0) : L = 0 := by
  apply ContinuousLinearMap.ext
  exact congrFun (meyerPoissonBoundary_halfDensity_dense.equalizer
    L.continuous (0 : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Y).continuous (funext hL))


/-- Every continuous cohomology-invariant reading of origin Hilbert space is constant. -/
theorem meyerHalfDensity_continuous_class_reading_iff_constant
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (F : Lp ℂ 2 (volume : Measure ℝ) → Y) (hF : Continuous F) :
    (∀ g h : DeningerMeyerStrongLogTarget,
      (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = Submodule.Quotient.mk h →
        F (deningerMeyerHalfDensityL2LM g) = F (deningerMeyerHalfDensityL2LM h)) ↔
      ∀ x, F x = F 0 := by
  constructor
  · intro hclass
    have hb (f : DeningerMeyerCap) :
        F (deningerMeyerHalfDensityL2LM (deningerMeyerStrongLogSumLM f)) = F 0 := by
      have hq : (Submodule.Quotient.mk (deningerMeyerStrongLogSumLM f) :
          DeningerMeyerStrongLogCohomology) = Submodule.Quotient.mk 0 := by
        change (LinearMap.range deningerMeyerStrongLogSumLM).mkQ
          (deningerMeyerStrongLogSumLM f) =
            (LinearMap.range deningerMeyerStrongLogSumLM).mkQ 0
        rw [map_zero]
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨f, rfl⟩
      simpa only [map_zero] using hclass (deningerMeyerStrongLogSumLM f) 0 hq
    exact congrFun (meyerPoissonBoundary_halfDensity_dense.equalizer
      hF continuous_const (funext hb))
  · intro hconst g h _
    exact (hconst _).trans (hconst _).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
