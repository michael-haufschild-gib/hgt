import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHalfLineDomain
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional

/-! Finite jump energy admits a compact continuous source to the spectral Weil
form. The extended-integral Lévy identity supplies spectral integrability, so
the prime–Gamma–polar identity does not require two source derivatives. -/

open Complex MeasureTheory Set Filter
open scoped FourierTransform CompactlySupported ComplexConjugate
open Zeta23
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
noncomputable section
set_option autoImplicit false

private theorem compact_weilTest_eq (f : C_c(ℝ, ℝ)) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) =
      fun x => (autocorr f x : ℂ) := by
  funext x
  simpa only [neg_neg, autocorr_neg] using (autocorr_eq_weilTest f (-x)).symm

private theorem compact_jump_lintegral_eq (f : C_c(ℝ, ℝ)) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
      ∫ u : ℝ, ‖(f u : ℂ) - (f (u+x) : ℂ)‖^2)) =
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
      ((autocorr f 0-autocorr f x)*archLevySinhWeight x) := by
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have he : (∫ u : ℝ, ‖(f u : ℂ)-(f (u+x) : ℂ)‖^2) =
      ∫ u, (f u-f (u+x))^2 := by
    congr 1 with u
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [he, integral_sub_shift_sq f.hasCompactSupport f.continuous x]
  unfold archLevySinhWeight
  rw [exp_half_div_sinh_eq hx]
  congr 1
  ring

/-- The positive spectral excess is finite whenever the physical jump energy is. -/
theorem integrable_archSymbol_of_compact_finite_jump (f : C_c(ℝ, ℝ))
    (hJ : IntegrableOn (fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x) (Ioi 0)) :
    Integrable (fun ξ : ℝ => gammaHardyPhaseRate (2*Real.pi*ξ)*
      ‖𝓕 (fun u => (f u : ℂ)) ξ‖^2) := by
  let F : ℝ → ℂ := fun u => (f u : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp f.continuous
  have hFcs : HasCompactSupport F := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hF1 := hFc.integrable_of_hasCompactSupport hFcs
  have hF2 : MemLp F 2 := hFc.memLp_of_hasCompactSupport hFcs
  have hfourier := GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hF1
  have hpos (ξ : ℝ) : 0 ≤
      2*(gammaHardyPhaseRate (2*Real.pi*ξ)-gammaHardyPhaseRate 0)*‖𝓕 F ξ‖^2 :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy _))) (sq_nonneg _)
  have hphys : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ (autocorr f 0-autocorr f x)*archLevySinhWeight x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x)
      (archLevySinhWeight_pos hx).le
  have hfinite := (hasFiniteIntegral_iff_ofReal hphys).mp hJ.2
  have he := lintegral_archSymbol_mul_normSq_fourier hF1 hF2
  rw [compact_jump_lintegral_eq f] at he
  have hcont : Continuous (fun ξ : ℝ =>
      2*(gammaHardyPhaseRate (2*Real.pi*ξ)-gammaHardyPhaseRate 0)*‖𝓕 F ξ‖^2) :=
    (continuous_const.mul ((continuous_gammaHardyPhaseRate.comp
      (continuous_const.mul continuous_id)).sub continuous_const)).mul (hfourier.norm.pow 2)
  have hi : Integrable (fun ξ : ℝ =>
      2*(gammaHardyPhaseRate (2*Real.pi*ξ)-gammaHardyPhaseRate 0)*‖𝓕 F ξ‖^2) :=
    ⟨hcont.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hpos)).mpr (he.trans_lt hfinite)⟩
  have hbase := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hF1 hF2
  exact ((hi.div_const 2).add (hbase.const_mul (gammaHardyPhaseRate 0))).congr
    (Eventually.of_forall fun ξ => by dsimp [F]; ring)

private theorem compact_spectral_arch_eq (f : C_c(ℝ, ℝ))
    (hJ : IntegrableOn (fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x) (Ioi 0)) :
    (1/(2*Real.pi) : ℂ) *
        (∫ r : ℝ, Zeta23.paperFT (fun x => (autocorr f x : ℂ)) r * (EF.gammaBracket r : ℂ)) =
      ((EF.gammaBracket 0*autocorr f 0+biScaleLevyEnergy f : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun u => (f u : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp f.continuous
  have hFcs : HasCompactSupport F := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hF1 := hFc.integrable_of_hasCompactSupport hFcs
  have hF2 : MemLp F 2 := hFc.memLp_of_hasCompactSupport hFcs
  have hk := EF.paperFT_weilTest hFc hFc hFcs hFcs
  have hreal (r : ℝ) :
      paperFT (fun x => (autocorr f x : ℂ)) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖^2*EF.gammaBracket r : ℝ) : ℂ) := by
    rw [← compact_weilTest_eq, hk, Complex.conj_ofReal, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have harch : (∫ r : ℝ, paperFT (fun x => (autocorr f x : ℂ)) r * (EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ‖paperFT F r‖^2*EF.gammaBracket r : ℝ) : ℂ) := by
    simp_rw [hreal]
    exact integral_complex_ofReal
  have hsplit := integral_archSymbol_mul_normSq_fourier_eq hF1 hF2
    (integrable_archSymbol_of_compact_finite_jump f hJ)
  have hnorm : (∫ u : ℝ, ‖F u‖^2) = autocorr f 0 := by
    unfold autocorr
    congr 1 with u
    simp [F, Complex.norm_real, sq_abs, pow_two]
  have hnonneg : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ (autocorr f 0-autocorr f x)*archLevySinhWeight x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x)
      (archLevySinhWeight_pos hx).le
  have hlev : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
      ∫ u : ℝ, ‖F u-F (u+x)‖^2)).toReal = biScaleLevyEnergy f := by
    rw [compact_jump_lintegral_eq f,
      ← ofReal_integral_eq_lintegral_ofReal hJ hnonneg,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]
    rfl
  rw [hnorm, hlev, ← WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate 0] at hsplit
  rw [harch, show (1/(2*Real.pi) : ℂ) = ((1/(2*Real.pi) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, WeilLevyPole.integral_paperFT_sq_mul_gammaBracket, hsplit]

private theorem compact_polar_transform_eq (f : C_c(ℝ, ℝ)) :
    paperFT (fun x => (autocorr f x : ℂ)) (I/2) +
      paperFT (fun x => (autocorr f x : ℂ)) (-I/2) =
    ((2*(∫ x in Ici (0 : ℝ), polarDensity x*autocorr f x) : ℝ) : ℂ) := by
  let h := autocorr f
  have hc : Continuous h := continuous_autocorr_compact f
  have hcs : HasCompactSupport h := hasCompactSupport_autocorr f.hasCompactSupport
  have hip : Integrable (fun x => h x*Real.exp (x/2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have him : Integrable (fun x => h x*Real.exp (-x/2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have heven : (fun x => h |x|*Real.cosh (|x|/2)) = fun x => h x*Real.cosh (x/2) := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · simp only [abs_of_nonpos hx, neg_div, Real.cosh_neg, h, autocorr_neg]
  have hh := integral_comp_abs (f := fun x => h x*Real.cosh (x/2))
  rw [heven] at hh
  have hs : (∫ x, h x*Real.exp (-x/2))+(∫ x, h x*Real.exp (x/2)) =
      2*(∫ x in Ici (0 : ℝ), polarDensity x*h x) := by
    rw [← integral_add him hip]
    have he : (fun x => h x*Real.exp (-x/2)+h x*Real.exp (x/2)) =
        fun x => 2*(h x*Real.cosh (x/2)) := by
      funext x
      rw [Real.cosh_eq]
      simp only [neg_div]
      ring
    rw [he, integral_const_mul, hh, integral_Ici_eq_integral_Ioi]
    simp only [polarDensity]
    rw [show (fun x => 2*Real.cosh (x/2)*h x) =
      fun x => 2*(h x*Real.cosh (x/2)) by funext x; ring, integral_const_mul]
  rw [WeilLevyPole.paperFT_ofReal_I_div_two, WeilLevyPole.paperFT_ofReal_neg_I_div_two,
    ← Complex.ofReal_add]
  exact congrArg Complex.ofReal hs

/-- Exact spectral Weil identity on the compact continuous finite-jump domain.
All prime atoms and both polar branches are retained. -/
theorem re_weilFullFunctional_eq_of_compact_finite_jump (f : C_c(ℝ, ℝ))
    (hJ : IntegrableOn (fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x) (Ioi 0)) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
    EF.gammaBracket 0*autocorr f 0+biScaleLevyEnergy f-2*fullPairing (autocorr f) := by
  have hprime (n : ℕ) :
      ((if 2 ≤ n then ArithmeticFunction.vonMangoldt n/Real.sqrt n else 0 : ℝ) : ℂ) *
        ((autocorr f (Real.log n) : ℂ)+(autocorr f (-Real.log n) : ℂ)) =
      ((2*primeTerm (autocorr f) n : ℝ) : ℂ) := by
    rw [autocorr_neg]
    by_cases hn : 2 ≤ n
    · simp only [primeTerm, primeWeight, if_pos hn]
      push_cast
      ring
    · simp [hn, primeTerm]
  rw [compact_weilTest_eq, weilFullFunctional, compact_spectral_arch_eq f hJ,
    compact_polar_transform_eq f]
  simp_rw [hprime]
  rw [← Complex.ofReal_tsum, tsum_mul_left]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.ofReal_re, fullPairing]
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
