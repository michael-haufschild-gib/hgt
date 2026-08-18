import GaloisForLFunctions.RHTower.CCMRestrictedWeilActualHeadCompletedErrorProducer
import GaloisForLFunctions.RHTower.GammaJumpBinetFormula
import GaloisForLFunctions.RHTower.DigammaDifferenceSeries
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCCMScalingBridge

/-!
# Exact Gamma energy in actual-head autocorrelations

The centered quarter-line Gamma multiplier has Levy density

`exp (-h / 2) / (1 - exp (-2h))`.

This module proves its exact Binet representation and lifts it, by Tonelli and unitary Fourier
Plancherel, to every actual complex `L²` head. On the complete CCM archimedean form domain the
result is the unconditional identity

`GammaDefectEnergy(f) = ||u||² - ||f||²`,

where `f` is the literal physical aperture head of `u`. Thus the full nonconstant Gamma energy is
carried by a positive weighted integral of the same squared translation losses used by the prime,
polar, and completed-error terms. No smoothness, pointwise autocorrelation sign, or limiting
interpretation is assumed.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

namespace RHTower

/-- Positive Levy density of the centered quarter-line Gamma multiplier. -/
def ccmGammaTranslationDensity (h : ℝ) : ℝ :=
  Real.exp (-(h / 2)) / (1 - Real.exp (-(2 * h)))

theorem ccmGammaTranslationDensity_pos {h : ℝ} (hh : 0 < h) :
    0 < ccmGammaTranslationDensity h := by
  unfold ccmGammaTranslationDensity
  exact div_pos (Real.exp_pos _)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

def ccmGammaBinetTerm (xi : ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  (2 - 2 * Real.cos (2 * Real.pi * xi * h)) *
    Real.exp (-((2 * ((n : ℝ) + 1 / 4)) * h))

theorem ccmGammaBinetTerm_nonneg (xi : ℝ) (n : ℕ) (h : ℝ) :
    0 ≤ ccmGammaBinetTerm xi n h := by
  unfold ccmGammaBinetTerm
  exact mul_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * xi * h)])
    (Real.exp_pos _).le

theorem integrableOn_ccmGammaBinetTerm (xi : ℝ) (n : ℕ) :
    IntegrableOn (ccmGammaBinetTerm xi n) (Ioi (0 : ℝ)) := by
  let alpha : ℝ := 2 * ((n : ℝ) + 1 / 4)
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have hexp : IntegrableOn (fun h : ℝ => Real.exp (-(alpha * h))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 halpha
  refine Integrable.bdd_mul (c := 4) hexp ?_ ?_
  · exact (by fun_prop : Continuous fun h : ℝ =>
      2 - 2 * Real.cos (2 * Real.pi * xi * h)).aestronglyMeasurable.restrict
  · filter_upwards with h
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      nlinarith [Real.neg_one_le_cos (2 * Real.pi * xi * h),
        Real.cos_le_one (2 * Real.pi * xi * h)]

theorem integral_ccmGammaBinetTerm (xi : ℝ) (n : ℕ) :
    (∫ h in Ioi (0 : ℝ), ccmGammaBinetTerm xi n h) =
      1 / ((n : ℝ) + 1 / 4) -
        ((n : ℝ) + 1 / 4) /
          (((n : ℝ) + 1 / 4) ^ 2 + (Real.pi * xi) ^ 2) := by
  let a : ℝ := (n : ℝ) + 1 / 4
  let alpha : ℝ := 2 * a
  let beta : ℝ := 2 * Real.pi * xi
  have ha : 0 < a := by dsimp only [a]; positivity
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have hexp : IntegrableOn (fun h : ℝ => Real.exp (-(alpha * h))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 halpha
  have hcos : IntegrableOn
      (fun h : ℝ => Real.exp (-(alpha * h)) * Real.cos (beta * h)) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn
        (fun h : ℝ => Real.cos (beta * h) * Real.exp (-(alpha * h))) (Ioi (0 : ℝ)) := by
      refine Integrable.bdd_mul (c := 1) hexp ?_ ?_
      · exact (by fun_prop : Continuous fun h : ℝ =>
          Real.cos (beta * h)).aestronglyMeasurable.restrict
      · filter_upwards with h
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (beta * h)
    exact h.congr (Filter.Eventually.of_forall fun h => mul_comm _ _)
  have hsplit :
      (∫ h in Ioi (0 : ℝ), ccmGammaBinetTerm xi n h) =
        2 * (∫ h in Ioi (0 : ℝ), Real.exp (-(alpha * h))) -
          2 * ∫ h in Ioi (0 : ℝ),
            Real.exp (-(alpha * h)) * Real.cos (beta * h) := by
    rw [show ccmGammaBinetTerm xi n = fun h : ℝ =>
        2 * Real.exp (-(alpha * h)) -
          2 * (Real.exp (-(alpha * h)) * Real.cos (beta * h)) by
      funext h
      unfold ccmGammaBinetTerm alpha beta a
      ring]
    rw [integral_sub (hexp.const_mul 2) (hcos.const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [hsplit, gammaSymbol_integral_Ioi_exp_neg_mul halpha,
    gammaSymbol_integral_Ioi_exp_neg_mul_cos halpha beta]
  have hdenAlpha : alpha ^ 2 + beta ^ 2 ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos halpha) (sq_nonneg beta))
  have hdenA : a ^ 2 + (Real.pi * xi) ^ 2 ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg (Real.pi * xi)))
  dsimp only [alpha, beta, a]
  field_simp [ne_of_gt ha, ne_of_gt halpha, hdenAlpha, hdenA]

theorem ccmGammaTranslationDensity_eq_tsum {h : ℝ} (hh : 0 < h) :
    ccmGammaTranslationDensity h =
      ∑' n : ℕ, Real.exp (-((2 * ((n : ℝ) + 1 / 4)) * h)) := by
  let x : ℝ := Real.exp (-(2 * h))
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by
    dsimp only [x]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hterm (n : ℕ) :
      Real.exp (-((2 * ((n : ℝ) + 1 / 4)) * h)) =
        Real.exp (-(h / 2)) * x ^ n := by
    dsimp only [x]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
  unfold ccmGammaTranslationDensity
  dsimp only [x]
  rw [div_eq_mul_inv]

theorem ccmGammaBinetIntegrand_eq_tsum {xi h : ℝ} (hh : 0 < h) :
    (2 - 2 * Real.cos (2 * Real.pi * xi * h)) *
        ccmGammaTranslationDensity h =
      ∑' n : ℕ, ccmGammaBinetTerm xi n h := by
  rw [ccmGammaTranslationDensity_eq_tsum hh, ← tsum_mul_left]
  exact tsum_congr fun n => rfl

theorem integral_ccmGammaTranslationDensity_mul_cosineDefect (xi : ℝ) :
    (∫ h in Ioi (0 : ℝ),
      (2 - 2 * Real.cos (2 * Real.pi * xi * h)) *
        ccmGammaTranslationDensity h) =
      2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) := by
  let a : ℂ := ((1 / 4 : ℝ) : ℂ)
  let b : ℂ := ((1 / 4 : ℝ) : ℂ) + ((Real.pi * xi : ℝ) : ℂ) * Complex.I
  have ha : 0 < a.re := by dsimp only [a]; norm_num
  have hb : 0 < b.re := by dsimp only [b]; simp [Complex.mul_re]
  have hsumC := hasSum_digamma_sub (a := a) (b := b) ha hb
  have hsumR := Complex.hasSum_re hsumC
  have hsummable : Summable (fun n : ℕ =>
      (1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ))).re) := hsumR.summable
  have hterm (n : ℕ) :
      (∫ h in Ioi (0 : ℝ), ccmGammaBinetTerm xi n h) =
        (1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ))).re := by
    rw [integral_ccmGammaBinetTerm]
    dsimp only [a, b]
    have hzero :
        (1 / (((1 / 4 : ℝ) : ℂ) + (n : ℂ))).re =
          1 / ((1 / 4 : ℝ) + (n : ℝ)) := by
      calc
        _ = ((1 / 4 : ℝ) + (n : ℝ)) /
            (((1 / 4 : ℝ) + (n : ℝ)) ^ 2 + 0 ^ 2) := by
          simpa using re_one_div_vertical (1 / 4) 0 n
        _ = _ := by
          have hpos : 0 < (1 / 4 : ℝ) + (n : ℝ) := by positivity
          rw [zero_pow (by norm_num), add_zero, pow_two]
          simp [one_div]
    have hheight :
        (1 / (((1 / 4 : ℝ) : ℂ) + ((Real.pi * xi : ℝ) : ℂ) * Complex.I +
          (n : ℂ))).re =
          ((1 / 4 : ℝ) + (n : ℝ)) /
            (((1 / 4 : ℝ) + (n : ℝ)) ^ 2 + (Real.pi * xi) ^ 2) := by
      exact re_one_div_vertical (1 / 4) (Real.pi * xi) n
    rw [Complex.sub_re, hzero, hheight]
    ring
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (ccmGammaBinetTerm xi n)
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    exact (by
      unfold ccmGammaBinetTerm
      fun_prop : Continuous (ccmGammaBinetTerm xi n)).aestronglyMeasurable.restrict
  have hnorm (n : ℕ) :
      (∫⁻ h in Ioi (0 : ℝ), ‖ccmGammaBinetTerm xi n h‖ₑ) =
        ENNReal.ofReal ((1 / (a + (n : ℂ)) - 1 / (b + (n : ℂ))).re) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_ccmGammaBinetTerm xi n)]
    congr 1
    rw [← hterm n]
    apply integral_congr_ae
    filter_upwards with h
    rw [Real.norm_of_nonneg (ccmGammaBinetTerm_nonneg xi n h)]
  have hsum : (∑' n : ℕ,
      ∫⁻ h in Ioi (0 : ℝ), ‖ccmGammaBinetTerm xi n h‖ₑ) ≠ ⊤ := by
    rw [tsum_congr hnorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro n
      rw [← hterm n]
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun h =>
        ccmGammaBinetTerm_nonneg xi n h)
    · exact hsummable
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh =>
      ccmGammaBinetIntegrand_eq_tsum hh), integral_tsum hmeas hsum,
    tsum_congr hterm, hsumR.tsum_eq]
  unfold gammaHardyPhaseRate
  dsimp only [a, b, linePt]
  simp only [Complex.sub_re]
  push_cast
  ring

/-- Plancherel law for the literal squared translation increment of an arbitrary `L²` head. -/
theorem ccmActualHeadTranslationDefect_fourierUnitary_symm
    (h : ℝ) (g : SoninL2) :
    ccmActualHeadTranslationDefect h (fourierUnitary.symm g) =
      ∫ xi : ℝ, (2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2 := by
  unfold ccmActualHeadTranslationDefect
  rw [logTranslation_defect_eq,
    re_inner_logTranslation_symm_fourierUnitary_symm]
  have hsq : Integrable (fun xi : ℝ => ‖g xi‖ ^ 2) :=
    (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have hcos : Integrable
      (fun xi : ℝ => ‖g xi‖ ^ 2 * Real.cos (2 * Real.pi * h * xi)) := by
    refine Integrable.mul_bdd (c := 1) hsq ?_ ?_
    · exact (by fun_prop : Continuous fun xi : ℝ =>
        Real.cos (2 * Real.pi * h * xi)).aestronglyMeasurable
    · filter_upwards with xi
      simpa [Real.norm_eq_abs] using
        Real.abs_cos_le_one (2 * Real.pi * h * xi)
  rw [fourierUnitary.symm.norm_map, norm_sq_eq_integral]
  calc
    2 * (∫ xi : ℝ, ‖g xi‖ ^ 2) -
          2 * ∫ xi : ℝ, ‖g xi‖ ^ 2 * Real.cos (2 * Real.pi * h * xi) =
        (∫ xi : ℝ, 2 * ‖g xi‖ ^ 2) -
          ∫ xi : ℝ, 2 * (‖g xi‖ ^ 2 * Real.cos (2 * Real.pi * h * xi)) := by
      rw [integral_const_mul, integral_const_mul]
    _ = ∫ xi : ℝ,
          2 * ‖g xi‖ ^ 2 -
            2 * (‖g xi‖ ^ 2 * Real.cos (2 * Real.pi * h * xi)) := by
      rw [integral_sub (hsq.const_mul 2) (hcos.const_mul 2)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with xi
      ring

theorem integrableOn_ccmGammaTranslationDensity_mul_cosineDefect (xi : ℝ) :
    IntegrableOn (fun h : ℝ =>
      (2 - 2 * Real.cos (2 * Real.pi * xi * h)) *
        ccmGammaTranslationDensity h) (Ioi 0) := by
  by_cases hxi : xi = 0
  · subst xi
    simp
  · by_contra hnot
    have hzero :
        (∫ h in Ioi (0 : ℝ),
          (2 - 2 * Real.cos (2 * Real.pi * xi * h)) *
            ccmGammaTranslationDensity h) = 0 :=
      integral_undef hnot
    rw [integral_ccmGammaTranslationDensity_mul_cosineDefect] at hzero
    have harg : 2 * Real.pi * xi ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi
    have hstrict := gammaHardyPhaseRate_zero_lt harg
    linarith

theorem ccmGammaSpectralMultiplier_nonneg (xi : ℝ) :
    0 ≤ 2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) := by
  by_cases hxi : xi = 0
  · simp [hxi]
  · exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (gammaHardyPhaseRate_zero_lt
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi)).le)

theorem integrable_ccmGammaCosineDefectSpectralDensity
    (h : ℝ) (g : SoninL2) :
    Integrable (fun xi : ℝ =>
      (2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2) := by
  have hsq : Integrable (fun xi : ℝ => ‖g xi‖ ^ 2) :=
    (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have h := Integrable.mul_bdd (c := 4) hsq
    (by
      exact (by fun_prop : Continuous fun xi : ℝ =>
        2 - 2 * Real.cos (2 * Real.pi * h * xi)).aestronglyMeasurable)
    (by
      filter_upwards with xi
      rw [Real.norm_eq_abs, abs_le]
      constructor <;>
        nlinarith [Real.neg_one_le_cos (2 * Real.pi * h * xi),
          Real.cos_le_one (2 * Real.pi * h * xi)])
  exact h.congr (Filter.Eventually.of_forall fun xi => by ring)

theorem ccmGammaCosineDefectSpectralDensity_nonneg
    (h : ℝ) (g : SoninL2) (xi : ℝ) :
    0 ≤ (2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2 :=
  mul_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * h * xi)]) (sq_nonneg _)

/-- Positive Γ energy written directly in the autocorrelations of one actual `L²` head. -/
def ccmActualHeadGammaAutocorrelationEnergyL (f : SoninL2) : ENNReal :=
  ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
    (ccmGammaTranslationDensity h * ccmActualHeadTranslationDefect h f)

def ccmActualHeadGammaSpectralJointL (g : SoninL2) : ENNReal :=
  ∫⁻ h in Ioi (0 : ℝ), ∫⁻ xi : ℝ, ENNReal.ofReal
    (ccmGammaTranslationDensity h *
      ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2))

theorem ccmActualHeadGammaAutocorrelationEnergyL_fourierUnitary_symm_eq_joint
    (g : SoninL2) :
    ccmActualHeadGammaAutocorrelationEnergyL (fourierUnitary.symm g) =
      ccmActualHeadGammaSpectralJointL g := by
  unfold ccmActualHeadGammaAutocorrelationEnergyL
    ccmActualHeadGammaSpectralJointL
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro h hh
  change ENNReal.ofReal
      (ccmGammaTranslationDensity h *
        ccmActualHeadTranslationDefect h (fourierUnitary.symm g)) = _
  rw [ccmActualHeadTranslationDefect_fourierUnitary_symm]
  have hdensity : 0 ≤ ccmGammaTranslationDensity h :=
    (ccmGammaTranslationDensity_pos hh).le
  have hint := integrable_ccmGammaCosineDefectSpectralDensity h g
  have hnonneg : 0 ≤ᵐ[volume] fun xi : ℝ =>
      (2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2 :=
    Filter.Eventually.of_forall
      (ccmGammaCosineDefectSpectralDensity_nonneg h g)
  rw [ENNReal.ofReal_mul hdensity,
    ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  have hmeas : AEMeasurable (fun xi : ℝ => ENNReal.ofReal
      ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2)) :=
    hint.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [← lintegral_const_mul'' _ hmeas]
  refine lintegral_congr fun xi => ?_
  rw [← ENNReal.ofReal_mul hdensity]

theorem aemeasurable_ccmActualHeadGammaSpectralJointKernel (g : SoninL2) :
    AEMeasurable (Function.uncurry fun h xi : ℝ => ENNReal.ofReal
      (ccmGammaTranslationDensity h *
        ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hscalar : Measurable fun p : ℝ × ℝ =>
      ccmGammaTranslationDensity p.1 *
        (2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2)) := by
    unfold ccmGammaTranslationDensity
    fun_prop
  have hg : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖g p.2‖ ^ 2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    ((MeasureTheory.Lp.aestronglyMeasurable g).norm.pow 2).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hreal : AEMeasurable (fun p : ℝ × ℝ =>
      ccmGammaTranslationDensity p.1 *
        ((2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2)) * ‖g p.2‖ ^ 2))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine (hscalar.aestronglyMeasurable.mul hg).aemeasurable.congr
      (Filter.Eventually.of_forall fun p => ?_)
    exact mul_assoc _ _ _
  exact hreal.ennreal_ofReal

theorem ccmActualHeadGammaSpectralJointL_swap (g : SoninL2) :
    ccmActualHeadGammaSpectralJointL g =
      ∫⁻ xi : ℝ, ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
        (ccmGammaTranslationDensity h *
          ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2)) := by
  unfold ccmActualHeadGammaSpectralJointL
  exact lintegral_lintegral_swap
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume)
    (aemeasurable_ccmActualHeadGammaSpectralJointKernel g)

theorem lintegral_ccmActualHeadGammaSpectralJoint_inner
    (g : SoninL2) (xi : ℝ) :
    (∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
      (ccmGammaTranslationDensity h *
        ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2))) =
      ENNReal.ofReal
        (2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) *
          ‖g xi‖ ^ 2) := by
  let G : ℝ := ‖g xi‖ ^ 2
  have hG : 0 ≤ G := sq_nonneg _
  let B : ℝ → ℝ := fun h =>
    (2 - 2 * Real.cos (2 * Real.pi * xi * h)) * ccmGammaTranslationDensity h
  have hBint : IntegrableOn B (Ioi 0) :=
    integrableOn_ccmGammaTranslationDensity_mul_cosineDefect xi
  have hBnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact mul_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * xi * h)])
      (ccmGammaTranslationDensity_pos hh).le
  have hBmeas : Measurable (fun h : ℝ => ENNReal.ofReal (B h)) := by
    apply Measurable.ennreal_ofReal
    dsimp only [B]
    unfold ccmGammaTranslationDensity
    fun_prop
  have hrewrite : (fun h : ℝ => ENNReal.ofReal
      (ccmGammaTranslationDensity h *
        ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * G))) =
      fun h : ℝ => ENNReal.ofReal (B h) * ENNReal.ofReal G := by
    funext h
    have halg :
        ccmGammaTranslationDensity h *
            ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * G) = G * B h := by
      dsimp only [B]
      rw [show 2 * Real.pi * h * xi = 2 * Real.pi * xi * h by ring]
      ring
    rw [halg, ENNReal.ofReal_mul hG, mul_comm]
  change (∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
      (ccmGammaTranslationDensity h *
        ((2 - 2 * Real.cos (2 * Real.pi * h * xi)) * G))) = _
  rw [hrewrite, lintegral_mul_const _ hBmeas,
    ← ofReal_integral_eq_lintegral_ofReal hBint hBnonneg,
    show (∫ h in Ioi (0 : ℝ), B h) =
        2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) by
      exact integral_ccmGammaTranslationDensity_mul_cosineDefect xi]
  rw [← ENNReal.ofReal_mul (ccmGammaSpectralMultiplier_nonneg xi)]

def ccmActualHeadGammaSpectralEnergyL (g : SoninL2) : ENNReal :=
  ∫⁻ xi : ℝ, ENNReal.ofReal
    (2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) *
      ‖g xi‖ ^ 2)

/-- Exact Γ Binet--Plancherel law on every actual `L²` head. -/
theorem ccmActualHeadGammaAutocorrelationEnergyL_eq_spectralEnergy
    (g : SoninL2) :
    ccmActualHeadGammaAutocorrelationEnergyL (fourierUnitary.symm g) =
      ccmActualHeadGammaSpectralEnergyL g := by
  rw [ccmActualHeadGammaAutocorrelationEnergyL_fourierUnitary_symm_eq_joint,
    ccmActualHeadGammaSpectralJointL_swap]
  unfold ccmActualHeadGammaSpectralEnergyL
  refine lintegral_congr fun xi => ?_
  exact lintegral_ccmActualHeadGammaSpectralJoint_inner g xi

theorem integrable_ccmGammaSpectralExcessDensity
    (q : CCMArchimedeanFourierL2) :
    Integrable (fun xi : ℝ =>
      2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) *
        ‖(ccmArchimedeanWeightedToL2 q : ℝ → ℂ) xi‖ ^ 2) := by
  let g : SoninL2 := ccmArchimedeanWeightedToL2 q
  have hcoe := ccmArchimedeanWeightedToL2_coeFn q
  have hgamma : Integrable (fun xi : ℝ =>
      2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    (integrable_two_gammaHardyPhaseRate_mul_norm_sq q).congr (by
      filter_upwards [hcoe] with xi hxi
      rw [hxi])
  have hplain : Integrable (fun xi : ℝ => ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have hdifference := hgamma.sub (hplain.const_mul (2 * gammaHardyPhaseRate 0))
  change Integrable (fun xi : ℝ =>
    2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) *
      ‖(g : ℝ → ℂ) xi‖ ^ 2)
  refine hdifference.congr (Filter.Eventually.of_forall fun xi => ?_)
  change
    2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(g : ℝ → ℂ) xi‖ ^ 2 -
        2 * gammaHardyPhaseRate 0 * ‖(g : ℝ → ℂ) xi‖ ^ 2 = _
  ring

theorem integral_ccmGammaSpectralExcessDensity_eq_norm_sub
    (q : CCMArchimedeanFourierL2) :
    (∫ xi : ℝ,
      2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) *
        ‖(ccmArchimedeanWeightedToL2 q : ℝ → ℂ) xi‖ ^ 2) =
      ‖q‖ ^ 2 - ‖ccmArchimedeanWeightedToL2 q‖ ^ 2 := by
  let g : SoninL2 := ccmArchimedeanWeightedToL2 q
  have hcoe := ccmArchimedeanWeightedToL2_coeFn q
  have hgamma : Integrable (fun xi : ℝ =>
      2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    (integrable_two_gammaHardyPhaseRate_mul_norm_sq q).congr (by
      filter_upwards [hcoe] with xi hxi
      rw [hxi])
  have hplain : Integrable (fun xi : ℝ => ‖(g : ℝ → ℂ) xi‖ ^ 2) :=
    (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have harch :
      (∫ xi : ℝ,
        2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(g : ℝ → ℂ) xi‖ ^ 2) =
        ‖q‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) * ‖g‖ ^ 2 := by
    calc
      _ = ∫ xi : ℝ,
          2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
            ‖(q : ℝ → ℂ) xi‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hcoe] with xi hxi
        rw [hxi]
      _ = _ := ccmArchimedean_form_eq_domainNorm_add_scalar q
  change (∫ xi : ℝ,
      2 * (gammaHardyPhaseRate (2 * Real.pi * xi) - gammaHardyPhaseRate 0) *
        ‖(g : ℝ → ℂ) xi‖ ^ 2) = _
  calc
    _ = ∫ xi : ℝ,
        (2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(g : ℝ → ℂ) xi‖ ^ 2 -
          (2 * gammaHardyPhaseRate 0) * ‖(g : ℝ → ℂ) xi‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards with xi
      ring
    _ = (∫ xi : ℝ,
          2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(g : ℝ → ℂ) xi‖ ^ 2) -
        ∫ xi : ℝ, (2 * gammaHardyPhaseRate 0) * ‖(g : ℝ → ℂ) xi‖ ^ 2 := by
      rw [integral_sub hgamma (hplain.const_mul _)]
    _ = _ := by
      rw [harch, integral_const_mul, ← norm_sq_eq_integral]
      ring

theorem ccmArchimedeanFormToAperture_val_eq_fourierUnitary_symm
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (ccmArchimedeanFormToAperture a u : SoninL2) =
      fourierUnitary.symm (ccmArchimedeanWeightedToL2 u.1) := rfl

/-- Finite real Γ energy carried by the actual head autocorrelations. -/
def ccmActualHeadGammaAutocorrelationEnergy (f : SoninL2) : ℝ :=
  (ccmActualHeadGammaAutocorrelationEnergyL f).toReal

theorem ccmActualHeadGammaAutocorrelationEnergy_nonneg (f : SoninL2) :
    0 ≤ ccmActualHeadGammaAutocorrelationEnergy f :=
  ENNReal.toReal_nonneg

/-- Exact full-form-domain identity: Γ excess equals weighted physical translation loss. -/
theorem ccmActualHeadGammaAutocorrelationEnergyL_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadGammaAutocorrelationEnergyL
        (ccmArchimedeanFormToAperture a u : SoninL2) =
      ENNReal.ofReal
        (‖u‖ ^ 2 - ‖ccmArchimedeanFormToAperture a u‖ ^ 2) := by
  rw [ccmArchimedeanFormToAperture_val_eq_fourierUnitary_symm,
    ccmActualHeadGammaAutocorrelationEnergyL_eq_spectralEnergy]
  unfold ccmActualHeadGammaSpectralEnergyL
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_ccmGammaSpectralExcessDensity u.1)
    (Filter.Eventually.of_forall fun xi =>
      mul_nonneg (ccmGammaSpectralMultiplier_nonneg xi) (sq_nonneg _)),
    integral_ccmGammaSpectralExcessDensity_eq_norm_sub]
  rw [norm_ccmArchimedeanFormToAperture]
  rfl

theorem ccmActualHeadGammaAutocorrelationEnergy_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadGammaAutocorrelationEnergy
        (ccmArchimedeanFormToAperture a u : SoninL2) =
      ‖u‖ ^ 2 - ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  have hnorm := norm_ccmArchimedeanFormToAperture_le a u
  have hnonneg :
      0 ≤ ‖u‖ ^ 2 - ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    nlinarith [norm_nonneg u, norm_nonneg (ccmArchimedeanFormToAperture a u)]
  unfold ccmActualHeadGammaAutocorrelationEnergy
  rw [ccmActualHeadGammaAutocorrelationEnergyL_formDomain,
    ENNReal.toReal_ofReal hnonneg]

end RHTower
