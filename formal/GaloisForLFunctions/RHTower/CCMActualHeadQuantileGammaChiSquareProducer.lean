import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileTransportProducer
import GaloisForLFunctions.HTGeometry.WeightedCauchySchwarz
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower


theorem logTranslationCLM_add_apply (a b : ℝ) (f : SoninL2) :
    logTranslationCLM a (logTranslationCLM b f) =
      logTranslationCLM (a + b) f := by
  change MellinL2.additiveTranslationUnitary a
      (MellinL2.additiveTranslationUnitary b f) =
    MellinL2.additiveTranslationUnitary (a + b) f
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv a)
      (MellinL2.realTranslation_measurePreserving a)
      (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv b)
        (MellinL2.realTranslation_measurePreserving b) f) =
    Lp.compMeasurePreserving (MellinL2.realTranslationEquiv (a + b))
      (MellinL2.realTranslation_measurePreserving (a + b)) f
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving f
      ((MellinL2.realTranslation_measurePreserving b).comp
        (MellinL2.realTranslation_measurePreserving a)),
    Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving (a + b))
  ] with x hx hy
  rw [hx, hy]
  simp [MellinL2.realTranslationEquiv, Function.comp_apply]

theorem logTranslationCLM_zero_apply (f : SoninL2) :
    logTranslationCLM 0 f = f := by
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv 0)
      (MellinL2.realTranslation_measurePreserving 0) f = f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving 0)] with x hx
  rw [hx]
  simp [MellinL2.realTranslationEquiv, Function.comp_apply]

theorem norm_logTranslationCLM_sub_logTranslationCLM_eq_sqrt_defect
    (h s : ℝ) (f : SoninL2) :
    ‖logTranslationCLM h f - logTranslationCLM s f‖ =
      Real.sqrt (ccmActualHeadTranslationDefect (h - s) f) := by
  have heq :
      logTranslationCLM h f - logTranslationCLM s f =
        logTranslationCLM s (logTranslationCLM (h - s) f - f) := by
    rw [map_sub, logTranslationCLM_add_apply]
    congr 2
    ring_nf
  rw [heq, logTranslation_norm]
  unfold ccmActualHeadTranslationDefect
  exact (Real.sqrt_sq (norm_nonneg _)).symm

theorem ccmActualHeadSymmetricAutocorrelation_eq_re_inner
    (h : ℝ) (f : SoninL2) :
    ccmActualHeadSymmetricAutocorrelation h f =
      (inner ℂ (logTranslationCLM h f) f).re := by
  have hadj : inner ℂ (logTranslationCLM (-h) f) f =
      inner ℂ f (logTranslationCLM h f) := by
    rw [inner_logTranslationCLM (-h)]
    simp
  have hre : (inner ℂ f (logTranslationCLM h f)).re =
      (inner ℂ (logTranslationCLM h f) f).re := by
    simpa using inner_re_symm (𝕜 := ℂ) f (logTranslationCLM h f)
  unfold ccmActualHeadSymmetricAutocorrelation
  rw [hadj]
  simp only [Complex.add_re, hre]
  ring

/-- Autocorrelation transport is Lipschitz in the Hilbert translation metric, with exact
same-head displacement defect. -/
theorem abs_ccmActualHeadSymmetricAutocorrelation_sub_le_norm_mul_sqrt_defect
    (h s : ℝ) (f : SoninL2) :
    |ccmActualHeadSymmetricAutocorrelation h f -
        ccmActualHeadSymmetricAutocorrelation s f| ≤
      ‖f‖ * Real.sqrt (ccmActualHeadTranslationDefect (h - s) f) := by
  rw [ccmActualHeadSymmetricAutocorrelation_eq_re_inner,
    ccmActualHeadSymmetricAutocorrelation_eq_re_inner]
  have hre :
      (inner ℂ (logTranslationCLM h f) f).re -
          (inner ℂ (logTranslationCLM s f) f).re =
        (inner ℂ (logTranslationCLM h f - logTranslationCLM s f) f).re := by
    rw [inner_sub_left, Complex.sub_re]
  rw [hre]
  calc
    _ ≤ ‖inner ℂ (logTranslationCLM h f - logTranslationCLM s f) f‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖logTranslationCLM h f - logTranslationCLM s f‖ * ‖f‖ :=
      norm_inner_le_norm _ _
    _ = ‖f‖ * Real.sqrt (ccmActualHeadTranslationDefect (h - s) f) := by
      rw [norm_logTranslationCLM_sub_logTranslationCLM_eq_sqrt_defect]
      ring

theorem integrableOn_ccmGammaHigherBinetModeDensity_mul_translationDefect_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    IntegrableOn (fun h : ℝ =>
      ccmGammaHigherBinetModeDensity h *
        ccmActualHeadTranslationDefect h
          (ccmArchimedeanFormToAperture a u : SoninL2))
      (Ioi (0 : ℝ)) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  let G : ℝ → ℝ := fun h =>
    ccmGammaHigherBinetModeDensity h * ccmActualHeadTranslationDefect h f
  have hgamma : ccmActualHeadGammaAutocorrelationEnergyL f ≠ ⊤ := by
    rw [ccmActualHeadGammaAutocorrelationEnergyL_formDomain]
    exact ENNReal.ofReal_ne_top
  have hsplit := ccmActualHeadGammaAutocorrelationEnergyL_eq_first_add_higher f
  have hhigher : ccmActualHeadGammaHigherBinetModeEnergyL f ≠ ⊤ := by
    apply ne_top_of_le_ne_top hgamma
    rw [hsplit]
    exact le_add_left le_rfl
  have hGmeas : Measurable G := by
    dsimp only [G]
    apply Measurable.mul
    · unfold ccmGammaHigherBinetModeDensity
      fun_prop
    · unfold ccmActualHeadTranslationDefect
      exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2 |>.measurable
  have hlint : (∫⁻ h in Ioi (0 : ℝ), ‖G h‖ₑ) =
      ccmActualHeadGammaHigherBinetModeEnergyL f := by
    unfold ccmActualHeadGammaHigherBinetModeEnergyL
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro h hh
    have hnonneg : 0 ≤ G h := mul_nonneg
      (ccmGammaHigherBinetModeDensity_pos hh).le
      (by dsimp only [G, f]; unfold ccmActualHeadTranslationDefect; positivity)
    change ‖G h‖ₑ = ENNReal.ofReal (G h)
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  change IntegrableOn G (Ioi (0 : ℝ))
  refine ⟨hGmeas.aestronglyMeasurable.restrict, ?_⟩
  rw [HasFiniteIntegral, hlint]
  exact lt_top_iff_ne_top.mpr hhigher

theorem ccmActualHeadGammaHigherBinetModeEnergy_eq_integral_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadGammaHigherBinetModeEnergy
        (ccmArchimedeanFormToAperture a u : SoninL2) =
      ∫ h in Ioi (0 : ℝ),
        ccmGammaHigherBinetModeDensity h *
          ccmActualHeadTranslationDefect h
            (ccmArchimedeanFormToAperture a u : SoninL2) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  have hint :=
    integrableOn_ccmGammaHigherBinetModeDensity_mul_translationDefect_formDomain a u
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun h : ℝ =>
      ccmGammaHigherBinetModeDensity h * ccmActualHeadTranslationDefect h f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact mul_nonneg (ccmGammaHigherBinetModeDensity_pos hh).le
      (by unfold ccmActualHeadTranslationDefect; positivity)
  change ccmActualHeadGammaHigherBinetModeEnergy f = _
  unfold ccmActualHeadGammaHigherBinetModeEnergy
    ccmActualHeadGammaHigherBinetModeEnergyL
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]

/-- Pointwise reciprocal of the higher-Binet density, continuously filled at the origin. -/
def ccmGammaHigherBinetDualDensity (h : ℝ) : ℝ :=
  Real.exp (h / 2) * (Real.exp (2 * h) - 1)

theorem ccmGammaHigherBinetDualDensity_nonneg {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ ccmGammaHigherBinetDualDensity h := by
  unfold ccmGammaHigherBinetDualDensity
  exact mul_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (by simpa using Real.exp_monotone (by linarith : 0 ≤ 2 * h)))

theorem ccmGammaHigherBinetModeDensity_mul_dual {h : ℝ} (hh : 0 < h) :
    ccmGammaHigherBinetModeDensity h * ccmGammaHigherBinetDualDensity h = 1 := by
  have hA : Real.exp (h / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hB : Real.exp (2 * h) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hden : 1 - Real.exp (-(2 * h)) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hC : Real.exp (h * 2) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  unfold ccmGammaHigherBinetModeDensity ccmGammaHigherBinetDualDensity
  rw [show Real.exp (-(h / 2)) = (Real.exp (h / 2))⁻¹ by
        rw [← Real.exp_neg],
      show Real.exp (-(2 * h)) = (Real.exp (2 * h))⁻¹ by
        rw [← Real.exp_neg]]
  field_simp [hC]

theorem ccmActualHeadTranslationDefect_neg (h : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect (-h) f = ccmActualHeadTranslationDefect h f := by
  have heq :
      logTranslationCLM h (logTranslationCLM (-h) f - f) =
        -(logTranslationCLM h f - f) := by
    rw [map_sub, logTranslationCLM_add_apply]
    rw [show h + -h = 0 by ring]
    rw [logTranslationCLM_zero_apply]
    abel
  unfold ccmActualHeadTranslationDefect
  calc
    ‖logTranslationCLM (-h) f - f‖ ^ 2 =
        ‖logTranslationCLM h (logTranslationCLM (-h) f - f)‖ ^ 2 := by
          rw [logTranslation_norm]
    _ = ‖-(logTranslationCLM h f - f)‖ ^ 2 := by rw [heq]
    _ = ‖logTranslationCLM h f - f‖ ^ 2 := by rw [norm_neg]

theorem ccmActualHeadTranslationDefect_abs (h : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect |h| f = ccmActualHeadTranslationDefect h f := by
  rcases le_total 0 h with hh | hh
  · rw [abs_of_nonneg hh]
  · rw [abs_of_nonpos hh, ccmActualHeadTranslationDefect_neg]

theorem integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    Integrable (fun r : ℝ =>
      ccmGammaHigherBinetModeDensity |r| *
        ccmActualHeadTranslationDefect |r|
          (ccmArchimedeanFormToAperture a u : SoninL2)) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  let G : ℝ → ℝ := fun h =>
    ccmGammaHigherBinetModeDensity h * ccmActualHeadTranslationDefect h f
  have hint : IntegrableOn G (Ioi (0 : ℝ)) := by
    simpa only [G, f] using
      integrableOn_ccmGammaHigherBinetModeDensity_mul_translationDefect_formDomain a u
  have hpos : IntegrableOn (fun r : ℝ => G |r|) (Ioi (0 : ℝ)) := by
    refine hint.congr_fun ?_ measurableSet_Ioi
    intro r hr
    change G r = G |r|
    rw [abs_of_pos hr]
  have hneg : IntegrableOn (fun r : ℝ => G |r|) (Iic (0 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hall := hneg.union hpos
  simpa [IntegrableOn, Iic_union_Ioi, G, f] using hall

theorem integral_ccmGammaHigherBinetSymmetricEnergy_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (∫ r : ℝ,
      ccmGammaHigherBinetModeDensity |r| *
        ccmActualHeadTranslationDefect |r|
          (ccmArchimedeanFormToAperture a u : SoninL2)) =
      2 * ccmActualHeadGammaHigherBinetModeEnergy
        (ccmArchimedeanFormToAperture a u : SoninL2) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  calc
    (∫ r : ℝ,
        ccmGammaHigherBinetModeDensity |r| *
          ccmActualHeadTranslationDefect |r| f) =
        2 * ∫ h in Ioi (0 : ℝ),
          ccmGammaHigherBinetModeDensity h *
            ccmActualHeadTranslationDefect h f := by
              simpa only using integral_comp_abs
                (f := fun h : ℝ => ccmGammaHigherBinetModeDensity h *
                  ccmActualHeadTranslationDefect h f)
    _ = _ := by
      rw [← ccmActualHeadGammaHigherBinetModeEnergy_eq_integral_formDomain a u]

/-- One quantile cell pushed to displacement from its actual prime logarithm. -/
def ccmOutgoingQuantileDisplacementCellDensity (n : ℕ) (r : ℝ) : ℝ :=
  (Ioc
    (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
    (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)).indicator
      (fun s : ℝ => Real.exp ((s + Real.log n) / 2)) r

/-- Literal finite-head displacement density. Overlapping displaced cells add before squaring. -/
def ccmOutgoingQuantileDisplacementDensity (N : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r

/-- Arithmetic chi-square cost seen by the reciprocal higher-Binet density. -/
def ccmOutgoingQuantileGammaChiSquare (N : ℕ) : ℝ :=
  ∫ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r ^ 2 *
    ccmGammaHigherBinetDualDensity |r|

theorem measurable_ccmOutgoingQuantileDisplacementCellDensity (n : ℕ) :
    Measurable (ccmOutgoingQuantileDisplacementCellDensity n) := by
  unfold ccmOutgoingQuantileDisplacementCellDensity
  exact (by fun_prop : Measurable fun s : ℝ =>
    Real.exp ((s + Real.log n) / 2)).indicator measurableSet_Ioc

theorem measurable_ccmOutgoingQuantileDisplacementDensity (N : ℕ) :
    Measurable (ccmOutgoingQuantileDisplacementDensity N) := by
  unfold ccmOutgoingQuantileDisplacementDensity
  exact Finset.measurable_sum (Finset.range N) fun n _ =>
    measurable_ccmOutgoingQuantileDisplacementCellDensity n

theorem ccmOutgoingQuantileDisplacementCellDensity_nonneg (n : ℕ) (r : ℝ) :
    0 ≤ ccmOutgoingQuantileDisplacementCellDensity n r := by
  unfold ccmOutgoingQuantileDisplacementCellDensity
  by_cases hr : r ∈ Ioc
      (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
      (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)
  · rw [Set.indicator_of_mem hr]
    positivity
  · simp [hr]

theorem ccmOutgoingQuantileDisplacementDensity_nonneg (N : ℕ) (r : ℝ) :
    0 ≤ ccmOutgoingQuantileDisplacementDensity N r := by
  unfold ccmOutgoingQuantileDisplacementDensity
  exact Finset.sum_nonneg fun n _ =>
    ccmOutgoingQuantileDisplacementCellDensity_nonneg n r

theorem integrable_ccmOutgoingQuantileDisplacementCellPair_mul_dual
    (n m : ℕ) :
    Integrable (fun r : ℝ =>
      ccmOutgoingQuantileDisplacementCellDensity n r *
        ccmOutgoingQuantileDisplacementCellDensity m r *
          ccmGammaHigherBinetDualDensity |r|) := by
  let Sn : Set ℝ := Ioc
    (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
    (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)
  let Sm : Set ℝ := Ioc
    (ccmOutgoingPrimeQuantileBoundary m - Real.log m)
    (ccmOutgoingPrimeQuantileBoundary (m + 1) - Real.log m)
  let F : ℝ → ℝ := fun r =>
    Real.exp ((r + Real.log n) / 2) *
      Real.exp ((r + Real.log m) / 2) *
        ccmGammaHigherBinetDualDensity |r|
  have hF : Continuous F := by
    dsimp only [F]
    unfold ccmGammaHigherBinetDualDensity
    fun_prop
  have hint : IntegrableOn F (Sn ∩ Sm) := by
    have hbase : IntegrableOn F (Icc
        (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
        (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)) :=
      hF.integrableOn_Icc
    refine hbase.mono_set ?_
    intro r hr
    exact ⟨hr.1.1.le, hr.1.2⟩
  have hind := hint.integrable_indicator (measurableSet_Ioc.inter measurableSet_Ioc)
  have heq : (fun r : ℝ =>
      ccmOutgoingQuantileDisplacementCellDensity n r *
        ccmOutgoingQuantileDisplacementCellDensity m r *
          ccmGammaHigherBinetDualDensity |r|) = (Sn ∩ Sm).indicator F := by
    funext r
    by_cases hn : r ∈ Sn <;> by_cases hm : r ∈ Sm <;>
      simp [ccmOutgoingQuantileDisplacementCellDensity, Sn, Sm, F, hn, hm]
  rw [heq]
  exact hind

set_option maxHeartbeats 200000 in
theorem integrable_ccmOutgoingQuantileGammaChiSquareDensity (N : ℕ) :
    Integrable (fun r : ℝ => ccmOutgoingQuantileDisplacementDensity N r ^ 2 *
      ccmGammaHigherBinetDualDensity |r|) := by
  have heq : (fun r : ℝ => ccmOutgoingQuantileDisplacementDensity N r ^ 2 *
      ccmGammaHigherBinetDualDensity |r|) =
      fun r : ℝ => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ccmOutgoingQuantileDisplacementCellDensity n r *
          ccmOutgoingQuantileDisplacementCellDensity m r *
            ccmGammaHigherBinetDualDensity |r| := by
    funext r
    unfold ccmOutgoingQuantileDisplacementDensity
    rw [pow_two, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [heq]
  exact integrable_finsetSum (Finset.range N) fun n _ =>
    integrable_finsetSum (Finset.range N) fun m _ =>
      integrable_ccmOutgoingQuantileDisplacementCellPair_mul_dual n m

theorem ccmOutgoingQuantileGammaChiSquare_nonneg (N : ℕ) :
    0 ≤ ccmOutgoingQuantileGammaChiSquare N := by
  unfold ccmOutgoingQuantileGammaChiSquare
  apply integral_nonneg
  intro r
  exact mul_nonneg (sq_nonneg _) (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem integrable_ccmOutgoingQuantileDisplacementCellDensity_mul_sqrtDefect
    (n : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ =>
      ccmOutgoingQuantileDisplacementCellDensity n r *
        Real.sqrt (ccmActualHeadTranslationDefect r f)) := by
  let S : Set ℝ := Ioc
    (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
    (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)
  let F : ℝ → ℝ := fun r =>
    Real.exp ((r + Real.log n) / 2) *
      Real.sqrt (ccmActualHeadTranslationDefect r f)
  have hF : Continuous F := by
    dsimp only [F]
    apply Continuous.mul (by fun_prop)
    apply Continuous.sqrt
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  have hint : IntegrableOn F S := by
    have hbase : IntegrableOn F (Icc
        (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
        (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)) :=
      hF.integrableOn_Icc
    refine hbase.mono_set ?_
    intro r hr
    exact ⟨hr.1.le, hr.2⟩
  have hind := hint.integrable_indicator measurableSet_Ioc
  have heq : (fun r : ℝ =>
      ccmOutgoingQuantileDisplacementCellDensity n r *
        Real.sqrt (ccmActualHeadTranslationDefect r f)) = S.indicator F := by
    funext r
    by_cases hr : r ∈ S <;>
      simp [ccmOutgoingQuantileDisplacementCellDensity, S, F, hr]
  rw [heq]
  exact hind

theorem integrable_ccmOutgoingQuantileDisplacementDensity_mul_sqrtDefect
    (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => ccmOutgoingQuantileDisplacementDensity N r *
      Real.sqrt (ccmActualHeadTranslationDefect r f)) := by
  have heq : (fun r : ℝ => ccmOutgoingQuantileDisplacementDensity N r *
      Real.sqrt (ccmActualHeadTranslationDefect r f)) =
      fun r : ℝ => ∑ n ∈ Finset.range N,
        ccmOutgoingQuantileDisplacementCellDensity n r *
          Real.sqrt (ccmActualHeadTranslationDefect r f) := by
    funext r
    unfold ccmOutgoingQuantileDisplacementDensity
    rw [Finset.sum_mul]
  rw [heq]
  exact integrable_finsetSum (Finset.range N) fun n _ =>
    integrable_ccmOutgoingQuantileDisplacementCellDensity_mul_sqrtDefect n f

theorem integral_quantileCell_sqrtDefect_eq_displacementDensity
    (n : ℕ) (f : SoninL2) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) *
        Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) =
      ∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r *
        Real.sqrt (ccmActualHeadTranslationDefect r f) := by
  let lo := ccmOutgoingPrimeQuantileBoundary n - Real.log n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n
  let S : Set ℝ := Ioc lo hi
  let G : ℝ → ℝ := fun r =>
    Real.exp ((r + Real.log n) / 2) *
      Real.sqrt (ccmActualHeadTranslationDefect r f)
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := ccmOutgoingPrimeQuantileBoundary n)
    (b := ccmOutgoingPrimeQuantileBoundary (n + 1)) G (Real.log n)
  have hlohi : lo ≤ hi := by
    dsimp only [lo, hi]
    exact sub_le_sub_right (ccmOutgoingPrimeQuantileBoundary_mono_step n) _
  calc
    (∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) *
        Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1), G (h - Real.log n) := by
        apply intervalIntegral.integral_congr
        intro h hh
        dsimp only [G]
        congr 2
        ring
    _ = ∫ r in lo..hi, G r := by simpa only [lo, hi] using hshift
    _ = ∫ r in S, G r := by
      rw [intervalIntegral.integral_of_le hlohi]
    _ = ∫ r : ℝ, S.indicator G r := by
      rw [integral_indicator measurableSet_Ioc]
    _ = ∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r *
        Real.sqrt (ccmActualHeadTranslationDefect r f) := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ S <;>
        simp [ccmOutgoingQuantileDisplacementCellDensity, S, G, lo, hi, hr]

theorem sum_integral_quantileCells_sqrtDefect_eq_displacementDensity
    (N : ℕ) (f : SoninL2) :
    (∑ n ∈ Finset.range N,
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) =
      ∫ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r *
        Real.sqrt (ccmActualHeadTranslationDefect r f) := by
  calc
    _ = ∑ n ∈ Finset.range N,
        ∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r *
          Real.sqrt (ccmActualHeadTranslationDefect r f) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_quantileCell_sqrtDefect_eq_displacementDensity n f
    _ = ∫ r : ℝ, ∑ n ∈ Finset.range N,
        ccmOutgoingQuantileDisplacementCellDensity n r *
          Real.sqrt (ccmActualHeadTranslationDefect r f) := by
      rw [integral_finsetSum (Finset.range N) fun n _ =>
        integrable_ccmOutgoingQuantileDisplacementCellDensity_mul_sqrtDefect n f]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      unfold ccmOutgoingQuantileDisplacementDensity
      rw [Finset.sum_mul]

theorem abs_integral_quantileCell_autocorrelationTransport_le_sqrtDefect
    (n : ℕ) (f : SoninL2) :
    |∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) *
        (ccmActualHeadSymmetricAutocorrelation h f -
          ccmActualHeadSymmetricAutocorrelation (Real.log n) f)| ≤
      ‖f‖ *
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) *
            Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) := by
  let F : ℝ → ℝ := fun h => Real.exp (h / 2) *
    (ccmActualHeadSymmetricAutocorrelation h f -
      ccmActualHeadSymmetricAutocorrelation (Real.log n) f)
  let G : ℝ → ℝ := fun h => ‖f‖ *
    (Real.exp (h / 2) *
      Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f))
  have hab := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hG : Continuous G := by
    dsimp only [G]
    apply Continuous.const_mul
    apply Continuous.mul (by fun_prop)
    apply Continuous.sqrt
    unfold ccmActualHeadTranslationDefect
    exact ((((continuous_logTranslationCLM f).comp
      (continuous_id.sub continuous_const)).sub continuous_const).norm).pow 2
  have hpoint : ∀ h : ℝ, ‖F h‖ ≤ G h := by
    intro h
    have hc :=
      abs_ccmActualHeadSymmetricAutocorrelation_sub_le_norm_mul_sqrt_defect
        h (Real.log n) f
    dsimp only [F, G]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (h / 2) *
          |ccmActualHeadSymmetricAutocorrelation h f -
            ccmActualHeadSymmetricAutocorrelation (Real.log n) f| ≤
        Real.exp (h / 2) *
          (‖f‖ * Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) :=
            mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ = _ := by ring
  have hnorm : ‖∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1), F h‖ ≤
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1), G h :=
    intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (Filter.Eventually.of_forall fun h _ => hpoint h)
      (hG.intervalIntegrable (μ := volume) _ _)
  change |∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1), F h| ≤ _
  calc
    |∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1), F h| =
      ‖∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1), F h‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1), G h := hnorm
    _ = ‖f‖ *
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) *
            Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) := by
      dsimp only [G]
      rw [intervalIntegral.integral_const_mul]

theorem abs_sum_integral_quantileCells_autocorrelationTransport_le_displacementRoot
    (N : ℕ) (f : SoninL2) :
    |∑ n ∈ Finset.range N,
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          (ccmActualHeadSymmetricAutocorrelation h f -
            ccmActualHeadSymmetricAutocorrelation (Real.log n) f)| ≤
      ‖f‖ * (∫ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r *
        Real.sqrt (ccmActualHeadTranslationDefect r f)) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        |∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) *
            (ccmActualHeadSymmetricAutocorrelation h f -
              ccmActualHeadSymmetricAutocorrelation (Real.log n) f)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, ‖f‖ *
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) *
            Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact abs_integral_quantileCell_autocorrelationTransport_le_sqrtDefect n f
    _ = ‖f‖ * (∑ n ∈ Finset.range N,
        ∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) *
            Real.sqrt (ccmActualHeadTranslationDefect (h - Real.log n) f)) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_integral_quantileCells_sqrtDefect_eq_displacementDensity]

/-- Weighted Cauchy--Schwarz pays the literal overlapping quantile displacement density with
the canonical higher-Binet Γ energy. -/
theorem integral_quantileDisplacementDensity_sqrtDefect_le_gammaChiSquare
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    let f := ccmArchimedeanFormToAperture a u
    (∫ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r *
        Real.sqrt (ccmActualHeadTranslationDefect r (f : SoninL2))) ≤
      Real.sqrt (ccmOutgoingQuantileGammaChiSquare N) *
        Real.sqrt (2 * ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2)) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  let ρ : ℝ → ℝ := ccmOutgoingQuantileDisplacementDensity N
  let κ : ℝ → ℝ := fun r => ccmGammaHigherBinetDualDensity |r|
  let e : ℝ → ℝ := fun r =>
    ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| f
  let A : ℝ → ℂ := fun r => Complex.ofReal (ρ r * Real.sqrt (κ r))
  let B : ℝ → ℂ := fun r => Complex.ofReal (Real.sqrt (e r))
  let W : ℝ → ℂ := fun _ => 1
  have hρm : Measurable ρ :=
    measurable_ccmOutgoingQuantileDisplacementDensity N
  have hκc : Continuous κ := by
    dsimp only [κ]
    unfold ccmGammaHigherBinetDualDensity
    fun_prop
  have hγm : Measurable fun r : ℝ => ccmGammaHigherBinetModeDensity |r| := by
    unfold ccmGammaHigherBinetModeDensity
    fun_prop
  have hEm : Measurable fun r : ℝ => ccmActualHeadTranslationDefect |r| f := by
    unfold ccmActualHeadTranslationDefect
    exact ((((continuous_logTranslationCLM f).comp continuous_abs).sub
      continuous_const).norm.pow 2).measurable
  have hem : Measurable e := by
    dsimp only [e]
    exact hγm.mul hEm
  have hAm : AEStronglyMeasurable A volume := by
    apply Measurable.aestronglyMeasurable
    dsimp only [A]
    fun_prop
  have hBm : AEStronglyMeasurable B volume := by
    apply Measurable.aestronglyMeasurable
    dsimp only [B]
    fun_prop
  have hWm : AEStronglyMeasurable W volume := by
    exact stronglyMeasurable_const.aestronglyMeasurable
  have hρ0 (r : ℝ) : 0 ≤ ρ r :=
    ccmOutgoingQuantileDisplacementDensity_nonneg N r
  have hκ0 (r : ℝ) : 0 ≤ κ r :=
    ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
  have hγ0 (r : ℝ) : 0 ≤ ccmGammaHigherBinetModeDensity |r| := by
    by_cases hr : r = 0
    · subst r
      simp [ccmGammaHigherBinetModeDensity]
    · exact (ccmGammaHigherBinetModeDensity_pos
        (abs_pos.mpr hr)).le
  have hE0 (r : ℝ) : 0 ≤ ccmActualHeadTranslationDefect |r| f := by
    unfold ccmActualHeadTranslationDefect
    positivity
  have he0 (r : ℝ) : 0 ≤ e r := mul_nonneg (hγ0 r) (hE0 r)
  have hAint : Integrable (fun r : ℝ => ‖A r‖ ^ 2 * ‖W r‖) := by
    refine (integrable_ccmOutgoingQuantileGammaChiSquareDensity N).congr
      (Filter.Eventually.of_forall fun r => ?_)
    dsimp only [A, W, ρ, κ]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ0 r) (Real.sqrt_nonneg _)), norm_one, mul_one]
    rw [mul_pow, Real.sq_sqrt (hκ0 r)]
  have hBint : Integrable (fun r : ℝ => ‖B r‖ ^ 2 * ‖W r‖) := by
    refine (integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u).congr
      (Filter.Eventually.of_forall fun r => ?_)
    dsimp only [B, W, e]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_one, mul_one, Real.sq_sqrt (he0 r)]
  have hroot (r : ℝ) :
      ‖A r‖ * ‖B r‖ * ‖W r‖ =
        ρ r * Real.sqrt (ccmActualHeadTranslationDefect r f) := by
    have hsqrt : Real.sqrt (κ r) * Real.sqrt (e r) =
        Real.sqrt (ccmActualHeadTranslationDefect |r| f) := by
      by_cases hr : r = 0
      · subst r
        have hdefzero : ccmActualHeadTranslationDefect 0 f = 0 := by
          unfold ccmActualHeadTranslationDefect
          rw [logTranslationCLM_zero_apply]
          simp
        dsimp only [κ, e]
        simp [hdefzero, ccmGammaHigherBinetDualDensity,
          ccmGammaHigherBinetModeDensity]
      · rw [← Real.sqrt_mul (hκ0 r)]
        congr 1
        dsimp only [κ, e]
        calc
          ccmGammaHigherBinetDualDensity |r| *
              (ccmGammaHigherBinetModeDensity |r| *
                ccmActualHeadTranslationDefect |r| f) =
            (ccmGammaHigherBinetModeDensity |r| *
              ccmGammaHigherBinetDualDensity |r|) *
                ccmActualHeadTranslationDefect |r| f := by ring
          _ = ccmActualHeadTranslationDefect |r| f := by
            rw [ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr)]
            ring
    dsimp only [A, B, W]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ0 r) (Real.sqrt_nonneg _)),
      abs_of_nonneg (Real.sqrt_nonneg _), norm_one, mul_one]
    rw [mul_assoc, hsqrt, ccmActualHeadTranslationDefect_abs]
  have hleft :
      (∫ r : ℝ, ‖A r‖ * ‖B r‖ * ‖W r‖) =
        ∫ r : ℝ, ρ r * Real.sqrt (ccmActualHeadTranslationDefect r f) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hroot
  have hAeq :
      (∫ r : ℝ, ‖A r‖ ^ 2 * ‖W r‖) =
        ccmOutgoingQuantileGammaChiSquare N := by
    unfold ccmOutgoingQuantileGammaChiSquare
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [A, W, ρ, κ]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ0 r) (Real.sqrt_nonneg _)), norm_one, mul_one]
    rw [mul_pow, Real.sq_sqrt (hκ0 r)]
  have hBeq :
      (∫ r : ℝ, ‖B r‖ ^ 2 * ‖W r‖) =
        2 * ccmActualHeadGammaHigherBinetModeEnergy f := by
    rw [← integral_ccmGammaHigherBinetSymmetricEnergy_formDomain a u]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [B, W, e]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_one, mul_one, Real.sq_sqrt (he0 r)]
  have hcs :=
    GaloisForLFunctions.HTGeometry.integral_mul_mul_weight_le_sqrt_mul_sqrt
      hAm hBm hWm hAint hBint
  rw [hleft, hAeq, hBeq] at hcs
  exact hcs

theorem abs_sum_integral_quantileCells_autocorrelationTransport_le_gammaChiSquare
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    let f := ccmArchimedeanFormToAperture a u
    |∑ n ∈ Finset.range N,
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          (ccmActualHeadSymmetricAutocorrelation h (f : SoninL2) -
            ccmActualHeadSymmetricAutocorrelation (Real.log n) (f : SoninL2))| ≤
      ‖f‖ * Real.sqrt (ccmOutgoingQuantileGammaChiSquare N) *
        Real.sqrt (2 * ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2)) := by
  let f := ccmArchimedeanFormToAperture a u
  have hroot :=
    abs_sum_integral_quantileCells_autocorrelationTransport_le_displacementRoot
      N (f : SoninL2)
  have hcs := integral_quantileDisplacementDensity_sqrtDefect_le_gammaChiSquare a u N
  dsimp only at hroot hcs ⊢
  calc
    _ ≤ ‖(f : SoninL2)‖ *
        (Real.sqrt (ccmOutgoingQuantileGammaChiSquare N) *
          Real.sqrt (2 * ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2))) :=
      hroot.trans (mul_le_mul_of_nonneg_left hcs (norm_nonneg _))
    _ = _ := by
      rw [show ‖(f : SoninL2)‖ = ‖f‖ by rfl]
      ring

/-- Signed finite quantile-cell autocorrelation current after prime--polar scalar cancellation. -/
def ccmOutgoingQuantileCellAutocorrelationCurrent (N : ℕ) (f : SoninL2) : ℝ :=
  ∑ n ∈ Finset.range N,
    ∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) *
        (ccmActualHeadSymmetricAutocorrelation h f -
          ccmActualHeadSymmetricAutocorrelation (Real.log n) f)

/-- Completing the Γ square absorbs the signed finite quantile current. The only price is the
source-only overlapping displacement chi-square, with no absolute prime or polar mass. -/
theorem quantileCells_higherGamma_signedControl
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    -(2 * ccmOutgoingQuantileGammaChiSquare N *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2) ≤
      ccmActualHeadGammaHigherBinetModeEnergy
          (ccmArchimedeanFormToAperture a u : SoninL2) +
        2 * ccmOutgoingQuantileCellAutocorrelationCurrent N
          (ccmArchimedeanFormToAperture a u : SoninL2) := by
  let f := ccmArchimedeanFormToAperture a u
  let A := ccmOutgoingQuantileGammaChiSquare N
  let H := ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2)
  let S := ccmOutgoingQuantileCellAutocorrelationCurrent N (f : SoninL2)
  have hA : 0 ≤ A := ccmOutgoingQuantileGammaChiSquare_nonneg N
  have hH : 0 ≤ H := ccmActualHeadGammaHigherBinetModeEnergy_nonneg _
  have hn : 0 ≤ ‖f‖ := norm_nonneg _
  have habs : |S| ≤ ‖f‖ * Real.sqrt A * Real.sqrt (2 * H) := by
    simpa only [A, H, S, f, ccmOutgoingQuantileCellAutocorrelationCurrent] using
      abs_sum_integral_quantileCells_autocorrelationTransport_le_gammaChiSquare a u N
  have hS : -(‖f‖ * Real.sqrt A * Real.sqrt (2 * H)) ≤ S :=
    (neg_le_neg habs).trans (neg_abs_le S)
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsH : Real.sqrt (2 * H) ^ 2 = 2 * H :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hH)
  have hsq : 0 ≤
      (Real.sqrt (2 * H) - 2 * ‖f‖ * Real.sqrt A) ^ 2 := sq_nonneg _
  dsimp only [A, H, S, f] at hS hsA hsH hsq ⊢
  nlinarith

/-- The terminal completed-error current is controlled with its actual orientation left intact.
The scalar is exactly the completed error relative to the quantile threshold. -/
theorem abs_quantileTerminalAutocorrelation_le_completedErrorMismatch
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    |∫ h in ccmOutgoingPrimeQuantileBoundary
          (Nat.floor (Real.exp (2 * a.1)) + 1)..(2 * a.1),
      Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1| ≤
      |criticalMellinCompletedError (2 * a.1) -
          2 * (1 - Real.exp (-((2 * a.1) / 2)))| * ‖f‖ ^ 2 := by
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  let b := ccmOutgoingPrimeQuantileBoundary N
  let T := 2 * a.1
  let F : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1
  let G : ℝ → ℝ := fun h => ‖f‖ ^ 2 * Real.exp (h / 2)
  have hG : Continuous G := by
    dsimp only [G]
    fun_prop
  have hpoint (h : ℝ) : ‖F h‖ ≤ G h := by
    have hc := abs_ccmActualHeadSymmetricAutocorrelation_le_norm_sq h f.1
    rw [show ‖(f.1 : SoninL2)‖ = ‖f‖ by rfl] at hc
    dsimp only [F, G]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (h / 2) * |ccmActualHeadSymmetricAutocorrelation h f.1| ≤
          Real.exp (h / 2) * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ = ‖f‖ ^ 2 * Real.exp (h / 2) := by ring
  have hnorm : ‖∫ h in b..T, F h‖ ≤ |∫ h in b..T, G h| :=
    intervalIntegral.norm_integral_le_abs_of_norm_le (μ := volume)
      (Filter.Eventually.of_forall fun h => hpoint h)
      (hG.intervalIntegrable (μ := volume) _ _)
  have hmass := integral_exp_half_quantileBoundary_to_eq_massMismatch T N
  have herror := quantileTerminalMass_eq_completedError_sub_threshold T
  change |∫ h in b..T, F h| ≤ _
  calc
    |∫ h in b..T, F h| = ‖∫ h in b..T, F h‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ |∫ h in b..T, G h| := hnorm
    _ = |‖f‖ ^ 2 * (∫ h in b..T, Real.exp (h / 2))| := by
      dsimp only [G]
      rw [intervalIntegral.integral_const_mul]
    _ = |‖f‖ ^ 2 *
        (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N))| := by
      rw [hmass]
    _ = |criticalMellinCompletedError T -
          2 * (1 - Real.exp (-(T / 2)))| * ‖f‖ ^ 2 := by
      rw [herror]
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖f‖)]
      ring

theorem quantileTerminalAutocorrelation_ge_neg_completedErrorMismatch
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    -(|criticalMellinCompletedError (2 * a.1) -
          2 * (1 - Real.exp (-((2 * a.1) / 2)))| * ‖f‖ ^ 2) ≤
      ∫ h in ccmOutgoingPrimeQuantileBoundary
          (Nat.floor (Real.exp (2 * a.1)) + 1)..(2 * a.1),
        Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1 := by
  have habs := abs_quantileTerminalAutocorrelation_le_completedErrorMismatch a f
  exact (neg_le_neg habs).trans (neg_abs_le _)

/-- Unconditional signed control of completed error against actual Γ-head autocorrelations.
Prime, polar, and first Γ mode have already cancelled; only higher Γ energy, literal cell current,
and terminal completed-error mismatch occur. -/
theorem higherGamma_add_outgoingQuantileAutocorrelationCurrent_lowerBound
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    (4 - 2 * |criticalMellinCompletedError (2 * a.1) -
          2 * (1 - Real.exp (-((2 * a.1) / 2)))| -
        2 * ccmOutgoingQuantileGammaChiSquare N) * ‖f‖ ^ 2 ≤
      ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  let ε := |criticalMellinCompletedError (2 * a.1) -
    2 * (1 - Real.exp (-((2 * a.1) / 2)))|
  let S := ccmOutgoingQuantileCellAutocorrelationCurrent N (f : SoninL2)
  let R := ∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
    Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1
  have hcells := quantileCells_higherGamma_signedControl a u N
  have hterminal := quantileTerminalAutocorrelation_ge_neg_completedErrorMismatch a f
  have hcurrent : ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f =
      4 * ‖f‖ ^ 2 + 2 * S + 2 * R := by
    unfold ccmActualHeadOutgoingQuantileAutocorrelationCurrent
    dsimp only [N, S, R, ccmOutgoingQuantileCellAutocorrelationCurrent]
  change -(2 * ccmOutgoingQuantileGammaChiSquare N * ‖f‖ ^ 2) ≤
      ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) + 2 * S at hcells
  change -(ε * ‖f‖ ^ 2) ≤ R at hterminal
  change (4 - 2 * ε - 2 * ccmOutgoingQuantileGammaChiSquare N) * ‖f‖ ^ 2 ≤ _
  rw [hcurrent]
  nlinarith

/-- Source-quadratic form of the signed Γ/quantile producer. This is the exact unconditional
source-only lower bound exposed after preserving prime--polar--Γ cancellation. -/
theorem ccmRestrictedWeilSourceQuadratic_ge_signedGammaQuantileProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    (2 * gammaHardyPhaseRate 0 + 4 -
        2 * |criticalMellinCompletedError (2 * a.1) -
          2 * (1 - Real.exp (-((2 * a.1) / 2)))| -
        2 * ccmOutgoingQuantileGammaChiSquare N) * ‖f‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hcore := higherGamma_add_outgoingQuantileAutocorrelationCurrent_lowerBound a u
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation a u
  dsimp only at hcore hsource ⊢
  rw [hsource]
  nlinarith

end RHTower
