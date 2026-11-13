import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.BoundedLipschitzCutoffsPreserveLogarithmicEnergy
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import GaloisForLFunctions.HTGeometry.HardyBoundary.LogarithmicWeightComparison
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing physical cutoffs in logarithmic energy

Uniformly bounded Lipschitz cutoffs tending pointwise to zero annihilate
finite-energy L² profiles in the positive logarithmic Fourier form.
The translation commutator gives an integrable jump majorant.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.HTGeometry
open CanonicalSystemOfTheWindowTower


/-- Bounded cutoffs tending pointwise to zero annihilate every L² profile strongly. -/
theorem tendsto_logarithmicCutoff_zero
    {χ : ℕ → ℝ → ℝ} (hm : ∀ n, Measurable (χ n))
    (hb : ∀ n x, |χ n x| ≤ 1)
    (hpt : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 0)) (f : RealLineL2) :
    Tendsto (fun n => logarithmicCutoffMultiplier (hm n) zero_le_one (hb n) f)
      atTop (𝓝 0) := by
  have hφ (n : ℕ) : Measurable (fun x : ℝ => (χ n x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hm n)
  have hφb (n : ℕ) (x : ℝ) : ‖(χ n x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb n x
  have hzb (x : ℝ) : ‖(0 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
  have ht := tendsto_lpBoundedMulCLM_apply (μ := (volume : Measure ℝ)) hφ
    (ψ := fun _ : ℝ => (0 : ℂ)) measurable_const zero_le_one hφb hzb
    (fun x => by
      simpa only [Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto 0).comp (hpt x)) f
  have hz : lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (φ := fun _ : ℝ => (0 : ℂ)) measurable_const zero_le_one hzb f = 0 := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (φ := fun _ : ℝ => (0 : ℂ)) measurable_const zero_le_one hzb f,
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
    rw [hx, hz, zero_mul]
  rw [hz] at ht
  exact ht

/-- The reference Lévy density has a finite second jump moment. -/
theorem integrable_logReferenceLevyDensity_sq :
    IntegrableOn (fun t : ℝ => logReferenceLevyDensity t * t ^ 2) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num)
  apply hi.mono'
    ((measurable_logReferenceLevyDensity.mul (measurable_id.pow_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (0 : ℝ) < t at ht
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, id_eq]
  rw [Real.norm_of_nonneg (mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg t))]
  calc
    _ = (t / 2) * Real.exp (-t) := by
      unfold logReferenceLevyDensity
      field_simp [ne_of_gt ht]
    _ ≤ Real.exp (t / 2) * Real.exp (-t) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith only [Real.add_one_le_exp (t / 2)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniform Lipschitz bounds dominate the cutoff commutator in the jump integral. -/
theorem tendsto_logarithmicCutoff_jumpEnergy_zero
    {χ : ℕ → ℝ → ℝ} (hm : ∀ n, Measurable (χ n))
    (hb : ∀ n x, |χ n x| ≤ 1)
    (hlip : ∀ n x y, |χ n x - χ n y| ≤ |x - y|)
    (hpt : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 0))
    {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ), logReferenceLevyDensity t *
      ‖logTranslationCLM t (logarithmicCutoffMultiplier (hm n) zero_le_one (hb n) f) -
        logarithmicCutoffMultiplier (hm n) zero_le_one (hb n) f‖ ^ 2)
      atTop (𝓝 0) := by
  let g : ℕ → RealLineL2 := fun n => logarithmicCutoffMultiplier (hm n) zero_le_one (hb n) f
  have hg : Tendsto g atTop (𝓝 0) := tendsto_logarithmicCutoff_zero hm hb hpt f
  have hE := (hasLogarithmicEnergy_iff_integrable_jump f).mp hf
  have hmajor := (hE.const_mul 2).add
    (integrable_logReferenceLevyDensity_sq.const_mul (2 * ‖f‖ ^ 2))
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun t : ℝ =>
      logReferenceLevyDensity t * ‖logTranslationCLM t (g n) - g n‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    measurable_logReferenceLevyDensity.aestronglyMeasurable.mul
      (((continuous_logTranslationCLM (g n)).sub continuous_const).aestronglyMeasurable.norm.pow 2)
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖logReferenceLevyDensity t * ‖logTranslationCLM t (g n) - g n‖ ^ 2‖ ≤
        2 * (logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2) +
          (2 * ‖f‖ ^ 2) * (logReferenceLevyDensity t * t ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (0 : ℝ) < t at ht
    have hl := logarithmicCutoff_translation_loss_le (hm n) zero_le_one (hb n)
      zero_le_one (fun x y => by simpa only [one_mul] using hlip n x y) f t
    simp only [one_mul] at hl
    have hs : ‖logTranslationCLM t (g n) - g n‖ ^ 2 ≤
        2 * ‖logTranslationCLM t f - f‖ ^ 2 + 2 * t ^ 2 * ‖f‖ ^ 2 := by
      calc
        _ ≤ (‖logTranslationCLM t f - f‖ + |t| * ‖f‖) ^ 2 := by
          simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hl
        _ ≤ 2 * ‖logTranslationCLM t f - f‖ ^ 2 + 2 * (|t| * ‖f‖) ^ 2 := by
          nlinarith only [sq_nonneg (‖logTranslationCLM t f - f‖ - |t| * ‖f‖)]
        _ = _ := by rw [mul_pow, sq_abs]; ring
    rw [Real.norm_of_nonneg (mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg _))]
    have hw := mul_le_mul_of_nonneg_left hs (logReferenceLevyDensity_nonneg ht.le)
    nlinarith only [hw]
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun n => logReferenceLevyDensity t *
        ‖logTranslationCLM t (g n) - g n‖ ^ 2) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro t
    have ht := (((logTranslationCLM t).continuous.tendsto 0).comp hg).sub hg
    simpa only [map_zero, sub_zero, norm_zero, zero_pow two_ne_zero, mul_zero] using
      (ht.norm.pow 2).const_mul (logReferenceLevyDensity t)
  have h := tendsto_integral_of_dominated_convergence _ hmeas hmajor hbound hpoint
  simpa only [integral_zero] using h

#print axioms tendsto_logarithmicCutoff_zero
#print axioms integrable_logReferenceLevyDensity_sq
#print axioms tendsto_logarithmicCutoff_jumpEnergy_zero

/-- The positive reference Fourier energy is mass plus the literal jump energy. -/
theorem logarithmicReferenceEnergy_eq_mass_add_jump {f : RealLineL2}
    (hf : HasLogarithmicEnergy f) :
    (∫ ξ : ℝ, positiveLogarithmicSymbol (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2) =
      ‖f‖ ^ 2 + ∫ t in Ioi (0 : ℝ),
        logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2 := by
  have hfull := (hasLogarithmicEnergy_iff_integrable f).mp hf
  have hsq : Integrable (fun ξ : ℝ => ‖fourierUnitary f ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hexc : Integrable (fun ξ : ℝ =>
      (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2) := by
    apply (hfull.sub hsq).congr
    exact Eventually.of_forall fun ξ => by dsimp only [Pi.sub_apply]; ring
  have hjump := (hasLogarithmicEnergy_iff_integrable_jump f).mp hf
  have hexcn : ∀ᵐ ξ : ℝ, 0 ≤
      (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) * ‖fourierUnitary f ξ‖ ^ 2 :=
    Eventually.of_forall fun ξ => mul_nonneg
      (sub_nonneg.mpr (one_le_positiveLogarithmicSymbol _)) (sq_nonneg _)
  have hjumpn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ logReferenceLevyDensity t * ‖logTranslationCLM t f - f‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg _)
  have he := logarithmicJumpEnergyL_eq_fourier f
  unfold logarithmicJumpEnergyL at he
  rw [← ofReal_integral_eq_lintegral_ofReal hjump hjumpn,
    ← ofReal_integral_eq_lintegral_ofReal hexc hexcn] at he
  have he' := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hjumpn),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hexcn)] at he'
  have hmass : (∫ ξ : ℝ, ‖fourierUnitary f ξ‖ ^ 2) = ‖f‖ ^ 2 := by
    rw [← _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume, fourierUnitary.norm_map]
  calc
    _ = (∫ ξ : ℝ, ‖fourierUnitary f ξ‖ ^ 2) +
        ∫ ξ : ℝ, (positiveLogarithmicSymbol (2 * Real.pi * ξ) - 1) *
          ‖fourierUnitary f ξ‖ ^ 2 := by
      rw [← integral_add hsq hexc]
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by dsimp only; ring
    _ = _ := by rw [hmass, ← he']

/-- Vanishing cutoffs converge in positive logarithmic Fourier energy. -/
theorem tendsto_logarithmicCutoff_positiveEnergy_zero
    {χ : ℕ → ℝ → ℝ} (hm : ∀ n, Measurable (χ n))
    (hb : ∀ n x, |χ n x| ≤ 1)
    (hlip : ∀ n x y, |χ n x - χ n y| ≤ |x - y|)
    (hpt : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 0))
    {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    Tendsto (fun n => ∫ ξ : ℝ, max (Real.log |ξ|) 0 *
      ‖fourierUnitary (logarithmicCutoffMultiplier (hm n) zero_le_one (hb n) f) ξ‖ ^ 2)
      atTop (𝓝 0) := by
  let g : ℕ → RealLineL2 := fun n => logarithmicCutoffMultiplier (hm n) zero_le_one (hb n) f
  have hg : Tendsto g atTop (𝓝 0) := tendsto_logarithmicCutoff_zero hm hb hpt f
  have hD (n : ℕ) : HasLogarithmicEnergy (g n) :=
    hasLogarithmicEnergy_cutoff (hm n) zero_le_one (hb n) zero_le_one
      (fun x y => by simpa only [one_mul] using hlip n x y) hf
  have hfull : Tendsto (fun n => ∫ ξ : ℝ,
      positiveLogarithmicSymbol (2 * Real.pi * ξ) * ‖fourierUnitary (g n) ξ‖ ^ 2)
      atTop (𝓝 0) := by
    have hmass : Tendsto (fun n => ‖g n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero, zero_pow two_ne_zero] using hg.norm.pow 2
    have hj := tendsto_logarithmicCutoff_jumpEnergy_zero hm hb hlip hpt hf
    have he (n : ℕ) := logarithmicReferenceEnergy_eq_mass_add_jump (hD n)
    simpa only [he, add_zero] using hmass.add hj
  have hc : (1 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  apply squeeze_zero (fun n => integral_nonneg fun ξ =>
    mul_nonneg (le_max_right _ _) (sq_nonneg _)) (fun n => ?_) hfull
  have hfi := (hasLogarithmicEnergy_iff_integrable (g n)).mp (hD n)
  have hpi := (integrable_logarithmicReference_iff_positiveLog hc (fourierUnitary (g n))).mp hfi
  apply integral_mono hpi hfi
  exact fun ξ => mul_le_mul_of_nonneg_right
    (max_log_abs_le_positiveLogarithmicSymbol hc ξ) (sq_nonneg _)

#print axioms logarithmicReferenceEnergy_eq_mass_add_jump
#print axioms tendsto_logarithmicCutoff_positiveEnergy_zero
end GaloisForLFunctions.HTGeometry

