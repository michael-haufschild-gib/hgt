import GaloisForLFunctions.HTGeometry.BurnolPositivePackets
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography
import Mathlib.MeasureTheory.Integral.Prod

/-! Finite positive measures act by strong mixtures of the literal weighted shifts. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexOrder NNReal

namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

theorem norm_burnolWeightedShift_apply_le (h : ℝ≥0) (f : BurnolHalfLineL2) :
    ‖burnolWeightedShift h f‖ ≤ ‖f‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (by
    simpa using mul_le_mul_of_nonneg_right (norm_burnolWeightedShift_le h) (norm_nonneg f))

theorem integrable_burnolWeightedShift (τ : Measure ℝ≥0) [IsFiniteMeasure τ]
    (f : BurnolHalfLineL2) : Integrable (fun h => burnolWeightedShift h f) τ :=
  (integrable_const ‖f‖).mono' (continuous_burnolWeightedShift_apply f).aestronglyMeasurable
    (ae_of_all _ fun h => norm_burnolWeightedShift_apply_le h f)

private theorem burnolShiftIntegral_bound (τ : Measure ℝ≥0) [IsFiniteMeasure τ]
    (f : BurnolHalfLineL2) :
    ‖∫ h, burnolWeightedShift h f ∂τ‖ ≤ (τ univ).toReal * ‖f‖ := by
  simpa only [measureReal_def, mul_comm] using
    (norm_integral_le_of_norm_le_const (ae_of_all τ fun h => norm_burnolWeightedShift_apply_le h f))

/-- Vectorwise Bochner integral; no operator-norm measurability assumption is made. -/
def burnolPositiveShiftMixture (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  ({ toFun := fun f => ∫ h, burnolWeightedShift h f ∂τ
     map_add' := fun f g => by
       simpa only [map_add] using integral_add
         (integrable_burnolWeightedShift τ f) (integrable_burnolWeightedShift τ g)
     map_smul' := fun c f => by
       simp only [map_smul, RingHom.id_apply, integral_smul] } :
    BurnolHalfLineL2 →ₗ[ℂ] BurnolHalfLineL2).mkContinuous (τ univ).toReal
      (burnolShiftIntegral_bound τ)

theorem burnolPositiveShiftMixture_apply (τ : Measure ℝ≥0) [IsFiniteMeasure τ]
    (f : BurnolHalfLineL2) :
    burnolPositiveShiftMixture τ f = ∫ h, burnolWeightedShift h f ∂τ := rfl

theorem norm_burnolPositiveShiftMixture_le (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    ‖burnolPositiveShiftMixture τ‖ ≤ (τ univ).toReal :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg (burnolShiftIntegral_bound τ)

theorem burnolPositiveShiftMixture_nonneg (τ : Measure ℝ≥0) [IsFiniteMeasure τ]
    {f : BurnolHalfLineL2} (hf : 0 ≤ f) : 0 ≤ burnolPositiveShiftMixture τ f :=
  integral_nonneg_of_ae (ae_of_all _ fun h => burnolWeightedShift_nonneg h hf)

def burnolMeasureLaplace (τ : Measure ℝ≥0) (lam : ℝ) : ℝ :=
  ∫ h : ℝ≥0, Real.exp (-(lam * h)) ∂τ

theorem burnolPositiveShiftMixture_rate (τ : Measure ℝ≥0) [IsFiniteMeasure τ]
    (lam : ℝ) (hlam : 0 < lam) :
    burnolPositiveShiftMixture τ (burnolRateFeature lam hlam) =
      (burnolMeasureLaplace τ lam : ℂ) • burnolRateFeature lam hlam := by
  rw [burnolPositiveShiftMixture_apply]
  have he : ∀ h : ℝ≥0, burnolWeightedShift h (burnolRateFeature lam hlam) =
      (Real.exp (-(lam * h)) : ℂ) • burnolRateFeature lam hlam := by
    intro h
    simpa only [burnolRateFeature, Nat.cast_zero, zero_add, one_mul, mul_one, mul_comm]
      using burnolWeightedShift_depthFeature h ⟨lam, hlam⟩ 0
  simp_rw [he]
  rw [integral_smul_const]
  congr 1
  exact integral_ofReal (𝕜 := ℂ)

theorem burnolPositiveShiftMixture_injective (τ σ : Measure ℝ≥0)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ]
    (he : burnolPositiveShiftMixture τ = burnolPositiveShiftMixture σ) : τ = σ := by
  apply LaplaceTomography.measure_eq_of_laplace_eq_succ
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := congrArg (fun T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 =>
    T (burnolRateFeature n hn')) he
  rw [burnolPositiveShiftMixture_rate, burnolPositiveShiftMixture_rate] at h
  have hne : burnolRateFeature n hn' ≠ 0 := by
    simpa only [burnolComplexFeature_ofReal, burnolRateFeature] using
      burnolComplexFeature_ne_zero (z := ((n : ℝ) : ℂ)) hn'
  exact Complex.ofReal_injective (smul_left_injective ℂ hne h)

/-- Positive convolution, including possible atoms at zero. -/
def burnolShiftMeasureConvolution (τ σ : Measure ℝ≥0) : Measure ℝ≥0 :=
  (τ.prod σ).map (fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2)

instance burnolShiftMeasureConvolution_finite (τ σ : Measure ℝ≥0)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] : IsFiniteMeasure (burnolShiftMeasureConvolution τ σ) := by
  unfold burnolShiftMeasureConvolution
  infer_instance

theorem burnolPositiveShiftMixture_comp (τ σ : Measure ℝ≥0)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    (burnolPositiveShiftMixture τ).comp (burnolPositiveShiftMixture σ) =
      burnolPositiveShiftMixture (burnolShiftMeasureConvolution τ σ) := by
  apply ContinuousLinearMap.ext
  intro f
  have hc : Continuous (fun p : ℝ≥0 × ℝ≥0 => burnolWeightedShift (p.1 + p.2) f) :=
    (continuous_burnolWeightedShift_apply f).comp (continuous_fst.add continuous_snd)
  have hi : Integrable (fun p : ℝ≥0 × ℝ≥0 => burnolWeightedShift (p.1 + p.2) f) (τ.prod σ) :=
    (integrable_const ‖f‖).mono' hc.aestronglyMeasurable
      (ae_of_all _ fun p => norm_burnolWeightedShift_apply_le _ f)
  change (∫ h, burnolWeightedShift h (∫ j, burnolWeightedShift j f ∂σ) ∂τ) = _
  simp_rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_burnolWeightedShift σ f)]
  have hs : ∀ h j : ℝ≥0, burnolWeightedShift h (burnolWeightedShift j f) =
      burnolWeightedShift (h + j) f := fun h j =>
    congrArg (fun T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 => T f)
      (burnolWeightedShift_comp h j)
  simp_rw [hs]
  rw [← integral_prod _ hi, burnolPositiveShiftMixture_apply, burnolShiftMeasureConvolution]
  exact (integral_map (φ := fun p : ℝ≥0 × ℝ≥0 => p.1 + p.2)
    (continuous_fst.add continuous_snd).measurable.aemeasurable
    (continuous_burnolWeightedShift_apply f).aestronglyMeasurable).symm

theorem burnolMeasureLaplace_nonneg (τ : Measure ℝ≥0) (lam : ℝ) :
    0 ≤ burnolMeasureLaplace τ lam := integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem tendsto_burnolMeasureLaplace_zero (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    Tendsto (burnolMeasureLaplace τ) (𝓝[>] (0 : ℝ)) (𝓝 (τ univ).toReal) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := τ) (l := 𝓝[>] (0 : ℝ))
    (F := fun lam (h : ℝ≥0) => Real.exp (-(lam * h))) (f := fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun _ => (by fun_prop : Continuous _).aestronglyMeasurable))
    (by
      filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact ae_of_all _ fun h => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hlam.le h.coe_nonneg)))
    (integrable_const 1)
    (ae_of_all _ fun h => by
      have hc : Continuous (fun lam : ℝ => Real.exp (-(lam * (h : ℝ)))) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds)
  change Tendsto (fun lam : ℝ => ∫ h : ℝ≥0, Real.exp (-(lam * h)) ∂τ) _ _
  simpa only [integral_const, measureReal_def, smul_eq_mul, mul_one] using h

/-- The mass bound is sharp, even when mass accumulates arbitrarily far along the half-line. -/
theorem norm_burnolPositiveShiftMixture (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    ‖burnolPositiveShiftMixture τ‖ = (τ univ).toReal := by
  apply le_antisymm (norm_burnolPositiveShiftMixture_le τ)
  apply le_of_tendsto (tendsto_burnolMeasureLaplace_zero τ)
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have h := (burnolPositiveShiftMixture τ).le_opNorm (burnolRateFeature lam hlam)
  rw [burnolPositiveShiftMixture_rate, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (burnolMeasureLaplace_nonneg τ lam)] at h
  have hn : burnolRateFeature lam hlam ≠ 0 := by
    simpa only [burnolComplexFeature_ofReal, burnolRateFeature] using
      burnolComplexFeature_ne_zero (z := (lam : ℂ)) hlam
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hn)

end GaloisForLFunctions.HTGeometry
