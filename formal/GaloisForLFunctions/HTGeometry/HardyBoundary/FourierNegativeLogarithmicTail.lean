import GaloisForLFunctions.HTGeometry.HardyBoundary.FourierFirstMomentWindow
import GaloisForLFunctions.HTGeometry.HardyBoundary.ExponentialDistributionTails
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Negative logarithmic Fourier tails from physical confinement

A physical cutoff at `exp(t/2)` controls the Fourier mass where the
negative logarithm exceeds `t`. Layer cake then gives a uniform integral
tail, including the logarithmic singularity at frequency zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform
namespace GaloisForLFunctions.HTGeometry

/-- The physical first moment bounds negative-logarithm superlevel measures. -/
theorem fourier_negativeLog_superlevel_le_firstMoment {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1)
    (hfirst : Integrable (fun u => |u| * ‖f u‖ ^ 2))
    {M : ℝ} (hM : (∫ u, |u| * ‖f u‖ ^ 2) ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    (volume.withDensity (fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)))
      {ξ | t < max (-Real.log |ξ|) 0} ≤
      ENNReal.ofReal ((8 + 2 * M) * Real.exp (-(t / 2))) := by
  let ν : Measure ℝ := volume.withDensity (fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2))
  have hsubset : {ξ : ℝ | t < max (-Real.log |ξ|) 0} ⊆
      Icc (-Real.exp (-t)) (Real.exp (-t)) := by
    intro ξ hξ
    by_cases hzero : ξ = 0
    · subst ξ
      exact ⟨neg_nonpos.mpr (Real.exp_pos _).le, (Real.exp_pos _).le⟩
    · have hl : t < -Real.log |ξ| :=
        (lt_max_iff.mp hξ).resolve_right (not_lt_of_ge ht)
      have hlog : Real.log |ξ| < -t := by linarith only [hl]
      exact abs_le.mp (((Real.log_lt_iff_lt_exp (abs_pos.mpr hzero)).mp hlog).le)
  have hbound := fourierWindow_mass_le_firstMoment hf1 hf2 hm hfirst hM
    (Real.exp_pos (t / 2)) (Real.exp_pos (-t)).le
  have hexp : Real.exp (-t) * Real.exp (t / 2) = Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hvalue : 8 * Real.exp (-t) * Real.exp (t / 2) + 2 * M / Real.exp (t / 2) =
      (8 + 2 * M) * Real.exp (-(t / 2)) := by
    rw [mul_assoc 8, hexp, div_eq_mul_inv (2 * M) (Real.exp (t / 2)), ← Real.exp_neg]
    ring
  calc
    _ ≤ ν (Icc (-Real.exp (-t)) (Real.exp (-t))) := measure_mono hsubset
    _ = ENNReal.ofReal (∫ ξ in Icc (-Real.exp (-t)) (Real.exp (-t)), ‖𝓕 f ξ‖ ^ 2) := by
      change (volume.withDensity (fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)))
        (Icc (-Real.exp (-t)) (Real.exp (-t))) = _
      rw [withDensity_apply _ measurableSet_Icc]
      exact (ofReal_integral_eq_lintegral_ofReal
        (RHTower.integrable_norm_sq_fourier hf1 hf2).integrableOn
        (Eventually.of_forall fun ξ => sq_nonneg ‖𝓕 f ξ‖)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hbound.trans_eq hvalue)

/-- Negative logarithmic Fourier tails decay uniformly under a first-moment bound. -/
theorem lintegral_negativeLog_fourier_tail_le_firstMoment {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1)
    (hfirst : Integrable (fun u => |u| * ‖f u‖ ^ 2))
    {M : ℝ} (hM : (∫ u, |u| * ‖f u‖ ^ 2) ≤ M)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ ξ in {ξ : ℝ | T < max (-Real.log |ξ|) 0},
      ENNReal.ofReal (max (-Real.log |ξ|) 0 * ‖𝓕 f ξ‖ ^ 2)) ≤
      ENNReal.ofReal ((8 + 2 * M) * (T + 2) * Real.exp (-(T / 2))) := by
  let X : ℝ → ℝ := fun ξ => max (-Real.log |ξ|) 0
  let d : ℝ → ENNReal := fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)
  let S : Set ℝ := {ξ | T < X ξ}
  have hFourier := RHTower.continuous_fourier_of_integrable hf1
  have hX : Measurable X := by dsimp only [X]; fun_prop
  have hd : Measurable d := by dsimp only [d]; fun_prop
  have hS : MeasurableSet S := measurableSet_lt measurable_const hX
  have hM0 : 0 ≤ M :=
    (integral_nonneg fun u => mul_nonneg (abs_nonneg u) (sq_nonneg ‖f u‖)).trans hM
  have hC : 0 ≤ 8 + 2 * M := by linarith only [hM0]
  have ht := lintegral_tail_le_of_exponential_tail (volume.withDensity d) hX hC
    (fun t ht => fourier_negativeLog_superlevel_le_firstMoment hf1 hf2 hm hfirst hM ht) hT
  calc
    _ = ∫⁻ ξ, S.indicator (fun ξ => ENNReal.ofReal (X ξ * ‖𝓕 f ξ‖ ^ 2)) ξ :=
      (lintegral_indicator hS _).symm
    _ = ∫⁻ ξ, d ξ * S.indicator (fun ξ => ENNReal.ofReal (X ξ)) ξ := by
      apply lintegral_congr
      intro ξ
      by_cases hξ : ξ ∈ S
      · rw [indicator_of_mem hξ, indicator_of_mem hξ,
          ENNReal.ofReal_mul (le_max_right _ _)]
        exact mul_comm _ _
      · simp only [indicator_of_notMem hξ, mul_zero]
    _ = ∫⁻ ξ, S.indicator (fun ξ => ENNReal.ofReal (X ξ)) ξ ∂volume.withDensity d :=
      (lintegral_withDensity_eq_lintegral_mul volume hd (hX.ennreal_ofReal.indicator hS)).symm
    _ = ∫⁻ ξ in S, ENNReal.ofReal (X ξ) ∂volume.withDensity d := lintegral_indicator hS _
    _ ≤ _ := ht

/-- The complete negative logarithmic Fourier integral is controlled by the first moment. -/
theorem lintegral_negativeLog_fourier_le_firstMoment {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1)
    (hfirst : Integrable (fun u => |u| * ‖f u‖ ^ 2))
    {M : ℝ} (hM : (∫ u, |u| * ‖f u‖ ^ 2) ≤ M) :
    (∫⁻ ξ, ENNReal.ofReal (max (-Real.log |ξ|) 0 * ‖𝓕 f ξ‖ ^ 2)) ≤
      ENNReal.ofReal (16 + 4 * M) := by
  let X : ℝ → ℝ := fun ξ => max (-Real.log |ξ|) 0
  let d : ℝ → ENNReal := fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)
  have hFourier := RHTower.continuous_fourier_of_integrable hf1
  have hX : Measurable X := by dsimp only [X]; fun_prop
  have hd : Measurable d := by dsimp only [d]; fun_prop
  have hM0 : 0 ≤ M :=
    (integral_nonneg fun u => mul_nonneg (abs_nonneg u) (sq_nonneg ‖f u‖)).trans hM
  have hC : 0 ≤ 8 + 2 * M := by linarith only [hM0]
  have hb := lintegral_le_of_exponential_tail (volume.withDensity d) hX
    (fun ξ => le_max_right _ _) hC
    (fun t ht => fourier_negativeLog_superlevel_le_firstMoment hf1 hf2 hm hfirst hM ht)
  calc
    _ = ∫⁻ ξ, d ξ * ENNReal.ofReal (X ξ) := by
      apply lintegral_congr
      intro ξ
      rw [ENNReal.ofReal_mul (le_max_right _ _)]
      exact mul_comm _ _
    _ = ∫⁻ ξ, ENNReal.ofReal (X ξ) ∂volume.withDensity d :=
      (lintegral_withDensity_eq_lintegral_mul volume hd hX.ennreal_ofReal).symm
    _ ≤ ENNReal.ofReal (2 * (8 + 2 * M)) := hb
    _ = _ := congrArg ENNReal.ofReal (by ring)

/-- Finite physical first moment makes the negative logarithmic Fourier part integrable. -/
theorem integrable_negativeLog_fourier_of_firstMoment {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1)
    (hfirst : Integrable (fun u => |u| * ‖f u‖ ^ 2)) :
    Integrable (fun ξ => max (-Real.log |ξ|) 0 * ‖𝓕 f ξ‖ ^ 2) := by
  have hFourier := RHTower.continuous_fourier_of_integrable hf1
  have hmeas : Measurable (fun ξ => max (-Real.log |ξ|) 0 * ‖𝓕 f ξ‖ ^ 2) := by fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ =>
    mul_nonneg (le_max_right _ _) (sq_nonneg ‖𝓕 f ξ‖))).mpr
  exact (lintegral_negativeLog_fourier_le_firstMoment hf1 hf2 hm hfirst le_rfl).trans_lt
    ENNReal.ofReal_lt_top

/-- The real negative-logarithm tail has the same quantitative decay as its extended integral. -/
theorem integral_negativeLog_fourier_tail_le_firstMoment {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1)
    (hfirst : Integrable (fun u => |u| * ‖f u‖ ^ 2))
    {M : ℝ} (hM : (∫ u, |u| * ‖f u‖ ^ 2) ≤ M)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ ξ in {ξ : ℝ | T < max (-Real.log |ξ|) 0},
      max (-Real.log |ξ|) 0 * ‖𝓕 f ξ‖ ^ 2) ≤
      (8 + 2 * M) * (T + 2) * Real.exp (-(T / 2)) := by
  have hi : IntegrableOn (fun ξ => max (-Real.log |ξ|) 0 * ‖𝓕 f ξ‖ ^ 2)
      {ξ : ℝ | T < max (-Real.log |ξ|) 0} :=
    (integrable_negativeLog_fourier_of_firstMoment hf1 hf2 hm hfirst).integrableOn
  have hM0 : 0 ≤ M :=
    (integral_nonneg fun u => mul_nonneg (abs_nonneg u) (sq_nonneg ‖f u‖)).trans hM
  have hC : 0 ≤ (8 + 2 * M) * (T + 2) * Real.exp (-(T / 2)) :=
    mul_nonneg (mul_nonneg (by linarith only [hM0]) (by linarith only [hT])) (Real.exp_pos _).le
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ξ => mul_nonneg (le_max_right _ _) (sq_nonneg ‖𝓕 f ξ‖))
    hi.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_negativeLog_fourier_tail_le_firstMoment hf1 hf2 hm hfirst hM hT)).trans_eq
      (ENNReal.toReal_ofReal hC)

/-- Negative logarithmic energy is bounded by sixteen plus four times physical first moment. -/
theorem integral_negativeLog_fourier_le_firstMoment {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1)
    (hfirst : Integrable (fun u => |u| * ‖f u‖ ^ 2))
    {M : ℝ} (hM : (∫ u, |u| * ‖f u‖ ^ 2) ≤ M) :
    (∫ ξ, max (-Real.log |ξ|) 0 * ‖𝓕 f ξ‖ ^ 2) ≤ 16 + 4 * M := by
  have hi := integrable_negativeLog_fourier_of_firstMoment hf1 hf2 hm hfirst
  have hM0 : 0 ≤ M :=
    (integral_nonneg fun u => mul_nonneg (abs_nonneg u) (sq_nonneg ‖f u‖)).trans hM
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ξ => mul_nonneg (le_max_right _ _) (sq_nonneg ‖𝓕 f ξ‖))
    hi.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_negativeLog_fourier_le_firstMoment hf1 hf2 hm hfirst hM)).trans_eq
      (ENNReal.toReal_ofReal (by linarith only [hM0]))

#print axioms fourier_negativeLog_superlevel_le_firstMoment
#print axioms lintegral_negativeLog_fourier_tail_le_firstMoment
#print axioms lintegral_negativeLog_fourier_le_firstMoment
#print axioms integrable_negativeLog_fourier_of_firstMoment
#print axioms integral_negativeLog_fourier_tail_le_firstMoment
#print axioms integral_negativeLog_fourier_le_firstMoment
end GaloisForLFunctions.HTGeometry
