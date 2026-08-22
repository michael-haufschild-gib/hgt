import GaloisForLFunctions.RHTower.ConnesPVIntegrand
import GaloisForLFunctions.RHTower.ConnesTraceMainTerm

/-!
# The truncated sign pairing, by Fubini

Step 1b (continued) of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Truncating to `|x| ≤ X` makes the sign pairing an honest double integral, and Fubini turns it into
a frequency integral against the truncated kernel of `ConnesSgnFourierKernel`:

  `∫_{-X}^{X} sgn(x) g(x) dx = ∫ 𝓕g(u) · (∫_{-X}^{X} sgn(x) e^{2πixu} dx) du`.

The double integral is dominated by `‖𝓕g(u)‖` on a set of finite `x`-measure, so Fubini applies
with no extra hypothesis.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Fourier inversion in the form used here. -/
theorem connes_fourierInv_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ u : ℝ, connesSpaceChar u x * (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u) = g x := by
  have hFint : Integrable (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) := by
    have h : Integrable ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
      (SchwartzMap.fourierTransformCLM ℂ g).integrable
    rwa [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe] at h
  have hinv : 𝓕⁻ (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x = g x :=
    g.integrable.fourierInv_fourier_eq hFint g.continuous.continuousAt
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [connesSpaceChar, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Complex.real_smul, smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The transform of a Schwartz function is integrable. -/
theorem connes_fourier_integrable (g : 𝓢(ℝ, ℂ)) :
    Integrable (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) volume := by
  have h : Integrable ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    (SchwartzMap.fourierTransformCLM ℂ g).integrable
  rwa [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe] at h

/-- The double integrand of the truncated sign pairing is integrable on the product. -/
theorem connes_sgnPairing_integrable (g : 𝓢(ℝ, ℂ)) (X : ℝ) :
    Integrable (Function.uncurry fun x u : ℝ =>
        (Real.sign x : ℂ) * connesSpaceChar u x * (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u)
      ((volume.restrict (Ioc (-X) X)).prod volume) := by
  set G : ℝ → ℂ := 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) with hG
  have hGint : Integrable G volume := connes_fourier_integrable g
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x u : ℝ => (Real.sign x : ℂ) * connesSpaceChar u x * G u)
      ((volume.restrict (Ioc (-X) X)).prod volume) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((Complex.measurable_ofReal.comp
          (connes_measurable_sign.comp measurable_fst)).aestronglyMeasurable)
      · refine Continuous.aestronglyMeasurable ?_
        unfold connesSpaceChar
        fun_prop
      
    · exact (hGint.aestronglyMeasurable.comp_snd)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (-X) X)) := by
    constructor
    simpa using (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := (-X : ℝ)) (b := X))
  rw [MeasureTheory.integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards with x
    show Integrable (fun u : ℝ => (Real.sign x : ℂ) * connesSpaceChar u x * G u) volume
    refine Integrable.mono' (hGint.norm) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ hGint.aestronglyMeasurable
      refine AEStronglyMeasurable.mul aestronglyMeasurable_const ?_
      refine Continuous.aestronglyMeasurable ?_
      unfold connesSpaceChar
      fun_prop
    · filter_upwards with u
      show ‖(Real.sign x : ℂ) * connesSpaceChar u x * G u‖ ≤ ‖G u‖
      rw [norm_mul, norm_mul, connesSpaceChar_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (connes_abs_sign_le_one x)
  · have hbdd : ∀ x : ℝ, ‖∫ u : ℝ, ‖(Real.sign x : ℂ) * connesSpaceChar u x * G u‖‖
        ≤ ∫ u : ℝ, ‖G u‖ := by
      intro x
      have hnn : (0 : ℝ) ≤ ∫ u : ℝ, ‖(Real.sign x : ℂ) * connesSpaceChar u x * G u‖ :=
        integral_nonneg fun u => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun u => norm_nonneg _) hGint.norm
        (Filter.Eventually.of_forall fun u => ?_)
      show ‖(Real.sign x : ℂ) * connesSpaceChar u x * G u‖ ≤ ‖G u‖
      rw [norm_mul, norm_mul, connesSpaceChar_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (connes_abs_sign_le_one x)
    refine Integrable.mono' (integrable_const (∫ u : ℝ, ‖G u‖)) ?_ ?_
    · exact hmeas.norm.integral_prod_right'
    · filter_upwards with x
      exact hbdd x

/-- **The truncated sign pairing.**  Fubini turns it into a frequency integral against the
truncated kernel. -/
theorem connes_sgn_pairing_truncated (g : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 ≤ X) :
    (∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * g x)
      = ∫ u : ℝ, (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u *
          (∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * connesSpaceChar u x) := by
  set G : ℝ → ℂ := 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) with hG
  have hXle : (-X : ℝ) ≤ X := by linarith
  rw [intervalIntegral.integral_of_le hXle]
  have hstep : (∫ x in Ioc (-X : ℝ) X, (Real.sign x : ℂ) * g x)
      = ∫ x in Ioc (-X : ℝ) X, ∫ u : ℝ, (Real.sign x : ℂ) * connesSpaceChar u x * G u := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [← connes_fourierInv_apply g x, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  rw [hstep, MeasureTheory.integral_integral_swap (connes_sgnPairing_integrable g X)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (∫ x in Ioc (-X : ℝ) X, (Real.sign x : ℂ) * connesSpaceChar u x * G u)
      = G u * ∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * connesSpaceChar u x
  rw [intervalIntegral.integral_of_le hXle, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  ring

end

end GaloisForLFunctions.RHTower
