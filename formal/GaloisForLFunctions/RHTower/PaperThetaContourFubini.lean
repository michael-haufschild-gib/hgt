import GaloisForLFunctions.RHTower.PaperThetaCutTransform
import Mathlib.MeasureTheory.Integral.Prod

/-! # Source transforms commute with native contour segments

The actual strip control supplies product integrability. The spatial cut is
retained, so Fubini does not require a divisor-dependent continuity premise.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint

theorem measurable_cutQuotient_path {γ : ℝ → ℂ} (hγ : Continuous γ) (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => cutQuotient (γ p.1) a p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun x => (differentiable_cutQuotient_parameter a x).continuous.comp hγ)
    (fun t => measurable_cutQuotient (γ t) a)

theorem integrable_cutTheta_path_product {A γ : ℝ → ℂ} (hA : Measurable A)
    (hγ : Continuous γ) {a b B T M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t ∈ uIoc a b, ‖A t‖ ≤ M ∧ |(γ t).im| ≤ B ∧ ‖γ t‖ ≤ T) (w : ℂ) :
    Integrable (fun p : ℝ × ℝ =>
      flatCharDensity w p.2*(A p.1*cutQuotient (γ p.1) 0 p.2))
      ((volume.restrict (uIoc a b)).prod volume) := by
  letI : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    dsimp [uIoc]
    infer_instance
  let C := M*(T*stripTailControl B 0+1)
  have hm : Measurable (fun p : ℝ × ℝ =>
      flatCharDensity w p.2*(A p.1*cutQuotient (γ p.1) 0 p.2)) :=
    ((continuous_flatCharDensity w).measurable.comp measurable_snd).mul
      ((hA.comp measurable_fst).mul (measurable_cutQuotient_path hγ 0))
  have hi : Integrable (fun p : ℝ × ℝ => C*‖flatCharDensity w p.2‖)
      ((volume.restrict (uIoc a b)).prod volume) :=
    (integrable_const C).mul_prod (integrable_flatCharDensity_all w).norm
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (uIoc a b)) (ν := volume)).ae
      (ae_restrict_mem measurableSet_uIoc)] with p hp
  obtain ⟨hAt, hIm, hγt⟩ := hb p.1 hp
  have hq : ‖cutQuotient (γ p.1) 0 p.2‖ ≤ T*stripTailControl B 0+1 := by
    have h := cutQuotient_add_one_strip hIm p.2
    have ht := norm_sub_le (cutQuotient (γ p.1) 0 p.2+1) (1 : ℂ)
    rw [add_sub_cancel_right, norm_one] at ht
    have hc := mul_le_mul_of_nonneg_right hγt (stripTailControl_nonneg B 0)
    linarith
  have hinner : ‖A p.1*cutQuotient (γ p.1) 0 p.2‖ ≤ C := by
    rw [norm_mul]
    exact mul_le_mul hAt hq (norm_nonneg _) hM
  calc
    ‖flatCharDensity w p.2*(A p.1*cutQuotient (γ p.1) 0 p.2)‖ =
        ‖flatCharDensity w p.2‖*‖A p.1*cutQuotient (γ p.1) 0 p.2‖ := norm_mul _ _
    _ ≤ ‖flatCharDensity w p.2‖*C := mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = C*‖flatCharDensity w p.2‖ := mul_comm _ _

/-- The literal source integral commutes with a finite parameter segment. -/
theorem cutThetaTransform_path_integral {A γ : ℝ → ℂ} (hA : Measurable A)
    (hγ : Continuous γ) {a b B T M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t ∈ uIoc a b, ‖A t‖ ≤ M ∧ |(γ t).im| ≤ B ∧ ‖γ t‖ ≤ T) (w : ℂ) :
    (∫ x, flatCharDensity w x*(∫ t in a..b, A t*cutQuotient (γ t) 0 x)) =
      ∫ t in a..b, A t*cutThetaTransform (γ t) w := by
  have hi := integrable_cutTheta_path_product hA hγ hM hb w
  calc
    _ = ∫ x, ∫ t in a..b, flatCharDensity w x*(A t*cutQuotient (γ t) 0 x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (intervalIntegral.integral_const_mul _ _).symm
    _ = ∫ t in a..b, ∫ x, flatCharDensity w x*(A t*cutQuotient (γ t) 0 x) :=
      (intervalIntegral_integral_swap hi).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change (∫ x, flatCharDensity w x*(A t*cutQuotient (γ t) 0 x)) =
        A t*cutThetaTransform (γ t) w
      rw [show (fun x => flatCharDensity w x*(A t*cutQuotient (γ t) 0 x)) =
        (fun x => A t*(flatCharDensity w x*cutQuotient (γ t) 0 x)) by funext x; ring,
        integral_const_mul]
      rfl

theorem integrable_cutTheta_path_integral {A γ : ℝ → ℂ} (hA : Measurable A)
    (hγ : Continuous γ) {a b B T M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t ∈ uIoc a b, ‖A t‖ ≤ M ∧ |(γ t).im| ≤ B ∧ ‖γ t‖ ≤ T) (w : ℂ) :
    Integrable (fun x => flatCharDensity w x*(∫ t in a..b, A t*cutQuotient (γ t) 0 x)) := by
  have hi : Integrable (fun x => ∫ t in uIoc a b,
      flatCharDensity w x*(A t*cutQuotient (γ t) 0 x)) :=
    (integrable_cutTheta_path_product hA hγ hM hb w).integral_prod_right
  have h : Integrable (fun x =>
      ∫ t in a..b, flatCharDensity w x*(A t*cutQuotient (γ t) 0 x)) := by
    simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    exact hi.smul (if a ≤ b then (1 : ℝ) else -1)
  apply h.congr
  filter_upwards [] with x
  exact intervalIntegral.integral_const_mul _ _

end RHTower.PaperThetaEndpoint
