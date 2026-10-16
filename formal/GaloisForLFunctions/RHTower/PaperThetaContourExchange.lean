import GaloisForLFunctions.RHTower.PaperThetaContourFubini
import GaloisForLFunctions.RHTower.PaperThetaXiContour

/-! # Fubini for the complete native rectangle period -/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open GaloisForLFunctions.HTGeometry

theorem cutThetaTransform_rectangle {A γ : ℂ → ℂ} (hA : Measurable A)
    (hγ : Continuous γ) (a b : ℂ) (hAc : ContinuousOn A (RectangleBorder a b)) (w : ℂ) :
    Integrable (fun x => flatCharDensity w x*
      RectangleIntegral' (fun s => A s*cutQuotient (γ s) 0 x) a b) ∧
    (∫ x, flatCharDensity w x*RectangleIntegral' (fun s => A s*cutQuotient (γ s) 0 x) a b) =
      RectangleIntegral' (fun s => A s*cutThetaTransform (γ s) w) a b := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn hAc
  obtain ⟨T₀, hT₀⟩ := (isCompact_rectangleBorder a b).exists_bound_of_continuousOn hγ.continuousOn
  let M := max M₀ 0
  let T := max T₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hrow {p q : ℝ} (σ : ℝ → ℂ) (hσ : Continuous σ)
      (hs : MapsTo σ (uIcc p q) (RectangleBorder a b)) :
      Integrable (fun x => flatCharDensity w x*
        (∫ t in p..q, A (σ t)*cutQuotient (γ (σ t)) 0 x)) ∧
      (∫ x, flatCharDensity w x*(∫ t in p..q, A (σ t)*cutQuotient (γ (σ t)) 0 x)) =
        ∫ t in p..q, A (σ t)*cutThetaTransform (γ (σ t)) w := by
    have hb : ∀ t ∈ uIoc p q, ‖A (σ t)‖ ≤ M ∧ |(γ (σ t)).im| ≤ T ∧ ‖γ (σ t)‖ ≤ T := by
      intro t ht
      have hm := hs (uIoc_subset_uIcc ht)
      have hN : ‖γ (σ t)‖ ≤ T := (hT₀ (σ t) hm).trans (le_max_left _ _)
      exact ⟨(hM₀ (σ t) hm).trans (le_max_left _ _), (abs_im_le_norm _).trans hN, hN⟩
    exact ⟨integrable_cutTheta_path_integral (hA.comp hσ.measurable) (hγ.comp hσ) hM hb w,
      cutThetaTransform_path_integral (hA.comp hσ.measurable) (hγ.comp hσ) hM hb w⟩
  let H (y x : ℝ) : ℂ := ∫ t in a.re..b.re,
    A ((t : ℂ)+(y : ℂ)*I)*cutQuotient (γ ((t : ℂ)+(y : ℂ)*I)) 0 x
  let V (r x : ℝ) : ℂ := ∫ t in a.im..b.im,
    A ((r : ℂ)+(t : ℂ)*I)*cutQuotient (γ ((r : ℂ)+(t : ℂ)*I)) 0 x
  have hB := hrow (fun t => (t : ℂ)+(a.im : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_left_im a b)
  have hU := hrow (fun t => (t : ℂ)+(b.im : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_right_im a b)
  have hR := hrow (fun t => (b.re : ℂ)+(t : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_right_re a b)
  have hL := hrow (fun t => (a.re : ℂ)+(t : ℂ)*I) (by fun_prop)
    (mapsTo_rectangleBorder_left_re a b)
  let c : ℂ := 1/(2*(Real.pi : ℂ)*I)
  have he : (fun x => flatCharDensity w x*
      RectangleIntegral' (fun s => A s*cutQuotient (γ s) 0 x) a b) =
      fun x => c*((flatCharDensity w x*H a.im x-flatCharDensity w x*H b.im x)+
        I*(flatCharDensity w x*V b.re x)-I*(flatCharDensity w x*V a.re x)) := by
    funext x
    dsimp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, H, V, c]
    ring
  have hiB : Integrable (fun x => flatCharDensity w x*H a.im x) := hB.1
  have hiU : Integrable (fun x => flatCharDensity w x*H b.im x) := hU.1
  have hiR : Integrable (fun x => flatCharDensity w x*V b.re x) := hR.1
  have hiL : Integrable (fun x => flatCharDensity w x*V a.re x) := hL.1
  have hiBU : Integrable (fun x => flatCharDensity w x*H a.im x-flatCharDensity w x*H b.im x) :=
    hiB.sub hiU
  have hiBUR : Integrable (fun x => flatCharDensity w x*H a.im x-flatCharDensity w x*H b.im x+
      I*(flatCharDensity w x*V b.re x)) := hiBU.add (hiR.const_mul I)
  constructor
  · rw [he]
    exact (((hiB.sub hiU).add (hiR.const_mul I)).sub (hiL.const_mul I)).const_mul c
  · rw [he, integral_const_mul,
      integral_sub hiBUR (hiL.const_mul I),
      integral_add hiBU (hiR.const_mul I), integral_sub hiB hiU,
      integral_const_mul, integral_const_mul]
    change c*(((∫ x, flatCharDensity w x*H a.im x)-(∫ x, flatCharDensity w x*H b.im x))+
      I*(∫ x, flatCharDensity w x*V b.re x)-I*(∫ x, flatCharDensity w x*V a.re x)) = _
    dsimp only [H, V]
    rw [hB.2, hU.2, hR.2, hL.2]
    rfl

end RHTower.PaperThetaEndpoint
