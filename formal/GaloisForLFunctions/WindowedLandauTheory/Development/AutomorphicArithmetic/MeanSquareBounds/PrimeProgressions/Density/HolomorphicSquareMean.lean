import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq
import Mathlib.MeasureTheory.Integral.Prod

/-! The disk submean inequality bounds a holomorphic value by the integral over a square. -/

open Complex MeasureTheory

namespace QH.PrimeProgressions

theorem normSq_le_integral_square (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (s : ℂ) {r : ℝ} (hr : 0 < r) :
    ‖f s‖ ^ 2 ≤ (Real.pi * r ^ 2)⁻¹ * ∫ σ in (s.re - r)..(s.re + r),
      ∫ t in (s.im - r)..(s.im + r), ‖f (σ + t * I)‖ ^ 2 := by
  let U := Set.Ioc (s.re - r) (s.re + r) ×ℂ Set.Ioc (s.im - r) (s.im + r)
  have hcont : Continuous fun z => ‖f z‖ ^ 2 := hf.continuous.norm.pow 2
  have hU : U ⊆ Metric.closedBall s (2 * r) := by
    intro z hz
    simp only [U, Complex.mem_reProdIm, Set.mem_Ioc] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (z - s)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have h₁ : |z.re - s.re| ≤ r := abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have h₂ : |z.im - s.im| ≤ r := abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    linarith only [h, h₁, h₂]
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2) U :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall s (2 * r))).mono_set hU
  have hball : Metric.ball s r ⊆ U := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h₁ := Complex.abs_re_le_norm (z - s)
    have h₂ := Complex.abs_im_le_norm (z - s)
    simp only [Complex.sub_re, Complex.sub_im] at h₁ h₂
    obtain ⟨h₃, h₄⟩ := abs_lt.mp (h₁.trans_lt hz)
    obtain ⟨h₅, h₆⟩ := abs_lt.mp (h₂.trans_lt hz)
    simp only [U, Complex.mem_reProdIm, Set.mem_Ioc]
    exact ⟨⟨by linarith only [h₃], by linarith only [h₄]⟩,
      ⟨by linarith only [h₅], by linarith only [h₆]⟩⟩
  have hmono : (∫ z in Metric.ball s r, ‖f z‖ ^ 2) ≤ ∫ z in U, ‖f z‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun z => sq_nonneg _) hball.eventuallyLE
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' U =
      Set.Ioc (s.re - r) (s.re + r) ×ˢ Set.Ioc (s.im - r) (s.im + r) := by
    ext p
    simp [U, Complex.measurableEquivRealProd_symm_apply, Complex.mem_reProdIm]
  have hint' := (hp.integrableOn_comp_preimage he).mpr hint
  rw [hpre, Measure.volume_eq_prod] at hint'
  have hiter : ∫ z in U, ‖f z‖ ^ 2 = ∫ σ in (s.re - r)..(s.re + r),
      ∫ t in (s.im - r)..(s.im + r), ‖f (σ + t * I)‖ ^ 2 := by
    rw [← hp.setIntegral_preimage_emb he (fun z => ‖f z‖ ^ 2) U, hpre, Measure.volume_eq_prod,
      setIntegral_prod (fun p => ‖f (Complex.measurableEquivRealProd.symm p)‖ ^ 2) hint',
      intervalIntegral.integral_of_le (by linarith only [hr])]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ _ => ?_
    rw [intervalIntegral.integral_of_le (by linarith only [hr])]
    simp [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
  have hd := GaloisForLFunctions.HTGeometry.normSq_value_mul_area_le_integral_ball f hf s hr
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity : 0 < Real.pi * r ^ 2), mul_comm, ← hiter]
  exact hd.trans hmono

end QH.PrimeProgressions
