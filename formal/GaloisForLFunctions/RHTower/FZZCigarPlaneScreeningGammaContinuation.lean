import GaloisForLFunctions.RHTower.FZZCigarSubtractedScreeningAnalytic
import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningBeta
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Original plane screening finite part and its Gamma continuation

The original two-puncture cutoff prescription is matched to the Gamma expression
through the separately analytic, explicitly pole-cleared source. Equality first
holds in the ordinary convergence chamber. Two connected one-variable identity
arguments extend it across the collision poles without assigning a zero value
to their finite residues. Division occurs only away from these poles.

For both position exponents in `(-3,-2)`, the continued original finite part is
strictly negative. The original integrand is nonnegative; subtraction therefore
does not preserve its sign. The original independently removed cutoff integrals,
with both forced local counterterms, converge to the displayed Gamma value.

These are first-strip position-source results. They do not identify the complete
FZZ correlator, its physical mixed replica-momentum response, or a phase frame.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem reciprocal_gamma_analytic (r : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => (Real.Gamma s)⁻¹) r := by
  have hc := Complex.differentiable_one_div_Gamma.analyticAt (r : ℂ)
  convert! hc.re_ofReal using 1
  simp only [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]

private theorem positive_gamma_analytic (r : ℝ) (hr : 0 < r) :
    AnalyticAt ℝ Real.Gamma r := by
  have h := (reciprocal_gamma_analytic r).inv (inv_ne_zero (Real.Gamma_pos_of_pos hr).ne')
  convert! h using 1
  ext s
  simp

private def clearedGamma (α β : ℝ) : ℝ :=
  4*Real.pi*Real.Gamma (-α/2-β/2-1)*Real.Gamma (2+α/2)*Real.Gamma (2+β/2)*
    (Real.Gamma (-α/2))⁻¹*(Real.Gamma (-β/2))⁻¹*(Real.Gamma (2+α/2+β/2))⁻¹

private theorem clearedGamma_analytic (α β : ℝ) (ha : -3 < α)
    (hs : α+β < -2) : AnalyticAt ℝ (fun s => clearedGamma s β) α := by
  have h1 : AnalyticAt ℝ (fun s : ℝ => -s/2-β/2-1) α := by fun_prop
  have h2 : AnalyticAt ℝ (fun s : ℝ => 2+s/2) α := by fun_prop
  have h3 : AnalyticAt ℝ (fun s : ℝ => -s/2) α := by fun_prop
  have h4 : AnalyticAt ℝ (fun s : ℝ => 2+s/2+β/2) α := by fun_prop
  have hg1 := (positive_gamma_analytic (-α/2-β/2-1) (by linarith)).comp_of_eq h1 rfl
  have hg2 := (positive_gamma_analytic (2+α/2) (by linarith)).comp_of_eq h2 rfl
  have hg3 := (reciprocal_gamma_analytic (-α/2)).comp_of_eq h3 rfl
  have hg4 := (reciprocal_gamma_analytic (2+α/2+β/2)).comp_of_eq h4 rfl
  exact (((((analyticAt_const.mul hg1).mul hg2).mul analyticAt_const).mul hg3).mul
    analyticAt_const).mul hg4

private theorem original_power_ball (α : ℝ) (ha : -2 < α) :
    (∫ z : ℂ in ball 0 (1/2), ‖z‖^α) = 2*Real.pi*(1/2 : ℝ)^(α+2)/(α+2) := by
  rw [← integral_indicator measurableSet_ball]
  have he : ((ball (0 : ℂ) (1/2)).indicator (fun z : ℂ => ‖z‖^α)) =
      fun z : ℂ => (Iio (1/2 : ℝ)).indicator (fun r : ℝ => r^α) ‖z‖ := by
    funext z
    simp [indicator]
  rw [he, integral_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  have hv : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [hv]
  have hh : (fun r : ℝ => r*(Iio (1/2 : ℝ)).indicator (fun r : ℝ => r^α) r) =ᶠ[
      ae (volume.restrict (Ioi 0))] (Iio (1/2 : ℝ)).indicator (fun r : ℝ => r^(α+1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases hR : r ∈ Iio (1/2 : ℝ)
    · rw [indicator_of_mem hR, indicator_of_mem hR, Real.rpow_add hr, Real.rpow_one, mul_comm]
    · rw [indicator_of_notMem hR, indicator_of_notMem hR, mul_zero]
  rw [integral_congr_ae hh, setIntegral_indicator measurableSet_Iio]
  have hset : Ioi (0 : ℝ) ∩ Iio (1/2) = Ioo 0 (1/2) := by ext r; simp
  rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1/2),
    integral_rpow (Or.inl (by linarith : -1 < α+1))]
  rw [show α+1+1 = α+2 by ring, Real.zero_rpow (by linarith : α+2 ≠ 0), sub_zero]
  ring

private theorem original_zero_finitePart (α β : ℝ) (ha : -2 < α) :
    fzzScreeningZeroFinitePart α β =
      ∫ z : ℂ in ball 0 (1/2), fzzScreeningPlaneKernel α β z := by
  have hk := (fzzScreeningPlaneKernel_integrable_zero_iff α β).mpr ha
  have hp : IntegrableOn (fun z : ℂ => ‖z‖^α) (ball 0 (1/2)) := by
    have h := (fzzScreeningPlaneKernel_integrable_zero_iff α 0).mpr ha
    unfold fzzScreeningPlaneKernel at h
    simpa only [Real.rpow_zero, mul_one] using h
  have he : fzzScreeningZeroSubtracted α β =
      fun z => fzzScreeningPlaneKernel α β z - ‖z‖^α := by
    funext z
    dsimp [fzzScreeningZeroSubtracted, fzzScreeningPlaneKernel]
    ring
  rw [fzzScreeningZeroFinitePart, he, integral_sub hk hp, original_power_ball α ha]
  ring


/-- The Gamma expression to be matched with the original subtracted plane source. -/
def fzzScreeningPlaneContinuedGamma (α β : ℝ) : ℝ :=
  Real.pi*Real.Gamma (-α/2-β/2-1)*Real.Gamma (1+α/2)*Real.Gamma (1+β/2) /
    (Real.Gamma (-α/2)*Real.Gamma (-β/2)*Real.Gamma (2+α/2+β/2))

theorem original_plane_gamma (α β : ℝ) (ha : -2 < α) (hb : -2 < β)
    (hs : α+β < -2) : Integrable (fzzScreeningPlaneKernel α β) ∧
      (∫ z : ℂ, fzzScreeningPlaneKernel α β z) = fzzScreeningPlaneContinuedGamma α β := by
  obtain ⟨x,y,hx,hy⟩ := (fzzScreeningBeta_chart_iff (-α/2) (-β/2)).mpr
    ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hpa : -2*(-α/2) = α := by ring
  have hpb : -2*(-β/2) = β := by ring
  constructor
  · unfold fzzScreeningPlaneKernel
    simpa only [hx,hy,hpa,hpb] using fzzScreeningBetaKernel_integrable x y
  · have h := fzzScreeningBetaIntegral_eq_gamma x y
    unfold fzzScreeningBetaIntegral at h
    rw [hx,hy,hpa,hpb,
      show -α/2 + -β/2 - 1 = -α/2-β/2-1 by ring,
      show 1- -α/2 = 1+α/2 by ring, show 1- -β/2 = 1+β/2 by ring,
      show 2- -α/2- -β/2 = 2+α/2+β/2 by ring] at h
    exact h

private theorem original_one_finitePart (α β : ℝ) (hb : -2 < β) :
    fzzScreeningOneFinitePart α β =
      ∫ z : ℂ in ball 1 (1/2), fzzScreeningPlaneKernel α β z := by
  rw [fzzScreeningOneFinitePart_reflection, original_zero_finitePart β α hb]
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding (fzzScreeningPlaneKernel α β) (ball 1 (1/2))
  have hp : (fun z : ℂ => 1-z) ⁻¹' ball 1 (1/2) = ball 0 (1/2) := by
    ext z
    simp [mem_ball, dist_eq_norm]
  rw [hp] at h
  simpa only [fzzScreeningPlaneKernel_reflection] using h

private theorem original_finitePart (α β : ℝ) (ha : -2 < α) (hb : -2 < β)
    (hs : α+β < -2) : fzzScreeningPlaneFinitePart α β = fzzScreeningPlaneContinuedGamma α β := by
  have hi := (original_plane_gamma α β ha hb hs).1
  have hu : (ball (0 : ℂ) (1/2) ∪ ball 1 (1/2)) ∪ fzzScreeningPlaneExterior = univ :=
    union_compl_self _
  have hm : MeasurableSet fzzScreeningPlaneExterior :=
    (isOpen_ball.union isOpen_ball).measurableSet.compl
  have hd : Disjoint (ball (0 : ℂ) (1/2) ∪ ball 1 (1/2)) fzzScreeningPlaneExterior :=
    disjoint_compl_right
  have hd01 : Disjoint (ball (0 : ℂ) (1/2)) (ball 1 (1/2)) :=
    ball_disjoint_ball (by norm_num [dist_eq_norm])
  have hh : (∫ z : ℂ, fzzScreeningPlaneKernel α β z) =
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningPlaneKernel α β z) +
      (∫ z : ℂ in ball 1 (1/2), fzzScreeningPlaneKernel α β z) +
      (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z) := by
    calc
      _ = ∫ z : ℂ in (ball 0 (1/2) ∪ ball 1 (1/2)) ∪ fzzScreeningPlaneExterior,
          fzzScreeningPlaneKernel α β z := by rw [hu, setIntegral_univ]
      _ = _ := by
        rw [setIntegral_union hd hm hi.integrableOn hi.integrableOn,
          setIntegral_union hd01 measurableSet_ball hi.integrableOn hi.integrableOn]
  rw [fzzScreeningPlaneFinitePart, original_zero_finitePart α β ha,
    original_one_finitePart α β hb, ← hh]
  exact (original_plane_gamma α β ha hb hs).2

private theorem source_clearing (α β : ℝ) (ha : α+2 ≠ 0) (hb : β+2 ≠ 0) :
    fzzScreeningPlaneClearedSource α β = (α+2)*(β+2)*fzzScreeningPlaneFinitePart α β := by
  unfold fzzScreeningPlaneClearedSource fzzScreeningPlaneFinitePart
    fzzScreeningZeroFinitePart fzzScreeningOneFinitePart
  field_simp [ha,hb]
  ring

private theorem gamma_clearing (α β : ℝ) (ha : α+2 ≠ 0) (hb : β+2 ≠ 0) :
    clearedGamma α β = (α+2)*(β+2)*fzzScreeningPlaneContinuedGamma α β := by
  have ha' : 1+α/2 ≠ 0 := by intro h; apply ha; linarith
  have hb' : 1+β/2 ≠ 0 := by intro h; apply hb; linarith
  have hga : Real.Gamma (2+α/2) = (1+α/2)*Real.Gamma (1+α/2) := by
    convert Real.Gamma_add_one ha' using 1 <;> congr 1 <;> ring
  have hgb : Real.Gamma (2+β/2) = (1+β/2)*Real.Gamma (1+β/2) := by
    convert Real.Gamma_add_one hb' using 1 <;> congr 1 <;> ring
  unfold clearedGamma fzzScreeningPlaneContinuedGamma
  rw [hga, hgb]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem original_cleared_identity (α β : ℝ) (ha : -2 < α) (hb : -2 < β)
    (hs : α+β < -2) : fzzScreeningPlaneClearedSource α β = clearedGamma α β := by
  have ha' : α+2 ≠ 0 := by linarith
  have hb' : β+2 ≠ 0 := by linarith
  rw [source_clearing α β ha' hb', original_finitePart α β ha hb hs,
    gamma_clearing α β ha' hb']


private theorem source_analytic_left (β : ℝ) (hb : -3 < β) :
    AnalyticOnNhd ℝ (fun α => fzzScreeningPlaneClearedSource α β) (Ioo (-3) (-2-β)) := by
  have h := fzzScreeningPlaneClearedSource_analytic_left (Real.log (β+3))
  rw [Real.exp_log (by linarith : 0 < β+3)] at h
  simpa only [show -3+(β+3) = β by ring] using h

private theorem source_analytic_right (α : ℝ) (ha : -3 < α) :
    AnalyticOnNhd ℝ (fun β => fzzScreeningPlaneClearedSource α β) (Ioo (-3) (-2-α)) := by
  have h := fzzScreeningPlaneClearedSource_analytic_right (Real.log (α+3))
  rw [Real.exp_log (by linarith : 0 < α+3)] at h
  simpa only [show -3+(α+3) = α by ring] using h

private theorem gamma_symm (α β : ℝ) : clearedGamma α β = clearedGamma β α := by
  unfold clearedGamma
  rw [show -α/2-β/2-1 = -β/2-α/2-1 by ring,
    show 2+α/2+β/2 = 2+β/2+α/2 by ring]
  ring

private theorem gamma_analytic_left (β : ℝ) :
    AnalyticOnNhd ℝ (fun α => clearedGamma α β) (Ioo (-3) (-2-β)) := by
  intro α hα
  exact clearedGamma_analytic α β hα.1 (by linarith [hα.2])

private theorem gamma_analytic_right (α : ℝ) :
    AnalyticOnNhd ℝ (fun β => clearedGamma α β) (Ioo (-3) (-2-α)) := by
  intro β hβ
  have h := gamma_analytic_left α β hβ
  apply h.congr
  filter_upwards with s
  exact gamma_symm s α

private theorem first_slice_identity (α β : ℝ) (ha : -3 < α) (hb : -2 < β)
    (hb0 : β < 0) (hs : α+β < -2) :
    fzzScreeningPlaneClearedSource α β = clearedGamma α β := by
  let a0 := -2-β/2
  have h0 : a0 ∈ Ioo (-3 : ℝ) (-2-β) := by
    dsimp [a0]
    constructor <;> linarith
  have he : (fun a => fzzScreeningPlaneClearedSource a β) =ᶠ[𝓝 a0]
      (fun a => clearedGamma a β) := by
    have hn : ∀ᶠ a : ℝ in 𝓝 a0, -2 < a ∧ a+β < -2 := by
      have hm : a0 ∈ Ioo (-2 : ℝ) (-2-β) := by
        dsimp [a0]
        constructor <;> linarith
      filter_upwards [isOpen_Ioo.mem_nhds hm] with a ha
      exact ⟨ha.1, by linarith [ha.2]⟩
    filter_upwards [hn] with a ha
    exact original_cleared_identity a β ha.1 hb ha.2
  have heq := (source_analytic_left β (by linarith)).eqOn_of_preconnected_of_eventuallyEq
    (gamma_analytic_left β) isPreconnected_Ioo h0 he
  exact heq ⟨ha, by linarith⟩

private theorem continued_cleared_identity (α β : ℝ) (ha : -3 < α) (ha2 : α < -2)
    (hb : -3 < β) (hb2 : β < -2) :
    fzzScreeningPlaneClearedSource α β = clearedGamma α β := by
  have h0 : (-1 : ℝ) ∈ Ioo (-3) (-2-α) := by
    constructor <;> linarith
  have he : (fun b => fzzScreeningPlaneClearedSource α b) =ᶠ[𝓝 (-1 : ℝ)]
      (fun b => clearedGamma α b) := by
    have hn : ∀ᶠ b : ℝ in 𝓝 (-1 : ℝ), b ∈ Ioo (-2) 0 :=
      isOpen_Ioo.mem_nhds (by norm_num)
    filter_upwards [hn] with b hb
    exact first_slice_identity α b ha hb.1 hb.2 (by linarith [hb.2])
  have heq := (source_analytic_right α ha).eqOn_of_preconnected_of_eventuallyEq
    (gamma_analytic_right α) isPreconnected_Ioo h0 he
  exact heq ⟨hb, by linarith⟩

private theorem first_power_range (u : ℝ) :
    -3 < fzzScreeningFirstContinuationPower u ∧ fzzScreeningFirstContinuationPower u < -2 := by
  have hden : 0 < 1+Real.exp u := by positivity
  have hp := inv_pos.mpr hden
  have hlt : (1+Real.exp u)⁻¹ < 1 := (inv_lt_one₀ hden).mpr (by linarith [Real.exp_pos u])
  unfold fzzScreeningFirstContinuationPower
  constructor <;> linarith

/-- Equality of the original pole-cleared source and its Gamma continuation is derived
from the convergent original integral and two connected analytic slices. -/
theorem fzzScreeningPlaneClearedSource_eq_gamma (u v : ℝ) :
    fzzScreeningPlaneClearedSource (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower v) =
      (fzzScreeningFirstContinuationPower u+2)*(fzzScreeningFirstContinuationPower v+2)*
        fzzScreeningPlaneContinuedGamma (fzzScreeningFirstContinuationPower u)
          (fzzScreeningFirstContinuationPower v) := by
  have hu := first_power_range u
  have hv := first_power_range v
  rw [continued_cleared_identity _ _ hu.1 hu.2 hv.1 hv.2,
    gamma_clearing _ _ (by linarith [hu.2]) (by linarith [hv.2])]

/-- The actual whole-plane cutoff finite part equals the continued Gamma expression. -/
theorem fzzScreeningPlaneFinitePart_eq_gamma (u v : ℝ) :
    fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower v) =
      fzzScreeningPlaneContinuedGamma (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) := by
  have hu := first_power_range u
  have hv := first_power_range v
  apply mul_left_cancel₀ (mul_ne_zero (by linarith [hu.2]) (by linarith [hv.2]) :
    (fzzScreeningFirstContinuationPower u+2)*(fzzScreeningFirstContinuationPower v+2) ≠ 0)
  rw [← fzzScreeningPlaneClearedSource_eq_finitePart]
  exact fzzScreeningPlaneClearedSource_eq_gamma u v

private theorem gamma_negative (s : ℝ) (hs : -1 < s) (hs0 : s < 0) : Real.Gamma s < 0 := by
  have hp := Real.Gamma_pos_of_pos (by linarith : 0 < s+1)
  rw [Real.Gamma_add_one hs0.ne] at hp
  rcases mul_pos_iff.mp hp with h|h
  · linarith [h.1]
  · exact h.2

private theorem cleared_gamma_negative (α β : ℝ) (ha : -3 < α) (ha2 : α < -2)
    (hb : -3 < β) (hb2 : β < -2) : clearedGamma α β < 0 := by
  have h1 := Real.Gamma_pos_of_pos (by linarith : 0 < -α/2-β/2-1)
  have h2 := Real.Gamma_pos_of_pos (by linarith : 0 < 2+α/2)
  have h3 := Real.Gamma_pos_of_pos (by linarith : 0 < 2+β/2)
  have h4 := Real.Gamma_pos_of_pos (by linarith : 0 < -α/2)
  have h5 := Real.Gamma_pos_of_pos (by linarith : 0 < -β/2)
  have h6 : Real.Gamma (2+α/2+β/2) < 0 := gamma_negative _ (by linarith) (by linarith)
  unfold clearedGamma
  apply mul_neg_of_pos_of_neg
  · positivity
  · exact inv_lt_zero'.mpr h6

/-- The original finite part is strictly negative throughout the first simultaneous
continuation strip, despite positivity of the unrenormalized cutoff integrand. -/
theorem fzzScreeningPlaneFinitePart_neg (u v : ℝ) :
    fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower v) < 0 := by
  have hu := first_power_range u
  have hv := first_power_range v
  have h := cleared_gamma_negative _ _ hu.1 hu.2 hv.1 hv.2
  rw [← continued_cleared_identity _ _ hu.1 hu.2 hv.1 hv.2,
    fzzScreeningPlaneClearedSource_eq_finitePart] at h
  have hp : 0 < (fzzScreeningFirstContinuationPower u+2)*(fzzScreeningFirstContinuationPower v+2) :=
    mul_pos_of_neg_of_neg (by linarith [hu.2]) (by linarith [hv.2])
  by_contra! hn
  exact not_lt_of_ge (mul_nonneg hp.le hn) h

/-- The Gamma value is the limit of the original two independently punctured plane
integrals with their two forced collision counterterms. -/
theorem fzzScreeningPlaneGamma_independent_cutoff_limit (u v : ℝ) :
    Tendsto (fun P : ℝ × ℝ =>
      fzzScreeningPlaneCutoff (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) P.1 P.2 +
      2*Real.pi*(Real.exp (-P.1))^(fzzScreeningFirstContinuationPower u+2)/
        (fzzScreeningFirstContinuationPower u+2) +
      2*Real.pi*(Real.exp (-P.2))^(fzzScreeningFirstContinuationPower v+2)/
        (fzzScreeningFirstContinuationPower v+2)) (atTop ×ˢ atTop)
      (𝓝 (fzzScreeningPlaneContinuedGamma (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v))) := by
  simpa only [fzzScreeningPlaneFinitePart_eq_gamma] using
    fzzScreeningPlaneFinitePart_independent_cutoff_limit u v

end GaloisForLFunctions.RHTower
