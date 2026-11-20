import GaloisForLFunctions.goldbach.LiLiu.Mellin.ProfileGeometry
import GaloisForLFunctions.goldbach.LiLiu.Mellin.HalfLineBeta
import GaloisForLFunctions.goldbach.LiLiu.Mellin.IntegratedInversion

/-! # Mellin transforms of the sum and difference profiles

The moment in the compact radial variable is the companion transform at
w−s. In the ratio variable the two orientations give Euler's integral on
the unit interval and on the positive half-line.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set MetaplecticMobiusDescent.CubicEisenstein
noncomputable section

def shapeBeta (d : ℝ) (w s : ℂ) : ℂ :=
  if d=1 then betaIntegral (1/2-s) (1/2+s-w) else betaIntegral (1/2-s) w

private def ratioKernel (d : ℝ) (w s : ℂ) (u : ℝ) : ℂ :=
  ((1+d*u:ℝ):ℂ)^(w-1) * (u:ℂ)^(-(1/2+s))

private theorem ratioKernel_beta {d : ℝ} (hd : d^2=1) {s w : ℂ}
    (hs : s.re < 1/2) (hw : 0 < w.re) (hw' : w.re < 1/2+s.re) :
    IntegrableOn (ratioKernel d w s) (shapeDomain d) ∧
    (∫ u in shapeDomain d, ratioKernel d w s u) = shapeBeta d w s := by
  have ha : 0 < (1/2-s : ℂ).re := by norm_num; linarith only [hs]
  have hb : 0 < (1/2+s-w : ℂ).re := by norm_num; linarith only [hw']
  have he : (1/2-s)-1 = -(1/2+s) := by ring
  rcases sq_eq_one_iff.mp hd with rfl | rfl
  · have H := halfLineBeta_integrable ha hb
    have E := halfLineBeta (1/2-s) (1/2+s-w)
    change IntegrableOn (fun u : ℝ => (u:ℂ)^((1/2-s)-1) *
      (1+(u:ℂ))^(-((1/2-s)+(1/2+s-w)))) (Ioi 0) at H
    have he' : -((1/2-s)+(1/2+s-w)) = w-1 := by ring
    simp only [he,he'] at H E
    have hf : ratioKernel 1 w s = fun u : ℝ => (u:ℂ)^(-(1/2+s))*(1+(u:ℂ))^(w-1) := by
      funext u
      simp [ratioKernel,mul_comm]
    simpa only [hf,shapeDomain_add,shapeBeta,if_pos rfl] using And.intro H E
  · have H := (betaIntegral_convergent ha hw).1.mono_set Ioo_subset_Ioc_self
    have E : (∫ u in Ioo (0:ℝ) 1, (u:ℂ)^((1/2-s)-1) * (1-(u:ℂ))^(w-1)) =
        betaIntegral (1/2-s) w := by
      rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one]
      exact setIntegral_congr_set Ioo_ae_eq_Ioc
    simp only [he] at H E
    have hf : ratioKernel (-1) w s = fun u : ℝ => (u:ℂ)^(-(1/2+s))*(1-(u:ℂ))^(w-1) := by
      funext u
      simp [ratioKernel,sub_eq_add_neg,mul_comm]
    simpa only [hf,shapeDomain_sub,shapeBeta,if_neg (by norm_num : (-1:ℝ) ≠ 1)] using And.intro H E

private def radialKernel (φ : TestWeight) (w : ℂ) (r : ℝ) := (r:ℂ)^w * (φ r:ℂ)

private theorem radial_moment (φ : TestWeight) (w s : ℂ) :
    (∫ r in centralInterval, radialKernel φ w r * (r:ℂ)^(-(1/2+s))) = mellin (companion φ) (w-s) := by
  rw [mellin]
  symm
  calc
    _ = ∫ r in centralInterval, (r:ℂ)^(w-s-1) • companion φ r := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun r hr => lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3) hr.1)
      intro r hr
      exact smul_eq_zero_of_right _ (Function.notMem_support.mp (fun h => hr.2 (companion_support φ h)))
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3) hr.1
      have h0 : (r:ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
      have hh : (Real.sqrt r : ℂ) = (r:ℂ)^(1/2:ℂ) := by
        rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hr0.le]; push_cast; rfl
      rw [smul_eq_mul, companion,Vstar,radialKernel,hh,← mul_assoc,← cpow_add _ _ h0]
      rw [mul_right_comm _ (φ r:ℂ), ← cpow_add _ _ h0]
      congr 2
      ring

/-- On each fixed pair of real parts the Beta factor is bounded at every height. -/
theorem shapeBeta_bound {d : ℝ} (hd : d^2=1) {σ c : ℝ} (hσ : σ < 1/2)
    (hc : 0 < c) (hc' : c < 1/2+σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s w : ℂ, s.re=σ → w.re=c → ‖shapeBeta d w s‖ ≤ B := by
  let g := ratioKernel d (c:ℂ) (σ:ℂ)
  refine ⟨∫ u in shapeDomain d, ‖g u‖, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro s w hs hw
  rw [← (ratioKernel_beta hd (hs.trans_lt hσ) (hc.trans_eq hw.symm) (by simpa [hs,hw] using hc')).2]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun (measurableSet_shapeDomain d)
  intro u hu
  simp only [g,ratioKernel,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hu.1,
    Complex.norm_cpow_eq_rpow_re_of_pos hu.2,sub_re,add_re,neg_re,ofReal_re,hw,hs]

theorem orientedProfile_mellin_beta (φ : TestWeight) {d : ℝ} (hd : d^2=1) {σ : ℝ} {w : ℂ}
    (hσ : σ < 1/2) (hw : 0 < w.re) (hw' : w.re < 1/2+σ) :
    Integrable (fun t : ℝ => mellin (companion φ) (w-((σ:ℂ)+t*I)) * shapeBeta d w ((σ:ℂ)+t*I) *
        mellin (companion φ) ((σ:ℂ)+t*I)) ∧
    mellin (orientedProfile φ d) w = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      mellin (companion φ) (w-((σ:ℂ)+t*I)) * shapeBeta d w ((σ:ℂ)+t*I) *
        mellin (companion φ) ((σ:ℂ)+t*I) := by
  let B (u : ℝ) := ((1+d*u:ℝ):ℂ)^(w-1)
  let μ := volume.restrict centralInterval
  let ν := volume.restrict (shapeDomain d)
  have hA : Measurable (radialKernel φ w) := (continuous_ofReal.measurable.pow_const w).mul
    (continuous_ofReal.comp φ.smooth.continuous).measurable
  have hB : Measurable B := (continuous_ofReal.measurable.comp
    (measurable_const.add (measurable_const.mul measurable_id))).pow_const _
  have hμ : ∀ᵐ r ∂μ, 0 < r := (ae_restrict_mem measurableSet_Icc).mono fun r hr =>
    lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3) hr.1
  have hν : ∀ᵐ u ∂ν, 0 < u := (ae_restrict_mem (measurableSet_shapeDomain d)).mono fun _ h => h.1
  have hI : Integrable (fun r => ‖radialKernel φ w r‖ * r ^ (-(1/2+σ))) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro r hr
    have hr0 : r ≠ 0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3) hr.1).ne'
    exact (((continuousAt_ofReal_cpow_const _ _ (Or.inr hr0)).mul
      (continuous_ofReal.comp φ.smooth.continuous).continuousAt).norm.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl hr0))).continuousWithinAt
  have hJ : Integrable (fun u => ‖B u‖ * u ^ (-(1/2+σ))) ν := by
    apply (ratioKernel_beta (s := (σ:ℂ)) hd hσ hw hw').1.norm.congr
    filter_upwards [hν] with u hu
    simp [B,ratioKernel,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hu]
  obtain ⟨hv,he⟩ := product_weight_inversion μ ν φ σ hA hB hμ hν hI hJ
  have H (t : ℝ) := (ratioKernel_beta (s := (σ:ℂ)+t*I) hd (by simpa using hσ) hw (by simpa using hw')).2
  simp only [μ,ν,B,radial_moment,← H] at hv he ⊢
  exact ⟨hv,(orientedProfile_mellin φ hd hw).trans he⟩

#print axioms orientedProfile_mellin_beta
end
end GaloisForLFunctions.Goldbach.LiLiu
