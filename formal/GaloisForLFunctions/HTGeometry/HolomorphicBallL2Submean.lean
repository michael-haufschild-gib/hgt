import GaloisForLFunctions.HTGeometry.HardyDiskGutzmer
import GaloisForLFunctions.HTGeometry.GutzmerIdentity
import GaloisForLFunctions.HTGeometry.NonnegativeSumCriterionNoGo
import GaloisForLFunctions.Bottcher.Brolin.RieszFlux

open MeasureTheory Set Complex Filter Topology
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem powerSeries_coeff_zero_eq
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ENNReal}
    (hp : HasFPowerSeriesOnBall f p 0 R) : p.coeff 0 = f 0 := by
  have hR : 0 < R := hp.r_pos
  have hs := hp.hasSum (show (0 : ℂ) ∈ Metric.eball 0 R by simpa using hR)
  have heq : (fun n : ℕ => (p n) fun _ => (0 : ℂ)) =
      fun n => if n = 0 then p.coeff 0 else 0 := by
    funext n
    by_cases hn : n = 0
    · subst n
      rw [if_pos rfl, FormalMultilinearSeries.coeff]
      congr
      funext i
      exact Fin.elim0 i
    · rw [if_neg hn]
      letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      exact (p n).map_zero
  rw [zero_add, heq] at hs
  simpa using hs.tsum_eq

/-- Circle `L²` submean inequality for an entire function. -/
theorem two_pi_mul_normSq_zero_le_circleIntegral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) :
    2 * Real.pi * ‖f 0‖ ^ 2 ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap 0 r θ)‖ ^ 2 := by
  let R : NNReal := ⟨r + 1, by linarith⟩
  let r' : NNReal := ⟨r + 1 / 2, by linarith⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries f 0 R
  have hR : 0 < R := by
    exact_mod_cast (show (0 : ℝ) < r + 1 by linarith)
  have hp : HasFPowerSeriesOnBall f p 0 R := by
    dsimp [p]
    exact hf.differentiableOn.hasFPowerSeriesOnBall hR
  have hrr' : r < (r' : ℝ) := by
    change r < r + 1 / 2
    norm_num
  have hr'R : (r' : ENNReal) < (R : ENNReal) := by
    rw [ENNReal.coe_lt_coe]
    change r + 1 / 2 < r + 1
    norm_num
  have hg := hasSum_circleAverage_normSq hp hr.le hrr' hr'R
  have hterm := GaloisForLFunctions.term_le_tsum_of_nonneg hg.summable
    (fun k => by positivity) 0
  have hp0 : p.coeff 0 = f 0 := powerSeries_coeff_zero_eq hp
  have havg : ‖f 0‖ ^ 2 ≤
      (2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap 0 r θ)‖ ^ 2 := by
    rw [← hg.tsum_eq]
    simpa [hp0] using hterm
  have hpi : 0 < 2 * Real.pi := by positivity
  calc
    2 * Real.pi * ‖f 0‖ ^ 2 ≤
        2 * Real.pi * ((2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap 0 r θ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left havg hpi.le
    _ = _ := by field_simp

private def holomorphicDiskPolarChartIntegrand (f : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  p.1 * ‖f (circleMap 0 p.1 p.2)‖ ^ 2

private theorem continuous_holomorphicDiskPolarChartIntegrand
    {f : ℂ → ℂ} (hf : Continuous f) :
    Continuous (holomorphicDiskPolarChartIntegrand f) := by
  have hcircle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) from by
      funext p
      simp [circleMap]]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  unfold holomorphicDiskPolarChartIntegrand
  exact continuous_fst.mul ((hf.comp hcircle).norm.pow 2)

private theorem integral_Ioo_holomorphicCircleNormSq
    {f : ℂ → ℂ} (ρ : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, ‖f (circleMap 0 ρ θ)‖ ^ 2) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap 0 ρ θ)‖ ^ 2 := by
  apply Bottcher.integral_Ioo_pi_eq_zero_two_pi
  intro θ
  change ‖f (circleMap 0 ρ (θ + 2 * Real.pi))‖ ^ 2 =
    ‖f (circleMap 0 ρ θ)‖ ^ 2
  have hcircle : circleMap 0 ρ (θ + 2 * Real.pi) = circleMap 0 ρ θ := by
    simp [circleMap, add_mul, Complex.exp_add, Complex.exp_mul_I]
  rw [hcircle]

private theorem integrable_holomorphicDiskPolarChartIntegrand
    {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} :
    Integrable (holomorphicDiskPolarChartIntegrand f)
      ((volume.restrict (Ioo 0 r)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  have hc := continuous_holomorphicDiskPolarChartIntegrand hf
  have hcompact : IntegrableOn (holomorphicDiskPolarChartIntegrand f)
      (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hioo : IntegrableOn (holomorphicDiskPolarChartIntegrand f)
      (Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi) :=
    hcompact.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hioo

/-- Disk `L²` submean inequality for an entire function, centered at the origin. -/
theorem pi_mul_sq_mul_normSq_zero_le_integral_ball
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) :
    Real.pi * r ^ 2 * ‖f 0‖ ^ 2 ≤
      ∫ z in Metric.ball (0 : ℂ) r, ‖f z‖ ^ 2 := by
  have hchart := integrable_holomorphicDiskPolarChartIntegrand (r := r) hf.continuous
  have hpolar :
      (∫ z in Metric.ball (0 : ℂ) r, ‖f z‖ ^ 2) =
        ∫ p in Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi,
          holomorphicDiskPolarChartIntegrand f p := by
    rw [Bottcher.integral_ball_eq_polar]
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    have hpTarget : p ∈ Complex.polarCoord.target := by
      rw [Complex.polarCoord_target]
      exact ⟨hp.1.1, hp.2⟩
    have hpoint : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
      rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    change p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 = _
    rw [hpoint]
    rfl
  rw [hpolar]
  have hprod :
      (∫ p in Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi,
          holomorphicDiskPolarChartIntegrand f p) =
        ∫ ρ in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi,
          holomorphicDiskPolarChartIntegrand f (ρ, θ) := by
    rw [← MeasureTheory.integral_prod _ hchart]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [hprod]
  have hslicele : ∀ ρ ∈ Ioo (0 : ℝ) r,
      2 * Real.pi * ‖f 0‖ ^ 2 * ρ ≤
        ∫ θ in Ioo (-Real.pi) Real.pi,
          holomorphicDiskPolarChartIntegrand f (ρ, θ) := by
    intro ρ hρ
    have hcircle := two_pi_mul_normSq_zero_le_circleIntegral hf hρ.1
    have hang := integral_Ioo_holomorphicCircleNormSq (f := f) ρ
    unfold holomorphicDiskPolarChartIntegrand
    rw [MeasureTheory.integral_const_mul, hang]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hcircle hρ.1.le
  have hlowerInt : IntegrableOn
      (fun ρ : ℝ => 2 * Real.pi * ‖f 0‖ ^ 2 * ρ) (Ioo 0 r) := by
    exact (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hslicesInt : IntegrableOn
      (fun ρ => ∫ θ in Ioo (-Real.pi) Real.pi,
        holomorphicDiskPolarChartIntegrand f (ρ, θ)) (Ioo 0 r) := by
    rw [integrable_prod_iff
      (continuous_holomorphicDiskPolarChartIntegrand hf.continuous).aestronglyMeasurable]
      at hchart
    apply hchart.2.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_of_nonneg]
    unfold holomorphicDiskPolarChartIntegrand
    exact mul_nonneg hρ.1.le (sq_nonneg _)
  calc
    Real.pi * r ^ 2 * ‖f 0‖ ^ 2 =
        ∫ ρ in Ioo 0 r, 2 * Real.pi * ‖f 0‖ ^ 2 * ρ := by
      have hIoo : (∫ ρ in Ioo 0 r, ρ) = ∫ ρ in (0 : ℝ)..r, ρ := by
        rw [intervalIntegral.integral_of_le hr.le,
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [MeasureTheory.integral_const_mul, hIoo, integral_id]
      ring
    _ ≤ ∫ ρ in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi,
          holomorphicDiskPolarChartIntegrand f (ρ, θ) := by
      exact MeasureTheory.setIntegral_mono_on hlowerInt hslicesInt measurableSet_Ioo hslicele

end

end GaloisForLFunctions.HTGeometry
