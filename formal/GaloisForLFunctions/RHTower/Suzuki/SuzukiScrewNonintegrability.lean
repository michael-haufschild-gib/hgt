import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewPointwiseNonnegativityCriterion
import GaloisForLFunctions.RHTower.XiWeilResolventChartDictionary
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

def suzukiPsiRealLaplace (r : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-r * t) * suzukiPsi t

theorem suzukiPsiLaplace_ofReal (r : ℝ) :
    suzukiPsiLaplace (r : ℂ) = (suzukiPsiRealLaplace r : ℂ) := by
  rw [suzukiPsiLaplace, suzukiPsiRealLaplace]
  calc
    (∫ t : ℝ in Ioi 0, Complex.exp (-(r : ℂ) * (t : ℂ)) * (suzukiPsi t : ℂ)) =
        ∫ t : ℝ in Ioi 0, ((Real.exp (-r * t) * suzukiPsi t : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      push_cast
      rw [show -(r : ℂ) * (t : ℂ) = ((-r * t : ℝ) : ℂ) by push_cast; ring]
    _ = ((∫ t : ℝ in Ioi 0, Real.exp (-r * t) * suzukiPsi t : ℝ) : ℂ) := integral_ofReal

theorem ccmXiScrewAllExponentialMoments_of_integrableOn_suzukiPsi
    (hPsi : IntegrableOn suzukiPsi (Ioi 0)) :
    CCMXiScrewAllExponentialMoments := by
  intro a ha
  have hPsiC : Integrable (fun t : ℝ => (suzukiPsi t : ℂ))
      (volume.restrict (Ioi 0)) := hPsi.ofReal
  let e : ℝ → ℂ := fun t => Complex.exp (-(a : ℂ) * (t : ℂ))
  have heMeas : AEStronglyMeasurable e (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous e).aestronglyMeasurable
  have heBound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ‖e t‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [e]
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have : 0 ≤ a * t := mul_nonneg ha.le ht.le
    linarith
  have hprod : Integrable (fun t => e t * (suzukiPsi t : ℂ))
      (volume.restrict (Ioi 0)) := hPsiC.bdd_mul heMeas heBound
  apply hprod.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ofReal_suzukiPsi_eq_xiScrewDivisor ht.le]

theorem exp_neg_ofReal_memLp_two {a : ℝ} (ha : 0 < a) :
    MemLp (fun t : ℝ => Complex.exp (-(a : ℂ) * (t : ℂ))) 2
      (volume.restrict (Ioi 0)) := by
  rw [memLp_two_iff_integrable_sq_norm]
  · have h := integrableOn_exp_mul_Ioi (a := -2 * a) (by linarith) 0
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [show Real.exp (-a * t) ^ (2 : ℕ) = Real.exp ((-2 * a) * t) by
      rw [sq, ← Real.exp_add]
      congr 1
      ring]
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-(a : ℂ) * (t : ℂ)))).aestronglyMeasurable

theorem ccmXiScrewAllExponentialMoments_of_memLp_two_suzukiPsi
    (hPsi : MemLp suzukiPsi 2 (volume.restrict (Ioi 0))) :
    CCMXiScrewAllExponentialMoments := by
  intro a ha
  have hPsiC : MemLp (fun t : ℝ => (suzukiPsi t : ℂ)) 2
      (volume.restrict (Ioi 0)) := hPsi.ofReal
  have he := exp_neg_ofReal_memLp_two ha
  have hprod : MemLp (fun t : ℝ =>
      (suzukiPsi t : ℂ) * Complex.exp (-(a : ℂ) * (t : ℂ))) 1
      (volume.restrict (Ioi 0)) := he.mul' hPsiC
  have hint0 : Integrable (fun t : ℝ =>
      (suzukiPsi t : ℂ) * Complex.exp (-(a : ℂ) * (t : ℂ)))
      (volume.restrict (Ioi 0)) := memLp_one_iff_integrable.mp hprod
  have hint : Integrable (fun t : ℝ =>
      Complex.exp (-(a : ℂ) * (t : ℂ)) * (suzukiPsi t : ℂ))
      (volume.restrict (Ioi 0)) := hint0.congr (Filter.Eventually.of_forall fun t => mul_comm _ _)
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ofReal_suzukiPsi_eq_xiScrewDivisor ht.le]

theorem mul_suzukiPsiLaplaceContinuation_ofReal_eq_xiResolventMoment
    {r : ℝ} (hr : 0 < r) :
    (r : ℂ) * suzukiPsiLaplaceContinuation (r : ℂ) =
      xiResolventMoment 0 (r ^ (2 : ℕ)) := by
  rw [suzukiPsiLaplaceContinuation, xiResolventMoment, ← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [pow_one, suzukiPsiLaplaceAtom, xiResolventPoint]
  push_cast
  field_simp [hr.ne']
  ring

theorem tendsto_xiResolventMoment_zero_sq_at_zero :
    Tendsto (fun r : ℝ => xiResolventMoment 0 (r ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 (xiResolventMoment 0 0)) := by
  rw [xiResolventMoment]
  apply tendsto_tsum_of_dominated_convergence
      (xiSpectralPoint_inv_sq_summable.mul_left 2)
  · intro q
    have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hden : Tendsto (fun r : ℝ =>
        xiSpectralPoint q ^ (2 : ℕ) + ((r ^ (2 : ℕ) : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 (xiSpectralPoint q ^ (2 : ℕ))) := by
      convert tendsto_const_nhds.add ((hr0.pow 2).ofReal) using 1
      all_goals simp
    have hinv := hden.inv₀ (pow_ne_zero 2 (xiSpectralPoint_ne_zero q))
    simpa only [xiResolventPoint, Nat.zero_add, pow_one, Complex.ofReal_zero, add_zero] using hinv
  · filter_upwards [self_mem_nhdsWithin] with r hr q
    simpa only [Nat.zero_add, pow_one] using norm_xiResolventPoint_le (sq_nonneg r) q

theorem xiResolventMoment_zero_zero_re_pos :
    0 < (xiResolventMoment 0 0).re := by
  have h := xiWeilPolarization_cauchyTest_re_pos 0
  rw [xiWeilPolarization_cauchyTest_eq_resolventMoment] at h
  simpa using h

theorem xiResolventMoment_zero_zero_ne : xiResolventMoment 0 0 ≠ 0 := by
  intro h
  have hp := xiResolventMoment_zero_zero_re_pos
  rw [h] at hp
  simp at hp

theorem eventually_suzukiPsiLaplace_eq_continuation_of_allMoments
    (hMom : CCMXiScrewAllExponentialMoments) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      suzukiPsiLaplace (r : ℂ) = suzukiPsiLaplaceContinuation (r : ℂ) := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_ccmXiScrew_all_exponential_moments hMom
  have hsource : SuzukiPsiPointwiseNonnegative :=
    suzukiPsiPointwiseNonnegative_of_riemannHypothesis hRH
  have hMomZero : SuzukiPsiMomentsAbove 0 :=
    suzukiPsiMomentsAbove_zero hsource
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hlt] with r hr0 hr1
  have hrpos : 0 < r := by simpa only [mem_Ioi] using hr0
  have hb : 0 < r / 2 := by linarith
  have hbHalf : r / 2 ≤ 1 / 2 := by linarith
  have hMomHalf : SuzukiPsiMomentsAbove (r / 2) := by
    intro a ha
    exact hMomZero a (lt_trans hb ha)
  have heq := suzukiPsiLaplace_eq_continuation_of_momentsAbove
    hsource hb hbHalf hMomHalf
  apply heq
  constructor
  · simp only [Complex.ofReal_re]
    linarith
  · simp only [Complex.ofReal_im, abs_zero]
    positivity

theorem tendsto_mul_suzukiPsiLaplaceContinuation_at_zero :
    Tendsto (fun r : ℝ => (r : ℂ) * suzukiPsiLaplaceContinuation (r : ℂ))
      (𝓝[>] 0) (𝓝 (xiResolventMoment 0 0)) := by
  refine tendsto_xiResolventMoment_zero_sq_at_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (mul_suzukiPsiLaplaceContinuation_ofReal_eq_xiResolventMoment hr).symm

theorem tendsto_mul_suzukiPsiLaplace_of_allMoments
    (hMom : CCMXiScrewAllExponentialMoments) :
    Tendsto (fun r : ℝ => (r : ℂ) * suzukiPsiLaplace (r : ℂ))
      (𝓝[>] 0) (𝓝 (xiResolventMoment 0 0)) := by
  refine tendsto_mul_suzukiPsiLaplaceContinuation_at_zero.congr' ?_
  filter_upwards [eventually_suzukiPsiLaplace_eq_continuation_of_allMoments hMom]
      with r hr
  rw [hr]

theorem abs_suzukiPsiRealLaplace_le_integral_abs
    (hPsi : IntegrableOn suzukiPsi (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    |suzukiPsiRealLaplace r| ≤ ∫ t : ℝ in Ioi 0, |suzukiPsi t| := by
  have heMeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-r * t))
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-r * t))).aestronglyMeasurable
  have heBound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ‖Real.exp (-r * t)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := by simpa only [mem_Ioi] using ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [hr, htpos])
  have hprod : Integrable (fun t : ℝ => Real.exp (-r * t) * suzukiPsi t)
      (volume.restrict (Ioi 0)) := hPsi.bdd_mul heMeas heBound
  rw [suzukiPsiRealLaplace]
  calc
    |∫ t : ℝ in Ioi 0, Real.exp (-r * t) * suzukiPsi t| ≤
        ∫ t : ℝ in Ioi 0, |Real.exp (-r * t) * suzukiPsi t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ in Ioi 0, |suzukiPsi t| := by
      apply integral_mono_ae hprod.norm hPsi.norm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := by simpa only [mem_Ioi] using ht
      simp only [Real.norm_eq_abs, norm_mul]
      rw [abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-r * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hr, htpos])
      exact mul_le_of_le_one_left (abs_nonneg _) he

theorem tendsto_mul_suzukiPsiLaplace_zero_of_integrableOn
    (hPsi : IntegrableOn suzukiPsi (Ioi 0)) :
    Tendsto (fun r : ℝ => (r : ℂ) * suzukiPsiLaplace (r : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  let M : ℝ := ∫ t : ℝ in Ioi 0, |suzukiPsi t|
  have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun r : ℝ => r * M) (𝓝[>] 0) (𝓝 0) := by
    simpa using hr0.mul_const M
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards with r
    exact norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : 0 < r := by simpa only [mem_Ioi] using hr
    rw [suzukiPsiLaplace_ofReal, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hrpos]
    dsimp only [M]
    exact mul_le_mul_of_nonneg_left
      (abs_suzukiPsiRealLaplace_le_integral_abs hPsi hrpos) hrpos.le

theorem integral_sq_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, Real.exp (-r * t) ^ (2 : ℕ)) = 1 / (2 * r) := by
  have hfun : (fun t : ℝ => Real.exp (-r * t) ^ (2 : ℕ)) =
      fun t : ℝ => Real.exp ((-2 * r) * t) := by
    funext t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_exp_mul_Ioi (by linarith : -2 * r < 0) 0]
  simp only [mul_zero, Real.exp_zero, neg_div]
  field_simp [hr.ne']

theorem sq_suzukiPsiRealLaplace_le
    (hPsi : MemLp suzukiPsi 2 (volume.restrict (Ioi 0)))
    {r : ℝ} (hr : 0 < r) :
    suzukiPsiRealLaplace r ^ (2 : ℕ) ≤
      (∫ t : ℝ in Ioi 0, suzukiPsi t ^ (2 : ℕ)) / (2 * r) := by
  have hPsiSq : Integrable (fun t : ℝ => suzukiPsi t ^ (2 : ℕ))
      (volume.restrict (Ioi 0)) :=
    (memLp_two_iff_integrable_sq hPsi.1).mp hPsi
  have heMeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-r * t))
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-r * t))).aestronglyMeasurable
  have heSq : Integrable (fun t : ℝ => Real.exp (-r * t) ^ (2 : ℕ))
      (volume.restrict (Ioi 0)) := by
    have h := integrableOn_exp_mul_Ioi (a := -2 * r) (by linarith) 0
    apply h.congr
    filter_upwards with t
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hcs := sq_integral_mul_le (μ := volume.restrict (Ioi 0))
    hPsi.1 heMeas hPsiSq heSq
  rw [integral_sq_exp_neg_mul_Ioi hr] at hcs
  rw [suzukiPsiRealLaplace]
  convert hcs using 1
  · congr 2
    funext t
    ring
  · ring

theorem tendsto_mul_suzukiPsiLaplace_zero_of_memLp_two
    (hPsi : MemLp suzukiPsi 2 (volume.restrict (Ioi 0))) :
    Tendsto (fun r : ℝ => (r : ℂ) * suzukiPsiLaplace (r : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := ∫ t : ℝ in Ioi 0, suzukiPsi t ^ (2 : ℕ)
  have hC : 0 ≤ C := integral_nonneg fun _ => sq_nonneg _
  let N : ℝ → ℝ := fun r => ‖(r : ℂ) * suzukiPsiLaplace (r : ℂ)‖
  have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun r : ℝ => C * r / 2) (𝓝[>] 0) (𝓝 0) := by
    convert (hr0.const_mul C).div_const 2 using 1
    all_goals ring
  have hsq : Tendsto (fun r => N r ^ (2 : ℕ)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards with r
      exact sq_nonneg (N r)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hrpos : 0 < r := by simpa only [mem_Ioi] using hr
      have hbase := sq_suzukiPsiRealLaplace_le hPsi hrpos
      dsimp only [N]
      rw [suzukiPsiLaplace_ofReal, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos hrpos, mul_pow, sq_abs]
      dsimp only [C]
      calc
        r ^ (2 : ℕ) * suzukiPsiRealLaplace r ^ (2 : ℕ) ≤
            r ^ (2 : ℕ) * ((∫ t : ℝ in Ioi 0, suzukiPsi t ^ (2 : ℕ)) / (2 * r)) := by
          gcongr
        _ = (∫ t : ℝ in Ioi 0, suzukiPsi t ^ (2 : ℕ)) * r / 2 := by
          field_simp [hrpos.ne']
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto N (𝓝[>] 0) (𝓝 0)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun r => Real.sqrt (N r ^ (2 : ℕ))) (𝓝[>] 0)
      (𝓝 (Real.sqrt 0)) at hsqrt
  have hsqrt' : Tendsto (fun r => Real.sqrt (N r ^ (2 : ℕ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hsqrt
  have hN (r : ℝ) : 0 ≤ N r := by dsimp only [N]; exact norm_nonneg _
  simpa only [Real.sqrt_sq (hN _)] using hsqrt'

/-- **Suzuki 2022, after Theorem 1.6 (the L1 clause).**  The literal screw function does not
belong to `L¹(0, ∞)`, unconditionally. -/
theorem not_integrableOn_suzukiPsi :
    ¬ IntegrableOn suzukiPsi (Ioi 0) := by
  intro hPsi
  have hzero := tendsto_mul_suzukiPsiLaplace_zero_of_integrableOn hPsi
  have hMom := ccmXiScrewAllExponentialMoments_of_integrableOn_suzukiPsi hPsi
  have hcentral := tendsto_mul_suzukiPsiLaplace_of_allMoments hMom
  have heq : (0 : ℂ) = xiResolventMoment 0 0 :=
    tendsto_nhds_unique hzero hcentral
  exact xiResolventMoment_zero_zero_ne heq.symm

/-- **Suzuki 2022, after Theorem 1.6 (the L2 clause).**  The literal screw function does not
belong to `L²(0, ∞)`, unconditionally. -/
theorem not_memLp_two_suzukiPsi :
    ¬ MemLp suzukiPsi 2 (volume.restrict (Ioi 0)) := by
  intro hPsi
  have hzero := tendsto_mul_suzukiPsiLaplace_zero_of_memLp_two hPsi
  have hMom := ccmXiScrewAllExponentialMoments_of_memLp_two_suzukiPsi hPsi
  have hcentral := tendsto_mul_suzukiPsiLaplace_of_allMoments hMom
  have heq : (0 : ℂ) = xiResolventMoment 0 0 :=
    tendsto_nhds_unique hzero hcentral
  exact xiResolventMoment_zero_zero_ne heq.symm

end

end RHTower
