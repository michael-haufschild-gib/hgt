import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalBetaKernel
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Uniform control of Suzuki's translated critical cusps

The literal primary Beta density converges to the origin atom when paired with
any translate of a compact smooth autocorrelation. Krein's increment inequality
and weighted Cauchy–Schwarz pay for every translate with the same Lévy energy.
The resulting estimate uses no derivative norm and imposes no arithmetic zeros.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.HTGeometry
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower

noncomputable section

/-- Primary Suzuki source tested at the translated correlation cusp. -/
def suzukiCriticalPrimaryCusp (f : ℝ → ℝ) (omega u : ℝ) : ℝ :=
  ∫ t in Ioi 0, autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t

theorem measurable_suzukiCriticalPrimaryCusp {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (omega : ℝ) :
    Measurable (suzukiCriticalPrimaryCusp f omega) := by
  have hm : Measurable (fun p : ℝ × ℝ => autocorr f (p.1 + p.2) *
      suzukiCriticalPrimaryDensity omega p.2) :=
    (((continuous_autocorr hf hfc).measurable.comp (measurable_fst.add measurable_snd)).mul
      ((measurable_suzukiCriticalPrimaryDensity omega).comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private theorem weighted_mean_sq_le {μ : Measure ℝ} {w g : ℝ → ℝ}
    (hnn : ∀ᵐ t ∂μ, 0 ≤ w t) (hw : Integrable w μ)
    (hg : Integrable (fun t => w t * g t) μ)
    (hg2 : Integrable (fun t => w t * g t ^ 2) μ) :
    (∫ t, w t * g t ∂μ) ^ 2 ≤ (∫ t, w t ∂μ) * ∫ t, w t * g t ^ 2 ∂μ := by
  apply sq_le_mul_of_quadratic_nonneg (integral_nonneg_of_ae
    (hnn.mono fun t ht => mul_nonneg ht (sq_nonneg _)))
  intro a
  have hpos : 0 ≤ ∫ t, w t * (1 + a * g t) ^ 2 ∂μ :=
    integral_nonneg_of_ae (hnn.mono fun t ht => mul_nonneg ht (sq_nonneg _))
  have he : (fun t => w t * (1 + a * g t) ^ 2) =
      fun t => (w t + (2 * a) * (w t * g t)) + a ^ 2 * (w t * g t ^ 2) := by
    funext t; ring
  have hi : Integrable (fun t => w t + (2 * a) * (w t * g t)) μ :=
    hw.add (hg.const_mul (2 * a))
  rw [he, integral_add hi (hg2.const_mul (a ^ 2)),
    integral_add hw (hg.const_mul (2 * a)), integral_const_mul, integral_const_mul] at hpos
  nlinarith only [hpos]

/-- The primary density is dominated by its shift times the full Lévy weight. -/
theorem suzukiCriticalPrimaryDensity_le_levy {omega t : ℝ}
    (homega : 0 < omega) (homega2 : omega ≤ 2) (ht : 0 < t) :
    suzukiCriticalPrimaryDensity omega t ≤
      (omega * suzukiCriticalPrimaryScale omega) * archLevySinhWeight t := by
  have he : archLevySinhWeight t =
      2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := by
    rw [archLevySinhWeight, exp_half_div_sinh_eq ht, archLevyDensity]
    ring
  have h := (div_le_iff₀ homega).mp
    (suzukiCriticalPrimaryDensity_div_le homega homega2 ht)
  rw [he]
  nlinarith only [h]

/-- A bounded autocorrelation is integrable against every admissible primary density. -/
theorem integrableOn_suzukiCriticalPrimaryCusp_integrand {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {omega : ℝ} (homega : 0 < omega)
    (homega5 : omega < 5 / 2) (u : ℝ) :
    IntegrableOn (fun t => autocorr f (u + t) *
      suzukiCriticalPrimaryDensity omega t) (Ioi 0) := by
  apply (integrableOn_suzukiCriticalPrimaryDensity homega homega5).bdd_mul
    (((continuous_autocorr hf hfc).comp (continuous_const.add continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, id_eq] using
      abs_autocorr_le_zero hfc hf.continuous (u + t)

/-- Every translated cusp is bounded by the exact kernel mass times source mass. -/
theorem abs_suzukiCriticalPrimaryCusp_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {omega : ℝ} (homega : 0 < omega) (homega5 : omega < 5 / 2) (u : ℝ) :
    |suzukiCriticalPrimaryCusp f omega u| ≤
      suzukiCriticalPrimaryMass omega * autocorr f 0 := by
  have hB := integrableOn_suzukiCriticalPrimaryDensity homega homega5
  have hi := integrableOn_suzukiCriticalPrimaryCusp_integrand hf hfc homega homega5 u
  calc
    _ ≤ ∫ t in Ioi 0, ‖autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t‖ := by
      simpa only [suzukiCriticalPrimaryCusp, Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (fun t => autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t)
          (μ := volume.restrict (Ioi 0)))
    _ ≤ ∫ t in Ioi 0, autocorr f 0 * suzukiCriticalPrimaryDensity omega t := by
      apply integral_mono_ae hi.norm (hB.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (suzukiCriticalPrimaryDensity_pos homega ht).le]
      exact mul_le_mul_of_nonneg_right (abs_autocorr_le_zero hfc hf.continuous (u + t))
        (suzukiCriticalPrimaryDensity_pos homega ht).le
    _ = _ := by
      rw [integral_const_mul, integral_suzukiCriticalPrimaryDensity homega homega5, mul_comm]

/-- Every translated primary cusp is controlled by the same source Lévy energy. -/
theorem suzukiCriticalPrimaryCusp_sub_mass_sq_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {omega : ℝ} (homega : 0 < omega) (homega2 : omega ≤ 2) (u : ℝ) :
    (suzukiCriticalPrimaryCusp f omega u -
      suzukiCriticalPrimaryMass omega * autocorr f u) ^ 2 ≤
        2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
          suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f := by
  have homega5 : omega < 5 / 2 := by linarith
  have hB := integrableOn_suzukiCriticalPrimaryDensity homega homega5
  have hC := continuous_autocorr hf hfc
  have hR := GaloisForLFunctions.BiScaleUncertainty.autocorr_zero_nonneg f
  have hJ := integrableOn_biScaleLevyIntegrand hf hfc
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi 0),
      0 ≤ suzukiCriticalPrimaryDensity omega t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (suzukiCriticalPrimaryDensity_pos homega ht).le
  have hdiff : ∀ t, |autocorr f (u + t) - autocorr f u| ≤ 2 * autocorr f 0 := by
    intro t
    calc
      _ ≤ |autocorr f (u + t)| + |autocorr f u| := abs_sub _ _
      _ ≤ _ := by linarith [abs_autocorr_le_zero hfc hf.continuous (u + t),
        abs_autocorr_le_zero hfc hf.continuous u]
  have hdm : AEStronglyMeasurable (fun t => autocorr f (u + t) - autocorr f u)
      (volume.restrict (Ioi 0)) :=
    ((hC.comp (continuous_const.add continuous_id)).sub continuous_const).aestronglyMeasurable
  have hdi := hB.bdd_mul hdm
    (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hdiff t)
  have hd2i := hB.bdd_mul (hdm.pow 2)
    (Eventually.of_forall fun t => show ‖(autocorr f (u + t) - autocorr f u) ^ 2‖ ≤
      (2 * autocorr f 0) ^ 2 from by
        rw [Real.norm_eq_abs, abs_pow, sq_abs]
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (autocorr f (u + t) - autocorr f u)) (hdiff t) 2)
  have hdi' : IntegrableOn (fun t => suzukiCriticalPrimaryDensity omega t *
      (autocorr f (u + t) - autocorr f u)) (Ioi 0) := by
    simpa only [IntegrableOn, mul_comm] using hdi
  have hd2i' : IntegrableOn (fun t => suzukiCriticalPrimaryDensity omega t *
      (autocorr f (u + t) - autocorr f u) ^ 2) (Ioi 0) := by
    simpa only [IntegrableOn, Pi.pow_apply, mul_comm] using hd2i
  have hbound : (∫ t in Ioi 0, suzukiCriticalPrimaryDensity omega t *
      (autocorr f (u + t) - autocorr f u) ^ 2) ≤
      (2 * autocorr f 0 * (omega * suzukiCriticalPrimaryScale omega)) *
        biScaleLevyEnergy f := by
    rw [biScaleLevyEnergy, ← integral_const_mul]
    apply integral_mono_ae hd2i' (hJ.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hk := autocorr_krein_increment_sq_le hfc hf.continuous (u + t) u
    rw [add_sub_cancel_left] at hk
    have hDt := autocorr_sub_nonneg hfc hf.continuous t
    calc
      _ ≤ suzukiCriticalPrimaryDensity omega t *
          (2 * autocorr f 0 * (autocorr f 0 - autocorr f t)) :=
        mul_le_mul_of_nonneg_left hk (suzukiCriticalPrimaryDensity_pos homega ht).le
      _ ≤ ((omega * suzukiCriticalPrimaryScale omega) * archLevySinhWeight t) *
          (2 * autocorr f 0 * (autocorr f 0 - autocorr f t)) :=
        mul_le_mul_of_nonneg_right
          (suzukiCriticalPrimaryDensity_le_levy homega homega2 ht)
          (mul_nonneg (mul_nonneg (by norm_num) hR) hDt)
      _ = _ := by ring
  have hM : 0 ≤ suzukiCriticalPrimaryMass omega := by
    rw [← integral_suzukiCriticalPrimaryDensity homega homega5]
    exact integral_nonneg_of_ae hnn
  have hcs := weighted_mean_sq_le hnn hB hdi' hd2i'
  have he : (∫ t in Ioi 0, suzukiCriticalPrimaryDensity omega t *
      (autocorr f (u + t) - autocorr f u)) =
      suzukiCriticalPrimaryCusp f omega u -
        suzukiCriticalPrimaryMass omega * autocorr f u := by
    have hci : Integrable (fun t => suzukiCriticalPrimaryDensity omega t * autocorr f (u + t))
        (volume.restrict (Ioi 0)) := by
      simpa only [IntegrableOn, mul_comm] using
        (integrableOn_suzukiCriticalPrimaryCusp_integrand hf hfc homega homega5 u)
    simp_rw [mul_sub]
    rw [integral_sub hci (hB.mul_const _), integral_mul_const,
      integral_suzukiCriticalPrimaryDensity homega homega5]
    congr 1
    unfold suzukiCriticalPrimaryCusp
    apply integral_congr_ae
    exact Eventually.of_forall fun t => mul_comm _ _
  rw [he, integral_suzukiCriticalPrimaryDensity homega homega5] at hcs
  calc
    _ ≤ _ := hcs
    _ ≤ _ := (mul_le_mul_of_nonneg_left hbound hM).trans_eq (by ring)

/-- An explicit error shared by all translated primary cusps. -/
def suzukiCriticalPrimaryCuspError (f : ℝ → ℝ) (omega : ℝ) : ℝ :=
  Real.sqrt (2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
    suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f) +
      |suzukiCriticalPrimaryMass omega - 1| * autocorr f 0

/-- The atom approximation holds uniformly in the cusp location. -/
theorem abs_suzukiCriticalPrimaryCusp_sub_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {omega : ℝ} (homega : 0 < omega) (homega2 : omega ≤ 2) (u : ℝ) :
    |suzukiCriticalPrimaryCusp f omega u - autocorr f u| ≤
      suzukiCriticalPrimaryCuspError f omega := by
  have hsq := suzukiCriticalPrimaryCusp_sub_mass_sq_le hf hfc homega homega2 u
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have hneg := Real.le_sqrt_of_sq_le
    (x := -(suzukiCriticalPrimaryCusp f omega u -
      suzukiCriticalPrimaryMass omega * autocorr f u))
    (by simpa only [neg_sq] using hsq)
  have habs : |suzukiCriticalPrimaryCusp f omega u -
      suzukiCriticalPrimaryMass omega * autocorr f u| ≤
      Real.sqrt (2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
        suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f) :=
    abs_le.mpr ⟨by linarith only [hneg], hsqrt⟩
  calc
    _ ≤ |suzukiCriticalPrimaryCusp f omega u -
        suzukiCriticalPrimaryMass omega * autocorr f u| +
        |suzukiCriticalPrimaryMass omega * autocorr f u - autocorr f u| :=
      abs_sub_le _ _ _
    _ = |suzukiCriticalPrimaryCusp f omega u -
        suzukiCriticalPrimaryMass omega * autocorr f u| +
        |suzukiCriticalPrimaryMass omega - 1| * |autocorr f u| := by
      rw [← sub_one_mul, abs_mul]
    _ ≤ _ := add_le_add habs (mul_le_mul_of_nonneg_left
      (abs_autocorr_le_zero hfc hf.continuous u) (abs_nonneg _))

theorem tendsto_suzukiCriticalPrimaryCuspError (f : ℝ → ℝ) :
    Tendsto (suzukiCriticalPrimaryCuspError f) (𝓝[>] 0) (𝓝 0) := by
  have hm := tendsto_suzukiCriticalPrimaryMass.mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  have ha := tendsto_suzukiCriticalPrimaryScale.mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  have hi : Tendsto (fun omega : ℝ => omega) (𝓝[>] 0) (𝓝 0) :=
    continuousWithinAt_id
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((((hm.const_mul (2 * autocorr f 0)).mul ha).mul hi).mul_const (biScaleLevyEnergy f))
  have hmass := ((hm.sub_const 1).abs).mul_const (autocorr f 0)
  unfold suzukiCriticalPrimaryCuspError
  simpa only [Function.comp_apply, mul_zero, zero_mul, Real.sqrt_zero,
    sub_self, abs_zero, add_zero] using hroot.add hmass

/-- Critical-shift convergence is uniform over every real translated cusp. -/
theorem tendstoUniformly_suzukiCriticalPrimaryCusp {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    TendstoUniformly (suzukiCriticalPrimaryCusp f) (autocorr f) (𝓝[>] 0) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have he := (tendsto_suzukiCriticalPrimaryCuspError f).eventually
    (Iio_mem_nhds hepsilon)
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, ho, he] with omega homega ho he u
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_suzukiCriticalPrimaryCusp_sub_le hf hfc homega ho.le u).trans_lt he

/-- The primary first variation on every compact smooth source, with its finite-energy
premise discharged by the autocorrelation Lévy identity. -/
theorem tendsto_suzukiCriticalPrimaryCusp_firstVariation {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun omega : ℝ =>
      (suzukiCriticalPrimaryCusp f omega 0 - autocorr f 0) / omega)
      (𝓝[>] 0)
      (𝓝 ((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))))) := by
  have hJ : IntegrableOn (fun t => (autocorr f 0 - autocorr f t) *
      (2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) (Ioi 0) := by
    apply (integrableOn_biScaleLevyIntegrand hf hfc).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [archLevySinhWeight, exp_half_div_sinh_eq ht, archLevyDensity]
    ring
  simpa only [suzukiCriticalPrimaryCusp, zero_add] using
    tendsto_suzukiCriticalPrimaryPairing_firstVariation
      (continuous_autocorr hf hfc).aestronglyMeasurable
      (Eventually.of_forall fun t => abs_autocorr_le_zero hfc hf.continuous t) hJ

end
end RHTower
