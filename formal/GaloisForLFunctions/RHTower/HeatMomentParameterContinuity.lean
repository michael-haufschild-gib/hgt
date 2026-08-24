import GaloisForLFunctions.RHTower.HeatFullWindowMoment
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Parameter continuity of full-window heat moments

For every locally integrable exponent, the exact full-window heat moment is continuous when its
complex exponent is shifted along the positive real regulator ray.  A two-power majorant handles
both sides of the unit phase scale.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Positive real half-shifts of a locally integrable exponent converge in the exact heat moment. -/
theorem tendsto_heatMoment_add_real_half
    {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun epsilon : ℝ => heatMoment x (lam + (epsilon : ℂ) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (heatMoment x lam)) := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn
      (continuous_heatMultiplier hx).continuousOn
  have hM0 : 0 ≤ M := by
    exact (norm_nonneg (heatMultiplier x 0)).trans
      (hM 0 (by constructor <;> linarith [Real.pi_pos]))
  let bound : ℝ → ℝ := fun theta =>
    M * (|theta| ^ lam.re + |theta| ^ (lam.re + 1 / 2))
  have hboundInt : Integrable bound
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    have hleft := integrableOn_abs_rpow_window hlam
    have hright := integrableOn_abs_rpow_window
      (show -1 < lam.re + 1 / 2 by linarith)
    exact (hleft.add hright).const_mul M
  have hmeas : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun theta : ℝ =>
        ((|theta| : ℝ) : ℂ) ^ (lam + (epsilon : ℂ) / 2) * heatMultiplier x theta)
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    have hepsilon0 : 0 < epsilon := hepsilon
    have hlocal : -1 < (lam + (epsilon : ℂ) / 2).re := by
      norm_num [Complex.add_re, Complex.div_re]
      linarith
    have hneg := integrableOn_abs_cpow_mul_heatMultiplier_neg hlocal hx
    have hpos : IntegrableOn (fun theta : ℝ =>
        ((|theta| : ℝ) : ℂ) ^ (lam + (epsilon : ℂ) / 2) * heatMultiplier x theta)
        (Ioc (0 : ℝ) Real.pi) := by
      refine (integrableOn_cpow_mul_heatMultiplier hlocal hx).congr_fun ?_ measurableSet_Ioc
      intro theta htheta
      simp only [abs_of_pos htheta.1]
    have hunion := hneg.union hpos
    rw [Ioc_union_Ioc_eq_Ioc (by linarith [Real.pi_pos]) Real.pi_pos.le] at hunion
    exact hunion.aestronglyMeasurable
  have hbound : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᵐ theta : ℝ ∂(volume.restrict (Ioc (-Real.pi) Real.pi)),
        ‖((|theta| : ℝ) : ℂ) ^ (lam + (epsilon : ℂ) / 2) *
            heatMultiplier x theta‖ ≤ bound theta := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with epsilon hepsilon hepsilonOne
    have hepsilon0 : 0 < epsilon := hepsilon
    have hneZero : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ 0 :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hneZero] with theta htheta htheta0
    have hpos : 0 < |theta| := abs_pos.mpr htheta0
    have hthetaIcc : theta ∈ Icc (-Real.pi) Real.pi := ⟨htheta.1.le, htheta.2⟩
    have hreLower : lam.re ≤ (lam + (epsilon : ℂ) / 2).re := by
      norm_num [Complex.add_re, Complex.div_re]
      linarith
    have hreUpper : (lam + (epsilon : ℂ) / 2).re ≤ lam.re + 1 / 2 := by
      norm_num [Complex.add_re, Complex.div_re]
      linarith [hepsilonOne.2]
    have hrpow : |theta| ^ (lam + (epsilon : ℂ) / 2).re ≤
        |theta| ^ lam.re + |theta| ^ (lam.re + 1 / 2) := by
      by_cases hunit : |theta| ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hpos hunit hreLower).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg hpos.le _))
      · have hone : 1 ≤ |theta| := le_of_not_ge hunit
        exact (Real.rpow_le_rpow_of_exponent_le hone hreUpper).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hpos.le _))
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    calc
      |theta| ^ (lam + (epsilon : ℂ) / 2).re * ‖heatMultiplier x theta‖
          ≤ |theta| ^ (lam + (epsilon : ℂ) / 2).re * M :=
        mul_le_mul_of_nonneg_left (hM theta hthetaIcc) (Real.rpow_nonneg hpos.le _)
      _ ≤ M * (|theta| ^ lam.re + |theta| ^ (lam.re + 1 / 2)) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hrpow hM0
  have hlim : ∀ᵐ theta : ℝ ∂(volume.restrict (Ioc (-Real.pi) Real.pi)),
      Tendsto (fun epsilon : ℝ =>
        ((|theta| : ℝ) : ℂ) ^ (lam + (epsilon : ℂ) / 2) * heatMultiplier x theta)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((|theta| : ℝ) : ℂ) ^ lam * heatMultiplier x theta)) := by
    have hneZero : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ 0 :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
    filter_upwards [MeasureTheory.ae_restrict_of_ae hneZero] with theta htheta0
    have hbase : (((|theta| : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr htheta0)
    have hexponent : Tendsto (fun epsilon : ℝ => lam + (epsilon : ℂ) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 lam) := by
      have hepsilon : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using tendsto_const_nhds.add (hepsilon.div_const 2)
    exact ((continuousAt_const_cpow hbase).tendsto.comp hexponent).mul_const _
  have hintegral := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hboundInt hlim
  have hscaled := hintegral.const_mul (1 / (2 * (Real.pi : ℂ)))
  simpa [heatMoment] using hscaled

end

end RHTower
