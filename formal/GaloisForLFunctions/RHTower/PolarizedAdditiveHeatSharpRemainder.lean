import GaloisForLFunctions.RHTower.PolarizedAdditiveHeatBoundary

/-!
# Sharp-strip polarized Jonquière remainder

Separate `L²` conditions are unnecessary after subtracting the four principal Jonquière
channels.  The difference is bounded by positive powers of the phase whenever both orders lie in
the open strip `0 < Re(s), Re(w) < 1`.  Its heat average therefore tends to zero at the aperture
boundary, including the complementary reflected case where the leading principal product itself
has order `|theta|^-1`.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- Heat average of the exact polarized germ after subtracting its four principal channels. -/
noncomputable def polarizedHeatSharpRemainder (s w : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ θ in Ioc (-Real.pi) Real.pi,
      ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) -
          germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
        heatMultiplier x θ

theorem aestronglyMeasurable_germPrincipal (s : ℂ) :
    AEStronglyMeasurable (germPrincipal s)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have hlead : Measurable (fun θ : ℝ => jonquiereLeadAt s θ) := by
    rw [show (fun θ : ℝ => jonquiereLeadAt s θ) =
      fun θ : ℝ => if θ ∈ Ioi 0 then jonquiereLead s else jonquiereLeadNeg s by
        funext θ
        rw [jonquiereLeadAt]
        rfl]
    exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have habs : Measurable fun θ : ℝ => |θ| := measurable_id.norm
  have hpow : Measurable (fun θ : ℝ => (((|θ| : ℝ)) : ℂ) ^ (s - 1)) :=
    (Complex.measurable_ofReal.comp habs).pow_const _
  exact ((hlead.mul hpow).add measurable_const).aestronglyMeasurable.restrict

/-- The subtracted polarized source is integrable on the sharp open product strip. -/
theorem integrableOn_polarizedHeatSharpRemainderSource
    {s w : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun θ : ℝ =>
      ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) -
          germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
        heatMultiplier x θ) (Ioc (-Real.pi) Real.pi) := by
  set K : ℝ := polarizedHeatErrorConst s w with hK
  have hKnn : 0 ≤ K := by rw [hK]; exact polarizedHeatErrorConst_nonneg s w
  have hmeas : AEStronglyMeasurable (fun θ : ℝ =>
      ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) -
          germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
        heatMultiplier x θ) (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    exact ((((aestronglyMeasurable_phaseGerm hs₀ hs₁).mul
      (aestronglyMeasurable_phaseGerm hw₀ hw₁).star).sub
      ((aestronglyMeasurable_germPrincipal s).mul
        (aestronglyMeasurable_germPrincipal w).star)).mul
      ((continuous_heatMultiplier hx).continuousOn.aestronglyMeasurable measurableSet_Ioc))
  have hmaj : IntegrableOn
      (fun θ : ℝ => K * (|θ| ^ s.re * heatMultiplierValue x θ)
        + K * (|θ| ^ w.re * heatMultiplierValue x θ)
        + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ))
      (Ioc (-Real.pi) Real.pi) :=
    (((integrableOn_rpow_mul_heatMultiplierValue hx hs₀).const_mul K).add
      ((integrableOn_rpow_mul_heatMultiplierValue hx hw₀).const_mul K)).add
      ((integrableOn_rpow_mul_heatMultiplierValue hx one_pos).const_mul K)
  refine Integrable.mono' hmaj hmeas ?_
  have hne₀ : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae hne₀] with θ hθ hne
  rw [norm_mul, norm_heatMultiplier hx]
  have hb := norm_polarizedGerm_sub_principal_le hs₀ hs₁ hw₀ hw₁ θ hθ hne
  have hvn : 0 ≤ heatMultiplierValue x θ := heatMultiplierValue_nonneg hx θ
  have hone : |θ| ^ (1 : ℝ) = |θ| := Real.rpow_one _
  calc
    ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ) -
          germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)‖ *
          heatMultiplierValue x θ
        ≤ (K * (|θ| ^ s.re + |θ| ^ w.re + |θ|)) *
            heatMultiplierValue x θ :=
          mul_le_mul_of_nonneg_right (by simpa [hK] using hb) hvn
    _ = K * (|θ| ^ s.re * heatMultiplierValue x θ)
          + K * (|θ| ^ w.re * heatMultiplierValue x θ)
          + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
        rw [hone]
        ring

/-- The sharp-strip Jonquière remainder is `o(1)` under the heat aperture. -/
theorem tendsto_polarizedHeatSharpRemainder
    {s w : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    Tendsto (polarizedHeatSharpRemainder s w)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  set K : ℝ := polarizedHeatErrorConst s w with hK
  have hKnn : 0 ≤ K := by rw [hK]; exact polarizedHeatErrorConst_nonneg s w
  have hbound : ∀ x : ℝ, 0 < x →
      ‖polarizedHeatSharpRemainder s w x‖ ≤
        K * (realHeatMoment x s.re + realHeatMoment x w.re + realHeatMoment x 1) := by
    intro x hx
    have hsrc := integrableOn_polarizedHeatSharpRemainderSource hs₀ hs₁ hw₀ hw₁ hx
    have hmaj : IntegrableOn
        (fun θ : ℝ => K * (|θ| ^ s.re * heatMultiplierValue x θ)
          + K * (|θ| ^ w.re * heatMultiplierValue x θ)
          + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ))
        (Ioc (-Real.pi) Real.pi) :=
      (((integrableOn_rpow_mul_heatMultiplierValue hx hs₀).const_mul K).add
        ((integrableOn_rpow_mul_heatMultiplierValue hx hw₀).const_mul K)).add
        ((integrableOn_rpow_mul_heatMultiplierValue hx one_pos).const_mul K)
    have hne₀ : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
      MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
    have hptwise : (fun θ : ℝ => ‖
          ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) -
            germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
              heatMultiplier x θ‖)
        ≤ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)]
          fun θ : ℝ => K * (|θ| ^ s.re * heatMultiplierValue x θ)
            + K * (|θ| ^ w.re * heatMultiplierValue x θ)
            + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
        MeasureTheory.ae_restrict_of_ae hne₀] with θ hθ hne
      rw [norm_mul, norm_heatMultiplier hx]
      have hb := norm_polarizedGerm_sub_principal_le hs₀ hs₁ hw₀ hw₁ θ hθ hne
      have hvn : 0 ≤ heatMultiplierValue x θ := heatMultiplierValue_nonneg hx θ
      have hone : |θ| ^ (1 : ℝ) = |θ| := Real.rpow_one _
      calc
        ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ) -
            germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)‖ *
              heatMultiplierValue x θ
          ≤ (K * (|θ| ^ s.re + |θ| ^ w.re + |θ|)) *
              heatMultiplierValue x θ :=
            mul_le_mul_of_nonneg_right (by simpa [hK] using hb) hvn
        _ = K * (|θ| ^ s.re * heatMultiplierValue x θ)
              + K * (|θ| ^ w.re * heatMultiplierValue x θ)
              + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
            rw [hone]
            ring
    have hstep : ‖∫ θ in Ioc (-Real.pi) Real.pi,
          ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) -
            germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
              heatMultiplier x θ‖
        ≤ ∫ θ in Ioc (-Real.pi) Real.pi,
            (K * (|θ| ^ s.re * heatMultiplierValue x θ)
              + K * (|θ| ^ w.re * heatMultiplierValue x θ)
              + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      exact MeasureTheory.setIntegral_mono_ae_restrict hsrc.norm hmaj hptwise
    have hval : (∫ θ in Ioc (-Real.pi) Real.pi,
          (K * (|θ| ^ s.re * heatMultiplierValue x θ)
            + K * (|θ| ^ w.re * heatMultiplierValue x θ)
            + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ))) =
        K * (2 * Real.pi) *
          (realHeatMoment x s.re + realHeatMoment x w.re + realHeatMoment x 1) := by
      calc
        _ = (∫ θ in Ioc (-Real.pi) Real.pi,
              (K * (|θ| ^ s.re * heatMultiplierValue x θ)
                + K * (|θ| ^ w.re * heatMultiplierValue x θ)))
            + ∫ θ in Ioc (-Real.pi) Real.pi,
              K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) :=
            MeasureTheory.integral_add
              (((integrableOn_rpow_mul_heatMultiplierValue hx hs₀).const_mul K).add
                ((integrableOn_rpow_mul_heatMultiplierValue hx hw₀).const_mul K))
              ((integrableOn_rpow_mul_heatMultiplierValue hx one_pos).const_mul K)
        _ = ((∫ θ in Ioc (-Real.pi) Real.pi,
              K * (|θ| ^ s.re * heatMultiplierValue x θ))
            + ∫ θ in Ioc (-Real.pi) Real.pi,
              K * (|θ| ^ w.re * heatMultiplierValue x θ))
            + ∫ θ in Ioc (-Real.pi) Real.pi,
              K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
            rw [MeasureTheory.integral_add
              ((integrableOn_rpow_mul_heatMultiplierValue hx hs₀).const_mul K)
              ((integrableOn_rpow_mul_heatMultiplierValue hx hw₀).const_mul K)]
        _ = _ := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul, realHeatMoment, realHeatMoment, realHeatMoment]
          field_simp
    rw [polarizedHeatSharpRemainder, norm_mul]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hnorm : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
      norm_num
    rw [hnorm]
    have hmul := mul_le_mul_of_nonneg_left (hstep.trans (le_of_eq hval))
      (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    refine hmul.trans (le_of_eq ?_)
    field_simp
  have hlim : Tendsto
      (fun x : ℝ => K *
        (realHeatMoment x s.re + realHeatMoment x w.re + realHeatMoment x 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hsum := ((tendsto_realHeatMoment hs₀).add (tendsto_realHeatMoment hw₀)).add
      (tendsto_realHeatMoment one_pos)
    rw [zero_add, zero_add] at hsum
    have h := hsum.const_mul K
    rw [mul_zero] at h
    exact h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hbound x hx

/-- Closed parameter space for the sharp polarized remainder. -/
structure PolarizedHeatOpenBistrip where
  s : ℂ
  w : ℂ
  s_re_pos : 0 < s.re
  s_re_lt_one : s.re < 1
  w_re_pos : 0 < w.re
  w_re_lt_one : w.re < 1

/-- Premise-free sharp-remainder capstone. -/
theorem polarizedHeatSharpRemainder_capstone :
    ∀ P : PolarizedHeatOpenBistrip,
      Tendsto (polarizedHeatSharpRemainder P.s P.w)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro P
  exact tendsto_polarizedHeatSharpRemainder
    P.s_re_pos P.s_re_lt_one P.w_re_pos P.w_re_lt_one

end RHTower
