import GaloisForLFunctions.RHTower.HeatEnergyReal

/-!
# The additive heat-aperture energy and its small-aperture expansion

This is equation `(7)`: the heat quadratic form of the boundary germ is, up to `o(1)`, the sum of
the four Gaussian moments of the Jonquière principal part.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The additive heat-aperture energy of the boundary germ. -/
noncomputable def heatEnergy (s : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ)))
    * ∫ θ in Ioc (-Real.pi) Real.pi,
        (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)) * heatMultiplier x θ

/-- The four principal terms of `(7)`. -/
noncomputable def heatEnergyPrincipal (s : ℂ) (x : ℝ) : ℂ :=
  ((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ) / 2 * heatMoment x (((2 * s.re - 2 : ℝ)) : ℂ)
    + ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ) / 2 * heatMoment x (((2 * s.re - 2 : ℝ)) : ℂ)
    + (jonquiereLead s * (starRingEnd ℂ) (riemannZeta s)
        + jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta s)) / 2 * heatMoment x (s - 1)
    + ((starRingEnd ℂ) (jonquiereLead s) * riemannZeta s
        + (starRingEnd ℂ) (jonquiereLeadNeg s) * riemannZeta s) / 2
      * heatMoment x ((starRingEnd ℂ) s - 1)
    + ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)

/-- The germ energy integrand is integrable on the window. -/
theorem integrableOn_germSq_mul_heatMultiplier {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun θ : ℝ => (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)) * heatMultiplier x θ)
      (Ioc (-Real.pi) Real.pi) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-Real.pi)) (b := Real.pi)).exists_bound_of_continuousOn
    ((continuous_heatMultiplier hx).continuousOn)
  have hL2 := memLp_phaseGerm h0 h1
  have hsq : Integrable (fun θ : ℝ => ‖phaseGerm s θ‖ ^ 2)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_phaseGerm h0' h1)).mp hL2
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)) * heatMultiplier x θ)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (aestronglyMeasurable_phaseGerm h0' h1).mul
        ((aestronglyMeasurable_phaseGerm h0' h1).star)
    · exact (continuous_heatMultiplier hx).continuousOn.aestronglyMeasurable measurableSet_Ioc
  refine Integrable.mono' (hsq.const_mul M) hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  have hmem : θ ∈ Icc (-Real.pi) Real.pi := ⟨hθ.1.le, hθ.2⟩
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  have hb := hM θ hmem
  have hnn : (0 : ℝ) ≤ ‖phaseGerm s θ‖ := norm_nonneg _
  have hstep : ‖phaseGerm s θ‖ * ‖phaseGerm s θ‖ * ‖heatMultiplier x θ‖
      ≤ ‖phaseGerm s θ‖ * ‖phaseGerm s θ‖ * M :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  refine hstep.trans (le_of_eq ?_)
  ring

/-- The squared principal part is integrable against the multiplier. -/
theorem integrableOn_principalSq_mul_heatMultiplier {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun θ : ℝ => (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)) * heatMultiplier x θ)
      (Ioc (-Real.pi) Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hl1 : (-1 : ℝ) < (((2 * s.re - 2 : ℝ)) : ℂ).re := by simp; linarith
  have hl2 : (-1 : ℝ) < (s - 1).re := by simp; linarith
  have hl3 : (-1 : ℝ) < ((starRingEnd ℂ) s - 1).re := by simp; linarith
  have hl4 : (-1 : ℝ) < (0 : ℂ).re := by simp
  have hi1 := integrableOn_halfSplit hx hl1 ((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ)
    ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ)
  have hi2 := integrableOn_halfSplit hx hl2 (jonquiereLead s * (starRingEnd ℂ) (riemannZeta s))
    (jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta s))
  have hi3 := integrableOn_halfSplit hx hl3 ((starRingEnd ℂ) (jonquiereLead s) * riemannZeta s)
    ((starRingEnd ℂ) (jonquiereLeadNeg s) * riemannZeta s)
  have hi4 := integrableOn_halfSplit hx hl4 ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)
    ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  refine (((hi1.add hi2).add hi3).add hi4).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_of_ae hne0] with θ hne
  simp only [Pi.add_apply]
  rw [germPrincipal_mul_conj s hne]
  simp only [ite_self]
  rw [add_mul, add_mul, add_mul]

/-- **The principal energy is the four-moment sum.** -/
theorem heatEnergyPrincipal_eq {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * (Real.pi : ℂ)))
      * (∫ θ in Ioc (-Real.pi) Real.pi,
          (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)) * heatMultiplier x θ)
      = heatEnergyPrincipal s x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hl1 : (-1 : ℝ) < (((2 * s.re - 2 : ℝ)) : ℂ).re := by simp; linarith
  have hl2 : (-1 : ℝ) < (s - 1).re := by simp; linarith
  have hl3 : (-1 : ℝ) < ((starRingEnd ℂ) s - 1).re := by simp; linarith
  have hl4 : (-1 : ℝ) < (0 : ℂ).re := by simp
  set g1 : ℝ → ℂ := fun θ => ((if 0 < θ then ((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ)
      else ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ))
    * ((|θ| : ℝ) : ℂ) ^ (((2 * s.re - 2 : ℝ)) : ℂ)) * heatMultiplier x θ with hg1
  set g2 : ℝ → ℂ := fun θ => ((if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (riemannZeta s)
      else jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta s))
    * ((|θ| : ℝ) : ℂ) ^ (s - 1)) * heatMultiplier x θ with hg2
  set g3 : ℝ → ℂ := fun θ => ((if 0 < θ then (starRingEnd ℂ) (jonquiereLead s) * riemannZeta s
      else (starRingEnd ℂ) (jonquiereLeadNeg s) * riemannZeta s)
    * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) s - 1)) * heatMultiplier x θ with hg3
  set g4 : ℝ → ℂ := fun θ => ((if 0 < θ then ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)
      else ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ))
    * ((|θ| : ℝ) : ℂ) ^ (0 : ℂ)) * heatMultiplier x θ with hg4
  have hi1 : IntegrableOn g1 (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx hl1 _ _
  have hi2 : IntegrableOn g2 (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx hl2 _ _
  have hi3 : IntegrableOn g3 (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx hl3 _ _
  have hi4 : IntegrableOn g4 (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx hl4 _ _
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hpt : (fun θ : ℝ =>
      (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)) * heatMultiplier x θ)
      =ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)] fun θ => g1 θ + g2 θ + g3 θ + g4 θ := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne0] with θ hne
    rw [germPrincipal_mul_conj s hne, hg1, hg2, hg3, hg4]
    simp only [ite_self]
    rw [add_mul, add_mul, add_mul]
  have hsum : (∫ θ in Ioc (-Real.pi) Real.pi, (g1 θ + g2 θ + g3 θ + g4 θ))
      = (∫ θ in Ioc (-Real.pi) Real.pi, g1 θ) + (∫ θ in Ioc (-Real.pi) Real.pi, g2 θ)
        + (∫ θ in Ioc (-Real.pi) Real.pi, g3 θ) + (∫ θ in Ioc (-Real.pi) Real.pi, g4 θ) := by
    rw [MeasureTheory.integral_add (f := fun θ => g1 θ + g2 θ + g3 θ) (g := g4)
        (by exact (hi1.add hi2).add hi3) hi4,
      MeasureTheory.integral_add (f := fun θ => g1 θ + g2 θ) (g := g3)
        (by exact hi1.add hi2) hi3,
      MeasureTheory.integral_add (f := g1) (g := g2) hi1 hi2]
  rw [MeasureTheory.integral_congr_ae hpt, hsum]
  have e1 := heatMoment_halfSplit hx hl1 ((‖jonquiereLead s‖ ^ 2 : ℝ) : ℂ)
    ((‖jonquiereLeadNeg s‖ ^ 2 : ℝ) : ℂ)
  have e2 := heatMoment_halfSplit hx hl2 (jonquiereLead s * (starRingEnd ℂ) (riemannZeta s))
    (jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta s))
  have e3 := heatMoment_halfSplit hx hl3 ((starRingEnd ℂ) (jonquiereLead s) * riemannZeta s)
    ((starRingEnd ℂ) (jonquiereLeadNeg s) * riemannZeta s)
  have e4 := heatMoment_halfSplit hx hl4 ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)
    ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)
  rw [heatMoment_zero hx] at e4
  rw [heatEnergyPrincipal]
  rw [mul_add, mul_add, mul_add, e1, e2, e3, e4]
  ring

/-- The norm of a real-exponent power test. -/
theorem norm_cpow_mul_heatMultiplier {x : ℝ} (hx : 0 < x) {lam : ℝ} (hlam : 0 < lam) (θ : ℝ) :
    ‖((|θ| : ℝ) : ℂ) ^ ((lam : ℝ) : ℂ) * heatMultiplier x θ‖
      = |θ| ^ lam * heatMultiplierValue x θ := by
  rw [norm_mul, norm_heatMultiplier hx]
  congr 1
  rcases eq_or_ne θ 0 with h | h
  · subst h
    have hz : ((|(0 : ℝ)| : ℝ) : ℂ) = 0 := by simp
    rw [hz, Complex.zero_cpow (by simpa using hlam.ne'), norm_zero, abs_zero,
      Real.zero_rpow hlam.ne']
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr h)]
    simp

/-- The real power test is integrable on the window. -/
theorem integrableOn_rpow_mul_heatMultiplierValue {x : ℝ} (hx : 0 < x) {lam : ℝ}
    (hlam : 0 < lam) :
    IntegrableOn (fun θ : ℝ => |θ| ^ lam * heatMultiplierValue x θ)
      (Ioc (-Real.pi) Real.pi) := by
  have hj := (integrableOn_halfSplit hx (lam := ((lam : ℝ) : ℂ))
    (by simp; linarith) 1 1).norm
  refine hj.congr ?_
  filter_upwards with θ
  rw [ite_self, one_mul]
  exact norm_cpow_mul_heatMultiplier hx hlam θ

/-- **Equation `(7)`.**  The additive heat-aperture energy of the boundary germ agrees with the
four-moment principal energy up to `o(1)` in the small-aperture limit. -/
theorem tendsto_heatEnergy_sub_principal {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    Tendsto (fun x : ℝ => heatEnergy s x - heatEnergyPrincipal s x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set K : ℝ := heatEnergyErrorConst s with hK
  have hKnn : 0 ≤ K := heatEnergyErrorConst_nonneg s
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hbound : ∀ x : ℝ, 0 < x →
      ‖heatEnergy s x - heatEnergyPrincipal s x‖
        ≤ K * (realHeatMoment x s.re + realHeatMoment x 1) := by
    intro x hx
    have hdiff : heatEnergy s x - heatEnergyPrincipal s x
        = (1 / (2 * (Real.pi : ℂ))) * ∫ θ in Ioc (-Real.pi) Real.pi,
            ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
              - (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)))
              * heatMultiplier x θ := by
      rw [heatEnergy, ← heatEnergyPrincipal_eq h0 h1 hx, ← mul_sub]
      congr 1
      rw [← MeasureTheory.integral_sub (integrableOn_germSq_mul_heatMultiplier h0 h1 hx)
        (integrableOn_principalSq_mul_heatMultiplier h0 h1 hx)]
      refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
      ring
    have hsrc : IntegrableOn
        (fun θ : ℝ => ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
          - (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ))) * heatMultiplier x θ)
        (Ioc (-Real.pi) Real.pi) := by
      refine ((integrableOn_germSq_mul_heatMultiplier h0 h1 hx).sub
        (integrableOn_principalSq_mul_heatMultiplier h0 h1 hx)).congr ?_
      filter_upwards with θ
      simp only [Pi.sub_apply]
      ring
    have hmaj : IntegrableOn
        (fun θ : ℝ => K * (|θ| ^ s.re * heatMultiplierValue x θ)
          + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ)) (Ioc (-Real.pi) Real.pi) :=
      ((integrableOn_rpow_mul_heatMultiplierValue hx h0').const_mul K).add
        ((integrableOn_rpow_mul_heatMultiplierValue hx one_pos).const_mul K)
    have hptwise : (fun θ : ℝ => ‖((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
          - (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ))) * heatMultiplier x θ‖)
        ≤ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)]
          fun θ : ℝ => K * (|θ| ^ s.re * heatMultiplierValue x θ)
            + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
        MeasureTheory.ae_restrict_of_ae hne0] with θ hθ hne
      rw [norm_mul, norm_heatMultiplier hx]
      have hb := norm_germSq_sub_principalSq_le h0' h1 θ hθ hne
      have hvn : 0 ≤ heatMultiplierValue x θ := heatMultiplierValue_nonneg hx θ
      have hone : |θ| ^ (1 : ℝ) = |θ| := Real.rpow_one _
      calc ‖(phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
            - (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ))‖
            * heatMultiplierValue x θ
          ≤ (K * (|θ| ^ s.re + |θ|)) * heatMultiplierValue x θ :=
            mul_le_mul_of_nonneg_right hb hvn
        _ = K * (|θ| ^ s.re * heatMultiplierValue x θ)
              + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
            rw [hone]; ring
    have hstep : ‖∫ θ in Ioc (-Real.pi) Real.pi,
        ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))
          - (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ))) * heatMultiplier x θ‖
        ≤ ∫ θ in Ioc (-Real.pi) Real.pi, (K * (|θ| ^ s.re * heatMultiplierValue x θ)
            + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      exact MeasureTheory.setIntegral_mono_ae_restrict hsrc.norm hmaj hptwise
    have hval : (∫ θ in Ioc (-Real.pi) Real.pi, (K * (|θ| ^ s.re * heatMultiplierValue x θ)
        + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ)))
        = K * (2 * Real.pi) * (realHeatMoment x s.re + realHeatMoment x 1) := by
      rw [MeasureTheory.integral_add
        ((integrableOn_rpow_mul_heatMultiplierValue hx h0').const_mul K)
        ((integrableOn_rpow_mul_heatMultiplierValue hx one_pos).const_mul K),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, realHeatMoment,
        realHeatMoment]
      field_simp
    rw [hdiff, norm_mul]
    have hnorm : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
      norm_num
    rw [hnorm]
    have := mul_le_mul_of_nonneg_left (hstep.trans (le_of_eq hval))
      (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))
    refine this.trans (le_of_eq ?_)
    field_simp
  have hlim : Tendsto (fun x : ℝ => K * (realHeatMoment x s.re + realHeatMoment x 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1' := (tendsto_realHeatMoment h0').add (tendsto_realHeatMoment one_pos)
    rw [add_zero] at h1'
    have := h1'.const_mul K
    rw [mul_zero] at this
    exact this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hbound x hx

end RHTower
