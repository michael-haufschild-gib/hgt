import GaloisForLFunctions.RHTower.HeatEchoCompleted
import GaloisForLFunctions.RHTower.HeatDoubleSum
import GaloisForLFunctions.RHTower.PolarizedAdditiveHeatFinitePart

/-!
# Polarized additive-heat boundary expansion

This module proves the full two-parameter additive-heat aperture expansion on
the open zeta strip.  It establishes absolute convergence of the polarized
double series, identifies it with the Fourier heat pairing, proves finite
pre-limit positivity, evaluates all three nonconstant polyhomogeneous
channels with the card's closed coefficients, and shows that the finite part
is exactly `ζ(s) * conj (ζ(w))`.  Consequently every finite superposition has
finite-part energy equal to the squared norm of one zeta-value functional.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The full-window heat moment differs from its Gaussian main term by `o(1)` for
every locally integrable exponent. -/
theorem tendsto_heatMoment_sub_term_of_neg_one_lt_re {lam : ℂ} (hlam : -1 < lam.re) :
    Tendsto (fun x : ℝ => heatMoment x lam - heatMomentTerm x lam)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  set C₁ : ℝ := heatTailConst * (Real.pi ^ (lam.re + 1) / (lam.re + 1)) with hC₁
  set C₂ : ℝ := 1 / 2 * (8 * Real.pi) ^ ((lam.re + 1) / 2)
    * Real.Gamma ((lam.re + 1) / 2) with hC₂
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hp : (0 : ℝ) < Real.pi ^ (lam.re + 1) := Real.rpow_pos_of_pos hpi _
    exact mul_nonneg heatTailConst_nonneg (div_nonneg hp.le (by linarith))
  have hC₂nn : 0 ≤ C₂ := by
    rw [hC₂]
    have hg : 0 ≤ Real.Gamma ((lam.re + 1) / 2) :=
      Real.Gamma_nonneg_of_nonneg (by linarith)
    have hp : (0 : ℝ) < (8 * Real.pi) ^ ((lam.re + 1) / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hmaj : Tendsto (fun x : ℝ => (1 / Real.pi)
      * (C₁ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-((Real.pi / 4) / x)))
        + C₂ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-((Real.pi / 8) / x)))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h₁ := (tendsto_rpow_neg_half_mul_exp (a := Real.pi / 4) (by positivity)).const_mul C₁
    have h₂ := (tendsto_rpow_neg_half_mul_exp (a := Real.pi / 8) (by positivity)).const_mul C₂
    rw [mul_zero] at h₁ h₂
    have h := (h₁.add h₂).const_mul (1 / Real.pi)
    rw [add_zero, mul_zero] at h
    exact h
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx hx₁
  have hx₀ : (0 : ℝ) < x := hx
  have hxle : x ≤ 1 := hx₁.2.le
  refine (norm_heatMoment_sub_term_le hlam hx₀ hxle).trans ?_
  have hpow : (0 : ℝ) ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx₀.le _
  have harg₁ : Real.pi / (4 * x) = (Real.pi / 4) / x := by rw [div_div]
  have harg₂ : Real.pi / (8 * x) = (Real.pi / 8) / x := by rw [div_div]
  rw [harg₁, harg₂]
  have hscale : (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
      ≤ (8 * Real.pi) ^ ((lam.re + 1) / 2) := by
    have hb : (0 : ℝ) < 8 * Real.pi := by positivity
    have hsplit : (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
        = (8 * Real.pi) ^ ((lam.re + 1) / 2) * x ^ ((lam.re + 1) / 2) := by
      rw [Real.mul_rpow hb.le hx₀.le]
    rw [hsplit]
    have hxpow : x ^ ((lam.re + 1) / 2) ≤ 1 :=
      Real.rpow_le_one hx₀.le hxle (by linarith)
    nlinarith [Real.rpow_pos_of_pos hb ((lam.re + 1) / 2),
      Real.rpow_nonneg hx₀.le ((lam.re + 1) / 2)]
  have hg : 0 ≤ Real.Gamma ((lam.re + 1) / 2) :=
    Real.Gamma_nonneg_of_nonneg (by linarith)
  have hstep : x ^ (-(1 : ℝ) / 2)
      * (Real.exp (-(Real.pi / 4 / x)) * heatTailConst
            * (Real.pi ^ (lam.re + 1) / (lam.re + 1))
        + Real.exp (-(Real.pi / 8 / x))
            * (1 / 2 * (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
                * Real.Gamma ((lam.re + 1) / 2)))
      ≤ C₁ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(Real.pi / 4 / x)))
        + C₂ * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(Real.pi / 8 / x))) := by
    rw [hC₁, hC₂]
    have he₂ : (0 : ℝ) < Real.exp (-(Real.pi / 8 / x)) := Real.exp_pos _
    nlinarith [mul_nonneg hpow he₂.le,
      mul_nonneg (mul_nonneg hpow he₂.le) hg,
      mul_le_mul_of_nonneg_right hscale hg,
      mul_nonneg (mul_nonneg hpow he₂.le)
        (mul_nonneg hg (le_of_lt (Real.rpow_pos_of_pos
          (by positivity : (0 : ℝ) < 8 * Real.pi) ((lam.re + 1) / 2))))]
  exact mul_le_mul_of_nonneg_left hstep (by positivity)

/-! ## Polarized heat kernel and its exact principal part -/

/-- Polarized additive-heat aperture, oriented as
`phaseGerm s · conj (phaseGerm w)`. -/
noncomputable def polarizedHeatEnergy (s w : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ)))
    * ∫ θ in Ioc (-Real.pi) Real.pi,
        (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) * heatMultiplier x θ

/-- Averaged coefficient of the doubly singular polarized channel. -/
noncomputable def polarizedHeatLeadingCoefficient (s w : ℂ) : ℂ :=
  (jonquiereLead s * (starRingEnd ℂ) (jonquiereLead w)
      + jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereLeadNeg w)) / 2

/-- Exact four-moment principal part of the polarized heat aperture. -/
noncomputable def polarizedHeatPrincipal (s w : ℂ) (x : ℝ) : ℂ :=
  polarizedHeatLeadingCoefficient s w
      * heatMoment x (s + (starRingEnd ℂ) w - 2)
    + ((jonquiereLead s + jonquiereLeadNeg s) / 2
        * (starRingEnd ℂ) (riemannZeta w)) * heatMoment x (s - 1)
    + (riemannZeta s
        * (((starRingEnd ℂ) (jonquiereLead w)
          + (starRingEnd ℂ) (jonquiereLeadNeg w)) / 2))
        * heatMoment x ((starRingEnd ℂ) w - 1)
    + riemannZeta s * (starRingEnd ℂ) (riemannZeta w)

/-- Product of two principal Jonquière germs, expanded into its four
side-dependent power channels. -/
theorem germPrincipal_mul_conj_two (s w : ℂ) {θ : ℝ} (hne : θ ≠ 0) :
    germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)
      = (if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (jonquiereLead w)
            else jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereLeadNeg w))
          * ((|θ| : ℝ) : ℂ) ^ (s + (starRingEnd ℂ) w - 2)
        + (if 0 < θ then jonquiereLead s * (starRingEnd ℂ) (riemannZeta w)
            else jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta w))
          * ((|θ| : ℝ) : ℂ) ^ (s - 1)
        + (if 0 < θ then riemannZeta s * (starRingEnd ℂ) (jonquiereLead w)
            else riemannZeta s * (starRingEnd ℂ) (jonquiereLeadNeg w))
          * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) w - 1)
        + riemannZeta s * (starRingEnd ℂ) (riemannZeta w)
          * ((|θ| : ℝ) : ℂ) ^ (0 : ℂ) := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hbase : (((|θ| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hconj := conj_ofReal_cpow hpos (w - 1)
  have hcw : (starRingEnd ℂ) (w - 1) = (starRingEnd ℂ) w - 1 := by
    rw [map_sub, map_one]
  rw [hcw] at hconj
  have hmul : ((|θ| : ℝ) : ℂ) ^ (s - 1)
      * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) w - 1)
      = ((|θ| : ℝ) : ℂ) ^ (s + (starRingEnd ℂ) w - 2) := by
    calc
      ((|θ| : ℝ) : ℂ) ^ (s - 1)
            * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) w - 1) =
          ((|θ| : ℝ) : ℂ) ^ ((s - 1) + ((starRingEnd ℂ) w - 1)) :=
            (Complex.cpow_add _ _ hbase).symm
      _ = ((|θ| : ℝ) : ℂ) ^ (s + (starRingEnd ℂ) w - 2) := by
        congr 1
        ring
  rw [germPrincipal, germPrincipal, jonquiereLeadAt, map_add, map_mul,
    hconj, Complex.cpow_zero]
  by_cases h : 0 < θ
  · simp only [jonquiereLeadAt, if_pos h]
    rw [← hmul]
    ring
  · simp only [jonquiereLeadAt, if_neg h]
    rw [← hmul]
    ring

/-- Polarized germ integrand is integrable on the phase window. -/
theorem integrableOn_polarizedGerm_mul_heatMultiplier
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun θ : ℝ => (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))
        * heatMultiplier x θ) (Ioc (-Real.pi) Real.pi) := by
  have hs₀' : (0 : ℝ) < s.re := by linarith
  have hw₀' : (0 : ℝ) < w.re := by linarith
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-Real.pi)) (b := Real.pi)).exists_bound_of_continuousOn
    ((continuous_heatMultiplier hx).continuousOn)
  have hMnn : 0 ≤ M := by
    exact (norm_nonneg (heatMultiplier x 0)).trans
      (hM 0 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hsSq : Integrable (fun θ : ℝ => ‖phaseGerm s θ‖ ^ 2)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm
      (aestronglyMeasurable_phaseGerm hs₀' hs₁)).mp (memLp_phaseGerm hs₀ hs₁)
  have hwSq : Integrable (fun θ : ℝ => ‖phaseGerm w θ‖ ^ 2)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm
      (aestronglyMeasurable_phaseGerm hw₀' hw₁)).mp (memLp_phaseGerm hw₀ hw₁)
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))
        * heatMultiplier x θ) (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    exact ((aestronglyMeasurable_phaseGerm hs₀' hs₁).mul
      (aestronglyMeasurable_phaseGerm hw₀' hw₁).star).mul
      ((continuous_heatMultiplier hx).continuousOn.aestronglyMeasurable measurableSet_Ioc)
  refine Integrable.mono' ((hsSq.add hwSq).const_mul (M / 2)) hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  have hb := hM θ ⟨hθ.1.le, hθ.2⟩
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  have ha : 0 ≤ ‖phaseGerm s θ‖ := norm_nonneg _
  have hc : 0 ≤ ‖phaseGerm w θ‖ := norm_nonneg _
  calc
    ‖phaseGerm s θ‖ * ‖phaseGerm w θ‖ * ‖heatMultiplier x θ‖
        ≤ ‖phaseGerm s θ‖ * ‖phaseGerm w θ‖ * M :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg ha hc)
    _ ≤ M / 2 * (‖phaseGerm s θ‖ ^ 2 + ‖phaseGerm w θ‖ ^ 2) := by
      nlinarith [sq_nonneg (‖phaseGerm s θ‖ - ‖phaseGerm w θ‖)]

/-- Product of two principal germs is integrable against the heat multiplier. -/
theorem integrableOn_polarizedPrincipal_mul_heatMultiplier
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (_hw₁ : w.re < 1) {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun θ : ℝ => (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ))
        * heatMultiplier x θ) (Ioc (-Real.pi) Real.pi) := by
  have h₀ : -1 < (s + (starRingEnd ℂ) w - 2).re := by
    norm_num [Complex.sub_re, Complex.add_re, Complex.conj_re]
    linarith
  have h₁ : -1 < (s - 1).re := by simp; linarith
  have h₂ : -1 < ((starRingEnd ℂ) w - 1).re := by simp; linarith
  have h₃ : -1 < (0 : ℂ).re := by simp
  have hi₀ := integrableOn_halfSplit hx h₀
    (jonquiereLead s * (starRingEnd ℂ) (jonquiereLead w))
    (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereLeadNeg w))
  have hi₁ := integrableOn_halfSplit hx h₁
    (jonquiereLead s * (starRingEnd ℂ) (riemannZeta w))
    (jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta w))
  have hi₂ := integrableOn_halfSplit hx h₂
    (riemannZeta s * (starRingEnd ℂ) (jonquiereLead w))
    (riemannZeta s * (starRingEnd ℂ) (jonquiereLeadNeg w))
  have hi₃ := integrableOn_halfSplit hx h₃
    (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))
    (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))
  have hne₀ : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  refine (((hi₀.add hi₁).add hi₂).add hi₃).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_of_ae hne₀] with θ hne
  simp only [Pi.add_apply]
  rw [germPrincipal_mul_conj_two s w hne]
  simp only [ite_self]
  rw [add_mul, add_mul, add_mul]

/-- Exact integration of the polarized principal germ. -/
theorem polarizedHeatPrincipal_eq
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (_hw₁ : w.re < 1) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * (Real.pi : ℂ)))
      * (∫ θ in Ioc (-Real.pi) Real.pi,
          (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ))
            * heatMultiplier x θ)
      = polarizedHeatPrincipal s w x := by
  have h₀ : -1 < (s + (starRingEnd ℂ) w - 2).re := by
    norm_num [Complex.sub_re, Complex.add_re, Complex.conj_re]
    linarith
  have h₁ : -1 < (s - 1).re := by simp; linarith
  have h₂ : -1 < ((starRingEnd ℂ) w - 1).re := by simp; linarith
  have h₃ : -1 < (0 : ℂ).re := by simp
  set g₀ : ℝ → ℂ := fun θ => ((if 0 < θ
      then jonquiereLead s * (starRingEnd ℂ) (jonquiereLead w)
      else jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereLeadNeg w))
    * ((|θ| : ℝ) : ℂ) ^ (s + (starRingEnd ℂ) w - 2)) * heatMultiplier x θ
  set g₁ : ℝ → ℂ := fun θ => ((if 0 < θ
      then jonquiereLead s * (starRingEnd ℂ) (riemannZeta w)
      else jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta w))
    * ((|θ| : ℝ) : ℂ) ^ (s - 1)) * heatMultiplier x θ
  set g₂ : ℝ → ℂ := fun θ => ((if 0 < θ
      then riemannZeta s * (starRingEnd ℂ) (jonquiereLead w)
      else riemannZeta s * (starRingEnd ℂ) (jonquiereLeadNeg w))
    * ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) w - 1)) * heatMultiplier x θ
  set g₃ : ℝ → ℂ := fun θ => ((if 0 < θ
      then riemannZeta s * (starRingEnd ℂ) (riemannZeta w)
      else riemannZeta s * (starRingEnd ℂ) (riemannZeta w))
    * ((|θ| : ℝ) : ℂ) ^ (0 : ℂ)) * heatMultiplier x θ
  have hi₀ : IntegrableOn g₀ (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx h₀ _ _
  have hi₁ : IntegrableOn g₁ (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx h₁ _ _
  have hi₂ : IntegrableOn g₂ (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx h₂ _ _
  have hi₃ : IntegrableOn g₃ (Ioc (-Real.pi) Real.pi) := integrableOn_halfSplit hx h₃ _ _
  have hne₀ : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hpt : (fun θ : ℝ =>
      (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) * heatMultiplier x θ)
      =ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)] fun θ => g₀ θ + g₁ θ + g₂ θ + g₃ θ := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne₀] with θ hne
    rw [germPrincipal_mul_conj_two s w hne]
    simp only [g₀, g₁, g₂, g₃, ite_self]
    rw [add_mul, add_mul, add_mul]
  have hsum : (∫ θ in Ioc (-Real.pi) Real.pi, (g₀ θ + g₁ θ + g₂ θ + g₃ θ))
      = (∫ θ in Ioc (-Real.pi) Real.pi, g₀ θ)
        + (∫ θ in Ioc (-Real.pi) Real.pi, g₁ θ)
        + (∫ θ in Ioc (-Real.pi) Real.pi, g₂ θ)
        + (∫ θ in Ioc (-Real.pi) Real.pi, g₃ θ) := by
    rw [MeasureTheory.integral_add (f := fun θ => g₀ θ + g₁ θ + g₂ θ) (g := g₃)
        ((hi₀.add hi₁).add hi₂) hi₃,
      MeasureTheory.integral_add (f := fun θ => g₀ θ + g₁ θ) (g := g₂)
        (hi₀.add hi₁) hi₂,
      MeasureTheory.integral_add (f := g₀) (g := g₁) hi₀ hi₁]
  rw [MeasureTheory.integral_congr_ae hpt, hsum]
  have e₀ := heatMoment_halfSplit hx h₀
    (jonquiereLead s * (starRingEnd ℂ) (jonquiereLead w))
    (jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereLeadNeg w))
  have e₁ := heatMoment_halfSplit hx h₁
    (jonquiereLead s * (starRingEnd ℂ) (riemannZeta w))
    (jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta w))
  have e₂ := heatMoment_halfSplit hx h₂
    (riemannZeta s * (starRingEnd ℂ) (jonquiereLead w))
    (riemannZeta s * (starRingEnd ℂ) (jonquiereLeadNeg w))
  have e₃ := heatMoment_halfSplit hx h₃
    (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))
    (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))
  rw [heatMoment_zero hx] at e₃
  rw [polarizedHeatPrincipal, polarizedHeatLeadingCoefficient]
  rw [mul_add, mul_add, mul_add, e₀, e₁, e₂, e₃]
  ring

/-! ## Polarized error estimate -/

/-- Constant controlling the cross error between the exact polarized germ and
the product of its two principal parts. -/
noncomputable def polarizedHeatErrorConst (s w : ℂ) : ℝ :=
  jonquiereConst s
      * (‖jonquiereLead w‖ + ‖jonquiereLeadNeg w‖ + ‖riemannZeta w‖
          + jonquiereConst w * Real.pi)
    + (‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖)
      * jonquiereConst w

theorem polarizedHeatErrorConst_nonneg (s w : ℂ) :
    0 ≤ polarizedHeatErrorConst s w := by
  rw [polarizedHeatErrorConst]
  have hs := jonquiereConst_nonneg s
  have hw := jonquiereConst_nonneg w
  have hpi := Real.pi_pos
  positivity

/-- The polarized germ product differs from the product of its principal
parts by `O(|θ|^Re(s)+|θ|^Re(w)+|θ|)`. -/
theorem norm_polarizedGerm_sub_principal_le
    {s w : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    ∀ θ ∈ Ioc (-Real.pi) Real.pi, θ ≠ 0 →
      ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)
          - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)‖
        ≤ polarizedHeatErrorConst s w
          * (|θ| ^ s.re + |θ| ^ w.re + |θ|) := by
  intro θ hθ hne
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hds := norm_phaseGerm_sub_principal_le hs₀ hs₁ θ hθ hne
  have hdw := norm_phaseGerm_sub_principal_le hw₀ hw₁ θ hθ hne
  have hgw := norm_phaseGerm_le hw₀ hw₁ θ hθ hne
  have hps := norm_germPrincipal_le (s := s) θ hne
  have hid : phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)
      - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)
      = (phaseGerm s θ - germPrincipal s θ)
          * (starRingEnd ℂ) (phaseGerm w θ)
        + germPrincipal s θ
          * (starRingEnd ℂ) (phaseGerm w θ - germPrincipal w θ) := by
    rw [map_sub]
    ring
  have hnorm : ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)
      - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)‖
      ≤ ‖phaseGerm s θ - germPrincipal s θ‖ * ‖phaseGerm w θ‖
        + ‖germPrincipal s θ‖ * ‖phaseGerm w θ - germPrincipal w θ‖ := by
    rw [hid]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  set A : ℝ := jonquiereConst s with hA
  set B : ℝ := ‖jonquiereLead w‖ + ‖jonquiereLeadNeg w‖ + ‖riemannZeta w‖
    + jonquiereConst w * Real.pi with hB
  set C : ℝ := ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖ with hC
  set D : ℝ := jonquiereConst w with hD
  have hAnn : 0 ≤ A := by rw [hA]; exact jonquiereConst_nonneg s
  have hBnn : 0 ≤ B := by
    rw [hB]
    have := jonquiereConst_nonneg w
    have := Real.pi_pos
    positivity
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hDnn : 0 ≤ D := by rw [hD]; exact jonquiereConst_nonneg w
  have hrS : |θ| * |θ| ^ (s.re - 1) = |θ| ^ s.re := by
    nth_rewrite 1 [← Real.rpow_one |θ|]
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  have hrW : |θ| * |θ| ^ (w.re - 1) = |θ| ^ w.re := by
    nth_rewrite 1 [← Real.rpow_one |θ|]
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  have hrS' : |θ| ^ (s.re - 1) * |θ| = |θ| ^ s.re := by
    rw [mul_comm, hrS]
  have hfirst :
      ‖phaseGerm s θ - germPrincipal s θ‖ * ‖phaseGerm w θ‖
        ≤ (A * B) * (|θ| ^ w.re + |θ|) := by
    calc
      ‖phaseGerm s θ - germPrincipal s θ‖ * ‖phaseGerm w θ‖
          ≤ (A * |θ|) * (B * (|θ| ^ (w.re - 1) + 1)) := by
            refine mul_le_mul ?_ ?_ (norm_nonneg _) ?_
            · simpa [hA] using hds
            · simpa [hB] using hgw
            · exact mul_nonneg hAnn (abs_nonneg θ)
      _ = (A * B) * (|θ| ^ w.re + |θ|) := by rw [mul_add, mul_one, ← hrW]; ring
  have hsecond :
      ‖germPrincipal s θ‖ * ‖phaseGerm w θ - germPrincipal w θ‖
        ≤ (C * D) * (|θ| ^ s.re + |θ|) := by
    calc
      ‖germPrincipal s θ‖ * ‖phaseGerm w θ - germPrincipal w θ‖
          ≤ (C * (|θ| ^ (s.re - 1) + 1)) * (D * |θ|) := by
            refine mul_le_mul ?_ ?_ (norm_nonneg _) ?_
            · simpa [hC] using hps
            · simpa [hD] using hdw
            · exact mul_nonneg hCnn
                (add_nonneg (Real.rpow_nonneg (abs_nonneg θ) _) zero_le_one)
      _ = (C * D) * (|θ| ^ (s.re - 1) * |θ| + |θ|) := by ring
      _ = (C * D) * (|θ| ^ s.re + |θ|) := by rw [hrS']
  calc
    ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)
        - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)‖
        ≤ ‖phaseGerm s θ - germPrincipal s θ‖ * ‖phaseGerm w θ‖
          + ‖germPrincipal s θ‖ * ‖phaseGerm w θ - germPrincipal w θ‖ := hnorm
    _ ≤ (A * B) * (|θ| ^ w.re + |θ|)
          + (C * D) * (|θ| ^ s.re + |θ|) := add_le_add hfirst hsecond
    _ ≤ (A * B + C * D) * (|θ| ^ s.re + |θ| ^ w.re + |θ|) := by
      have hsnn := Real.rpow_nonneg (abs_nonneg θ) s.re
      have hwnn := Real.rpow_nonneg (abs_nonneg θ) w.re
      have hθnn := abs_nonneg θ
      nlinarith [mul_nonneg (mul_nonneg hAnn hBnn) hsnn,
        mul_nonneg (mul_nonneg hCnn hDnn) hwnn]
    _ = polarizedHeatErrorConst s w
          * (|θ| ^ s.re + |θ| ^ w.re + |θ|) := by
      rw [polarizedHeatErrorConst, ← hA, ← hB, ← hC, ← hD]

/-- Polarized heat energy agrees with its exact four-moment principal part up
to `o(1)` at the aperture boundary. -/
theorem tendsto_polarizedHeatEnergy_sub_principal
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) :
    Tendsto (fun x : ℝ => polarizedHeatEnergy s w x - polarizedHeatPrincipal s w x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hs₀' : (0 : ℝ) < s.re := by linarith
  have hw₀' : (0 : ℝ) < w.re := by linarith
  set K : ℝ := polarizedHeatErrorConst s w with hK
  have hKnn : 0 ≤ K := by rw [hK]; exact polarizedHeatErrorConst_nonneg s w
  have hne₀ : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hbound : ∀ x : ℝ, 0 < x →
      ‖polarizedHeatEnergy s w x - polarizedHeatPrincipal s w x‖
        ≤ K * (realHeatMoment x s.re + realHeatMoment x w.re + realHeatMoment x 1) := by
    intro x hx
    have hdiff : polarizedHeatEnergy s w x - polarizedHeatPrincipal s w x
        = (1 / (2 * (Real.pi : ℂ))) * ∫ θ in Ioc (-Real.pi) Real.pi,
            ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))
              - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ))
              * heatMultiplier x θ := by
      rw [polarizedHeatEnergy, ← polarizedHeatPrincipal_eq hs₀ hs₁ hw₀ hw₁ hx,
        ← mul_sub]
      congr 1
      rw [← MeasureTheory.integral_sub
        (integrableOn_polarizedGerm_mul_heatMultiplier hs₀ hs₁ hw₀ hw₁ hx)
        (integrableOn_polarizedPrincipal_mul_heatMultiplier hs₀ hs₁ hw₀ hw₁ hx)]
      refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
      ring
    have hsrc : IntegrableOn
        (fun θ : ℝ => ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))
          - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ))
          * heatMultiplier x θ) (Ioc (-Real.pi) Real.pi) := by
      refine ((integrableOn_polarizedGerm_mul_heatMultiplier hs₀ hs₁ hw₀ hw₁ hx).sub
        (integrableOn_polarizedPrincipal_mul_heatMultiplier hs₀ hs₁ hw₀ hw₁ hx)).congr ?_
      filter_upwards with θ
      simp only [Pi.sub_apply]
      ring
    have hmaj : IntegrableOn
        (fun θ : ℝ => K * (|θ| ^ s.re * heatMultiplierValue x θ)
          + K * (|θ| ^ w.re * heatMultiplierValue x θ)
          + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ))
          (Ioc (-Real.pi) Real.pi) :=
      (((integrableOn_rpow_mul_heatMultiplierValue hx hs₀').const_mul K).add
        ((integrableOn_rpow_mul_heatMultiplierValue hx hw₀').const_mul K)).add
        ((integrableOn_rpow_mul_heatMultiplierValue hx one_pos).const_mul K)
    have hptwise : (fun θ : ℝ => ‖((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))
          - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ))
          * heatMultiplier x θ‖)
        ≤ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)]
          fun θ : ℝ => K * (|θ| ^ s.re * heatMultiplierValue x θ)
            + K * (|θ| ^ w.re * heatMultiplierValue x θ)
            + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
        MeasureTheory.ae_restrict_of_ae hne₀] with θ hθ hne
      rw [norm_mul, norm_heatMultiplier hx]
      have hb := norm_polarizedGerm_sub_principal_le hs₀' hs₁ hw₀' hw₁ θ hθ hne
      have hvn : 0 ≤ heatMultiplierValue x θ := heatMultiplierValue_nonneg hx θ
      have hone : |θ| ^ (1 : ℝ) = |θ| := Real.rpow_one _
      calc
        ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)
            - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)‖
              * heatMultiplierValue x θ
            ≤ (K * (|θ| ^ s.re + |θ| ^ w.re + |θ|))
                * heatMultiplierValue x θ := mul_le_mul_of_nonneg_right (by simpa [hK] using hb) hvn
        _ = K * (|θ| ^ s.re * heatMultiplierValue x θ)
              + K * (|θ| ^ w.re * heatMultiplierValue x θ)
              + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
            rw [hone]
            ring
    have hstep : ‖∫ θ in Ioc (-Real.pi) Real.pi,
        ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))
          - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ))
          * heatMultiplier x θ‖
        ≤ ∫ θ in Ioc (-Real.pi) Real.pi,
          (K * (|θ| ^ s.re * heatMultiplierValue x θ)
            + K * (|θ| ^ w.re * heatMultiplierValue x θ)
            + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      exact MeasureTheory.setIntegral_mono_ae_restrict hsrc.norm hmaj hptwise
    have hval : (∫ θ in Ioc (-Real.pi) Real.pi,
          (K * (|θ| ^ s.re * heatMultiplierValue x θ)
            + K * (|θ| ^ w.re * heatMultiplierValue x θ)
            + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ)))
        = K * (2 * Real.pi)
          * (realHeatMoment x s.re + realHeatMoment x w.re + realHeatMoment x 1) := by
      calc
        (∫ θ in Ioc (-Real.pi) Real.pi,
            (K * (|θ| ^ s.re * heatMultiplierValue x θ)
              + K * (|θ| ^ w.re * heatMultiplierValue x θ))
              + K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ)) =
            (∫ θ in Ioc (-Real.pi) Real.pi,
              (K * (|θ| ^ s.re * heatMultiplierValue x θ)
                + K * (|θ| ^ w.re * heatMultiplierValue x θ)))
              + ∫ θ in Ioc (-Real.pi) Real.pi,
                K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) :=
              MeasureTheory.integral_add
                (((integrableOn_rpow_mul_heatMultiplierValue hx hs₀').const_mul K).add
                  ((integrableOn_rpow_mul_heatMultiplierValue hx hw₀').const_mul K))
                ((integrableOn_rpow_mul_heatMultiplierValue hx one_pos).const_mul K)
        _ = ((∫ θ in Ioc (-Real.pi) Real.pi,
                K * (|θ| ^ s.re * heatMultiplierValue x θ))
              + ∫ θ in Ioc (-Real.pi) Real.pi,
                K * (|θ| ^ w.re * heatMultiplierValue x θ))
              + ∫ θ in Ioc (-Real.pi) Real.pi,
                K * (|θ| ^ (1 : ℝ) * heatMultiplierValue x θ) := by
              rw [MeasureTheory.integral_add
                ((integrableOn_rpow_mul_heatMultiplierValue hx hs₀').const_mul K)
                ((integrableOn_rpow_mul_heatMultiplierValue hx hw₀').const_mul K)]
        _ = K * (2 * Real.pi)
              * (realHeatMoment x s.re + realHeatMoment x w.re + realHeatMoment x 1) := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
                MeasureTheory.integral_const_mul, realHeatMoment, realHeatMoment, realHeatMoment]
              field_simp
    rw [hdiff, norm_mul]
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
      (fun x : ℝ => K * (realHeatMoment x s.re + realHeatMoment x w.re + realHeatMoment x 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hsum := ((tendsto_realHeatMoment hs₀').add (tendsto_realHeatMoment hw₀')).add
      (tendsto_realHeatMoment one_pos)
    rw [zero_add, zero_add] at hsum
    have h := hsum.const_mul K
    rw [mul_zero] at h
    exact h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hbound x hx

/-! ## Gaussian and polyhomogeneous normal forms -/

/-- Conjugation commutes with the Gaussian heat-moment main term at positive aperture. -/
theorem conj_heatMomentTerm {x : ℝ} (hx : 0 < x) (lam : ℂ) :
    (starRingEnd ℂ) (heatMomentTerm x lam) =
      heatMomentTerm x ((starRingEnd ℂ) lam) := by
  have hbase : (0 : ℝ) < 4 * Real.pi * x := by positivity
  rw [heatMomentTerm, heatMomentTerm, map_div₀, map_mul,
    conj_ofReal_cpow hbase, ← Complex.Gamma_conj]
  simp only [map_add, map_one, map_div₀, map_ofNat, Complex.conj_ofReal]

/-- One-sided averaged Jonquière coefficient times its Gaussian moment is
the diagonal echo coefficient times the corresponding aperture power. -/
theorem averagedLead_mul_heatMomentTerm
    {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ((jonquiereLead s + jonquiereLeadNeg s) / 2) * heatMomentTerm x (s - 1)
      = heatEchoC s * ((x : ℝ) : ℂ) ^ ((s - 1) / 2) := by
  rw [heatMomentTerm_split hx, jonquiereLead_avg, heatEchoC]
  ring

/-- Conjugate version of the averaged echo coefficient identity. -/
theorem averagedConjLead_mul_heatMomentTerm
    {w : ℂ} {x : ℝ} (hx : 0 < x) :
    (((starRingEnd ℂ) (jonquiereLead w)
        + (starRingEnd ℂ) (jonquiereLeadNeg w)) / 2)
        * heatMomentTerm x ((starRingEnd ℂ) w - 1)
      = (starRingEnd ℂ) (heatEchoC w)
          * ((x : ℝ) : ℂ) ^ (((starRingEnd ℂ) w - 1) / 2) := by
  have h := congrArg (starRingEnd ℂ) (averagedLead_mul_heatMomentTerm (s := w) hx)
  simpa only [map_mul, map_div₀, map_add, map_ofNat, conj_heatMomentTerm hx,
    map_sub, map_one, conj_ofReal_cpow hx] using h

/-- Explicit coefficient of the doubly singular polarized Gaussian channel,
before the harmless square-root normalization is rewritten. -/
noncomputable def polarizedHeatL (s w : ℂ) : ℂ :=
  polarizedHeatLeadingCoefficient s w
    * ((((4 * Real.pi : ℝ)) : ℂ) ^ ((s + (starRingEnd ℂ) w - 2) / 2)
      * Complex.Gamma ((s + (starRingEnd ℂ) w - 1) / 2)
      / ((Real.sqrt Real.pi : ℝ) : ℂ))

/-- Gaussian four-term model before powers of `x` are split off. -/
noncomputable def polarizedHeatGaussianPrincipal (s w : ℂ) (x : ℝ) : ℂ :=
  polarizedHeatLeadingCoefficient s w
      * heatMomentTerm x (s + (starRingEnd ℂ) w - 2)
    + ((jonquiereLead s + jonquiereLeadNeg s) / 2
        * (starRingEnd ℂ) (riemannZeta w)) * heatMomentTerm x (s - 1)
    + (riemannZeta s
        * (((starRingEnd ℂ) (jonquiereLead w)
          + (starRingEnd ℂ) (jonquiereLeadNeg w)) / 2))
        * heatMomentTerm x ((starRingEnd ℂ) w - 1)
    + riemannZeta s * (starRingEnd ℂ) (riemannZeta w)

/-- Card's four-term polyhomogeneous expansion, with constant term displayed. -/
noncomputable def polarizedHeatPolyhomogeneous (s w : ℂ) (x : ℝ) : ℂ :=
  polarizedHeatL s w
      * ((x : ℝ) : ℂ) ^ ((s + (starRingEnd ℂ) w - 2) / 2)
    + (heatEchoC s * (starRingEnd ℂ) (riemannZeta w))
      * ((x : ℝ) : ℂ) ^ ((s - 1) / 2)
    + (riemannZeta s * (starRingEnd ℂ) (heatEchoC w))
      * ((x : ℝ) : ℂ) ^ (((starRingEnd ℂ) w - 1) / 2)
    + riemannZeta s * (starRingEnd ℂ) (riemannZeta w)

theorem polarizedHeatGaussianPrincipal_eq_polyhomogeneous
    {s w : ℂ} {x : ℝ} (hx : 0 < x) :
    polarizedHeatGaussianPrincipal s w x = polarizedHeatPolyhomogeneous s w x := by
  have hlead := heatMomentTerm_split hx (s + (starRingEnd ℂ) w - 2)
  have hs := averagedLead_mul_heatMomentTerm (s := s) hx
  have hw := averagedConjLead_mul_heatMomentTerm (w := w) hx
  rw [polarizedHeatGaussianPrincipal, polarizedHeatPolyhomogeneous, polarizedHeatL,
    hlead]
  rw [show (s + (starRingEnd ℂ) w - 2 + 1) / 2 =
      (s + (starRingEnd ℂ) w - 1) / 2 by ring]
  rw [show ((jonquiereLead s + jonquiereLeadNeg s) / 2
        * (starRingEnd ℂ) (riemannZeta w)) * heatMomentTerm x (s - 1) =
      (((jonquiereLead s + jonquiereLeadNeg s) / 2) * heatMomentTerm x (s - 1))
        * (starRingEnd ℂ) (riemannZeta w) by ring,
    hs]
  rw [show (riemannZeta s
        * (((starRingEnd ℂ) (jonquiereLead w)
          + (starRingEnd ℂ) (jonquiereLeadNeg w)) / 2))
        * heatMomentTerm x ((starRingEnd ℂ) w - 1) =
      riemannZeta s *
        ((((starRingEnd ℂ) (jonquiereLead w)
          + (starRingEnd ℂ) (jonquiereLeadNeg w)) / 2)
        * heatMomentTerm x ((starRingEnd ℂ) w - 1)) by ring,
    hw]
  ring

/-- Replacing exact full-window moments by Gaussian moments changes the
polarized principal part by `o(1)`. -/
theorem tendsto_polarizedHeatPrincipal_sub_gaussian
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hw₀ : 1 / 2 < w.re) :
    Tendsto (fun x : ℝ => polarizedHeatPrincipal s w x
        - polarizedHeatGaussianPrincipal s w x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h₀re : -1 < (s + (starRingEnd ℂ) w - 2).re := by
    norm_num [Complex.sub_re, Complex.add_re, Complex.conj_re]
    linarith
  have h₁re : -1 < (s - 1).re := by simp; linarith
  have h₂re : -1 < ((starRingEnd ℂ) w - 1).re := by simp; linarith
  have h₀ := (tendsto_heatMoment_sub_term_of_neg_one_lt_re h₀re).const_mul
    (polarizedHeatLeadingCoefficient s w)
  have h₁ := (tendsto_heatMoment_sub_term_of_neg_one_lt_re h₁re).const_mul
    ((jonquiereLead s + jonquiereLeadNeg s) / 2
      * (starRingEnd ℂ) (riemannZeta w))
  have h₂ := (tendsto_heatMoment_sub_term_of_neg_one_lt_re h₂re).const_mul
    (riemannZeta s * (((starRingEnd ℂ) (jonquiereLead w)
      + (starRingEnd ℂ) (jonquiereLeadNeg w)) / 2))
  rw [mul_zero] at h₀ h₁ h₂
  have h := (h₀.add h₁).add h₂
  rw [zero_add, zero_add] at h
  refine h.congr fun x => ?_
  rw [polarizedHeatPrincipal, polarizedHeatGaussianPrincipal]
  ring

/-- Full constant-order two-parameter expansion of the polarized additive
heat aperture. -/
theorem tendsto_polarizedHeatEnergy_sub_polyhomogeneous
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) :
    Tendsto (fun x : ℝ => polarizedHeatEnergy s w x
        - polarizedHeatPolyhomogeneous s w x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h₀ := tendsto_polarizedHeatEnergy_sub_principal hs₀ hs₁ hw₀ hw₁
  have h₁ := tendsto_polarizedHeatPrincipal_sub_gaussian hs₀ hw₀
  have h := h₀.add h₁
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [polarizedHeatGaussianPrincipal_eq_polyhomogeneous hx]
  ring

/-- The three nonconstant polyhomogeneous channels. -/
noncomputable def polarizedHeatSingularPart (s w : ℂ) (x : ℝ) : ℂ :=
  polarizedHeatPolyhomogeneous s w x
    - riemannZeta s * (starRingEnd ℂ) (riemannZeta w)

/-- The polarized finite part is exactly the rank-one zeta-value kernel. -/
theorem tendsto_polarizedHeatFinitePart
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) :
    Tendsto (fun x : ℝ => polarizedHeatEnergy s w x
        - polarizedHeatSingularPart s w x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))) := by
  have h := (tendsto_polarizedHeatEnergy_sub_polyhomogeneous
    hs₀ hs₁ hw₀ hw₁).add_const
      (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))
  rw [zero_add] at h
  refine h.congr fun x => ?_
  rw [polarizedHeatSingularPart]
  ring

/-- Closed-form echo coefficient appearing in the two cross channels. -/
theorem polarizedHeatCrossCoefficient_eq
    {s : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1) :
    heatEchoC s =
      1 / 2 * ((Real.pi : ℝ) : ℂ) ^ ((s - 1) / 2)
        * Complex.Gamma ((1 - s) / 2) :=
  heatEchoC_eq_completed (by linarith) (by linarith)

/-- Principal complex half-power of `4π`. -/
theorem four_pi_cpow_half_eq_two_sqrt_pi :
    ((((4 * Real.pi : ℝ)) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) =
      2 * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < 4 * Real.pi := by positivity
  have hcpow : ((Real.sqrt (4 * Real.pi) : ℝ) : ℂ) =
      (((4 * Real.pi : ℝ)) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_cpow hpos.le]
  have hsqrt : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
      have hnn := Real.sqrt_nonneg (4 : ℝ)
      nlinarith
    rw [h4]
  rw [← hcpow, hsqrt]
  push_cast
  ring

/-- Doubly singular coefficient in the exact closed form displayed on the card. -/
noncomputable def polarizedHeatLClosed (s w : ℂ) : ℂ :=
  ((((4 * Real.pi : ℝ)) : ℂ) ^ ((s + (starRingEnd ℂ) w - 3) / 2))
    * Complex.Gamma ((s + (starRingEnd ℂ) w - 1) / 2)
    * ((starRingEnd ℂ) (jonquiereLead w) * jonquiereLead s
      + (starRingEnd ℂ) (jonquiereLeadNeg w) * jonquiereLeadNeg s)

/-- The internally convenient leading coefficient equals the card's closed
`(4π)^((s+conj(w)-3)/2)Γ((s+conj(w)-1)/2)` formula. -/
theorem polarizedHeatL_eq_closed (s w : ℂ) :
    polarizedHeatL s w = polarizedHeatLClosed s w := by
  have hbase : ((((4 * Real.pi : ℝ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hsqrt : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpow : ((((4 * Real.pi : ℝ)) : ℂ) ^
        ((s + (starRingEnd ℂ) w - 2) / 2)) =
      ((((4 * Real.pi : ℝ)) : ℂ) ^
          ((s + (starRingEnd ℂ) w - 3) / 2))
        * (2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
    calc
      ((((4 * Real.pi : ℝ)) : ℂ) ^
          ((s + (starRingEnd ℂ) w - 2) / 2)) =
          ((((4 * Real.pi : ℝ)) : ℂ) ^
            (((s + (starRingEnd ℂ) w - 3) / 2) + ((1 / 2 : ℝ) : ℂ))) := by
              congr 1
              norm_num
              ring
      _ = ((((4 * Real.pi : ℝ)) : ℂ) ^
            ((s + (starRingEnd ℂ) w - 3) / 2))
          * ((((4 * Real.pi : ℝ)) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) :=
            Complex.cpow_add ((s + (starRingEnd ℂ) w - 3) / 2)
              (((1 / 2 : ℝ) : ℂ)) hbase
      _ = ((((4 * Real.pi : ℝ)) : ℂ) ^
            ((s + (starRingEnd ℂ) w - 3) / 2))
          * (2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
            rw [four_pi_cpow_half_eq_two_sqrt_pi]
  rw [polarizedHeatL, polarizedHeatLClosed, polarizedHeatLeadingCoefficient, hpow]
  field_simp

/-- Card's closed subleading coefficient
`C(s)=½π^((s-1)/2)Γ((1-s)/2)`. -/
noncomputable def polarizedHeatCClosed (s : ℂ) : ℂ :=
  1 / 2 * ((Real.pi : ℝ) : ℂ) ^ ((s - 1) / 2)
    * Complex.Gamma ((1 - s) / 2)

/-- Literal closed-form version of equation (6) on the card. -/
noncomputable def polarizedHeatPolyhomogeneousClosed (s w : ℂ) (x : ℝ) : ℂ :=
  polarizedHeatLClosed s w
      * ((x : ℝ) : ℂ) ^ ((s + (starRingEnd ℂ) w - 2) / 2)
    + (polarizedHeatCClosed s * (starRingEnd ℂ) (riemannZeta w))
      * ((x : ℝ) : ℂ) ^ ((s - 1) / 2)
    + (riemannZeta s * (starRingEnd ℂ) (polarizedHeatCClosed w))
      * ((x : ℝ) : ℂ) ^ (((starRingEnd ℂ) w - 1) / 2)
    + riemannZeta s * (starRingEnd ℂ) (riemannZeta w)

theorem polarizedHeatPolyhomogeneous_eq_closed
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) (x : ℝ) :
    polarizedHeatPolyhomogeneous s w x =
      polarizedHeatPolyhomogeneousClosed s w x := by
  have hs := polarizedHeatCrossCoefficient_eq hs₀ hs₁
  have hw := polarizedHeatCrossCoefficient_eq hw₀ hw₁
  rw [polarizedHeatPolyhomogeneous, polarizedHeatPolyhomogeneousClosed,
    polarizedHeatL_eq_closed, hs, hw]
  simp only [polarizedHeatCClosed]

/-- Full two-parameter expansion with exactly the card's displayed `L` and
`C` coefficients. -/
theorem tendsto_polarizedHeatEnergy_sub_polyhomogeneousClosed
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) :
    Tendsto (fun x : ℝ => polarizedHeatEnergy s w x
        - polarizedHeatPolyhomogeneousClosed s w x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  refine (tendsto_polarizedHeatEnergy_sub_polyhomogeneous
    hs₀ hs₁ hw₀ hw₁).congr fun x => ?_
  rw [polarizedHeatPolyhomogeneous_eq_closed hs₀ hs₁ hw₀ hw₁]

/-- Literal closed-form nonconstant part of the polarized expansion. -/
noncomputable def polarizedHeatSingularPartClosed (s w : ℂ) (x : ℝ) : ℂ :=
  polarizedHeatPolyhomogeneousClosed s w x
    - riemannZeta s * (starRingEnd ℂ) (riemannZeta w)

/-- Finite-part limit after subtracting the card's literal three singular channels. -/
theorem tendsto_polarizedHeatFinitePartClosed
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) :
    Tendsto (fun x : ℝ => polarizedHeatEnergy s w x
        - polarizedHeatSingularPartClosed s w x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))) := by
  have h := (tendsto_polarizedHeatEnergy_sub_polyhomogeneousClosed
    hs₀ hs₁ hw₀ hw₁).add_const
      (riemannZeta s * (starRingEnd ℂ) (riemannZeta w))
  rw [zero_add] at h
  refine h.congr fun x => ?_
  rw [polarizedHeatSingularPartClosed]
  ring

/-! ## Closed strip-valued capstones -/

/-- Parameter space of the open zeta strip used by the heat aperture. -/
abbrev AdditiveHeatStrip : Type :=
  {s : ℂ // 1 / 2 < s.re ∧ s.re < 1}

namespace AdditiveHeatStrip

instance : Coe AdditiveHeatStrip ℂ := ⟨Subtype.val⟩

theorem lower (s : AdditiveHeatStrip) : 1 / 2 < (s : ℂ).re := s.property.1

theorem upper (s : AdditiveHeatStrip) : (s : ℂ).re < 1 := s.property.2

end AdditiveHeatStrip

/-- Premise-free strip-valued form of the polarized finite-part theorem. -/
theorem polarizedHeatFinitePart_rankOneKernel (s w : AdditiveHeatStrip) :
    Tendsto (fun x : ℝ => polarizedHeatEnergy (s : ℂ) (w : ℂ) x
        - polarizedHeatSingularPartClosed (s : ℂ) (w : ℂ) x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (riemannZeta (s : ℂ) * (starRingEnd ℂ) (riemannZeta (w : ℂ)))) :=
  tendsto_polarizedHeatFinitePartClosed s.lower s.upper w.lower w.upper

/-- Premise-free strip-valued full closed-form expansion. -/
theorem polarizedHeatBoundaryExpansion (s w : AdditiveHeatStrip) :
    Tendsto (fun x : ℝ => polarizedHeatEnergy (s : ℂ) (w : ℂ) x
        - polarizedHeatPolyhomogeneousClosed (s : ℂ) (w : ℂ) x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  tendsto_polarizedHeatEnergy_sub_polyhomogeneousClosed
    s.lower s.upper w.lower w.upper

/-- Every finite polarized heat superposition has finite part equal to the
squared norm of the single zeta-value functional. -/
theorem tendsto_finite_polarizedHeatFinitePart_rankOne
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (s : ι → AdditiveHeatStrip) :
    Tendsto (fun x : ℝ => ∑ i ∈ S, ∑ j ∈ S,
        (starRingEnd ℂ) (c i) * c j
          * (polarizedHeatEnergy (s j : ℂ) (s i : ℂ) x
            - polarizedHeatSingularPartClosed (s j : ℂ) (s i : ℂ) x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((‖∑ i ∈ S, c i * riemannZeta (s i : ℂ)‖ ^ 2 : ℝ) : ℂ))) := by
  have h : Tendsto (fun x : ℝ => ∑ i ∈ S, ∑ j ∈ S,
      (starRingEnd ℂ) (c i) * c j
        * (polarizedHeatEnergy (s j : ℂ) (s i : ℂ) x
          - polarizedHeatSingularPartClosed (s j : ℂ) (s i : ℂ) x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑ i ∈ S, ∑ j ∈ S,
        (starRingEnd ℂ) (c i) * c j * riemannZeta (s j : ℂ)
          * (starRingEnd ℂ) (riemannZeta (s i : ℂ)))) := by
    apply tendsto_finsetSum S
    intro i hi
    apply tendsto_finsetSum S
    intro j hj
    have hij := polarizedHeatFinitePart_rankOneKernel (s j) (s i)
    have hmul := hij.const_mul ((starRingEnd ℂ) (c i) * c j)
    simpa only [mul_assoc] using hmul
  have hgram := GaloisForLFunctions.RHTower.finite_riemannZeta_value_rankOne_gram
    S c (fun i => (s i : ℂ))
  have hgram' : (∑ i ∈ S, ∑ j ∈ S,
      (starRingEnd ℂ) (c i) * c j * riemannZeta (s j : ℂ)
        * (starRingEnd ℂ) (riemannZeta (s i : ℂ))) =
      ((‖∑ i ∈ S, c i * riemannZeta (s i : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    simpa using hgram
  rw [hgram'] at h
  exact h

/-! ## Absolutely convergent polarized double series -/

/-- Polarized additive-heat pair term. -/
noncomputable def polarizedHeatPairTerm (s w : ℂ) (x : ℝ) (p : ℕ × ℕ) : ℂ :=
  (((p.1 : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
    * (starRingEnd ℂ) ((((p.2 : ℝ) + 1 : ℝ) : ℂ) ^ (-w))
    * ((heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ)) : ℝ) : ℂ)

theorem norm_polarizedHeatPairTerm (s w : ℂ) (x : ℝ) (p : ℕ × ℕ) :
    ‖polarizedHeatPairTerm s w x p‖ =
      ((p.1 : ℝ) + 1) ^ (-s.re) * ((p.2 : ℝ) + 1) ^ (-w.re)
        * heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ)) := by
  rw [polarizedHeatPairTerm, norm_mul, norm_mul, RCLike.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (p.1 : ℝ) + 1),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (p.2 : ℝ) + 1),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (heatCoeff_pos x _),
    Complex.neg_re, Complex.neg_re]

theorem norm_polarizedHeatPairTerm_le (s w : ℂ) (x : ℝ) (p : ℕ × ℕ) :
    ‖polarizedHeatPairTerm s w x p‖ ≤
      (heatLeftMajorant s x p + heatRightMajorant w x p) / 2 := by
  have h₁ : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
  have h₂ : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
  have hsq₁ : (((p.1 : ℝ) + 1) ^ (-s.re)) ^ 2 =
      ((p.1 : ℝ) + 1) ^ (-2 * s.re) := by
    rw [← Real.rpow_natCast (((p.1 : ℝ) + 1) ^ (-s.re)) 2, ← Real.rpow_mul h₁.le]
    congr 1
    push_cast
    ring
  have hsq₂ : (((p.2 : ℝ) + 1) ^ (-w.re)) ^ 2 =
      ((p.2 : ℝ) + 1) ^ (-2 * w.re) := by
    rw [← Real.rpow_natCast (((p.2 : ℝ) + 1) ^ (-w.re)) 2, ← Real.rpow_mul h₂.le]
    congr 1
    push_cast
    ring
  rw [norm_polarizedHeatPairTerm, heatLeftMajorant, heatRightMajorant, ← hsq₁, ← hsq₂]
  have hc := (heatCoeff_pos x ((p.1 : ℤ) - (p.2 : ℤ))).le
  nlinarith [sq_nonneg (((p.1 : ℝ) + 1) ^ (-s.re) - ((p.2 : ℝ) + 1) ^ (-w.re)), hc]

/-- Absolute convergence of the polarized additive-heat double series. -/
theorem summable_polarizedHeatPairTerm
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hw₀ : 1 / 2 < w.re)
    {x : ℝ} (hx : 0 < x) :
    Summable (polarizedHeatPairTerm s w x) := by
  refine Summable.of_norm_bounded ?_ (norm_polarizedHeatPairTerm_le s w x)
  exact (((summable_heatLeftMajorant hs₀ hx).add
    (summable_heatRightMajorant hw₀ hx)).div_const 2)

/-- Absolutely convergent polarized double sum, equation (1). -/
noncomputable def polarizedHeatDoubleSum (s w : ℂ) (x : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ, polarizedHeatPairTerm s w x p

theorem tendsto_polarizedSquareSum
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hw₀ : 1 / 2 < w.re)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      polarizedHeatPairTerm s w x p) atTop
      (nhds (polarizedHeatDoubleSum s w x)) := by
  refine (summable_polarizedHeatPairTerm hs₀ hw₀ hx).hasSum.comp
    (tendsto_atTop_finset_of_monotone ?_ ?_)
  · intro a b hab
    have hr : Finset.range a ⊆ Finset.range b := Finset.range_subset_range.mpr hab
    exact Finset.product_subset_product hr hr
  · intro p
    refine ⟨max p.1 p.2 + 1, ?_⟩
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩

theorem sum_polarizedHeatPairTerm_eq (s w : ℂ) (x : ℝ) (N : ℕ) :
    (∑ p ∈ Finset.range N ×ˢ Finset.range N, polarizedHeatPairTerm s w x p) =
      ∑ n ∈ modeSet N, ∑ m ∈ modeSet N,
        ((((n : ℝ) : ℂ) ^ (-s))
          * (starRingEnd ℂ) (((m : ℝ) : ℂ) ^ (-w)))
          * ((heatCoeff x (n - m) : ℝ) : ℂ) := by
  rw [Finset.sum_product, sum_modeSet]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_modeSet]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb₁ : ((((i : ℤ) + 1 : ℤ) : ℝ) : ℂ) = (((i : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have hb₂ : ((((j : ℤ) + 1 : ℤ) : ℝ) : ℂ) = (((j : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have hk : ((i : ℤ) + 1) - ((j : ℤ) + 1) = (i : ℤ) - (j : ℤ) := by ring
  rw [hb₁, hb₂, hk, polarizedHeatPairTerm]

/-- Cross version of the finite heat quadratic-form identity. -/
theorem integral_heatMultiplier_mul_trigPoly_cross
    {x : ℝ} (hx : 0 < x) (T : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
      heatMultiplier x θ * ((∑ n ∈ T, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))
        * (starRingEnd ℂ) (∑ m ∈ T, b m * Complex.exp (I * (m : ℂ) * (θ : ℂ))))) =
      2 * Real.pi * ∑ n ∈ T, ∑ m ∈ T,
        a n * (starRingEnd ℂ) (b m) * ((heatCoeff x (n - m) : ℝ) : ℂ) := by
  have hexpand : ∀ θ : ℝ,
      heatMultiplier x θ * ((∑ n ∈ T, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))
        * (starRingEnd ℂ) (∑ m ∈ T, b m * Complex.exp (I * (m : ℂ) * (θ : ℂ)))) =
      ∑ n ∈ T, ∑ m ∈ T, (a n * (starRingEnd ℂ) (b m))
        * (heatMultiplier x θ * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ))) := by
    intro θ
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, conj_exp_I_mul_real]
    have hmul : Complex.exp (I * (n : ℂ) * (θ : ℂ))
        * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ)) =
      Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      heatMultiplier x θ
          * (a n * Complex.exp (I * (n : ℂ) * (θ : ℂ))
            * ((starRingEnd ℂ) (b m)
              * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ)))) =
          (a n * (starRingEnd ℂ) (b m))
            * (heatMultiplier x θ
              * (Complex.exp (I * (n : ℂ) * (θ : ℂ))
                * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ)))) := by ring
      _ = (a n * (starRingEnd ℂ) (b m))
            * (heatMultiplier x θ
              * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ))) := by
          rw [hmul]
  rw [setIntegral_congr_fun measurableSet_Ioc fun θ _ => hexpand θ,
    MeasureTheory.integral_finsetSum _ (fun n _ => MeasureTheory.integrable_finsetSum _
      fun m _ => ((integrableOn_heatMultiplier_mul_exp hx (n - m)).const_mul _)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun m _ =>
    ((integrableOn_heatMultiplier_mul_exp hx (n - m)).const_mul _)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_heatMultiplier_mul_exp hx]
  ring

/-- Truncated polarized integral equals truncated polarized double sum. -/
theorem polarizedHeatQuadratic_trunc_eq
    {s w : ℂ} {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ θ in Ioc (-Real.pi) Real.pi,
      heatMultiplier x θ *
        (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc w N θ)) =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, polarizedHeatPairTerm s w x p := by
  have hq := integral_heatMultiplier_mul_trigPoly_cross hx (modeSet N)
    (fun n : ℤ => (((n : ℝ)) : ℂ) ^ (-s))
    (fun n : ℤ => (((n : ℝ)) : ℂ) ^ (-w))
  simp only [dirichletTrunc] at hq ⊢
  rw [hq, ← sum_polarizedHeatPairTerm_eq]
  field_simp

/-- Polarized heat pairing passes to the two independent `L²` boundary limits. -/
theorem tendsto_polarizedHeatIntegral_trunc
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => ∫ θ in Ioc (-Real.pi) Real.pi,
      heatMultiplier x θ
        * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc w N θ)))
      atTop (nhds (∫ θ in Ioc (-Real.pi) Real.pi,
        heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)))) := by
  have hs₀' : (0 : ℝ) < s.re := by linarith
  have hw₀' : (0 : ℝ) < w.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-Real.pi)) (b := Real.pi)).exists_bound_of_continuousOn
    ((continuous_heatMultiplier hx).continuousOn)
  have hM₀ : (0 : ℝ) ≤ M :=
    le_trans (norm_nonneg _) (hM 0 ⟨by linarith, hpi.le⟩)
  set As : ℝ := Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2) with hAs
  set Bw : ℝ := Real.sqrt
    (2 * Real.pi * ∑' i : ℕ, ((i : ℝ) + 1) ^ (-2 * w.re)) with hBw
  set epsS : ℕ → ℝ := fun N => Real.sqrt
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)
    with hepsS
  set epsW : ℕ → ℝ := fun N => Real.sqrt
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm w θ - dirichletTrunc w N θ‖ ^ 2)
    with hepsW
  have hAs₀ : 0 ≤ As := Real.sqrt_nonneg _
  have hBw₀ : 0 ≤ Bw := Real.sqrt_nonneg _
  have hepsSlim : Tendsto epsS atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_integral_germ_sub_trunc hs₀ hs₁)
    rw [Real.sqrt_zero] at h
    exact h
  have hepsWlim : Tendsto epsW atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_integral_germ_sub_trunc hw₀ hw₁)
    rw [Real.sqrt_zero] at h
    exact h
  have hkey : ∀ N : ℕ,
      ‖(∫ θ in Ioc (-Real.pi) Real.pi,
          heatMultiplier x θ
            * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc w N θ)))
        - (∫ θ in Ioc (-Real.pi) Real.pi,
          heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)))‖
        ≤ M * (epsS N * Bw + As * epsW N) := by
    intro N
    set us : ℝ → ℂ := fun θ => phaseGerm s θ - dirichletTrunc s N θ with hus
    set uw : ℝ → ℂ := fun θ => phaseGerm w θ - dirichletTrunc w N θ with huw
    have hmemus : MemLp us 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      memLp_germ_sub_trunc hs₀ hs₁ N
    have hmemuw : MemLp uw 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      memLp_germ_sub_trunc hw₀ hw₁ N
    have hmemtw : MemLp (dirichletTrunc w N) 2
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := memLp_dirichletTrunc w N
    have hmemgs : MemLp (phaseGerm s) 2
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := memLp_phaseGerm hs₀ hs₁
    have hint₁ : IntegrableOn (fun θ : ℝ => heatMultiplier x θ
        * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc w N θ)))
        (Ioc (-Real.pi) Real.pi) := by
      refine ((continuous_heatMultiplier hx).mul
        ((continuous_dirichletTrunc s N).mul
          (Complex.continuous_conj.comp (continuous_dirichletTrunc w N)))).integrableOn_Ioc
    have hint₂ : IntegrableOn (fun θ : ℝ => heatMultiplier x θ
        * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)))
        (Ioc (-Real.pi) Real.pi) := by
      refine (integrableOn_polarizedGerm_mul_heatMultiplier
        hs₀ hs₁ hw₀ hw₁ hx).congr ?_
      filter_upwards with θ
      ring
    rw [← MeasureTheory.integral_sub hint₁ hint₂]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hptw : ∀ θ ∈ Ioc (-Real.pi) Real.pi,
        ‖heatMultiplier x θ
            * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc w N θ))
          - heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))‖
        ≤ M * (‖us θ‖ * ‖dirichletTrunc w N θ‖)
          + M * (‖phaseGerm s θ‖ * ‖uw θ‖) := by
      intro θ hθ
      have hmem : θ ∈ Icc (-Real.pi) Real.pi := ⟨hθ.1.le, hθ.2⟩
      have hid : dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc w N θ)
          - phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ) =
        (-us θ) * (starRingEnd ℂ) (dirichletTrunc w N θ)
          + phaseGerm s θ * (starRingEnd ℂ) (-uw θ) := by
        rw [hus, huw]
        simp only [map_sub, map_neg]
        ring
      rw [← mul_sub, hid, norm_mul]
      have hb := hM θ hmem
      have hinner : ‖(-us θ) * (starRingEnd ℂ) (dirichletTrunc w N θ)
          + phaseGerm s θ * (starRingEnd ℂ) (-uw θ)‖ ≤
          ‖us θ‖ * ‖dirichletTrunc w N θ‖ + ‖phaseGerm s θ‖ * ‖uw θ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, norm_neg, norm_neg]
      calc
        ‖heatMultiplier x θ‖ * ‖(-us θ) * (starRingEnd ℂ) (dirichletTrunc w N θ)
            + phaseGerm s θ * (starRingEnd ℂ) (-uw θ)‖ ≤
            M * (‖us θ‖ * ‖dirichletTrunc w N θ‖
              + ‖phaseGerm s θ‖ * ‖uw θ‖) :=
          mul_le_mul hb hinner (norm_nonneg _) hM₀
        _ = M * (‖us θ‖ * ‖dirichletTrunc w N θ‖)
            + M * (‖phaseGerm s θ‖ * ‖uw θ‖) := by ring
    have hmajint : IntegrableOn (fun θ : ℝ =>
        M * (‖us θ‖ * ‖dirichletTrunc w N θ‖)
          + M * (‖phaseGerm s θ‖ * ‖uw θ‖)) (Ioc (-Real.pi) Real.pi) :=
      ((integrable_norm_mul hmemus hmemtw).const_mul M).add
        ((integrable_norm_mul hmemgs hmemuw).const_mul M)
    have hmono := MeasureTheory.setIntegral_mono_on (hint₁.sub hint₂).norm hmajint
      measurableSet_Ioc hptw
    refine hmono.trans ?_
    rw [MeasureTheory.integral_add ((integrable_norm_mul hmemus hmemtw).const_mul M)
      ((integrable_norm_mul hmemgs hmemuw).const_mul M),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hcs₁ := integral_norm_mul_le_sqrt hmemus hmemtw
    have hcs₂ := integral_norm_mul_le_sqrt hmemgs hmemuw
    have htw : Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖dirichletTrunc w N θ‖ ^ 2)
        ≤ Bw := by
      rw [hBw]
      exact Real.sqrt_le_sqrt (integral_dirichletTrunc_normSq_le hw₀ N)
    have hepsSN : epsS N = Real.sqrt
        (∫ θ in Ioc (-Real.pi) Real.pi, ‖us θ‖ ^ 2) := by rw [hepsS, hus]
    have hepsWN : epsW N = Real.sqrt
        (∫ θ in Ioc (-Real.pi) Real.pi, ‖uw θ‖ ^ 2) := by rw [hepsW, huw]
    have h₁ : (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖us θ‖ * ‖dirichletTrunc w N θ‖) ≤ epsS N * Bw := by
      rw [hepsSN]
      exact hcs₁.trans (mul_le_mul_of_nonneg_left htw (Real.sqrt_nonneg _))
    have h₂ : (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖phaseGerm s θ‖ * ‖uw θ‖) ≤ As * epsW N := by
      rw [hAs, hepsWN]
      exact hcs₂
    nlinarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmaj : Tendsto (fun N : ℕ => M * (epsS N * Bw + As * epsW N))
      atTop (nhds 0) := by
    have h₁ := hepsSlim.mul_const Bw
    have h₂ := hepsWlim.const_mul As
    rw [zero_mul] at h₁
    rw [mul_zero] at h₂
    have h := (h₁.add h₂).const_mul M
    rw [zero_add, mul_zero] at h
    exact h
  exact squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _)
    (Filter.Eventually.of_forall hkey) hmaj

/-- Polarized Fourier aperture equals its absolutely convergent double series. -/
theorem polarizedHeatEnergy_eq_doubleSum
    {s w : ℂ} (hs₀ : 1 / 2 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 1 / 2 < w.re) (hw₁ : w.re < 1) {x : ℝ} (hx : 0 < x) :
    polarizedHeatEnergy s w x = polarizedHeatDoubleSum s w x := by
  have hlim := (tendsto_polarizedHeatIntegral_trunc
    hs₀ hs₁ hw₀ hw₁ hx).const_mul (1 / (2 * (Real.pi : ℂ)))
  have hcomm : (∫ θ in Ioc (-Real.pi) Real.pi,
      heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ))) =
      ∫ θ in Ioc (-Real.pi) Real.pi,
        (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) * heatMultiplier x θ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    ring
  rw [hcomm] at hlim
  have hlim' : Tendsto (fun N : ℕ => ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      polarizedHeatPairTerm s w x p) atTop (nhds (polarizedHeatEnergy s w x)) := by
    refine hlim.congr fun N => polarizedHeatQuadratic_trunc_eq hx N
  exact tendsto_nhds_unique hlim' (tendsto_polarizedSquareSum hs₀ hw₀ hx)

/-- Premise-free strip-valued double-series representation. -/
theorem polarizedHeatEnergy_eq_doubleSum_closed
    (s w : AdditiveHeatStrip) {x : ℝ} (hx : 0 < x) :
    polarizedHeatEnergy (s : ℂ) (w : ℂ) x =
      polarizedHeatDoubleSum (s : ℂ) (w : ℂ) x :=
  polarizedHeatEnergy_eq_doubleSum s.lower s.upper w.lower w.upper hx

/-! ## Positivity before finite-part extraction -/

/-- Finite polarized heat energy in the natural source/conjugate-source order. -/
noncomputable def finitePolarizedHeatEnergy
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (s : ι → AdditiveHeatStrip) (x : ℝ) : ℂ :=
  ∑ j ∈ S, ∑ i ∈ S, c j * (starRingEnd ℂ) (c i)
    * polarizedHeatEnergy (s j : ℂ) (s i : ℂ) x

/-- Finite polarized kernel is exactly the heat integral of the squared norm
of the finite phase superposition. -/
theorem finitePolarizedHeatEnergy_eq_integral_normSq
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (s : ι → AdditiveHeatStrip)
    {x : ℝ} (hx : 0 < x) :
    finitePolarizedHeatEnergy S c s x =
      (1 / (2 * (Real.pi : ℂ))) * ∫ θ in Ioc (-Real.pi) Real.pi,
        ((∑ j ∈ S, c j * phaseGerm (s j : ℂ) θ)
          * (starRingEnd ℂ) (∑ i ∈ S, c i * phaseGerm (s i : ℂ) θ))
          * heatMultiplier x θ := by
  classical
  have hexpand : ∀ θ : ℝ,
      ((∑ j ∈ S, c j * phaseGerm (s j : ℂ) θ)
        * (starRingEnd ℂ) (∑ i ∈ S, c i * phaseGerm (s i : ℂ) θ))
        * heatMultiplier x θ =
      ∑ j ∈ S, ∑ i ∈ S,
        (c j * (starRingEnd ℂ) (c i))
          * ((phaseGerm (s j : ℂ) θ
            * (starRingEnd ℂ) (phaseGerm (s i : ℂ) θ))
            * heatMultiplier x θ) := by
    intro θ
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc fun θ _ => hexpand θ,
    MeasureTheory.integral_finsetSum _ (fun j _ => MeasureTheory.integrable_finsetSum _
      fun i _ => ((integrableOn_polarizedGerm_mul_heatMultiplier
        (s j).lower (s j).upper (s i).lower (s i).upper hx).const_mul _)),
    Finset.mul_sum]
  rw [finitePolarizedHeatEnergy]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
    ((integrableOn_polarizedGerm_mul_heatMultiplier
      (s j).lower (s j).upper (s i).lower (s i).upper hx).const_mul _)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul, polarizedHeatEnergy]
  ring

/-- Pre-limit polarized additive-heat energy is nonnegative for every finite
superposition and every positive aperture. -/
theorem finitePolarizedHeatEnergy_re_nonneg
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (s : ι → AdditiveHeatStrip)
    {x : ℝ} (hx : 0 < x) :
    0 ≤ (finitePolarizedHeatEnergy S c s x).re := by
  classical
  rw [finitePolarizedHeatEnergy_eq_integral_normSq S c s hx]
  let F : ℝ → ℂ := fun θ => ∑ j ∈ S, c j * phaseGerm (s j : ℂ) θ
  have hcongr : (∫ θ in Ioc (-Real.pi) Real.pi,
      ((∑ j ∈ S, c j * phaseGerm (s j : ℂ) θ)
        * (starRingEnd ℂ) (∑ i ∈ S, c i * phaseGerm (s i : ℂ) θ))
        * heatMultiplier x θ) =
      (((∫ θ in Ioc (-Real.pi) Real.pi,
        ‖F θ‖ ^ 2 * heatMultiplierValue x θ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [heatMultiplier_eq_value hx]
    change (F θ * (starRingEnd ℂ) (F θ))
        * ((heatMultiplierValue x θ : ℝ) : ℂ) =
      (((‖F θ‖ ^ 2 * heatMultiplierValue x θ : ℝ)) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
  rw [hcongr]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnorm : (1 / (2 * (Real.pi : ℂ))) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hnorm, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (by positivity) (integral_nonneg fun θ =>
    mul_nonneg (sq_nonneg ‖F θ‖) (heatMultiplierValue_nonneg hx θ))

end RHTower
