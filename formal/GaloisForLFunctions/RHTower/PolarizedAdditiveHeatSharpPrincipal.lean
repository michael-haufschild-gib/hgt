import GaloisForLFunctions.RHTower.PolarizedAdditiveHeatSharpRemainder

/-!
# Exact principal decomposition on the sharp polarized strip

The four Jonquière principal channels are integrable under their natural conditions: both
individual orders have positive real part and their total real part exceeds one.  Separate
`L²` bounds are unnecessary.  This module upgrades the earlier half-strip formula to that sharp
domain and identifies the exact heat energy with its principal part plus the subtracted remainder.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Product of the two principal germs is integrable on the natural product strip. -/
theorem integrableOn_polarizedPrincipal_mul_heatMultiplier_of_sum_re_gt_one
    {s w : ℂ} (hs₀ : 0 < s.re) (hw₀ : 0 < w.re)
    (hsum : 1 < s.re + w.re) {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun θ : ℝ => (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
        heatMultiplier x θ) (Ioc (-Real.pi) Real.pi) := by
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

/-- Exact integration of all four principal channels on the natural product strip. -/
theorem polarizedHeatPrincipal_eq_of_sum_re_gt_one
    {s w : ℂ} (hs₀ : 0 < s.re) (hw₀ : 0 < w.re)
    (hsum : 1 < s.re + w.re) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ θ in Ioc (-Real.pi) Real.pi,
          (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
            heatMultiplier x θ) =
      polarizedHeatPrincipal s w x := by
  have h₀ : -1 < (s + (starRingEnd ℂ) w - 2).re := by
    norm_num [Complex.sub_re, Complex.add_re, Complex.conj_re]
    linarith
  have h₁ : -1 < (s - 1).re := by simp; linarith
  have h₂ : -1 < ((starRingEnd ℂ) w - 1).re := by simp; linarith
  have h₃ : -1 < (0 : ℂ).re := by simp
  set g₀ : ℝ → ℂ := fun θ => ((if 0 < θ
      then jonquiereLead s * (starRingEnd ℂ) (jonquiereLead w)
      else jonquiereLeadNeg s * (starRingEnd ℂ) (jonquiereLeadNeg w)) *
    ((|θ| : ℝ) : ℂ) ^ (s + (starRingEnd ℂ) w - 2)) * heatMultiplier x θ
  set g₁ : ℝ → ℂ := fun θ => ((if 0 < θ
      then jonquiereLead s * (starRingEnd ℂ) (riemannZeta w)
      else jonquiereLeadNeg s * (starRingEnd ℂ) (riemannZeta w)) *
    ((|θ| : ℝ) : ℂ) ^ (s - 1)) * heatMultiplier x θ
  set g₂ : ℝ → ℂ := fun θ => ((if 0 < θ
      then riemannZeta s * (starRingEnd ℂ) (jonquiereLead w)
      else riemannZeta s * (starRingEnd ℂ) (jonquiereLeadNeg w)) *
    ((|θ| : ℝ) : ℂ) ^ ((starRingEnd ℂ) w - 1)) * heatMultiplier x θ
  set g₃ : ℝ → ℂ := fun θ => ((if 0 < θ
      then riemannZeta s * (starRingEnd ℂ) (riemannZeta w)
      else riemannZeta s * (starRingEnd ℂ) (riemannZeta w)) *
    ((|θ| : ℝ) : ℂ) ^ (0 : ℂ)) * heatMultiplier x θ
  have hi₀ : IntegrableOn g₀ (Ioc (-Real.pi) Real.pi) :=
    integrableOn_halfSplit hx h₀ _ _
  have hi₁ : IntegrableOn g₁ (Ioc (-Real.pi) Real.pi) :=
    integrableOn_halfSplit hx h₁ _ _
  have hi₂ : IntegrableOn g₂ (Ioc (-Real.pi) Real.pi) :=
    integrableOn_halfSplit hx h₂ _ _
  have hi₃ : IntegrableOn g₃ (Ioc (-Real.pi) Real.pi) :=
    integrableOn_halfSplit hx h₃ _ _
  have hne₀ : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hpt : (fun θ : ℝ =>
      (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) * heatMultiplier x θ)
      =ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)]
        fun θ => g₀ θ + g₁ θ + g₂ θ + g₃ θ := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne₀] with θ hne
    rw [germPrincipal_mul_conj_two s w hne]
    simp only [g₀, g₁, g₂, g₃, ite_self]
    rw [add_mul, add_mul, add_mul]
  have hsumIntegral :
      (∫ θ in Ioc (-Real.pi) Real.pi, (g₀ θ + g₁ θ + g₂ θ + g₃ θ)) =
        (∫ θ in Ioc (-Real.pi) Real.pi, g₀ θ) +
        (∫ θ in Ioc (-Real.pi) Real.pi, g₁ θ) +
        (∫ θ in Ioc (-Real.pi) Real.pi, g₂ θ) +
        (∫ θ in Ioc (-Real.pi) Real.pi, g₃ θ) := by
    rw [MeasureTheory.integral_add (f := fun θ => g₀ θ + g₁ θ + g₂ θ) (g := g₃)
        ((hi₀.add hi₁).add hi₂) hi₃,
      MeasureTheory.integral_add (f := fun θ => g₀ θ + g₁ θ) (g := g₂)
        (hi₀.add hi₁) hi₂,
      MeasureTheory.integral_add (f := g₀) (g := g₁) hi₀ hi₁]
  rw [MeasureTheory.integral_congr_ae hpt, hsumIntegral]
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

/-- Exact sharp-strip decomposition: full heat energy equals four principal moments plus the
subtracted Jonquière remainder. -/
theorem polarizedHeatEnergy_eq_principal_add_sharpRemainder
    {s w : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1)
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1)
    (hsum : 1 < s.re + w.re) {x : ℝ} (hx : 0 < x) :
    polarizedHeatEnergy s w x =
      polarizedHeatPrincipal s w x + polarizedHeatSharpRemainder s w x := by
  have hp := integrableOn_polarizedPrincipal_mul_heatMultiplier_of_sum_re_gt_one
    hs₀ hw₀ hsum hx
  have hr := integrableOn_polarizedHeatSharpRemainderSource hs₀ hs₁ hw₀ hw₁ hx
  rw [polarizedHeatEnergy, polarizedHeatSharpRemainder]
  calc
    (1 / (2 * (Real.pi : ℂ))) *
          ∫ θ in Ioc (-Real.pi) Real.pi,
            (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) *
              heatMultiplier x θ =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ θ in Ioc (-Real.pi) Real.pi,
            ((germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
                heatMultiplier x θ +
              ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) -
                germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
                  heatMultiplier x θ) := by
            congr 1
            apply setIntegral_congr_fun measurableSet_Ioc
            intro θ hθ
            ring
    _ = (1 / (2 * (Real.pi : ℂ))) *
          (∫ θ in Ioc (-Real.pi) Real.pi,
            (germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
              heatMultiplier x θ) +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ θ in Ioc (-Real.pi) Real.pi,
            ((phaseGerm s θ * (starRingEnd ℂ) (phaseGerm w θ)) -
              germPrincipal s θ * (starRingEnd ℂ) (germPrincipal w θ)) *
                heatMultiplier x θ := by
          rw [MeasureTheory.integral_add hp hr]
          ring
    _ = _ := by
      rw [polarizedHeatPrincipal_eq_of_sum_re_gt_one hs₀ hw₀ hsum hx]

end

end RHTower
