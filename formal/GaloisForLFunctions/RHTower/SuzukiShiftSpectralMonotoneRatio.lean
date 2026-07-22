import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio
import GaloisForLFunctions.RHTower.SuzukiCarlemanStieltjesFlux

/-!
# Monotone spectral-ratio criterion for Suzuki's shift-variable source jet

The normalized Euler--Gamma triangle jet is a quotient of two cross-resolvent matrix elements.
Its negative-Stieltjes orientation is not supplied by ordinary Donoghue positivity.  This module
isolates a source-pure sufficient condition: both cross spectral measures share a positive base
measure and their response ratio is monotone in the restricted-Weil spectral value.

The squared resolvent reweights that base measure toward lower spectral values.  Existing
monotone-likelihood integration then makes the exact quotient-rule numerator nonpositive.  This
is the real-axis shadow of the paper anti-Pick identity; it replaces an infinite list of opaque
shift-derivative sign tests by one two-sample spectral-order condition.

No RH assumption, Xi-divisor input, estimate, or numerical computation occurs here.
-/

open MeasureTheory

namespace RHTower

noncomputable section

variable {α : Type*}

/-- Resolvent weight in the real form-shift variable. -/
def suzukiShiftResolventKernel (node : α → ℝ) (lambda : ℝ) (x : α) : ℝ :=
  1 / (node x - lambda)

/-- Exact two-sample identity: replacing one resolvent weight by its square produces the spectral
increment divided by a positive squared denominator. -/
theorem suzukiShiftResolventKernel_sq_cross_eq
    {node : α → ℝ} {lambda : ℝ} {x y : α} :
    suzukiShiftResolventKernel node lambda x ^ 2 *
          suzukiShiftResolventKernel node lambda y -
        suzukiShiftResolventKernel node lambda y ^ 2 *
          suzukiShiftResolventKernel node lambda x =
      (node y - node x) /
        ((node x - lambda) ^ 2 * (node y - lambda) ^ 2) := by
  simp only [suzukiShiftResolventKernel]
  field_simp
  ring

variable [MeasurableSpace α] {μ : Measure α}

/-- **Monotone spectral-ratio cross-Wronskian law.**  If source response and spectral node
monovary under a common positive base measure, then the squared-resolvent cross-Wronskian has the
negative sign required by Suzuki's shift-variable negative-Stieltjes conjecture. -/
theorem suzukiShiftSpectralMonotoneRatio_crossWronskian_nonpos
    [SFinite μ] {node response : α → ℝ} {lambda : ℝ}
    (hres : Integrable (suzukiShiftResolventKernel node lambda) μ)
    (hresSq : Integrable (fun x => suzukiShiftResolventKernel node lambda x ^ 2) μ)
    (hresponseRes : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x) μ)
    (hresponseResSq : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x ^ 2) μ)
    (hpair : ∀ᵐ z : α × α ∂μ.prod μ,
      lambda < node z.1 ∧ lambda < node z.2 ∧
        0 ≤ (response z.2 - response z.1) * (node z.2 - node z.1)) :
    (∫ x, response x * suzukiShiftResolventKernel node lambda x ^ 2 ∂μ) *
        (∫ x, suzukiShiftResolventKernel node lambda x ∂μ) ≤
      (∫ x, response x * suzukiShiftResolventKernel node lambda x ∂μ) *
        (∫ x, suzukiShiftResolventKernel node lambda x ^ 2 ∂μ) := by
  apply HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
    hres hresSq hresponseRes hresponseResSq
  filter_upwards [hpair] with z hz
  rw [suzukiShiftResolventKernel_sq_cross_eq]
  rw [← mul_div_assoc]
  exact div_nonneg hz.2.2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Quotient-rule form of the monotone spectral-ratio law.  The displayed expression is exactly
`(N' D - N D') / D²` for the source quotient `q=N/D`. -/
theorem suzukiShiftSpectralMonotoneRatio_derivativeNumerator_nonpos
    [SFinite μ] {node response : α → ℝ} {lambda : ℝ}
    (hres : Integrable (suzukiShiftResolventKernel node lambda) μ)
    (hresSq : Integrable (fun x => suzukiShiftResolventKernel node lambda x ^ 2) μ)
    (hresponseRes : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x) μ)
    (hresponseResSq : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x ^ 2) μ)
    (hpair : ∀ᵐ z : α × α ∂μ.prod μ,
      lambda < node z.1 ∧ lambda < node z.2 ∧
        0 ≤ (response z.2 - response z.1) * (node z.2 - node z.1)) :
    ((∫ x, response x * suzukiShiftResolventKernel node lambda x ^ 2 ∂μ) *
          (∫ x, suzukiShiftResolventKernel node lambda x ∂μ) -
        (∫ x, response x * suzukiShiftResolventKernel node lambda x ∂μ) *
          (∫ x, suzukiShiftResolventKernel node lambda x ^ 2 ∂μ)) /
        (∫ x, suzukiShiftResolventKernel node lambda x ∂μ) ^ 2 ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · exact sub_nonpos.mpr <|
      suzukiShiftSpectralMonotoneRatio_crossWronskian_nonpos
        hres hresSq hresponseRes hresponseResSq hpair
  · exact sq_nonneg _

end

end RHTower
