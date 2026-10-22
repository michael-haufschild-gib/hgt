import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanStieltjesFlux
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAntiPickIdentity
import Mathlib.Analysis.Calculus.ParametricIntegral

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
    suzukiShiftResolventKernel node lambda x ^ (2 : ℕ) *
          suzukiShiftResolventKernel node lambda y -
        suzukiShiftResolventKernel node lambda y ^ (2 : ℕ) *
          suzukiShiftResolventKernel node lambda x =
      (node y - node x) /
        ((node x - lambda) ^ (2 : ℕ) * (node y - lambda) ^ (2 : ℕ)) := by
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
    (hresSq : Integrable (fun x => suzukiShiftResolventKernel node lambda x ^ (2 : ℕ)) μ)
    (hresponseRes : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x) μ)
    (hresponseResSq : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x ^ (2 : ℕ)) μ)
    (hpair : ∀ᵐ z : α × α ∂μ.prod μ,
      lambda < node z.1 ∧ lambda < node z.2 ∧
        0 ≤ (response z.2 - response z.1) * (node z.2 - node z.1)) :
    (∫ x, response x * suzukiShiftResolventKernel node lambda x ^ (2 : ℕ) ∂μ) *
        (∫ x, suzukiShiftResolventKernel node lambda x ∂μ) ≤
      (∫ x, response x * suzukiShiftResolventKernel node lambda x ∂μ) *
        (∫ x, suzukiShiftResolventKernel node lambda x ^ (2 : ℕ) ∂μ) := by
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
    (hresSq : Integrable (fun x => suzukiShiftResolventKernel node lambda x ^ (2 : ℕ)) μ)
    (hresponseRes : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x) μ)
    (hresponseResSq : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lambda x ^ (2 : ℕ)) μ)
    (hpair : ∀ᵐ z : α × α ∂μ.prod μ,
      lambda < node z.1 ∧ lambda < node z.2 ∧
        0 ≤ (response z.2 - response z.1) * (node z.2 - node z.1)) :
    ((∫ x, response x * suzukiShiftResolventKernel node lambda x ^ (2 : ℕ) ∂μ) *
          (∫ x, suzukiShiftResolventKernel node lambda x ∂μ) -
        (∫ x, response x * suzukiShiftResolventKernel node lambda x ∂μ) *
          (∫ x, suzukiShiftResolventKernel node lambda x ^ (2 : ℕ) ∂μ)) /
        (∫ x, suzukiShiftResolventKernel node lambda x ∂μ) ^ (2 : ℕ) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · exact sub_nonpos.mpr <|
      suzukiShiftSpectralMonotoneRatio_crossWronskian_nonpos
        hres hresSq hresponseRes hresponseResSq hpair
  · exact sq_nonneg _

/-! ## The displayed expression is the derivative

The cross-Wronskian law signs an expression built from four integrals.  That it is the *derivative*
of the quotient is a separate fact, and it is what turns the sign into monotonicity: the kernel's
derivative in the shift variable is its own square, so differentiating under the integral turns each
matrix element into its squared-kernel counterpart, and the quotient rule assembles them. -/

omit [MeasurableSpace α] in
/-- The kernel's derivative in the shift variable is its own square. -/
theorem hasDerivAt_suzukiShiftResolventKernel {node : α → ℝ} {lam : ℝ} {x : α}
    (h : node x - lam ≠ 0) :
    HasDerivAt (fun l => suzukiShiftResolventKernel node l x)
      (suzukiShiftResolventKernel node lam x ^ (2 : ℕ)) lam := by
  simpa [suzukiShiftResolventKernel, div_pow] using hasDerivAt_cauchyTermReal 1 (node x) lam h

/-- **Differentiation under the integral.**  Under the standard domination hypotheses a weighted
matrix element is differentiable in the shift variable, with the squared kernel as derivative. -/
theorem hasDerivAt_integral_weighted_suzukiShiftResolventKernel
    {node g : α → ℝ} {lam : ℝ} {s : Set ℝ} {bound : α → ℝ}
    (hs : s ∈ nhds lam)
    (hF_meas : ∀ᶠ l in nhds lam,
      AEStronglyMeasurable (fun x => g x * suzukiShiftResolventKernel node l x) μ)
    (hF_int : Integrable (fun x => g x * suzukiShiftResolventKernel node lam x) μ)
    (hF'_meas : AEStronglyMeasurable
      (fun x => g x * suzukiShiftResolventKernel node lam x ^ (2 : ℕ)) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ l ∈ s,
      ‖g x * suzukiShiftResolventKernel node l x ^ (2 : ℕ)‖ ≤ bound x)
    (bound_int : Integrable bound μ)
    (h_ne : ∀ᵐ x ∂μ, ∀ l ∈ s, node x - l ≠ 0) :
    HasDerivAt (fun l => ∫ x, g x * suzukiShiftResolventKernel node l x ∂μ)
      (∫ x, g x * suzukiShiftResolventKernel node lam x ^ (2 : ℕ) ∂μ) lam :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound bound_int
    (h_ne.mono fun x hx l hl =>
      HasDerivAt.const_mul (g x) (hasDerivAt_suzukiShiftResolventKernel (hx l hl)))).2

/-- **`(4)` is the derivative of the quotient.**  With both matrix elements differentiable in the
shift variable, the quotient rule produces exactly the expression the cross-Wronskian law signs. -/
theorem hasDerivAt_suzukiShiftRatio {node response : α → ℝ} {lam : ℝ}
    (hD : HasDerivAt (fun l => ∫ x, suzukiShiftResolventKernel node l x ∂μ)
      (∫ x, suzukiShiftResolventKernel node lam x ^ (2 : ℕ) ∂μ) lam)
    (hN : HasDerivAt (fun l => ∫ x, response x * suzukiShiftResolventKernel node l x ∂μ)
      (∫ x, response x * suzukiShiftResolventKernel node lam x ^ (2 : ℕ) ∂μ) lam)
    (hD0 : (∫ x, suzukiShiftResolventKernel node lam x ∂μ) ≠ 0) :
    HasDerivAt (fun l => (∫ x, response x * suzukiShiftResolventKernel node l x ∂μ) /
        (∫ x, suzukiShiftResolventKernel node l x ∂μ))
      (((∫ x, response x * suzukiShiftResolventKernel node lam x ^ (2 : ℕ) ∂μ) *
            (∫ x, suzukiShiftResolventKernel node lam x ∂μ) -
          (∫ x, response x * suzukiShiftResolventKernel node lam x ∂μ) *
            (∫ x, suzukiShiftResolventKernel node lam x ^ (2 : ℕ) ∂μ)) /
        (∫ x, suzukiShiftResolventKernel node lam x ∂μ) ^ (2 : ℕ)) lam :=
  hN.div hD hD0

/-- **Theorem B.**  Monotone likelihood makes the source quotient nonincreasing in the shift
variable: its derivative is the cross-Wronskian expression, which the two-sample identity signs. -/
theorem deriv_suzukiShiftRatio_nonpos
    [SFinite μ] {node response : α → ℝ} {lam : ℝ}
    (hD : HasDerivAt (fun l => ∫ x, suzukiShiftResolventKernel node l x ∂μ)
      (∫ x, suzukiShiftResolventKernel node lam x ^ (2 : ℕ) ∂μ) lam)
    (hN : HasDerivAt (fun l => ∫ x, response x * suzukiShiftResolventKernel node l x ∂μ)
      (∫ x, response x * suzukiShiftResolventKernel node lam x ^ (2 : ℕ) ∂μ) lam)
    (hD0 : (∫ x, suzukiShiftResolventKernel node lam x ∂μ) ≠ 0)
    (hres : Integrable (suzukiShiftResolventKernel node lam) μ)
    (hresSq : Integrable (fun x => suzukiShiftResolventKernel node lam x ^ (2 : ℕ)) μ)
    (hresponseRes : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lam x) μ)
    (hresponseResSq : Integrable
      (fun x => response x * suzukiShiftResolventKernel node lam x ^ (2 : ℕ)) μ)
    (hpair : ∀ᵐ z : α × α ∂μ.prod μ,
      lam < node z.1 ∧ lam < node z.2 ∧
        0 ≤ (response z.2 - response z.1) * (node z.2 - node z.1)) :
    deriv (fun l => (∫ x, response x * suzukiShiftResolventKernel node l x ∂μ) /
      (∫ x, suzukiShiftResolventKernel node l x ∂μ)) lam ≤ 0 := by
  rw [(hasDerivAt_suzukiShiftRatio hD hN hD0).deriv]
  exact suzukiShiftSpectralMonotoneRatio_derivativeNumerator_nonpos
    hres hresSq hresponseRes hresponseResSq hpair

end

end RHTower
