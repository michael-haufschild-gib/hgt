import GaloisForLFunctions.RHTower.GammaJumpNearDiagonalLipschitz
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# The order-minus-one commutator kernel is an integrable convolution kernel

The weighted symbol difference obeys `(1+|ξ|)|r(ξ) − r(η)| ≤ C(|ξ−η| + |ξ−η|²)` with no region
hypothesis, so against a Schwartz cutoff transform the whole commutator kernel is the convolution
kernel

`K(t) = C |χ̂(t)| (|t| + t²)`,

which is integrable because a Schwartz function has finite moments of every order.  Young's
inequality then gives the `L²` bound for the weighted transform, which is the `H¹` half of the
order-minus-one statement.

The exterior constants of the cutoff contribute nothing: a constant multiplication operator commutes
with every multiplier, so the commutator only sees `χ` up to an additive constant.  In the operator
formulation this is a one-line remark rather than a delta cancellation.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The convolution kernel of the commutator against a Schwartz cutoff transform. -/
def commutatorKernel (C : ℝ) (χ : SchwartzMap ℝ ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (C * (‖χ t‖ * (|t| + t ^ 2)))

theorem measurable_commutatorKernel (C : ℝ) (χ : SchwartzMap ℝ ℝ) :
    Measurable (commutatorKernel C χ) := by
  unfold commutatorKernel
  fun_prop

/-- **The commutator kernel is integrable.**  Schwartz decay beats the two polynomial weights. -/
theorem lintegral_commutatorKernel_ne_top {C : ℝ} (hC : 0 ≤ C) (χ : SchwartzMap ℝ ℝ) :
    (∫⁻ t : ℝ, commutatorKernel C χ t) ≠ ⊤ := by
  have h1 : Integrable (fun t : ℝ => ‖t‖ ^ 1 * ‖χ t‖) volume :=
    SchwartzMap.integrable_pow_mul volume χ 1
  have h2 : Integrable (fun t : ℝ => ‖t‖ ^ 2 * ‖χ t‖) volume :=
    SchwartzMap.integrable_pow_mul volume χ 2
  have hsum : Integrable (fun t : ℝ => C * (‖t‖ ^ 1 * ‖χ t‖ + ‖t‖ ^ 2 * ‖χ t‖)) volume :=
    (h1.add h2).const_mul C
  have hnn : ∀ᵐ t ∂(volume : Measure ℝ),
      0 ≤ C * (‖t‖ ^ 1 * ‖χ t‖ + ‖t‖ ^ 2 * ‖χ t‖) := by
    filter_upwards with t
    positivity
  have hfin : (∫⁻ t : ℝ,
      ENNReal.ofReal (C * (‖t‖ ^ 1 * ‖χ t‖ + ‖t‖ ^ 2 * ‖χ t‖))) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hsum hnn]
    exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top hfin (lintegral_mono fun t => ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  have hnorm : ‖t‖ = |t| := Real.norm_eq_abs t
  rw [hnorm, pow_one, sq_abs]
  exact le_of_eq (by ring)

variable {X : Type*} [NormedAddCommGroup X]

/-- **`(32)`: the weighted commutator transform is `L²`-bounded.**  A profile dominated by the
commutator convolution majorant has finite weighted squared mass, with the explicit constant
`(∫K)²`. -/
theorem lintegral_sq_commutator_le (C : ℝ) (χ : SchwartzMap ℝ ℝ)
    {G : ℝ → X} {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (hG : ∀ ξ : ℝ, ‖G ξ‖ₑ ≤ ∫⁻ η : ℝ, commutatorKernel C χ η * F (ξ - η)) :
    (∫⁻ ξ : ℝ, ‖G ξ‖ₑ ^ 2)
      ≤ (∫⁻ t : ℝ, commutatorKernel C χ t) ^ 2 * ∫⁻ ξ : ℝ, F ξ ^ 2 :=
  GaloisForLFunctions.HTGeometry.lintegral_enorm_sq_le_of_convolution_bound
    (measurable_commutatorKernel C χ) hF hG

/-- **The exterior constants cancel.**  A constant multiplication operator commutes with every
linear multiplier, so the commutator only ever sees the cutoff up to an additive constant. -/
theorem commutator_const_eq_zero {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (R : Y →ₗ[ℂ] Y) (c : ℂ) (y : Y) : R (c • y) - c • R y = 0 := by
  rw [map_smul, sub_self]

end GaloisForLFunctions.RHTower
