import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Reconstruction of a ray map from its peeling field

This module formalizes Okten--Turan, arXiv:2608.19244v1, equations `(9)`--`(10)`.  A continuous
peeling field determines a positive ray-map derivative up to one nonzero multiplicative constant;
one further integration determines the ray map up to an additive constant.  The reconstructed
derivative has logarithmic rate exactly the prescribed peeling field.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Equation `(9)`: derivative reconstructed from a continuous peeling field. -/
def rayDerivative (kappa : ℝ → ℝ) (C uref u : ℝ) : ℝ :=
  C * Real.exp (-∫ v in uref..u, kappa v)

/-- Equation `(10)`: ray map reconstructed from its derivative and one reference value. -/
def reconstructedRayMap (kappa : ℝ → ℝ) (C p0 uref u : ℝ) : ℝ :=
  p0 + ∫ s in uref..u, rayDerivative kappa C uref s

/-- The reconstructed derivative solves `p″ = -kappa * p′`. -/
theorem hasDerivAt_rayDerivative (kappa : ℝ → ℝ) (hkappa : Continuous kappa)
    (C uref u : ℝ) :
    HasDerivAt (fun x => C * Real.exp (-∫ v in uref..x, kappa v))
      (-kappa u * (C * Real.exp (-∫ v in uref..u, kappa v))) u := by
  have hInt : HasDerivAt (fun x => ∫ v in uref..x, kappa v) (kappa u) u :=
    (hkappa.integral_hasStrictDerivAt uref u).hasDerivAt
  have hExp := (Real.hasDerivAt_exp (-∫ v in uref..u, kappa v)).comp u hInt.neg
  have hMul := hExp.const_mul C
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hMul

/-- The reconstructed derivative is continuous. -/
theorem continuous_rayDerivative (kappa : ℝ → ℝ) (hkappa : Continuous kappa)
    (C uref : ℝ) : Continuous (fun x => C * Real.exp (-∫ v in uref..x, kappa v)) := by
  exact continuous_iff_continuousAt.mpr fun u =>
    (hasDerivAt_rayDerivative kappa hkappa C uref u).continuousAt

/-- Equation `(10)`: the derivative of the reconstructed ray map is equation `(9)`. -/
theorem hasDerivAt_reconstructedRayMap (kappa : ℝ → ℝ) (hkappa : Continuous kappa)
    (C p0 uref u : ℝ) :
    HasDerivAt (fun x => p0 + ∫ s in uref..x,
      C * Real.exp (-∫ v in uref..s, kappa v))
      (C * Real.exp (-∫ v in uref..u, kappa v)) u := by
  have hInt := (continuous_rayDerivative kappa hkappa C uref).integral_hasStrictDerivAt uref u
  exact HasDerivAt.const_add p0 hInt.hasDerivAt

/-- A nonzero integration constant gives an everywhere nonzero reconstructed derivative. -/
theorem rayDerivative_ne_zero (kappa : ℝ → ℝ) {C : ℝ} (hC : C ≠ 0)
    (uref u : ℝ) : rayDerivative kappa C uref u ≠ 0 := by
  exact mul_ne_zero hC (Real.exp_ne_zero _)

/-- A positive integration constant gives an everywhere positive reconstructed derivative. -/
theorem rayDerivative_pos (kappa : ℝ → ℝ) {C : ℝ} (hC : 0 < C)
    (uref u : ℝ) : 0 < rayDerivative kappa C uref u := by
  exact mul_pos hC (Real.exp_pos _)

/-- The logarithmic rate of the reconstructed derivative is exactly the prescribed peeling field,
closing equation `(9)` rather than merely constructing a candidate. -/
theorem rayDerivative_logarithmic_rate (kappa : ℝ → ℝ) {C : ℝ} (hC : C ≠ 0)
    (uref u : ℝ) :
    -(-kappa u * rayDerivative kappa C uref u) / rayDerivative kappa C uref u = kappa u := by
  field_simp [rayDerivative_ne_zero kappa hC uref u]

/-- Equation `(11)`: a constant peeling field gives an exponential ray-map derivative. -/
theorem rayDerivative_const (kappa C uref u : ℝ) :
    rayDerivative (fun _ => kappa) C uref u =
      C * Real.exp (-kappa * (u - uref)) := by
  have hInt : (∫ _v in uref..u, kappa) = (u - uref) * kappa := by simp
  rw [rayDerivative, hInt]
  congr 2
  ring

end

end GaloisForLFunctions.HTGeometry
