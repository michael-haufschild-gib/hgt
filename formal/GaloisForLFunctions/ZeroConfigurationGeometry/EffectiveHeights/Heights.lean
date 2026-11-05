import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LatticeRate

/-!
# Finite camera height expressions

All thresholds use finite arithmetic, logarithms, exponentials and maxima.
The point height pays the isolation floor and spline tail. The moment height
also pays the numerical relative-rate bound.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Logarithmic height paying for the camera floor and the spline tail. -/
def cameraBaseLogHeight (J : ℕ) (θ lam A S M K' : ℝ) : ℝ :=
  let β := lam - θ / 2
  let ℓ := 2 * Real.pi * A / lam
  let e := 6 * slackBound ℓ * (1 + slackBound ℓ)
  let c := 2 * growthRate ℓ * lam ^ 2 +
    2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M)
  let K := c / 2 + 2
  let MK := e * lam + K + K' + 2 + J
  let ρ := 8 * MK / β
  let α := 1 / (8 * MK * (1 + ρ))
  let q := max 0 (Real.log α⁻¹)
  max (max 1 (2 * Real.pi / lam))
    (2 * MK * q + (lam + 4) + (Real.log (max S 1) + 605) + 1)

theorem one_le_cameraBaseLogHeight (J : ℕ) (θ lam A S M K' : ℝ) :
    1 ≤ cameraBaseLogHeight J θ lam A S M K' := by
  unfold cameraBaseLogHeight
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- A finite height for the moment camera, with the lattice rate replaced by its numerical bound. -/
def cameraMomentHeight (J : ℕ) (θ lam A S M K' : ℝ) : ℝ :=
  2 * Real.pi * Real.exp
    (max (cameraBaseLogHeight J θ lam A S M K')
      (Real.log (max (6 * cameraSlowConstant lam (2 * Real.pi * A / lam) M) (4 * lam) + 1)))

theorem cameraMomentHeight_ge (J : ℕ) (θ lam A S M K' : ℝ) :
    2 * Real.pi * Real.exp 1 ≤ cameraMomentHeight J θ lam A S M K' := by
  unfold cameraMomentHeight
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    ((one_le_cameraBaseLogHeight J θ lam A S M K').trans (le_max_left _ _))) (by positivity)

/-- A finite height for exact local isolation and multiplicity readout to error one quarter. -/
def cameraPointHeight (θ lam A S M : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (cameraBaseLogHeight 0 θ lam A S M 0)

theorem cameraPointHeight_ge (θ lam A S M : ℝ) :
    2 * Real.pi * Real.exp 1 ≤ cameraPointHeight θ lam A S M := by
  unfold cameraPointHeight
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (one_le_cameraBaseLogHeight 0 θ lam A S M 0)) (by positivity)


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.cameraMomentHeight_ge
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.cameraPointHeight_ge
