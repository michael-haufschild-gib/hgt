import GaloisForLFunctions.BiScaleUncertainty.FiniteGridTraceStability
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.CompatibleTowers
import Mathlib.Algebra.Ring.GeomSum

/-!
# Compatible towers for the arithmetic finite-grid shift

The masked successor is nilpotent at the arithmetic longest-run length, so
its inverse limit vanishes. The difference operator `1 - S` is invertible:
its inverse is the finite geometric sum terminating at that same run length.
Consequently every datum has exactly one compatible difference tower.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

open ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
open scoped BigOperators

theorem finiteGridShiftLinear_pow_apply (d : ℕ) (D : Finset ℕ) (n : ℕ)
    (x : SequenceData ℂ) :
    ((finiteGridShift d D).toLinearMap ^ n) x = (finiteGridShift d D ^ n) x := by
  exact LinearMap.congr_fun
    (map_pow ContinuousLinearMap.toLinearMapRingHom (finiteGridShift d D) n).symm x

/-- No nonzero trace datum admits infinitely many successive masked antishifts. -/
theorem finiteGridShift_backwardOrbit_eq_zero (d : ℕ) (D : Finset ℕ)
    (x : backwardOrbits (finiteGridShift d D).toLinearMap) : x = 0 := by
  apply (backwardOrbits_uniform_torsion_iff (finiteGridShift d D).toLinearMap x
    (finiteGridRunLength d D)).mp
  intro n
  rw [finiteGridShiftLinear_pow_apply, finiteGridShift_nilpotent]
  rfl

/-- The exact finite Green operator, cut off at the arithmetic longest run. -/
def finiteGridGreen (d : ℕ) (D : Finset ℕ) : SequenceData ℂ →L[ℂ] SequenceData ℂ :=
  ∑ i ∈ Finset.range (finiteGridRunLength d D), finiteGridShift d D ^ i

theorem finiteGridGreen_inverse (d : ℕ) (D : Finset ℕ) :
    (1 - finiteGridShift d D) * finiteGridGreen d D = 1 ∧
      finiteGridGreen d D * (1 - finiteGridShift d D) = 1 := by
  constructor
  · rw [finiteGridGreen, mul_neg_geom_sum, finiteGridShift_nilpotent, sub_zero]
  · rw [finiteGridGreen, geom_sum_mul_neg, finiteGridShift_nilpotent, sub_zero]

/-- Solving the finite-grid difference equation is a linear automorphism. -/
def finiteGridDifferenceEquiv (d : ℕ) (D : Finset ℕ) :
    SequenceData ℂ ≃ₗ[ℂ] SequenceData ℂ :=
  LinearEquiv.ofLinear (1 - finiteGridShift d D).toLinearMap
    (finiteGridGreen d D).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      change ((1 - finiteGridShift d D) * finiteGridGreen d D) x = x
      rw [(finiteGridGreen_inverse d D).1]
      rfl)
    (by
      apply LinearMap.ext
      intro x
      change (finiteGridGreen d D * (1 - finiteGridShift d D)) x = x
      rw [(finiteGridGreen_inverse d D).2]
      rfl)

/-- Every datum is the initial value of exactly one compatible difference tower. -/
def finiteGridDifferenceTowerEquiv (d : ℕ) (D : Finset ℕ) :
    backwardOrbits (1 - finiteGridShift d D).toLinearMap ≃ₗ[ℂ] SequenceData ℂ :=
  backwardOrbitsEquiv (finiteGridDifferenceEquiv d D)

/-- The compatible tower is obtained by iterating the exact finite Green operator. -/
theorem finiteGridDifference_backwardOrbit_formula (d : ℕ) (D : Finset ℕ)
    (x : backwardOrbits (1 - finiteGridShift d D).toLinearMap) (n : ℕ) :
    x.1 n = ((finiteGridGreen d D).toLinearMap ^ n) (x.1 0) := by
  have h := congrArg (fun y : backwardOrbits (1 - finiteGridShift d D).toLinearMap => y.1 n)
    ((finiteGridDifferenceTowerEquiv d D).symm_apply_apply x)
  exact h.symm

#print axioms finiteGridShift_backwardOrbit_eq_zero
#print axioms finiteGridGreen_inverse
#print axioms finiteGridDifferenceTowerEquiv
#print axioms finiteGridDifference_backwardOrbit_formula

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
