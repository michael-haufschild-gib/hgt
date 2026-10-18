import GaloisForLFunctions.BiScaleUncertainty.HyperbolicShiftCommutatorAndParityIntertwining
import GaloisForLFunctions.BiScaleUncertainty.UnitCorrelationBump
import GaloisForLFunctions.BiScaleUncertainty.UniversalRamanujanCovarianceAndBiScaleRigidity

/-!
# Classical reductions and the exact hyperbolic square defect

The difference of the two boosted correlations is a hyperbolic addition identity.
Squaring produces a nonzero cross term, exhibited on an actual smooth bump.
The finite joint energy has the same zero set as its additive summand alone.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.ClassicalBoundaries
set_option autoImplicit false

/-- The exact term omitted by a squared version of the hyperbolic difference identity. -/
theorem squared_hyperbolic_defect (f : C_c(ℝ, ℝ)) (α x : ℝ) :
    autocorr (coshMultiplier α f) x^2-autocorr (sinhMultiplier α f) x^2-
      Real.cosh (α*x)^2*autocorr f x^2 =
      2*Real.cosh (α*x)*autocorr f x*autocorr (sinhMultiplier α f) x := by
  have hd : autocorr (coshMultiplier α f) x-autocorr (sinhMultiplier α f) x =
      Real.cosh (α*x)*autocorr f x :=
    autocorr_coshMultiplier_sub_sinhMultiplier f.continuous f.hasCompactSupport α x
  have hc : autocorr (coshMultiplier α f) x =
      Real.cosh (α*x)*autocorr f x+autocorr (sinhMultiplier α f) x := by
    linarith only [hd]
  rw [hc]
  ring

/-- The squared formula is valid exactly on these two correlation zero sets. -/
theorem squared_hyperbolic_eq_iff (f : C_c(ℝ, ℝ)) (α x : ℝ) :
    (autocorr (coshMultiplier α f) x^2-autocorr (sinhMultiplier α f) x^2 =
      Real.cosh (α*x)^2*autocorr f x^2) ↔
      (autocorr f x = 0 ∨ autocorr (sinhMultiplier α f) x = 0) := by
  rw [← sub_eq_zero, squared_hyperbolic_defect]
  simp only [mul_eq_zero, show (2 : ℝ) ≠ 0 by norm_num,
    (Real.cosh_pos (α*x)).ne', false_or]

/-- The origin defect is the product of two actual nonnegative source energies. -/
theorem origin_defect (f : C_c(ℝ, ℝ)) (α : ℝ) :
    autocorr (coshMultiplier α f) 0^2-autocorr (sinhMultiplier α f) 0^2-
      autocorr f 0^2 = 2*autocorr f 0*autocorr (sinhMultiplier α f) 0 := by
  simpa only [mul_zero, Real.cosh_zero, one_pow, one_mul, mul_one]
    using squared_hyperbolic_defect f α 0

/-- A literal smooth bump strictly violates the squared formula at zero lag. -/
theorem seed_squared_formula_strict :
    autocorr SharpCycle.seed 0^2 <
      autocorr (coshMultiplier 1 SharpCycle.seed) 0^2-
        autocorr (sinhMultiplier 1 SharpCycle.seed) 0^2 := by
  have hs := continuous_sinhMultiplier 1 SharpCycle.seed.continuous
  have hc := hasCompactSupport_sinhMultiplier 1 SharpCycle.seed.hasCompactSupport
  have hp : 0 < sinhMultiplier 1 SharpCycle.seed (1/4) := by
    unfold sinhMultiplier
    apply mul_pos
    · exact Real.sinh_pos_iff.mpr (by norm_num)
    · exact (SharpCycle.seed_pos_iff _).mpr (by norm_num)
  have hS : 0 < autocorr (sinhMultiplier 1 SharpCycle.seed) 0 := by
    unfold autocorr
    simp only [add_zero]
    apply (hs.mul hs).integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
      (fun u => by
        change 0 ≤ sinhMultiplier 1 SharpCycle.seed u*sinhMultiplier 1 SharpCycle.seed u
        nlinarith only [sq_nonneg (sinhMultiplier 1 SharpCycle.seed u)])
      (x := 1/4)
    exact (mul_pos hp hp).ne'
  have hd := origin_defect SharpCycle.seed 1
  have hh := mul_pos SharpCycle.seed_mass_pos hS
  linarith only [hd, hh]

/-- Additive path energy alone has the finite-window constancy zero set. -/
theorem additive_zero_iff_const (N : ℕ) (f : ℕ → ℝ) :
    additiveStepEnergy N f = 0 ↔ ∀ n ∈ Finset.Icc 1 N, f n = f 1 := by
  simpa [biScaleJointEnergy, multiplicativeScaleEnergy]
    using biScaleJointEnergy_eq_zero_iff_const 1 N f

/-- The multiplicative term changes no zero-energy states in this finite model. -/
theorem joint_zero_iff_additive_zero (K N : ℕ) (f : ℕ → ℝ) :
    biScaleJointEnergy K N f = 0 ↔ additiveStepEnergy N f = 0 :=
  (biScaleJointEnergy_eq_zero_iff_const K N f).trans (additive_zero_iff_const N f).symm

end GaloisForLFunctions.BiScaleUncertainty.ClassicalBoundaries
