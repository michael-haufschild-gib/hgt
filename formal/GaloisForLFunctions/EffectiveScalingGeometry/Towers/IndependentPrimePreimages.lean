import GaloisForLFunctions.EffectiveScalingGeometry.Towers.PrimeTailAndGauge
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.IndependentPreimages

/-!
# Independent division by prime-tail and two-prime operators

Square-zero prime-tail correction admits no nonzero independently divisible
root. The invertible two-prime gauge has the opposite behavior: independent
division is automatically coherent and has an explicit affine dependence on depth.
-/

noncomputable section

namespace GaloisForLFunctions.EffectiveScalingGeometry

open RHTower ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
open RepresentationLifting.OperatorKernels

variable (R : Type*) [CommRing R]

/-- No common nonzero image survives independent division by every prime-tail power. -/
theorem primeTailShear_independentRoot_eq_zero (k : ℕ)
    (x : independentPreimages (primeTailShear R k)) : x.1 0 = 0 :=
  independentRoot_eq_zero_of_pow_eq_zero _ 2 (primeTailShear_sq R k) x

/-- Two-prime gauge division cannot create a compatibility defect. -/
theorem primeTwoPrimeGauge_independentPreimages_eq (k : ℕ) :
    independentPreimages (primeTwoPrimeGauge R k) =
      backwardOrbits (primeTwoPrimeGauge R k) :=
  independentPreimages_eq_backwardOrbits _ (primeTwoPrimeGaugeEquiv R k).injective

/-- Independent choices obey the same affine inverse-gauge formula as coherent towers. -/
theorem primeTwoPrimeGauge_independentPreimage_formula (k : ℕ)
    (x : independentPreimages (primeTwoPrimeGauge R k)) (n : ℕ) :
    x.1 n = x.1 0 + n • primeTailShear R k (x.1 0) := by
  have hx : x.1 ∈ backwardOrbits (primeTwoPrimeGauge R k) := by
    rw [← primeTwoPrimeGauge_independentPreimages_eq]
    exact x.2
  exact primeTwoPrimeGauge_backwardOrbit_formula R k ⟨x.1, hx⟩ n

/-- The automatic compatibility also holds inside each actual arithmetic cutoff. -/
theorem primeTwoPrimeCutoff_independentPreimages_eq (k N : ℕ) :
    independentPreimages (primeTwoPrimeCutoffEquiv R k N).toLinearMap =
      backwardOrbits (primeTwoPrimeCutoffEquiv R k N).toLinearMap :=
  independentPreimages_eq_backwardOrbits _ (primeTwoPrimeCutoffEquiv R k N).injective

#print axioms primeTailShear_independentRoot_eq_zero
#print axioms primeTwoPrimeGauge_independentPreimage_formula
#print axioms primeTwoPrimeCutoff_independentPreimages_eq

end GaloisForLFunctions.EffectiveScalingGeometry
