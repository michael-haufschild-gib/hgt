import GaloisForLFunctions.BiScaleUncertainty.Towers.FiniteGrid
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.IndependentPreimages

/-!
# Independent antishifts on finite arithmetic grids

The independent-preimage criterion of Aznay–Chabbabi–Zariouh applies before
any compatibility or growth condition: a masked shift has only the zero
infinitely divisible datum. For its difference operator, injectivity forces
all independent choices to be the existing finite Green-operator tower.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

open ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
open RepresentationLifting.OperatorKernels

/-- Unrelated antishifts at every depth already force the initial datum to vanish. -/
theorem finiteGridShift_independentRoot_eq_zero (d : ℕ) (D : Finset ℕ)
    (x : independentPreimages (finiteGridShift d D).toLinearMap) : x.1 0 = 0 := by
  rw [← x.2 (finiteGridRunLength d D), finiteGridShiftLinear_pow_apply,
    finiteGridShift_nilpotent]
  rfl

/-- Independently solving every power of the difference equation automatically gives compatibility. -/
theorem finiteGridDifference_independentPreimages_eq (d : ℕ) (D : Finset ℕ) :
    independentPreimages (1 - finiteGridShift d D).toLinearMap =
      backwardOrbits (1 - finiteGridShift d D).toLinearMap :=
  independentPreimages_eq_backwardOrbits _ (finiteGridDifferenceEquiv d D).injective

/-- Even independently chosen solutions are the iterates of the exact finite Green operator. -/
theorem finiteGridDifference_independentPreimage_formula (d : ℕ) (D : Finset ℕ)
    (x : independentPreimages (1 - finiteGridShift d D).toLinearMap) (n : ℕ) :
    x.1 n = ((finiteGridGreen d D).toLinearMap ^ n) (x.1 0) := by
  have hx : x.1 ∈ backwardOrbits (1 - finiteGridShift d D).toLinearMap := by
    rw [← finiteGridDifference_independentPreimages_eq]
    exact x.2
  exact finiteGridDifference_backwardOrbit_formula d D ⟨x.1, hx⟩ n

#print axioms finiteGridShift_independentRoot_eq_zero
#print axioms finiteGridDifference_independentPreimages_eq
#print axioms finiteGridDifference_independentPreimage_formula

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
