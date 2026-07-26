import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain

/-!
# Hedenmalm Fourier family versus the intrinsic Xi multiplicity chain

This small bridge keeps the Fourier-model comparison out of the intrinsic Xi divided-chain
module used by Deninger's source cohomology.
-/

open Complex

namespace RHTower

noncomputable section

theorem xiThetaEigenFourier_eq_I_mul_dividedChain_one (alpha z : ℂ) :
    xiThetaEigenFourier alpha z = I * xiThetaDividedChain alpha 1 z := by
  simp [xiThetaEigenFourier, xiThetaDividedChain]

/-- The original Hedenmalm quotient has a nonzero base value exactly at a simple zero. -/
theorem xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one
    (rho : XiDivisorSupport) :
    xiThetaEigenFourier (xiSpectralPointSupport rho)
      (xiSpectralPointSupport rho) ≠ 0 ↔ xiSupportMultiplicity rho = 1 := by
  rw [xiThetaEigenFourier_eq_I_mul_dividedChain_one]
  constructor
  · intro hne
    apply (xiThetaDividedChain_one_self_ne_zero_iff_multiplicity_one rho).mp
    intro hzero
    apply hne
    rw [hzero, mul_zero]
  · intro hm
    exact mul_ne_zero I_ne_zero
      ((xiThetaDividedChain_one_self_ne_zero_iff_multiplicity_one rho).mpr hm)

end

end RHTower
