import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeSourceSign

/-!
# CCM polar negative-Hessian Lorentz-signature universality

The local CCM polar source has negative Hessian kernel `2 cosh((x-y)/2)`.  Combining that source
identity with the polar-prime kernel factorization shows that every finite sampled negative-Hessian
energy has only two feature channels, regardless of sample size: a positive cosh channel and a
negative sinh channel.
-/

open scoped BigOperators ComplexConjugate
open Finset Complex

noncomputable section

namespace RHTower

variable {ι : Type*}

/-- Finite complex quadratic form of the sampled negative Hessian of the local CCM polar
potential. -/
def ccmPolarNegativeHessianQuadraticForm
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s,
    ((-(-2 * Real.cosh ((x i - x j) / 2)) : ℝ) : ℂ) * v i * conj (v j)

/-- Real energy of the sampled negative CCM polar Hessian. -/
def ccmPolarNegativeHessianEnergy
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) : ℝ :=
  (ccmPolarNegativeHessianQuadraticForm s x v).re

/-- The sampled negative Hessian is exactly the existing finite polar quadratic form. -/
theorem ccmPolarNegativeHessianQuadraticForm_eq_polarQuadraticForm
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) :
    ccmPolarNegativeHessianQuadraticForm s x v =
      polarQuadraticForm s x v := by
  unfold ccmPolarNegativeHessianQuadraticForm polarQuadraticForm
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_ccmPolarPotential_secondDerivative_eq_polarKernel]

/-- **CCM polar negative-Hessian Lorentz-signature law.**  Every finite sampled negative-Hessian
energy factors through one positive cosh feature and one negative sinh feature. -/
theorem ccmPolarNegativeHessianEnergy_eq_lorentzSignature
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) :
    ccmPolarNegativeHessianEnergy s x v =
      2 * Complex.normSq (polarCoshFeature s x v) -
        2 * Complex.normSq (polarSinhFeature s x v) := by
  rw [ccmPolarNegativeHessianEnergy,
    ccmPolarNegativeHessianQuadraticForm_eq_polarQuadraticForm]
  exact polarEnergy_eq_signature s x v

end RHTower
