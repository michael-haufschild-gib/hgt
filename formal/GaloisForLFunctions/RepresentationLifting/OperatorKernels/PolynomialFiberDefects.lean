import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel
import GaloisForLFunctions.HTGeometry.PolynomialQuotientMultiplicationRank

/-!
# Operator defects in polynomial fibres

For the algebra `K[X]/(Xⁿ⁺¹-a)`, multiplication by `Q` has operator-quotient
dimension `(n+1) deg gcd(Xⁿ⁺¹-a,Q)`. Repeated roots and inseparable fibres
are included. The greatest common divisor measures the exact obstruction.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

open GaloisForLFunctions.HTGeometry

variable {K W : Type*} [Field K]
  [AddCommGroup W] [Module K W]

/-- The family includes the nilpotent fibre at zero and every nonzero scalar fibre. -/
def powerFiberPolynomial (n : ℕ) (a : K) : K[X] := X ^ (n + 1) - C a

theorem powerFiberPolynomial_monic (n : ℕ) (a : K) :
    (powerFiberPolynomial n a).Monic :=
  monic_X_pow_sub_C a (Nat.succ_ne_zero n)

@[simp] theorem powerFiberPolynomial_natDegree (n : ℕ) (a : K) :
    (powerFiberPolynomial n a).natDegree = n + 1 :=
  natDegree_X_pow_sub_C

variable [DecidableEq K]

/-- Arbitrary observation spaces see exactly the common-divisor multiplicity. -/
theorem powerFiber_observation_defect [FiniteDimensional K W]
    (n : ℕ) (a : K) (Q : K[X]) :
    Module.finrank K ((polyQuot (powerFiberPolynomial n a) →ₗ[K] W) ⧸
      (precompose (W := W) (polyQuotMul (powerFiberPolynomial n a) Q)).range) =
      Module.finrank K W * (EuclideanDomain.gcd (powerFiberPolynomial n a) Q).natDegree := by
  have hp := (powerFiberPolynomial_monic n a).ne_zero
  letI := finiteDimensional_polynomialQuotient hp
  rw [finrank_compositionCokernel, finrank_ker_polyQuotMul _ _ hp]

/-- Passing to the full endomorphism algebra multiplies the divisor defect by fibre degree. -/
theorem powerFiber_endomorphism_defect (n : ℕ) (a : K) (Q : K[X]) :
    Module.finrank K (Module.End K (polyQuot (powerFiberPolynomial n a)) ⧸
      (precompose (W := polyQuot (powerFiberPolynomial n a))
        (polyQuotMul (powerFiberPolynomial n a) Q)).range) =
      (n + 1) * (EuclideanDomain.gcd (powerFiberPolynomial n a) Q).natDegree := by
  have hp := (powerFiberPolynomial_monic n a).ne_zero
  letI := finiteDimensional_polynomialQuotient hp
  rw [powerFiber_observation_defect, finrank_polynomialQuotient hp,
    powerFiberPolynomial_natDegree]

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.powerFiber_observation_defect
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.powerFiber_endomorphism_defect
