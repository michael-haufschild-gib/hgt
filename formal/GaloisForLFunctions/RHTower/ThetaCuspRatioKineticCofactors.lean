import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticModel
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem kinetic_coeff_mul (p q : KineticPolynomial) (n : ℕ) :
    (p*q).coeff n=∑ j ∈ Finset.range (n+1),p.coeff j*q.coeff (n-j) := by
  rw [Polynomial.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i*q.coeff j) n

def kineticCof2 : KineticPolynomial := cof2_75 kineticMoment6 kineticMoment8 kineticMoment10
def kineticCof4 : KineticPolynomial := cof4_75 kineticMoment4 kineticMoment6 kineticMoment8 kineticMoment10
def kineticCof6 : KineticPolynomial := cof6_75 kineticMoment2 kineticMoment4 kineticMoment6 kineticMoment8 kineticMoment10
def kineticCof8 : KineticPolynomial := cof8_75 kineticMoment2 kineticMoment4 kineticMoment6 kineticMoment8
def kineticCof10 : KineticPolynomial := cof10_75 kineticMoment2 kineticMoment4 kineticMoment6

theorem completeKineticSlope_cofactors : completeKineticSlope=
    kineticCof2*kineticBlock2+kineticCof4*kineticBlock4+kineticCof6*kineticBlock6+
      kineticCof8*kineticBlock8+kineticCof10*kineticBlock10 := rfl

theorem kineticMoment2_coeff (j : ℕ) : kineticMoment2.coeff j=
    ((if j=0 then clearMoment2KineticCoeff0 else 0) + ((if j=1 then clearMoment2KineticCoeff1 else 0) + (if j=2 then clearMoment2KineticCoeff2 else 0))) := by
  simp only [kineticMoment2,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]

theorem kineticMoment4_coeff (j : ℕ) : kineticMoment4.coeff j=
    (((if j=0 then clearMoment4KineticCoeff0 else 0) + (if j=1 then clearMoment4KineticCoeff1 else 0)) + ((if j=2 then clearMoment4KineticCoeff2 else 0) + ((if j=3 then clearMoment4KineticCoeff3 else 0) + (if j=4 then clearMoment4KineticCoeff4 else 0)))) := by
  simp only [kineticMoment4,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]

theorem kineticMoment6_coeff (j : ℕ) : kineticMoment6.coeff j=
    (((if j=0 then clearMoment6KineticCoeff0 else 0) + ((if j=1 then clearMoment6KineticCoeff1 else 0) + (if j=2 then clearMoment6KineticCoeff2 else 0))) + (((if j=3 then clearMoment6KineticCoeff3 else 0) + (if j=4 then clearMoment6KineticCoeff4 else 0)) + ((if j=5 then clearMoment6KineticCoeff5 else 0) + (if j=6 then clearMoment6KineticCoeff6 else 0)))) := by
  simp only [kineticMoment6,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]

theorem kineticMoment8_coeff (j : ℕ) : kineticMoment8.coeff j=
    ((((if j=0 then clearMoment8KineticCoeff0 else 0) + (if j=1 then clearMoment8KineticCoeff1 else 0)) + ((if j=2 then clearMoment8KineticCoeff2 else 0) + (if j=3 then clearMoment8KineticCoeff3 else 0))) + (((if j=4 then clearMoment8KineticCoeff4 else 0) + (if j=5 then clearMoment8KineticCoeff5 else 0)) + ((if j=6 then clearMoment8KineticCoeff6 else 0) + ((if j=7 then clearMoment8KineticCoeff7 else 0) + (if j=8 then clearMoment8KineticCoeff8 else 0))))) := by
  simp only [kineticMoment8,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]

theorem kineticMoment10_coeff (j : ℕ) : kineticMoment10.coeff j=
    ((((if j=0 then clearMoment10KineticCoeff0 else 0) + (if j=1 then clearMoment10KineticCoeff1 else 0)) + ((if j=2 then clearMoment10KineticCoeff2 else 0) + ((if j=3 then clearMoment10KineticCoeff3 else 0) + (if j=4 then clearMoment10KineticCoeff4 else 0)))) + (((if j=5 then clearMoment10KineticCoeff5 else 0) + ((if j=6 then clearMoment10KineticCoeff6 else 0) + (if j=7 then clearMoment10KineticCoeff7 else 0))) + ((if j=8 then clearMoment10KineticCoeff8 else 0) + ((if j=9 then clearMoment10KineticCoeff9 else 0) + (if j=10 then clearMoment10KineticCoeff10 else 0))))) := by
  simp only [kineticMoment10,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]

end
end HTGeometry.ThetaRatioKineticContraction
