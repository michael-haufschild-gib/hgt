import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticModel
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticBlock8Coeff0Norm : {P : Poly // kineticBlock8.coeff 0=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 0=kineticBlock8.coeff 0 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff1Norm : {P : Poly // kineticBlock8.coeff 1=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 1=kineticBlock8.coeff 1 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff2Norm : {P : Poly // kineticBlock8.coeff 2=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 2=kineticBlock8.coeff 2 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff3Norm : {P : Poly // kineticBlock8.coeff 3=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 3=kineticBlock8.coeff 3 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff4Norm : {P : Poly // kineticBlock8.coeff 4=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 4=kineticBlock8.coeff 4 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff5Norm : {P : Poly // kineticBlock8.coeff 5=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 5=kineticBlock8.coeff 5 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff6Norm : {P : Poly // kineticBlock8.coeff 6=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 6=kineticBlock8.coeff 6 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff7Norm : {P : Poly // kineticBlock8.coeff 7=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 7=kineticBlock8.coeff 7 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff8Norm : {P : Poly // kineticBlock8.coeff 8=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 8=kineticBlock8.coeff 8 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock8Coeff9Norm : {P : Poly // kineticBlock8.coeff 9=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock8.coeff 9=kineticBlock8.coeff 9 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock8,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment8KineticCoeff0Norm.property,clearMoment8KineticCoeff1Norm.property,clearMoment8KineticCoeff2Norm.property,clearMoment8KineticCoeff3Norm.property,clearMoment8KineticCoeff4Norm.property,clearMoment8KineticCoeff5Norm.property,clearMoment8KineticCoeff6Norm.property,clearMoment8KineticCoeff7Norm.property,clearMoment8KineticCoeff8Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment8KineticCoeff0Norm,clearMoment8KineticCoeff1Norm,clearMoment8KineticCoeff2Norm,clearMoment8KineticCoeff3Norm,clearMoment8KineticCoeff4Norm,clearMoment8KineticCoeff5Norm,clearMoment8KineticCoeff6Norm,clearMoment8KineticCoeff7Norm,clearMoment8KineticCoeff8Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
