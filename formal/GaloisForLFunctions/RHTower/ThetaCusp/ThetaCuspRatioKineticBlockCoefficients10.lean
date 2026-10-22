import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticModel
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticBlock10Coeff0Norm : {P : Poly // kineticBlock10.coeff 0=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 0=kineticBlock10.coeff 0 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff1Norm : {P : Poly // kineticBlock10.coeff 1=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 1=kineticBlock10.coeff 1 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff2Norm : {P : Poly // kineticBlock10.coeff 2=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 2=kineticBlock10.coeff 2 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff3Norm : {P : Poly // kineticBlock10.coeff 3=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 3=kineticBlock10.coeff 3 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff4Norm : {P : Poly // kineticBlock10.coeff 4=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 4=kineticBlock10.coeff 4 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff5Norm : {P : Poly // kineticBlock10.coeff 5=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 5=kineticBlock10.coeff 5 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff6Norm : {P : Poly // kineticBlock10.coeff 6=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 6=kineticBlock10.coeff 6 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff7Norm : {P : Poly // kineticBlock10.coeff 7=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 7=kineticBlock10.coeff 7 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff8Norm : {P : Poly // kineticBlock10.coeff 8=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 8=kineticBlock10.coeff 8 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff9Norm : {P : Poly // kineticBlock10.coeff 9=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 9=kineticBlock10.coeff 9 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff10Norm : {P : Poly // kineticBlock10.coeff 10=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 10=kineticBlock10.coeff 10 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock10Coeff11Norm : {P : Poly // kineticBlock10.coeff 11=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock10.coeff 11=kineticBlock10.coeff 11 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock10,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment10KineticCoeff0Norm.property,clearMoment10KineticCoeff1Norm.property,clearMoment10KineticCoeff2Norm.property,clearMoment10KineticCoeff3Norm.property,clearMoment10KineticCoeff4Norm.property,clearMoment10KineticCoeff5Norm.property,clearMoment10KineticCoeff6Norm.property,clearMoment10KineticCoeff7Norm.property,clearMoment10KineticCoeff8Norm.property,clearMoment10KineticCoeff9Norm.property,clearMoment10KineticCoeff10Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment10KineticCoeff0Norm,clearMoment10KineticCoeff1Norm,clearMoment10KineticCoeff2Norm,clearMoment10KineticCoeff3Norm,clearMoment10KineticCoeff4Norm,clearMoment10KineticCoeff5Norm,clearMoment10KineticCoeff6Norm,clearMoment10KineticCoeff7Norm,clearMoment10KineticCoeff8Norm,clearMoment10KineticCoeff9Norm,clearMoment10KineticCoeff10Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
