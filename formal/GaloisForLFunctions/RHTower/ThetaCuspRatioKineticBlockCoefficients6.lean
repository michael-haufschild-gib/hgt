import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticModel
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticBlock6Coeff0Norm : {P : Poly // kineticBlock6.coeff 0=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 0=kineticBlock6.coeff 0 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock6Coeff1Norm : {P : Poly // kineticBlock6.coeff 1=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 1=kineticBlock6.coeff 1 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock6Coeff2Norm : {P : Poly // kineticBlock6.coeff 2=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 2=kineticBlock6.coeff 2 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock6Coeff3Norm : {P : Poly // kineticBlock6.coeff 3=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 3=kineticBlock6.coeff 3 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock6Coeff4Norm : {P : Poly // kineticBlock6.coeff 4=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 4=kineticBlock6.coeff 4 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock6Coeff5Norm : {P : Poly // kineticBlock6.coeff 5=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 5=kineticBlock6.coeff 5 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock6Coeff6Norm : {P : Poly // kineticBlock6.coeff 6=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 6=kineticBlock6.coeff 6 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock6Coeff7Norm : {P : Poly // kineticBlock6.coeff 7=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock6.coeff 7=kineticBlock6.coeff 7 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock6,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment6KineticCoeff0Norm.property,clearMoment6KineticCoeff1Norm.property,clearMoment6KineticCoeff2Norm.property,clearMoment6KineticCoeff3Norm.property,clearMoment6KineticCoeff4Norm.property,clearMoment6KineticCoeff5Norm.property,clearMoment6KineticCoeff6Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment6KineticCoeff0Norm,clearMoment6KineticCoeff1Norm,clearMoment6KineticCoeff2Norm,clearMoment6KineticCoeff3Norm,clearMoment6KineticCoeff4Norm,clearMoment6KineticCoeff5Norm,clearMoment6KineticCoeff6Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
