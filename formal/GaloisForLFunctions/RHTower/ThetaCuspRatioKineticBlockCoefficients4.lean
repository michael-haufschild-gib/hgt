import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticModel
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticBlock4Coeff0Norm : {P : Poly // kineticBlock4.coeff 0=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock4.coeff 0=kineticBlock4.coeff 0 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock4,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment4KineticCoeff0Norm.property,clearMoment4KineticCoeff1Norm.property,clearMoment4KineticCoeff2Norm.property,clearMoment4KineticCoeff3Norm.property,clearMoment4KineticCoeff4Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment4KineticCoeff0Norm,clearMoment4KineticCoeff1Norm,clearMoment4KineticCoeff2Norm,clearMoment4KineticCoeff3Norm,clearMoment4KineticCoeff4Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock4Coeff1Norm : {P : Poly // kineticBlock4.coeff 1=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock4.coeff 1=kineticBlock4.coeff 1 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock4,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment4KineticCoeff0Norm.property,clearMoment4KineticCoeff1Norm.property,clearMoment4KineticCoeff2Norm.property,clearMoment4KineticCoeff3Norm.property,clearMoment4KineticCoeff4Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment4KineticCoeff0Norm,clearMoment4KineticCoeff1Norm,clearMoment4KineticCoeff2Norm,clearMoment4KineticCoeff3Norm,clearMoment4KineticCoeff4Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock4Coeff2Norm : {P : Poly // kineticBlock4.coeff 2=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock4.coeff 2=kineticBlock4.coeff 2 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock4,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment4KineticCoeff0Norm.property,clearMoment4KineticCoeff1Norm.property,clearMoment4KineticCoeff2Norm.property,clearMoment4KineticCoeff3Norm.property,clearMoment4KineticCoeff4Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment4KineticCoeff0Norm,clearMoment4KineticCoeff1Norm,clearMoment4KineticCoeff2Norm,clearMoment4KineticCoeff3Norm,clearMoment4KineticCoeff4Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock4Coeff3Norm : {P : Poly // kineticBlock4.coeff 3=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock4.coeff 3=kineticBlock4.coeff 3 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock4,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment4KineticCoeff0Norm.property,clearMoment4KineticCoeff1Norm.property,clearMoment4KineticCoeff2Norm.property,clearMoment4KineticCoeff3Norm.property,clearMoment4KineticCoeff4Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment4KineticCoeff0Norm,clearMoment4KineticCoeff1Norm,clearMoment4KineticCoeff2Norm,clearMoment4KineticCoeff3Norm,clearMoment4KineticCoeff4Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock4Coeff4Norm : {P : Poly // kineticBlock4.coeff 4=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock4.coeff 4=kineticBlock4.coeff 4 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock4,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment4KineticCoeff0Norm.property,clearMoment4KineticCoeff1Norm.property,clearMoment4KineticCoeff2Norm.property,clearMoment4KineticCoeff3Norm.property,clearMoment4KineticCoeff4Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment4KineticCoeff0Norm,clearMoment4KineticCoeff1Norm,clearMoment4KineticCoeff2Norm,clearMoment4KineticCoeff3Norm,clearMoment4KineticCoeff4Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock4Coeff5Norm : {P : Poly // kineticBlock4.coeff 5=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock4.coeff 5=kineticBlock4.coeff 5 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock4,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment4KineticCoeff0Norm.property,clearMoment4KineticCoeff1Norm.property,clearMoment4KineticCoeff2Norm.property,clearMoment4KineticCoeff3Norm.property,clearMoment4KineticCoeff4Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment4KineticCoeff0Norm,clearMoment4KineticCoeff1Norm,clearMoment4KineticCoeff2Norm,clearMoment4KineticCoeff3Norm,clearMoment4KineticCoeff4Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
