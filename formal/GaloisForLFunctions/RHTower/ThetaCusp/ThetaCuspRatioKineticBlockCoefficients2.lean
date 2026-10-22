import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticModel
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticBlock2Coeff0Norm : {P : Poly // kineticBlock2.coeff 0=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock2.coeff 0=kineticBlock2.coeff 0 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock2,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment2KineticCoeff0Norm.property,clearMoment2KineticCoeff1Norm.property,clearMoment2KineticCoeff2Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment2KineticCoeff0Norm,clearMoment2KineticCoeff1Norm,clearMoment2KineticCoeff2Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock2Coeff1Norm : {P : Poly // kineticBlock2.coeff 1=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock2.coeff 1=kineticBlock2.coeff 1 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock2,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment2KineticCoeff0Norm.property,clearMoment2KineticCoeff1Norm.property,clearMoment2KineticCoeff2Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment2KineticCoeff0Norm,clearMoment2KineticCoeff1Norm,clearMoment2KineticCoeff2Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock2Coeff2Norm : {P : Poly // kineticBlock2.coeff 2=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock2.coeff 2=kineticBlock2.coeff 2 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock2,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment2KineticCoeff0Norm.property,clearMoment2KineticCoeff1Norm.property,clearMoment2KineticCoeff2Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment2KineticCoeff0Norm,clearMoment2KineticCoeff1Norm,clearMoment2KineticCoeff2Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticBlock2Coeff3Norm : {P : Poly // kineticBlock2.coeff 3=P} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have he : kineticBlock2.coeff 3=kineticBlock2.coeff 3 := rfl
  conv at he =>
    rhs
    simp only [kineticBlock2,kineticBlockTerm,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
    norm_num only
    simp only [clearMoment2KineticCoeff0Norm.property,clearMoment2KineticCoeff1Norm.property,clearMoment2KineticCoeff2Norm.property]
    norm_num [kineticSlopeUp,kineticUp,kineticStay,kineticDown,clearMoment2KineticCoeff0Norm,clearMoment2KineticCoeff1Norm,clearMoment2KineticCoeff2Norm,pderiv_X,Pi.single_apply,hUK,hKU]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
