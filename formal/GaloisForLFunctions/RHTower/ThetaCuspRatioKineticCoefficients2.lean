import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockMoments
/-! Complete kinetic coefficient decomposition; every literal source term is retained. -/
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment2Part0KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((0+0)/2)*(1152) else 0)) + (((if 0=d then (X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((0+0)/2)*(-1620) else 0)) + ((if 1=d then (X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((1+1)/2)*(1440) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((2+0)/2)*(-12) else 0)) + (((if 2=d then (X Coord.U : Poly)^(3-1)*(X Coord.K : Poly)^((0+2)/2)*(-5184) else 0)) + ((if 0=d then (X Coord.U : Poly)^(3-2)*(X Coord.K : Poly)^((0+0)/2)*(-31104) else 0))))) + ((((if 1=d then (X Coord.U : Poly)^(3-2)*(X Coord.K : Poly)^((1+1)/2)*(8640) else 0)) + (((if 0=d then (X Coord.U : Poly)^(3-2)*(X Coord.K : Poly)^((2+0)/2)*(576) else 0)) + ((if 0=d then (X Coord.U : Poly)^(3-3)*(X Coord.K : Poly)^((0+0)/2)*(-3888) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(3-3)*(X Coord.K : Poly)^((2+0)/2)*(-3024) else 0)) + (((if 1=d then (X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((1+1)/2)*(-480) else 0)) + ((if 2=d then (X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((0+2)/2)*(-1728) else 0))))))

theorem clearMoment2Part0_kinetic : clearMoment2Part0=
    ((X Coord.J)^0*clearMoment2Part0KineticCoeff 0 + ((X Coord.J)^1*clearMoment2Part0KineticCoeff 1 + (X Coord.J)^2*clearMoment2Part0KineticCoeff 2)) := by
  norm_num [clearMoment2Part0,clearMoment2Part0KineticCoeff]
  ring

def clearMoment2Part1KineticCoeff (d : ℕ) : Poly := ((if 0=d then (X Coord.U : Poly)^(3-0)*(X Coord.K : Poly)^((0+0)/2)*(0) else 0))

theorem clearMoment2Part1_kinetic : clearMoment2Part1=
    ((X Coord.J)^0*clearMoment2Part1KineticCoeff 0 + ((X Coord.J)^1*clearMoment2Part1KineticCoeff 1 + (X Coord.J)^2*clearMoment2Part1KineticCoeff 2)) := by
  norm_num [clearMoment2Part1,clearMoment2Part1KineticCoeff]

def clearMoment2KineticCoeff0 : Poly := ((clearMoment2Part0KineticCoeff 0) + (clearMoment2Part1KineticCoeff 0))

def clearMoment2KineticCoeff1 : Poly := ((clearMoment2Part0KineticCoeff 1) + (clearMoment2Part1KineticCoeff 1))

def clearMoment2KineticCoeff2 : Poly := ((clearMoment2Part0KineticCoeff 2) + (clearMoment2Part1KineticCoeff 2))

theorem clearMoment2_kinetic : clearMoment2=
    ((X Coord.J)^0*clearMoment2KineticCoeff0 + ((X Coord.J)^1*clearMoment2KineticCoeff1 + (X Coord.J)^2*clearMoment2KineticCoeff2)) := by
  simp only [clearMoment2,clearMoment2KineticCoeff0,clearMoment2KineticCoeff1,clearMoment2KineticCoeff2,clearMoment2Part0_kinetic,clearMoment2Part1_kinetic]
  ring

def clearMoment2KineticCoeff0Norm : {P : Poly // clearMoment2KineticCoeff0=P} := by
  have he : clearMoment2KineticCoeff0=clearMoment2KineticCoeff0 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment2KineticCoeff0,clearMoment2Part0KineticCoeff,clearMoment2Part1KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment2KineticCoeff1Norm : {P : Poly // clearMoment2KineticCoeff1=P} := by
  have he : clearMoment2KineticCoeff1=clearMoment2KineticCoeff1 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment2KineticCoeff1,clearMoment2Part0KineticCoeff,clearMoment2Part1KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment2KineticCoeff2Norm : {P : Poly // clearMoment2KineticCoeff2=P} := by
  have he : clearMoment2KineticCoeff2=clearMoment2KineticCoeff2 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment2KineticCoeff2,clearMoment2Part0KineticCoeff,clearMoment2Part1KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem clearMoment2KineticCoeff0_noJ : pderiv Coord.J clearMoment2KineticCoeff0=0 := by
  rw [clearMoment2KineticCoeff0Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment2KineticCoeff0Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment2KineticCoeff1_noJ : pderiv Coord.J clearMoment2KineticCoeff1=0 := by
  rw [clearMoment2KineticCoeff1Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment2KineticCoeff1Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment2KineticCoeff2_noJ : pderiv Coord.J clearMoment2KineticCoeff2=0 := by
  rw [clearMoment2KineticCoeff2Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment2KineticCoeff2Norm,pderiv_X,Pi.single_apply,hJU,hJK]

end
end HTGeometry.ThetaRatioKineticContraction
