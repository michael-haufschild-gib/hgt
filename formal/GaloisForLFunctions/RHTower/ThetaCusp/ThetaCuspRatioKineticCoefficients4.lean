import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoments
/-! Complete kinetic coefficient decomposition; every literal source term is retained. -/
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment4Part0KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+0)/2)*(819072) else 0)) + (((if 0=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((0+0)/2)*(20481984) else 0)) + ((if 1=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((1+1)/2)*(-6697728) else 0)))) + (((if 1=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((3+1)/2)*(158976) else 0)) + (((if 2=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((0+2)/2)*(11524032) else 0)) + ((if 2=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((2+2)/2)*(502848) else 0))))) + ((((if 3=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((1+3)/2)*(-373248) else 0)) + (((if 4=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((0+4)/2)*(-746496) else 0)) + ((if 0=d then (X Coord.U : Poly)^(5-1)*(X Coord.K : Poly)^((2+0)/2)*(-312768) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((0+0)/2)*(70368912) else 0)) + (((if 1=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((1+1)/2)*(-24603264) else 0)) + ((if 1=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((3+1)/2)*(10368) else 0))))))

theorem clearMoment4Part0_kinetic : clearMoment4Part0=
    (((X Coord.J)^0*clearMoment4Part0KineticCoeff 0 + (X Coord.J)^1*clearMoment4Part0KineticCoeff 1) + ((X Coord.J)^2*clearMoment4Part0KineticCoeff 2 + ((X Coord.J)^3*clearMoment4Part0KineticCoeff 3 + (X Coord.J)^4*clearMoment4Part0KineticCoeff 4))) := by
  norm_num [clearMoment4Part0,clearMoment4Part0KineticCoeff]
  ring

def clearMoment4Part1KineticCoeff (d : ℕ) : Poly := (((((if 2=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((0+2)/2)*(559872) else 0)) + (((if 2=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((2+2)/2)*(2177280) else 0)) + ((if 3=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((1+3)/2)*(2239488) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((2+0)/2)*(-609120) else 0)) + (((if 0=d then (X Coord.U : Poly)^(5-2)*(X Coord.K : Poly)^((4+0)/2)*(23760) else 0)) + ((if 0=d then (X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((0+0)/2)*(25894080) else 0))))) + ((((if 1=d then (X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((1+1)/2)*(-4478976) else 0)) + (((if 1=d then (X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((3+1)/2)*(-1866240) else 0)) + ((if 2=d then (X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((0+2)/2)*(1679616) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((2+2)/2)*(-2426112) else 0)) + (((if 0=d then (X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((2+0)/2)*(10435392) else 0)) + ((if 0=d then (X Coord.U : Poly)^(5-3)*(X Coord.K : Poly)^((4+0)/2)*(-165888) else 0))))))

theorem clearMoment4Part1_kinetic : clearMoment4Part1=
    (((X Coord.J)^0*clearMoment4Part1KineticCoeff 0 + (X Coord.J)^1*clearMoment4Part1KineticCoeff 1) + ((X Coord.J)^2*clearMoment4Part1KineticCoeff 2 + ((X Coord.J)^3*clearMoment4Part1KineticCoeff 3 + (X Coord.J)^4*clearMoment4Part1KineticCoeff 4))) := by
  norm_num [clearMoment4Part1,clearMoment4Part1KineticCoeff]
  ring

def clearMoment4Part2KineticCoeff (d : ℕ) : Poly := (((((if 0=d then (X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((0+0)/2)*(11337408) else 0)) + (((if 1=d then (X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((1+1)/2)*(-3359232) else 0)) + ((if 1=d then (X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((3+1)/2)*(1119744) else 0)))) + (((if 0=d then (X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((2+0)/2)*(1399680) else 0)) + (((if 0=d then (X Coord.U : Poly)^(5-4)*(X Coord.K : Poly)^((4+0)/2)*(451008) else 0)) + ((if 0=d then (X Coord.U : Poly)^(5-5)*(X Coord.K : Poly)^((2+0)/2)*(1679616) else 0))))) + ((((if 0=d then (X Coord.U : Poly)^(5-5)*(X Coord.K : Poly)^((4+0)/2)*(-186624) else 0)) + (((if 1=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((1+1)/2)*(376704) else 0)) + ((if 1=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((3+1)/2)*(-31104) else 0)))) + (((if 2=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+2)/2)*(3841344) else 0)) + (((if 2=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((2+2)/2)*(-164160) else 0)) + ((if 3=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((1+3)/2)*(-373248) else 0))))))

theorem clearMoment4Part2_kinetic : clearMoment4Part2=
    (((X Coord.J)^0*clearMoment4Part2KineticCoeff 0 + (X Coord.J)^1*clearMoment4Part2KineticCoeff 1) + ((X Coord.J)^2*clearMoment4Part2KineticCoeff 2 + ((X Coord.J)^3*clearMoment4Part2KineticCoeff 3 + (X Coord.J)^4*clearMoment4Part2KineticCoeff 4))) := by
  norm_num [clearMoment4Part2,clearMoment4Part2KineticCoeff]
  ring

def clearMoment4Part3KineticCoeff (d : ℕ) : Poly := (((if 4=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+4)/2)*(-248832) else 0)) + (((if 0=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((2+0)/2)*(93312) else 0)) + ((if 0=d then (X Coord.U : Poly)^(5-0)*(X Coord.K : Poly)^((0+0)/2)*(0) else 0))))

theorem clearMoment4Part3_kinetic : clearMoment4Part3=
    (((X Coord.J)^0*clearMoment4Part3KineticCoeff 0 + (X Coord.J)^1*clearMoment4Part3KineticCoeff 1) + ((X Coord.J)^2*clearMoment4Part3KineticCoeff 2 + ((X Coord.J)^3*clearMoment4Part3KineticCoeff 3 + (X Coord.J)^4*clearMoment4Part3KineticCoeff 4))) := by
  norm_num [clearMoment4Part3,clearMoment4Part3KineticCoeff]
  ring

def clearMoment4KineticCoeff0 : Poly := (((clearMoment4Part0KineticCoeff 0) + (clearMoment4Part1KineticCoeff 0)) + ((clearMoment4Part2KineticCoeff 0) + (clearMoment4Part3KineticCoeff 0)))

def clearMoment4KineticCoeff1 : Poly := (((clearMoment4Part0KineticCoeff 1) + (clearMoment4Part1KineticCoeff 1)) + ((clearMoment4Part2KineticCoeff 1) + (clearMoment4Part3KineticCoeff 1)))

def clearMoment4KineticCoeff2 : Poly := (((clearMoment4Part0KineticCoeff 2) + (clearMoment4Part1KineticCoeff 2)) + ((clearMoment4Part2KineticCoeff 2) + (clearMoment4Part3KineticCoeff 2)))

def clearMoment4KineticCoeff3 : Poly := (((clearMoment4Part0KineticCoeff 3) + (clearMoment4Part1KineticCoeff 3)) + ((clearMoment4Part2KineticCoeff 3) + (clearMoment4Part3KineticCoeff 3)))

def clearMoment4KineticCoeff4 : Poly := (((clearMoment4Part0KineticCoeff 4) + (clearMoment4Part1KineticCoeff 4)) + ((clearMoment4Part2KineticCoeff 4) + (clearMoment4Part3KineticCoeff 4)))

theorem clearMoment4_kinetic : clearMoment4=
    (((X Coord.J)^0*clearMoment4KineticCoeff0 + (X Coord.J)^1*clearMoment4KineticCoeff1) + ((X Coord.J)^2*clearMoment4KineticCoeff2 + ((X Coord.J)^3*clearMoment4KineticCoeff3 + (X Coord.J)^4*clearMoment4KineticCoeff4))) := by
  simp only [clearMoment4,clearMoment4KineticCoeff0,clearMoment4KineticCoeff1,clearMoment4KineticCoeff2,clearMoment4KineticCoeff3,clearMoment4KineticCoeff4,clearMoment4Part0_kinetic,clearMoment4Part1_kinetic,clearMoment4Part2_kinetic,clearMoment4Part3_kinetic]
  ring

def clearMoment4KineticCoeff0Norm : {P : Poly // clearMoment4KineticCoeff0=P} := by
  have he : clearMoment4KineticCoeff0=clearMoment4KineticCoeff0 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment4KineticCoeff0,clearMoment4Part0KineticCoeff,clearMoment4Part1KineticCoeff,clearMoment4Part2KineticCoeff,clearMoment4Part3KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment4KineticCoeff1Norm : {P : Poly // clearMoment4KineticCoeff1=P} := by
  have he : clearMoment4KineticCoeff1=clearMoment4KineticCoeff1 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment4KineticCoeff1,clearMoment4Part0KineticCoeff,clearMoment4Part1KineticCoeff,clearMoment4Part2KineticCoeff,clearMoment4Part3KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment4KineticCoeff2Norm : {P : Poly // clearMoment4KineticCoeff2=P} := by
  have he : clearMoment4KineticCoeff2=clearMoment4KineticCoeff2 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment4KineticCoeff2,clearMoment4Part0KineticCoeff,clearMoment4Part1KineticCoeff,clearMoment4Part2KineticCoeff,clearMoment4Part3KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment4KineticCoeff3Norm : {P : Poly // clearMoment4KineticCoeff3=P} := by
  have he : clearMoment4KineticCoeff3=clearMoment4KineticCoeff3 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment4KineticCoeff3,clearMoment4Part0KineticCoeff,clearMoment4Part1KineticCoeff,clearMoment4Part2KineticCoeff,clearMoment4Part3KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment4KineticCoeff4Norm : {P : Poly // clearMoment4KineticCoeff4=P} := by
  have he : clearMoment4KineticCoeff4=clearMoment4KineticCoeff4 := rfl
  conv at he =>
    rhs
    norm_num [clearMoment4KineticCoeff4,clearMoment4Part0KineticCoeff,clearMoment4Part1KineticCoeff,clearMoment4Part2KineticCoeff,clearMoment4Part3KineticCoeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem clearMoment4KineticCoeff0_noJ : pderiv Coord.J clearMoment4KineticCoeff0=0 := by
  rw [clearMoment4KineticCoeff0Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment4KineticCoeff0Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment4KineticCoeff1_noJ : pderiv Coord.J clearMoment4KineticCoeff1=0 := by
  rw [clearMoment4KineticCoeff1Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment4KineticCoeff1Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment4KineticCoeff2_noJ : pderiv Coord.J clearMoment4KineticCoeff2=0 := by
  rw [clearMoment4KineticCoeff2Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment4KineticCoeff2Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment4KineticCoeff3_noJ : pderiv Coord.J clearMoment4KineticCoeff3=0 := by
  rw [clearMoment4KineticCoeff3Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment4KineticCoeff3Norm,pderiv_X,Pi.single_apply,hJU,hJK]

theorem clearMoment4KineticCoeff4_noJ : pderiv Coord.J clearMoment4KineticCoeff4=0 := by
  rw [clearMoment4KineticCoeff4Norm.property]
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  norm_num [clearMoment4KineticCoeff4Norm,pderiv_X,Pi.single_apply,hJU,hJK]

end
end HTGeometry.ThetaRatioKineticContraction
