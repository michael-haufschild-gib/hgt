import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioSquareMoments
/-! # Exact coefficients in the squared drift for the full third-slope sign problem. -/

namespace HTGeometry.ThetaRatioSquare
noncomputable section
open MvPolynomial ThetaRatioSource

def moment2Part0Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(1152) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-1620) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(1440) else 0))) + ((if (2+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-12) else 0) + ((if (0+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(-5184) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-31104) else 0)))) + (((if (1+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(8640) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(576) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-3888) else 0))) + ((if (2+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-3024) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-480) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-1728) else 0)))))

theorem moment2Part0_coeffs : moment2Part0=((X Coord.U)^0*moment2Part0Coeff 0 + (X Coord.U)^1*moment2Part0Coeff 1) := by
  norm_num [moment2Part0,moment2Part0Coeff] <;> ring

def moment2Part1Coeff (d : ℕ) : Poly := (if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(0) else 0)

theorem moment2Part1_coeffs : moment2Part1=((X Coord.U)^0*moment2Part1Coeff 0 + (X Coord.U)^1*moment2Part1Coeff 1) := by
  norm_num [moment2Part1,moment2Part1Coeff] <;> ring

def moment2Coeff0 : Poly := ((moment2Part0Coeff 0) + (moment2Part1Coeff 0))

def moment2Coeff1 : Poly := ((moment2Part0Coeff 1) + (moment2Part1Coeff 1))

theorem moment2_coeffs : moment2=((X Coord.U)^0*moment2Coeff0 + (X Coord.U)^1*moment2Coeff1) := by
  simp only [moment2,moment2Coeff0,moment2Coeff1,moment2Part0_coeffs,moment2Part1_coeffs]
  ring

def moment2Coeff0Norm : {P : Poly // moment2Coeff0=P} := by
  have h : moment2Coeff0=moment2Coeff0 := rfl
  conv at h =>
    rhs
    norm_num [moment2Coeff0,moment2Part0Coeff,moment2Part1Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment2Coeff1Norm : {P : Poly // moment2Coeff1=P} := by
  have h : moment2Coeff1=moment2Coeff1 := rfl
  conv at h =>
    rhs
    norm_num [moment2Coeff1,moment2Part0Coeff,moment2Part1Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩


def moment4Part0Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(819072) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(20481984) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(-6697728) else 0))) + ((if (3+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(158976) else 0) + ((if (0+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(11524032) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(502848) else 0)))) + (((if (1+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(-373248) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(-746496) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-312768) else 0))) + ((if (0+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(70368912) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(-24603264) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(10368) else 0)))))

theorem moment4Part0_coeffs : moment4Part0=((X Coord.U)^0*moment4Part0Coeff 0 + ((X Coord.U)^1*moment4Part0Coeff 1 + (X Coord.U)^2*moment4Part0Coeff 2)) := by
  norm_num [moment4Part0,moment4Part0Coeff] <;> ring

def moment4Part1Coeff (d : ℕ) : Poly := ((((if (0+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(559872) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(2177280) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(2239488) else 0))) + ((if (2+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-609120) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(23760) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(25894080) else 0)))) + (((if (1+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(-4478976) else 0) + ((if (3+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(-1866240) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(1679616) else 0))) + ((if (2+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(-2426112) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(10435392) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-165888) else 0)))))

theorem moment4Part1_coeffs : moment4Part1=((X Coord.U)^0*moment4Part1Coeff 0 + ((X Coord.U)^1*moment4Part1Coeff 1 + (X Coord.U)^2*moment4Part1Coeff 2)) := by
  norm_num [moment4Part1,moment4Part1Coeff] <;> ring

def moment4Part2Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(11337408) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(-3359232) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(1119744) else 0))) + ((if (2+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(1399680) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(451008) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(1679616) else 0)))) + (((if (4+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-186624) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(376704) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-31104) else 0))) + ((if (0+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(3841344) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-164160) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(-373248) else 0)))))

theorem moment4Part2_coeffs : moment4Part2=((X Coord.U)^0*moment4Part2Coeff 0 + ((X Coord.U)^1*moment4Part2Coeff 1 + (X Coord.U)^2*moment4Part2Coeff 2)) := by
  norm_num [moment4Part2,moment4Part2Coeff] <;> ring

def moment4Part3Coeff (d : ℕ) : Poly := ((if (0+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(-248832) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(93312) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(0) else 0)))

theorem moment4Part3_coeffs : moment4Part3=((X Coord.U)^0*moment4Part3Coeff 0 + ((X Coord.U)^1*moment4Part3Coeff 1 + (X Coord.U)^2*moment4Part3Coeff 2)) := by
  norm_num [moment4Part3,moment4Part3Coeff] <;> ring

def moment4Coeff0 : Poly := (((moment4Part0Coeff 0) + (moment4Part1Coeff 0)) + ((moment4Part2Coeff 0) + (moment4Part3Coeff 0)))

def moment4Coeff1 : Poly := (((moment4Part0Coeff 1) + (moment4Part1Coeff 1)) + ((moment4Part2Coeff 1) + (moment4Part3Coeff 1)))

def moment4Coeff2 : Poly := (((moment4Part0Coeff 2) + (moment4Part1Coeff 2)) + ((moment4Part2Coeff 2) + (moment4Part3Coeff 2)))

theorem moment4_coeffs : moment4=((X Coord.U)^0*moment4Coeff0 + ((X Coord.U)^1*moment4Coeff1 + (X Coord.U)^2*moment4Coeff2)) := by
  simp only [moment4,moment4Coeff0,moment4Coeff1,moment4Coeff2,moment4Part0_coeffs,moment4Part1_coeffs,moment4Part2_coeffs,moment4Part3_coeffs]
  ring

def moment4Coeff0Norm : {P : Poly // moment4Coeff0=P} := by
  have h : moment4Coeff0=moment4Coeff0 := rfl
  conv at h =>
    rhs
    norm_num [moment4Coeff0,moment4Part0Coeff,moment4Part1Coeff,moment4Part2Coeff,moment4Part3Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment4Coeff1Norm : {P : Poly // moment4Coeff1=P} := by
  have h : moment4Coeff1=moment4Coeff1 := rfl
  conv at h =>
    rhs
    norm_num [moment4Coeff1,moment4Part0Coeff,moment4Part1Coeff,moment4Part2Coeff,moment4Part3Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment4Coeff2Norm : {P : Poly // moment4Coeff2=P} := by
  have h : moment4Coeff2=moment4Coeff2 := rfl
  conv at h =>
    rhs
    norm_num [moment4Coeff2,moment4Part0Coeff,moment4Part1Coeff,moment4Part2Coeff,moment4Part3Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩


def moment6Part0Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(-8338360320) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-90870584832) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(31536096768) else 0))) + ((if (3+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(-934861824) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(21026304) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(-32045393664) else 0)))) + (((if (2+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(-4303176192) else 0) + ((if (4+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(149154048) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(3321160704) else 0))) + ((if (3+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(377478144) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(4911197184) else 0) + (if (2+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(-127650816) else 0)))))

theorem moment6Part0_coeffs : moment6Part0=(((X Coord.U)^0*moment6Part0Coeff 0 + (X Coord.U)^1*moment6Part0Coeff 1) + ((X Coord.U)^2*moment6Part0Coeff 2 + (X Coord.U)^3*moment6Part0Coeff 3)) := by
  norm_num [moment6Part0,moment6Part0Coeff] <;> ring

def moment6Part1Coeff (d : ℕ) : Poly := ((((if (1+5)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^5*(-232906752) else 0) + ((if (0+6)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^6*(-107495424) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(1239681024) else 0))) + ((if (4+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-54120960) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-262125911808) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(98870035968) else 0)))) + (((if (3+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(1579585536) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(-73446912) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(-6505152768) else 0))) + ((if (2+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(-17677398528) else 0) + ((if (4+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(-85536000) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(-11663253504) else 0)))))

theorem moment6Part1_coeffs : moment6Part1=(((X Coord.U)^0*moment6Part1Coeff 0 + (X Coord.U)^1*moment6Part1Coeff 1) + ((X Coord.U)^2*moment6Part1Coeff 2 + (X Coord.U)^3*moment6Part1Coeff 3)) := by
  norm_num [moment6Part1,moment6Part1Coeff] <;> ring

def moment6Part2Coeff (d : ℕ) : Poly := ((((if (3+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(1206337536) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(886837248) else 0) + (if (2+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(1155575808) else 0))) + ((if (1+5)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^5*(537477120) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-5641643520) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(110419200) else 0)))) + (((if (6+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(1492992) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-203900763456) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(50993141760) else 0))) + ((if (3+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(15311379456) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(-151041024) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(-16144468992) else 0)))))

theorem moment6Part2_coeffs : moment6Part2=(((X Coord.U)^0*moment6Part2Coeff 0 + (X Coord.U)^1*moment6Part2Coeff 1) + ((X Coord.U)^2*moment6Part2Coeff 2 + (X Coord.U)^3*moment6Part2Coeff 3)) := by
  norm_num [moment6Part2,moment6Part2Coeff] <;> ring

def moment6Part3Coeff (d : ℕ) : Poly := ((((if (2+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(7874039808) else 0) + ((if (4+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(-1541514240) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(-1370566656) else 0))) + ((if (3+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(-1818464256) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(241864704) else 0) + (if (2+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(-1101828096) else 0)))) + (((if (2+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-47910346560) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(1067535936) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-18035136) else 0))) + ((if (0+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-122353307136) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(39484412928) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(-2002102272) else 0)))))

theorem moment6Part3_coeffs : moment6Part3=(((X Coord.U)^0*moment6Part3Coeff 0 + (X Coord.U)^1*moment6Part3Coeff 1) + ((X Coord.U)^2*moment6Part3Coeff 2 + (X Coord.U)^3*moment6Part3Coeff 3)) := by
  norm_num [moment6Part3,moment6Part3Coeff] <;> ring

def moment6Part4Coeff (d : ℕ) : Poly := ((((if (5+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(750228480) else 0) + ((if (0+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-3083774976) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-524040192) else 0))) + ((if (4+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(1350411264) else 0) + ((if (1+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(-967458816) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(1182449664) else 0)))) + (((if (2+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-15444069120) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-4425228288) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(93747456) else 0))) + ((if (0+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(952342272) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(6167549952) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(1612431360) else 0)))))

theorem moment6Part4_coeffs : moment6Part4=(((X Coord.U)^0*moment6Part4Coeff 0 + (X Coord.U)^1*moment6Part4Coeff 1) + ((X Coord.U)^2*moment6Part4Coeff 2 + (X Coord.U)^3*moment6Part4Coeff 3)) := by
  norm_num [moment6Part4,moment6Part4Coeff] <;> ring

def moment6Part5Coeff (d : ℕ) : Poly := ((((if (5+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(-488208384) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(1451188224) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(-698720256) else 0))) + ((if (2+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-23657391360) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(915390720) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-151352064) else 0)))) + (((if (3+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(-967458816) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(214990848) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(-3083774976) else 0))) + ((if (4+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(-604661760) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(69424128) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(241864704) else 0)))))

theorem moment6Part5_coeffs : moment6Part5=(((X Coord.U)^0*moment6Part5Coeff 0 + (X Coord.U)^1*moment6Part5Coeff 1) + ((X Coord.U)^2*moment6Part5Coeff 2 + (X Coord.U)^3*moment6Part5Coeff 3)) := by
  norm_num [moment6Part5,moment6Part5Coeff] <;> ring

def moment6Part6Coeff (d : ℕ) : Poly := ((((if (6+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(-26873856) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(953026560) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(112637952) else 0))) + ((if (5+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-1990656) else 0) + ((if (0+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-10518875136) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(833836032) else 0)))) + (((if (4+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-17418240) else 0) + ((if (1+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(2364152832) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(-90160128) else 0))) + ((if (0+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(1547486208) else 0) + ((if (2+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(-211756032) else 0) + (if (1+5)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^5*(-137355264) else 0)))))

theorem moment6Part6_coeffs : moment6Part6=(((X Coord.U)^0*moment6Part6Coeff 0 + (X Coord.U)^1*moment6Part6Coeff 1) + ((X Coord.U)^2*moment6Part6Coeff 2 + (X Coord.U)^3*moment6Part6Coeff 3)) := by
  norm_num [moment6Part6,moment6Part6Coeff] <;> ring

def moment6Part7Coeff (d : ℕ) : Poly := (((if (0+6)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^6*(-35831808) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(-167712768) else 0)) + ((if (4+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(5971968) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(0) else 0)))

theorem moment6Part7_coeffs : moment6Part7=(((X Coord.U)^0*moment6Part7Coeff 0 + (X Coord.U)^1*moment6Part7Coeff 1) + ((X Coord.U)^2*moment6Part7Coeff 2 + (X Coord.U)^3*moment6Part7Coeff 3)) := by
  norm_num [moment6Part7,moment6Part7Coeff] <;> ring

def moment6Coeff0 : Poly := ((((moment6Part0Coeff 0) + (moment6Part1Coeff 0)) + ((moment6Part2Coeff 0) + (moment6Part3Coeff 0))) + (((moment6Part4Coeff 0) + (moment6Part5Coeff 0)) + ((moment6Part6Coeff 0) + (moment6Part7Coeff 0))))

def moment6Coeff1 : Poly := ((((moment6Part0Coeff 1) + (moment6Part1Coeff 1)) + ((moment6Part2Coeff 1) + (moment6Part3Coeff 1))) + (((moment6Part4Coeff 1) + (moment6Part5Coeff 1)) + ((moment6Part6Coeff 1) + (moment6Part7Coeff 1))))

def moment6Coeff2 : Poly := ((((moment6Part0Coeff 2) + (moment6Part1Coeff 2)) + ((moment6Part2Coeff 2) + (moment6Part3Coeff 2))) + (((moment6Part4Coeff 2) + (moment6Part5Coeff 2)) + ((moment6Part6Coeff 2) + (moment6Part7Coeff 2))))

def moment6Coeff3 : Poly := ((((moment6Part0Coeff 3) + (moment6Part1Coeff 3)) + ((moment6Part2Coeff 3) + (moment6Part3Coeff 3))) + (((moment6Part4Coeff 3) + (moment6Part5Coeff 3)) + ((moment6Part6Coeff 3) + (moment6Part7Coeff 3))))

theorem moment6_coeffs : moment6=(((X Coord.U)^0*moment6Coeff0 + (X Coord.U)^1*moment6Coeff1) + ((X Coord.U)^2*moment6Coeff2 + (X Coord.U)^3*moment6Coeff3)) := by
  simp only [moment6,moment6Coeff0,moment6Coeff1,moment6Coeff2,moment6Coeff3,moment6Part0_coeffs,moment6Part1_coeffs,moment6Part2_coeffs,moment6Part3_coeffs,moment6Part4_coeffs,moment6Part5_coeffs,moment6Part6_coeffs,moment6Part7_coeffs]
  ring

def moment6Coeff0Norm : {P : Poly // moment6Coeff0=P} := by
  have h : moment6Coeff0=moment6Coeff0 := rfl
  conv at h =>
    rhs
    norm_num [moment6Coeff0,moment6Part0Coeff,moment6Part1Coeff,moment6Part2Coeff,moment6Part3Coeff,moment6Part4Coeff,moment6Part5Coeff,moment6Part6Coeff,moment6Part7Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment6Coeff1Norm : {P : Poly // moment6Coeff1=P} := by
  have h : moment6Coeff1=moment6Coeff1 := rfl
  conv at h =>
    rhs
    norm_num [moment6Coeff1,moment6Part0Coeff,moment6Part1Coeff,moment6Part2Coeff,moment6Part3Coeff,moment6Part4Coeff,moment6Part5Coeff,moment6Part6Coeff,moment6Part7Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment6Coeff2Norm : {P : Poly // moment6Coeff2=P} := by
  have h : moment6Coeff2=moment6Coeff2 := rfl
  conv at h =>
    rhs
    norm_num [moment6Coeff2,moment6Part0Coeff,moment6Part1Coeff,moment6Part2Coeff,moment6Part3Coeff,moment6Part4Coeff,moment6Part5Coeff,moment6Part6Coeff,moment6Part7Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment6Coeff3Norm : {P : Poly // moment6Coeff3=P} := by
  have h : moment6Coeff3=moment6Coeff3 := rfl
  conv at h =>
    rhs
    norm_num [moment6Coeff3,moment6Part0Coeff,moment6Part1Coeff,moment6Part2Coeff,moment6Part3Coeff,moment6Part4Coeff,moment6Part5Coeff,moment6Part6Coeff,moment6Part7Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩


def moment8Part0Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(48721763450880) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(465200636755968) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(-208222828609536) else 0))) + ((if (3+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(4892833382400) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(-196203036672) else 0) + (if (7+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(2516189184) else 0)))) + (((if (0+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(106607673040896) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(39495108722688) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(-1766119956480) else 0))) + ((if (6+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(28747726848) else 0) + ((if (1+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(-30631036059648) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(-4672396099584) else 0)))))

theorem moment8Part0_coeffs : moment8Part0=(((X Coord.U)^0*moment8Part0Coeff 0 + (X Coord.U)^1*moment8Part0Coeff 1) + ((X Coord.U)^2*moment8Part0Coeff 2 + ((X Coord.U)^3*moment8Part0Coeff 3 + (X Coord.U)^4*moment8Part0Coeff 4))) := by
  norm_num [moment8Part0,moment8Part0Coeff] <;> ring

def moment8Part1Coeff (d : ℕ) : Poly := ((((if (5+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(175615672320) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(-32021435621376) else 0) + (if (2+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(3499943510016) else 0))) + ((if (4+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(277618876416) else 0) + ((if (1+5)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^5*(3851131060224) else 0) + (if (3+5)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^5*(-19707494400) else 0)))) + (((if (0+6)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^6*(1500528623616) else 0) + ((if (2+6)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^6*(-133186830336) else 0) + (if (1+7)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^7*(-79976595456) else 0))) + ((if (0+8)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^8*(-15479341056) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-5043506135040) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(280455561216) else 0)))))

theorem moment8Part1_coeffs : moment8Part1=(((X Coord.U)^0*moment8Part1Coeff 0 + (X Coord.U)^1*moment8Part1Coeff 1) + ((X Coord.U)^2*moment8Part1Coeff 2 + ((X Coord.U)^3*moment8Part1Coeff 3 + (X Coord.U)^4*moment8Part1Coeff 4))) := by
  norm_num [moment8Part1,moment8Part1Coeff] <;> ring

def moment8Part2Coeff (d : ℕ) : Poly := ((((if (6+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-6975258624) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(1390654809612288) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(-653518510829568) else 0))) + ((if (3+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(-15706344517632) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(943376855040) else 0) + (if (7+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(-18251993088) else 0)))) + (((if (0+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(9961318766592) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(161480364963840) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(290179418112) else 0))) + ((if (6+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(-114128787456) else 0) + ((if (1+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(44438285795328) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(-18974447271936) else 0)))))

theorem moment8Part2_coeffs : moment8Part2=(((X Coord.U)^0*moment8Part2Coeff 0 + (X Coord.U)^1*moment8Part2Coeff 1) + ((X Coord.U)^2*moment8Part2Coeff 2 + ((X Coord.U)^3*moment8Part2Coeff 3 + (X Coord.U)^4*moment8Part2Coeff 4))) := by
  norm_num [moment8Part2,moment8Part2Coeff] <;> ring

def moment8Part3Coeff (d : ℕ) : Poly := ((((if (5+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(-51729186816) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(-13697040052224) else 0) + (if (2+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(-13151151415296) else 0))) + ((if (4+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(909402329088) else 0) + ((if (1+5)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^5*(-5423574122496) else 0) + (if (3+5)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^5*(976703422464) else 0)))) + (((if (0+6)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^6*(336675667968) else 0) + ((if (2+6)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^6*(545646772224) else 0) + (if (1+7)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^7*(108355387392) else 0))) + ((if (2+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(60218694660096) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-1816099356672) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(37381533696) else 0)))))

theorem moment8Part3_coeffs : moment8Part3=(((X Coord.U)^0*moment8Part3Coeff 0 + (X Coord.U)^1*moment8Part3Coeff 1) + ((X Coord.U)^2*moment8Part3Coeff 2 + ((X Coord.U)^3*moment8Part3Coeff 3 + (X Coord.U)^4*moment8Part3Coeff 4))) := by
  norm_num [moment8Part3,moment8Part3Coeff] <;> ring

def moment8Part4Coeff (d : ℕ) : Poly := ((((if (8+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(95551488) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(1594560904169472) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(-616167263969280) else 0))) + ((if (3+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(-114204482150400) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(992594829312) else 0) + (if (7+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(39070605312) else 0)))) + (((if (0+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(43236339148800) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(62404116940800) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(19329491220480) else 0))) + ((if (6+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(-81859258368) else 0) + ((if (1+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(5636415062016) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(14700214222848) else 0)))))

theorem moment8Part4_coeffs : moment8Part4=(((X Coord.U)^0*moment8Part4Coeff 0 + (X Coord.U)^1*moment8Part4Coeff 1) + ((X Coord.U)^2*moment8Part4Coeff 2 + ((X Coord.U)^3*moment8Part4Coeff 3 + (X Coord.U)^4*moment8Part4Coeff 4))) := by
  norm_num [moment8Part4,moment8Part4Coeff] <;> ring

def moment8Part5Coeff (d : ℕ) : Poly := ((((if (5+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(-1588280721408) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(-6765439500288) else 0) + (if (2+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(9166672281600) else 0))) + ((if (4+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(-1954051817472) else 0) + ((if (1+5)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^5*(-1369921683456) else 0) + (if (3+5)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^5*(-1377661353984) else 0)))) + (((if (0+6)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^6*(34828517376) else 0) + ((if (2+6)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^6*(-328935997440) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(304304294430720) else 0))) + ((if (4+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-3709196789760) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(12712826880) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-2030469120) else 0)))))

theorem moment8Part5_coeffs : moment8Part5=(((X Coord.U)^0*moment8Part5Coeff 0 + (X Coord.U)^1*moment8Part5Coeff 1) + ((X Coord.U)^2*moment8Part5Coeff 2 + ((X Coord.U)^3*moment8Part5Coeff 3 + (X Coord.U)^4*moment8Part5Coeff 4))) := by
  norm_num [moment8Part5,moment8Part5Coeff] <;> ring

def moment8Part6Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(1043671487738112) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(-374639477501952) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(-62359251038208) else 0))) + ((if (5+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(-9293006278656) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(118839177216) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-901187887104) else 0)))) + (((if (2+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(65431174643712) else 0) + ((if (4+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-10667684634624) else 0) + (if (6+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(1263071232000) else 0))) + ((if (1+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(16143017803776) else 0) + ((if (3+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(-10015133663232) else 0) + (if (5+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(1932552732672) else 0)))))

theorem moment8Part6_coeffs : moment8Part6=(((X Coord.U)^0*moment8Part6Coeff 0 + (X Coord.U)^1*moment8Part6Coeff 1) + ((X Coord.U)^2*moment8Part6Coeff 2 + ((X Coord.U)^3*moment8Part6Coeff 3 + (X Coord.U)^4*moment8Part6Coeff 4))) := by
  norm_num [moment8Part6,moment8Part6Coeff] <;> ring

def moment8Part7Coeff (d : ℕ) : Poly := ((((if (0+4)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^4*(-914248581120) else 0) + ((if (2+4)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^4*(2002639749120) else 0) + (if (4+4)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^4*(1852683632640) else 0))) + ((if (1+5)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^5*(-208971104256) else 0) + ((if (3+5)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^5*(564995948544) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(267216539010048) else 0)))) + (((if (4+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(30406152273408) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-1095470189568) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(17800632576) else 0))) + ((if (0+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(1258724385792) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(-8567815274496) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(-89526703915008) else 0)))))

theorem moment8Part7_coeffs : moment8Part7=(((X Coord.U)^0*moment8Part7Coeff 0 + (X Coord.U)^1*moment8Part7Coeff 1) + ((X Coord.U)^2*moment8Part7Coeff 2 + ((X Coord.U)^3*moment8Part7Coeff 3 + (X Coord.U)^4*moment8Part7Coeff 4))) := by
  norm_num [moment8Part7,moment8Part7Coeff] <;> ring

def moment8Part8Coeff (d : ℕ) : Poly := ((((if (5+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(7415249338368) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(-582911852544) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(33892500971520) else 0))) + ((if (2+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(-19133916733440) else 0) + ((if (4+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(8028456984576) else 0) + (if (6+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(-1076405428224) else 0)))) + (((if (1+3)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^3*(3656994324480) else 0) + ((if (3+3)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^3*(-1044855521280) else 0) + (if (5+3)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^3*(-1458927894528) else 0))) + ((if (2+4)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^4*(522427760640) else 0) + ((if (4+4)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^4*(-599824465920) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(320229714622464) else 0)))))

theorem moment8Part8_coeffs : moment8Part8=(((X Coord.U)^0*moment8Part8Coeff 0 + (X Coord.U)^1*moment8Part8Coeff 1) + ((X Coord.U)^2*moment8Part8Coeff 2 + ((X Coord.U)^3*moment8Part8Coeff 3 + (X Coord.U)^4*moment8Part8Coeff 4))) := by
  norm_num [moment8Part8,moment8Part8Coeff] <;> ring

def moment8Part9Coeff (d : ℕ) : Poly := ((((if (4+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-8830480343040) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(3199829723136) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-75026580480) else 0))) + ((if (0+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(25140203394048) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(-67785001943040) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(16900538056704) else 0)))) + (((if (5+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(-4563503235072) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(357852266496) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(-5485491486720) else 0))) + ((if (4+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(-232190115840) else 0) + ((if (6+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(676576198656) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^3*(-696570347520) else 0)))))

theorem moment8Part9_coeffs : moment8Part9=(((X Coord.U)^0*moment8Part9Coeff 0 + (X Coord.U)^1*moment8Part9Coeff 1) + ((X Coord.U)^2*moment8Part9Coeff 2 + ((X Coord.U)^3*moment8Part9Coeff 3 + (X Coord.U)^4*moment8Part9Coeff 4))) := by
  norm_num [moment8Part9,moment8Part9Coeff] <;> ring

def moment8Part10Coeff (d : ℕ) : Poly := ((((if (5+3)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^3*(402462867456) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(-1704420569088) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(34018391549952) else 0))) + ((if (6+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(-2749759819776) else 0) + ((if (8+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(139464115200) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(3656994324480) else 0)))) + (((if (5+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(417942208512) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(-171562696704) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^2*(522427760640) else 0))) + ((if (6+2)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^2*(-166402916352) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(33892500971520) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(-7144199626752) else 0)))))

theorem moment8Part10_coeffs : moment8Part10=(((X Coord.U)^0*moment8Part10Coeff 0 + (X Coord.U)^1*moment8Part10Coeff 1) + ((X Coord.U)^2*moment8Part10Coeff 2 + ((X Coord.U)^3*moment8Part10Coeff 3 + (X Coord.U)^4*moment8Part10Coeff 4))) := by
  norm_num [moment8Part10,moment8Part10Coeff] <;> ring

def moment8Part11Coeff (d : ℕ) : Poly := ((((if (6+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(1306553131008) else 0) + ((if (8+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(-64765992960) else 0) + (if (5+1)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^1*(-208971104256) else 0))) + ((if (7+1)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^1*(38698352640) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(-914248581120) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(-110290305024) else 0)))) + (((if (8+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(18381717504) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^0*(34828517376) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^0*(-3869835264) else 0))) + ((if (1+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-14932547665920) else 0) + ((if (3+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-473768165376) else 0) + (if (5+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(18268913664) else 0)))))

theorem moment8Part11_coeffs : moment8Part11=(((X Coord.U)^0*moment8Part11Coeff 0 + (X Coord.U)^1*moment8Part11Coeff 1) + ((X Coord.U)^2*moment8Part11Coeff 2 + ((X Coord.U)^3*moment8Part11Coeff 3 + (X Coord.U)^4*moment8Part11Coeff 4))) := by
  norm_num [moment8Part11,moment8Part11Coeff] <;> ring

def moment8Part12Coeff (d : ℕ) : Poly := ((((if (7+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-127401984) else 0) + ((if (0+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(36181024800768) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-3344970940416) else 0))) + ((if (4+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(260254384128) else 0) + ((if (6+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-1795571712) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(-15123423707136) else 0)))) + (((if (3+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(1215558254592) else 0) + ((if (5+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(-24953536512) else 0) + (if (0+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(-9391203348480) else 0))) + ((if (2+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(2944819224576) else 0) + ((if (4+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(-106218418176) else 0) + (if (1+5)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^5*(1838171750400) else 0)))))

theorem moment8Part12_coeffs : moment8Part12=(((X Coord.U)^0*moment8Part12Coeff 0 + (X Coord.U)^1*moment8Part12Coeff 1) + ((X Coord.U)^2*moment8Part12Coeff 2 + ((X Coord.U)^3*moment8Part12Coeff 3 + (X Coord.U)^4*moment8Part12Coeff 4))) := by
  norm_num [moment8Part12,moment8Part12Coeff] <;> ring

def moment8Part13Coeff (d : ℕ) : Poly := ((((if (3+5)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^5*(-173091520512) else 0) + (if (0+6)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^6*(464057745408) else 0)) + ((if (2+6)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^6*(-117205843968) else 0) + (if (1+7)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^7*(-38698352640) else 0))) + (((if (0+8)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^8*(-5159780352) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(-293964152832) else 0)) + ((if (4+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(-37786632192) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(382205952) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(0) else 0)))))

theorem moment8Part13_coeffs : moment8Part13=(((X Coord.U)^0*moment8Part13Coeff 0 + (X Coord.U)^1*moment8Part13Coeff 1) + ((X Coord.U)^2*moment8Part13Coeff 2 + ((X Coord.U)^3*moment8Part13Coeff 3 + (X Coord.U)^4*moment8Part13Coeff 4))) := by
  norm_num [moment8Part13,moment8Part13Coeff] <;> ring

def moment8Coeff0 : Poly := ((((moment8Part0Coeff 0) + ((moment8Part1Coeff 0) + (moment8Part2Coeff 0))) + (((moment8Part3Coeff 0) + (moment8Part4Coeff 0)) + ((moment8Part5Coeff 0) + (moment8Part6Coeff 0)))) + (((moment8Part7Coeff 0) + ((moment8Part8Coeff 0) + (moment8Part9Coeff 0))) + (((moment8Part10Coeff 0) + (moment8Part11Coeff 0)) + ((moment8Part12Coeff 0) + (moment8Part13Coeff 0)))))

def moment8Coeff1 : Poly := ((((moment8Part0Coeff 1) + ((moment8Part1Coeff 1) + (moment8Part2Coeff 1))) + (((moment8Part3Coeff 1) + (moment8Part4Coeff 1)) + ((moment8Part5Coeff 1) + (moment8Part6Coeff 1)))) + (((moment8Part7Coeff 1) + ((moment8Part8Coeff 1) + (moment8Part9Coeff 1))) + (((moment8Part10Coeff 1) + (moment8Part11Coeff 1)) + ((moment8Part12Coeff 1) + (moment8Part13Coeff 1)))))

def moment8Coeff2 : Poly := ((((moment8Part0Coeff 2) + ((moment8Part1Coeff 2) + (moment8Part2Coeff 2))) + (((moment8Part3Coeff 2) + (moment8Part4Coeff 2)) + ((moment8Part5Coeff 2) + (moment8Part6Coeff 2)))) + (((moment8Part7Coeff 2) + ((moment8Part8Coeff 2) + (moment8Part9Coeff 2))) + (((moment8Part10Coeff 2) + (moment8Part11Coeff 2)) + ((moment8Part12Coeff 2) + (moment8Part13Coeff 2)))))

def moment8Coeff3 : Poly := ((((moment8Part0Coeff 3) + ((moment8Part1Coeff 3) + (moment8Part2Coeff 3))) + (((moment8Part3Coeff 3) + (moment8Part4Coeff 3)) + ((moment8Part5Coeff 3) + (moment8Part6Coeff 3)))) + (((moment8Part7Coeff 3) + ((moment8Part8Coeff 3) + (moment8Part9Coeff 3))) + (((moment8Part10Coeff 3) + (moment8Part11Coeff 3)) + ((moment8Part12Coeff 3) + (moment8Part13Coeff 3)))))

def moment8Coeff4 : Poly := ((((moment8Part0Coeff 4) + ((moment8Part1Coeff 4) + (moment8Part2Coeff 4))) + (((moment8Part3Coeff 4) + (moment8Part4Coeff 4)) + ((moment8Part5Coeff 4) + (moment8Part6Coeff 4)))) + (((moment8Part7Coeff 4) + ((moment8Part8Coeff 4) + (moment8Part9Coeff 4))) + (((moment8Part10Coeff 4) + (moment8Part11Coeff 4)) + ((moment8Part12Coeff 4) + (moment8Part13Coeff 4)))))

theorem moment8_coeffs : moment8=(((X Coord.U)^0*moment8Coeff0 + (X Coord.U)^1*moment8Coeff1) + ((X Coord.U)^2*moment8Coeff2 + ((X Coord.U)^3*moment8Coeff3 + (X Coord.U)^4*moment8Coeff4))) := by
  simp only [moment8,moment8Coeff0,moment8Coeff1,moment8Coeff2,moment8Coeff3,moment8Coeff4,moment8Part0_coeffs,moment8Part1_coeffs,moment8Part2_coeffs,moment8Part3_coeffs,moment8Part4_coeffs,moment8Part5_coeffs,moment8Part6_coeffs,moment8Part7_coeffs,moment8Part8_coeffs,moment8Part9_coeffs,moment8Part10_coeffs,moment8Part11_coeffs,moment8Part12_coeffs,moment8Part13_coeffs]
  ring

def moment8Coeff0Norm : {P : Poly // moment8Coeff0=P} := by
  have h : moment8Coeff0=moment8Coeff0 := rfl
  conv at h =>
    rhs
    norm_num [moment8Coeff0,moment8Part0Coeff,moment8Part1Coeff,moment8Part2Coeff,moment8Part3Coeff,moment8Part4Coeff,moment8Part5Coeff,moment8Part6Coeff,moment8Part7Coeff,moment8Part8Coeff,moment8Part9Coeff,moment8Part10Coeff,moment8Part11Coeff,moment8Part12Coeff,moment8Part13Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment8Coeff1Norm : {P : Poly // moment8Coeff1=P} := by
  have h : moment8Coeff1=moment8Coeff1 := rfl
  conv at h =>
    rhs
    norm_num [moment8Coeff1,moment8Part0Coeff,moment8Part1Coeff,moment8Part2Coeff,moment8Part3Coeff,moment8Part4Coeff,moment8Part5Coeff,moment8Part6Coeff,moment8Part7Coeff,moment8Part8Coeff,moment8Part9Coeff,moment8Part10Coeff,moment8Part11Coeff,moment8Part12Coeff,moment8Part13Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment8Coeff2Norm : {P : Poly // moment8Coeff2=P} := by
  have h : moment8Coeff2=moment8Coeff2 := rfl
  conv at h =>
    rhs
    norm_num [moment8Coeff2,moment8Part0Coeff,moment8Part1Coeff,moment8Part2Coeff,moment8Part3Coeff,moment8Part4Coeff,moment8Part5Coeff,moment8Part6Coeff,moment8Part7Coeff,moment8Part8Coeff,moment8Part9Coeff,moment8Part10Coeff,moment8Part11Coeff,moment8Part12Coeff,moment8Part13Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment8Coeff3Norm : {P : Poly // moment8Coeff3=P} := by
  have h : moment8Coeff3=moment8Coeff3 := rfl
  conv at h =>
    rhs
    norm_num [moment8Coeff3,moment8Part0Coeff,moment8Part1Coeff,moment8Part2Coeff,moment8Part3Coeff,moment8Part4Coeff,moment8Part5Coeff,moment8Part6Coeff,moment8Part7Coeff,moment8Part8Coeff,moment8Part9Coeff,moment8Part10Coeff,moment8Part11Coeff,moment8Part12Coeff,moment8Part13Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment8Coeff4Norm : {P : Poly // moment8Coeff4=P} := by
  have h : moment8Coeff4=moment8Coeff4 := rfl
  conv at h =>
    rhs
    norm_num [moment8Coeff4,moment8Part0Coeff,moment8Part1Coeff,moment8Part2Coeff,moment8Part3Coeff,moment8Part4Coeff,moment8Part5Coeff,moment8Part6Coeff,moment8Part7Coeff,moment8Part8Coeff,moment8Part9Coeff,moment8Part10Coeff,moment8Part11Coeff,moment8Part12Coeff,moment8Part13Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩


def moment10Part0Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(-312165555505201152) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-2936102282906370048) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(1818995586674982912) else 0))) + ((if (3+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(-56594005935390720) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(1534590913609728) else 0) + (if (7+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(-43083242274816) else 0)))) + (((if (9+1)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^1*(266524950528) else 0) + ((if (0+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(-367565196123832320) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(-460966580336590848) else 0))) + ((if (4+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(24334188461752320) else 0) + ((if (6+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(-708382995775488) else 0) + (if (8+2)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^2*(4615386365952) else 0)))))

theorem moment10Part0_coeffs : moment10Part0=(((X Coord.U)^0*moment10Part0Coeff 0 + ((X Coord.U)^1*moment10Part0Coeff 1 + (X Coord.U)^2*moment10Part0Coeff 2)) + ((X Coord.U)^3*moment10Part0Coeff 3 + ((X Coord.U)^4*moment10Part0Coeff 4 + (X Coord.U)^5*moment10Part0Coeff 5))) := by
  norm_num [moment10Part0,moment10Part0Coeff] <;> ring

def moment10Part1Coeff (d : ℕ) : Poly := ((((if (1+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(260607039842746368) else 0) + ((if (3+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(60342327082156032) else 0) + (if (5+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(-4217261764313088) else 0))) + ((if (7+3)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^3*(74382549516288) else 0) + ((if (0+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(207945326055112704) else 0) + (if (2+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(-57642006020308992) else 0)))) + (((if (4+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(-5306918690930688) else 0) + ((if (6+4)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^4*(266907136573440) else 0) + (if (1+5)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^5*(-54580396493242368) else 0))) + ((if (3+5)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^5*(3929776432349184) else 0) + ((if (5+5)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^5*(281445092425728) else 0) + (if (0+6)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^6*(-17956085932818432) else 0)))))

theorem moment10Part1_coeffs : moment10Part1=(((X Coord.U)^0*moment10Part1Coeff 0 + ((X Coord.U)^1*moment10Part1Coeff 1 + (X Coord.U)^2*moment10Part1Coeff 2)) + ((X Coord.U)^3*moment10Part1Coeff 3 + ((X Coord.U)^4*moment10Part1Coeff 4 + (X Coord.U)^5*moment10Part1Coeff 5))) := by
  norm_num [moment10Part1,moment10Part1Coeff] <;> ring

def moment10Part2Coeff (d : ℕ) : Poly := ((((if (2+6)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^6*(4715990223814656) else 0) + ((if (4+6)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^6*(12592873930752) else 0) + (if (1+7)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^7*(2225170756141056) else 0))) + ((if (3+7)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^7*(-94841922650112) else 0) + ((if (0+8)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^8*(386039286595584) else 0) + (if (2+8)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^8*(-73851936178176) else 0)))) + (((if (1+9)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^9*(-21175738564608) else 0) + ((if (0+10)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^10*(-2229025112064) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(61684770355347456) else 0))) + ((if (4+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-197242493534208) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(80341172158464) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^1*(X Coord.J : Poly)^0*(-762883080192) else 0)))))

theorem moment10Part2_coeffs : moment10Part2=(((X Coord.U)^0*moment10Part2Coeff 0 + ((X Coord.U)^1*moment10Part2Coeff 1 + (X Coord.U)^2*moment10Part2Coeff 2)) + ((X Coord.U)^3*moment10Part2Coeff 3 + ((X Coord.U)^4*moment10Part2Coeff 4 + (X Coord.U)^5*moment10Part2Coeff 5))) := by
  norm_num [moment10Part2,moment10Part2Coeff] <;> ring

def moment10Part3Coeff (d : ℕ) : Poly := ((((if (0+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-9455534033560731648) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(6034557931751079936) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(77107829817212928) else 0))) + ((if (5+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(-7239659433099264) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(247320885067776) else 0) + (if (9+1)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^1*(-3329120010240) else 0)))) + (((if (0+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(283490304519241728) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(-1830188307339214848) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(25356104889532416) else 0))) + ((if (6+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(1132149688565760) else 0) + ((if (8+2)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^2*(-27635385434112) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(-183915869383655424) else 0)))))

theorem moment10Part3_coeffs : moment10Part3=(((X Coord.U)^0*moment10Part3Coeff 0 + ((X Coord.U)^1*moment10Part3Coeff 1 + (X Coord.U)^2*moment10Part3Coeff 2)) + ((X Coord.U)^3*moment10Part3Coeff 3 + ((X Coord.U)^4*moment10Part3Coeff 4 + (X Coord.U)^5*moment10Part3Coeff 5))) := by
  norm_num [moment10Part3,moment10Part3Coeff] <;> ring

def moment10Part4Coeff (d : ℕ) : Poly := ((((if (3+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(299556403542392832) else 0) + ((if (5+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(-5141271574904832) else 0) + (if (7+3)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^3*(-100206207074304) else 0))) + ((if (0+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(29860612486004736) else 0) + ((if (2+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(145249023007457280) else 0) + (if (4+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(-30422992425910272) else 0)))) + (((if (6+4)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^4*(244872425963520) else 0) + ((if (1+5)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^5*(32470139150401536) else 0) + (if (3+5)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^5*(-20769282027159552) else 0))) + ((if (5+5)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^5*(1027096417271808) else 0) + ((if (0+6)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^6*(-8705631717752832) else 0) + (if (2+6)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^6*(-10727531636981760) else 0)))))

theorem moment10Part4_coeffs : moment10Part4=(((X Coord.U)^0*moment10Part4Coeff 0 + ((X Coord.U)^1*moment10Part4Coeff 1 + (X Coord.U)^2*moment10Part4Coeff 2)) + ((X Coord.U)^3*moment10Part4Coeff 3 + ((X Coord.U)^4*moment10Part4Coeff 4 + (X Coord.U)^5*moment10Part4Coeff 5))) := by
  norm_num [moment10Part4,moment10Part4Coeff] <;> ring

def moment10Part5Coeff (d : ℕ) : Poly := ((((if (4+6)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^6*(1085108257751040) else 0) + ((if (1+7)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^7*(-1743654893912064) else 0) + (if (3+7)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^7*(661215532548096) else 0))) + ((if (0+8)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^8*(91947285872640) else 0) + ((if (2+8)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^8*(185194836393984) else 0) + (if (1+9)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^9*(20061226008576) else 0)))) + (((if (2+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-412258829129220096) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(19009199682551808) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(-403853428260864) else 0))) + ((if (8+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(7818213851136) else 0) + ((if (10+0)/2=d then (X Coord.K : Poly)^2*(X Coord.J : Poly)^0*(6115295232) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-13150464920064589824) else 0)))))

theorem moment10Part5_coeffs : moment10Part5=(((X Coord.U)^0*moment10Part5Coeff 0 + ((X Coord.U)^1*moment10Part5Coeff 1 + (X Coord.U)^2*moment10Part5Coeff 2)) + ((X Coord.U)^3*moment10Part5Coeff 3 + ((X Coord.U)^4*moment10Part5Coeff 4 + (X Coord.U)^5*moment10Part5Coeff 5))) := by
  norm_num [moment10Part5,moment10Part5Coeff] <;> ring

def moment10Part6Coeff (d : ℕ) : Poly := ((((if (1+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(7490578609634623488) else 0) + ((if (3+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(1074125894882033664) else 0) + (if (5+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(-15869968032301056) else 0))) + ((if (7+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(-691019570479104) else 0) + ((if (9+1)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^1*(19221849980928) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(93245636404076544) else 0)))) + (((if (2+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(-1594312423014629376) else 0) + ((if (4+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(-240029402699907072) else 0) + (if (6+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(4743924629667840) else 0))) + ((if (8+2)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^2*(67437439377408) else 0) + ((if (1+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(79758889488580608) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(6742504921595904) else 0)))))

theorem moment10Part6_coeffs : moment10Part6=(((X Coord.U)^0*moment10Part6Coeff 0 + ((X Coord.U)^1*moment10Part6Coeff 1 + (X Coord.U)^2*moment10Part6Coeff 2)) + ((X Coord.U)^3*moment10Part6Coeff 3 + ((X Coord.U)^4*moment10Part6Coeff 4 + (X Coord.U)^5*moment10Part6Coeff 5))) := by
  norm_num [moment10Part6,moment10Part6Coeff] <;> ring

def moment10Part7Coeff (d : ℕ) : Poly := ((((if (5+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(35264505271320576) else 0) + ((if (7+3)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^3*(-339866777124864) else 0) + (if (0+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(-162275805732519936) else 0))) + ((if (2+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(37155767614193664) else 0) + ((if (4+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(20442577957208064) else 0) + (if (6+4)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^4*(-1788924764307456) else 0)))) + (((if (1+5)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^5*(21372728658886656) else 0) + ((if (3+5)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^5*(21837248204636160) else 0) + (if (5+5)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^5*(-2644485466226688) else 0))) + ((if (0+6)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^6*(-2526460650455040) else 0) + ((if (2+6)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^6*(3281403593097216) else 0) + (if (4+6)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^6*(-1958740337885184) else 0)))))

theorem moment10Part7_coeffs : moment10Part7=(((X Coord.U)^0*moment10Part7Coeff 0 + ((X Coord.U)^1*moment10Part7Coeff 1 + (X Coord.U)^2*moment10Part7Coeff 2)) + ((X Coord.U)^3*moment10Part7Coeff 3 + ((X Coord.U)^4*moment10Part7Coeff 4 + (X Coord.U)^5*moment10Part7Coeff 5))) := by
  norm_num [moment10Part7,moment10Part7Coeff] <;> ring

def moment10Part8Coeff (d : ℕ) : Poly := ((((if (1+7)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^7*(-573416710078464) else 0) + ((if (3+7)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^7*(-648089051332608) else 0) + (if (0+8)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^8*(5015306502144) else 0))) + ((if (2+8)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^8*(-80802160312320) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-2447771852650954752) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(20716788679262208) else 0)))) + (((if (6+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(1256456716075008) else 0) + ((if (8+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-27614129209344) else 0) + (if (10+0)/2=d then (X Coord.K : Poly)^3*(X Coord.J : Poly)^0*(-209066655744) else 0))) + ((if (0+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-8554127497378209792) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(4188357258535084032) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(1578703866224246784) else 0)))))

theorem moment10Part8_coeffs : moment10Part8=(((X Coord.U)^0*moment10Part8Coeff 0 + ((X Coord.U)^1*moment10Part8Coeff 1 + (X Coord.U)^2*moment10Part8Coeff 2)) + ((X Coord.U)^3*moment10Part8Coeff 3 + ((X Coord.U)^4*moment10Part8Coeff 4 + (X Coord.U)^5*moment10Part8Coeff 5))) := by
  norm_num [moment10Part8,moment10Part8Coeff] <;> ring

def moment10Part9Coeff (d : ℕ) : Poly := ((((if (5+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(54261410809724928) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(-266793322807296) else 0) + (if (9+1)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^1*(-44450211815424) else 0))) + ((if (0+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-518080260483588096) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-801251635915653120) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-151499636071022592) else 0)))) + (((if (6+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-14721930448404480) else 0) + ((if (8+2)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^2*(-7410716614656) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(468204878877622272) else 0))) + ((if (3+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(-66591881423290368) else 0) + ((if (5+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(-4292773429837824) else 0) + (if (7+3)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^3*(1325204017053696) else 0)))))

theorem moment10Part9_coeffs : moment10Part9=(((X Coord.U)^0*moment10Part9Coeff 0 + ((X Coord.U)^1*moment10Part9Coeff 1 + (X Coord.U)^2*moment10Part9Coeff 2)) + ((X Coord.U)^3*moment10Part9Coeff 3 + ((X Coord.U)^4*moment10Part9Coeff 4 + (X Coord.U)^5*moment10Part9Coeff 5))) := by
  norm_num [moment10Part9,moment10Part9Coeff] <;> ring

def moment10Part10Coeff (d : ℕ) : Poly := ((((if (0+4)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^4*(-158036696275746816) else 0) + ((if (2+4)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^4*(49152197917605888) else 0) + (if (4+4)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^4*(-34257886947311616) else 0))) + ((if (6+4)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^4*(3518770258575360) else 0) + ((if (1+5)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^5*(10641226570924032) else 0) + (if (3+5)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^5*(-3685971650936832) else 0)))) + (((if (5+5)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^5*(3117090387787776) else 0) + ((if (0+6)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^6*(-229450272473088) else 0) + (if (2+6)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^6*(1490381915553792) else 0))) + ((if (4+6)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^6*(1283129018155008) else 0) + ((if (1+7)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^7*(-40122452017152) else 0) + (if (3+7)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^7*(191696159637504) else 0)))))

theorem moment10Part10_coeffs : moment10Part10=(((X Coord.U)^0*moment10Part10Coeff 0 + ((X Coord.U)^1*moment10Part10Coeff 1 + (X Coord.U)^2*moment10Part10Coeff 2)) + ((X Coord.U)^3*moment10Part10Coeff 3 + ((X Coord.U)^4*moment10Part10Coeff 4 + (X Coord.U)^5*moment10Part10Coeff 5))) := by
  norm_num [moment10Part10,moment10Part10Coeff] <;> ring

def moment10Part11Coeff (d : ℕ) : Poly := ((((if (2+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-3961660559120695296) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-173128209213800448) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(5898464181780480) else 0))) + ((if (8+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(-87926724108288) else 0) + ((if (10+0)/2=d then (X Coord.K : Poly)^4*(X Coord.J : Poly)^0*(2911629017088) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(677116232091085824) else 0)))) + (((if (1+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(632117280995205120) else 0) + ((if (3+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(1344442243046768640) else 0) + (if (5+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(1706936929468416) else 0))) + ((if (7+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(7781627281932288) else 0) + ((if (9+1)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^1*(-69760642424832) else 0) + (if (0+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(-1228382486731505664) else 0)))))

theorem moment10Part11_coeffs : moment10Part11=(((X Coord.U)^0*moment10Part11Coeff 0 + ((X Coord.U)^1*moment10Part11Coeff 1 + (X Coord.U)^2*moment10Part11Coeff 2)) + ((X Coord.U)^3*moment10Part11Coeff 3 + ((X Coord.U)^4*moment10Part11Coeff 4 + (X Coord.U)^5*moment10Part11Coeff 5))) := by
  norm_num [moment10Part11,moment10Part11Coeff] <;> ring

def moment10Part12Coeff (d : ℕ) : Poly := ((((if (2+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(-54432845479378944) else 0) + ((if (4+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(-113036754199707648) else 0) + (if (6+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(8431935683788800) else 0))) + ((if (8+2)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^2*(-896245999976448) else 0) + ((if (1+3)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^3*(633002521774915584) else 0) + (if (3+3)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^3*(-236508689461542912) else 0)))) + (((if (5+3)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^3*(48716063613517824) else 0) + ((if (7+3)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^3*(-3315615516721152) else 0) + (if (0+4)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^4*(32705127157137408) else 0))) + ((if (2+4)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^4*(-26210932150173696) else 0) + ((if (4+4)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^4*(4425276589277184) else 0) + (if (6+4)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^4*(-3051879793754112) else 0)))))

theorem moment10Part12_coeffs : moment10Part12=(((X Coord.U)^0*moment10Part12Coeff 0 + ((X Coord.U)^1*moment10Part12Coeff 1 + (X Coord.U)^2*moment10Part12Coeff 2)) + ((X Coord.U)^3*moment10Part12Coeff 3 + ((X Coord.U)^4*moment10Part12Coeff 4 + (X Coord.U)^5*moment10Part12Coeff 5))) := by
  norm_num [moment10Part12,moment10Part12Coeff] <;> ring

def moment10Part13Coeff (d : ℕ) : Poly := ((((if (1+5)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^5*(1376701634838528) else 0) + ((if (3+5)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^5*(-2049588590542848) else 0) + (if (5+5)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^5*(-1604433700454400) else 0))) + ((if (2+6)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^6*(140428582060032) else 0) + ((if (4+6)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^6*(-296460339904512) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-4382336574963588096) else 0)))) + (((if (4+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-28115931239221248) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-30272545686878208) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(1220349372668928) else 0))) + ((if (10+0)/2=d then (X Coord.K : Poly)^5*(X Coord.J : Poly)^0*(-21649604520960) else 0) + ((if (0+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(328311602422530048) else 0) + (if (1+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(2303805099558223872) else 0)))))

theorem moment10Part13_coeffs : moment10Part13=(((X Coord.U)^0*moment10Part13Coeff 0 + ((X Coord.U)^1*moment10Part13Coeff 1 + (X Coord.U)^2*moment10Part13Coeff 2)) + ((X Coord.U)^3*moment10Part13Coeff 3 + ((X Coord.U)^4*moment10Part13Coeff 4 + (X Coord.U)^5*moment10Part13Coeff 5))) := by
  norm_num [moment10Part13,moment10Part13Coeff] <;> ring

def moment10Part14Coeff (d : ℕ) : Poly := ((((if (3+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(-578663556564123648) else 0) + ((if (5+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(211281541027430400) else 0) + (if (7+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(-15769153018920960) else 0))) + ((if (9+1)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^1*(658392165236736) else 0) + ((if (0+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(53484012180504576) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(-974558059750490112) else 0)))) + (((if (4+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(335431848736456704) else 0) + ((if (6+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(-48404603792130048) else 0) + (if (8+2)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^2*(2351529262153728) else 0))) + ((if (1+3)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^3*(-130820508628549632) else 0) + ((if (3+3)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^3*(48960675900555264) else 0) + (if (5+3)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^3*(-7059740472115200) else 0)))))

theorem moment10Part14_coeffs : moment10Part14=(((X Coord.U)^0*moment10Part14Coeff 0 + ((X Coord.U)^1*moment10Part14Coeff 1 + (X Coord.U)^2*moment10Part14Coeff 2)) + ((X Coord.U)^3*moment10Part14Coeff 3 + ((X Coord.U)^4*moment10Part14Coeff 4 + (X Coord.U)^5*moment10Part14Coeff 5))) := by
  norm_num [moment10Part14,moment10Part14Coeff] <;> ring

def moment10Part15Coeff (d : ℕ) : Poly := ((((if (7+3)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^3*(1984745630859264) else 0) + ((if (2+4)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^4*(-3441754087096320) else 0) + (if (4+4)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^4*(1525489061068800) else 0))) + ((if (6+4)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^4*(1318886295994368) else 0) + ((if (3+5)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^5*(-280857164120064) else 0) + (if (5+5)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^5*(312063515688960) else 0)))) + (((if (2+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(-294241410708922368) else 0) + ((if (4+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(-613251565613383680) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(53149080840781824) else 0))) + ((if (8+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(-4460464678846464) else 0) + ((if (10+0)/2=d then (X Coord.K : Poly)^6*(X Coord.J : Poly)^0*(91471564873728) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(383949003059269632) else 0)))))

theorem moment10Part15_coeffs : moment10Part15=(((X Coord.U)^0*moment10Part15Coeff 0 + ((X Coord.U)^1*moment10Part15Coeff 1 + (X Coord.U)^2*moment10Part15Coeff 2)) + ((X Coord.U)^3*moment10Part15Coeff 3 + ((X Coord.U)^4*moment10Part15Coeff 4 + (X Coord.U)^5*moment10Part15Coeff 5))) := by
  norm_num [moment10Part15,moment10Part15Coeff] <;> ring

def moment10Part16Coeff (d : ℕ) : Poly := ((((if (1+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(-106968024361009152) else 0) + ((if (3+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(682255339279220736) else 0) + (if (5+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(-212576273746624512) else 0))) + ((if (7+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(26346124845121536) else 0) + ((if (9+1)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^1*(-1070124255608832) else 0) + (if (2+2)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^2*(196230762942824448) else 0)))) + (((if (4+2)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^2*(-58131790753038336) else 0) + ((if (6+2)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^2*(8073877241069568) else 0) + (if (8+2)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^2*(-916075143364608) else 0))) + ((if (3+3)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^3*(4589005449461760) else 0) + ((if (5+3)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^3*(-493171806044160) else 0) + (if (7+3)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^3*(-713659540045824) else 0)))))

theorem moment10Part16_coeffs : moment10Part16=(((X Coord.U)^0*moment10Part16Coeff 0 + ((X Coord.U)^1*moment10Part16Coeff 1 + (X Coord.U)^2*moment10Part16Coeff 2)) + ((X Coord.U)^3*moment10Part16Coeff 3 + ((X Coord.U)^4*moment10Part16Coeff 4 + (X Coord.U)^5*moment10Part16Coeff 5))) := by
  norm_num [moment10Part16,moment10Part16Coeff] <;> ring

def moment10Part17Coeff (d : ℕ) : Poly := ((((if (4+4)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^4*(351071455150080) else 0) + ((if (6+4)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^4*(-226246048874496) else 0) + (if (2+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(-1288727614526312448) else 0))) + ((if (4+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(374568440387198976) else 0) + ((if (6+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(-88589516401631232) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(6618583363719168) else 0)))) + (((if (10+0)/2=d then (X Coord.K : Poly)^7*(X Coord.J : Poly)^0*(-213164635115520) else 0) + ((if (3+1)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^1*(-130820508628549632) else 0) + (if (5+1)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^1*(36177913453215744) else 0))) + ((if (7+1)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^1*(-4810932762181632) else 0) + ((if (9+1)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^1*(298317860831232) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^2*(-3441754087096320) else 0)))))

theorem moment10Part17_coeffs : moment10Part17=(((X Coord.U)^0*moment10Part17Coeff 0 + ((X Coord.U)^1*moment10Part17Coeff 1 + (X Coord.U)^2*moment10Part17Coeff 2)) + ((X Coord.U)^3*moment10Part17Coeff 3 + ((X Coord.U)^4*moment10Part17Coeff 4 + (X Coord.U)^5*moment10Part17Coeff 5))) := by
  norm_num [moment10Part17,moment10Part17Coeff] <;> ring

def moment10Part18Coeff (d : ℕ) : Poly := ((((if (6+2)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^2*(-66034868944896) else 0) + ((if (8+2)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^2*(245239200350208) else 0) + (if (5+3)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^3*(-280857164120064) else 0))) + ((if (7+3)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^3*(111451255603200) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(53484012180504576) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(-182663105027899392) else 0)))) + (((if (6+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(51833819612971008) else 0) + ((if (8+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(-5853234192187392) else 0) + (if (10+0)/2=d then (X Coord.K : Poly)^8*(X Coord.J : Poly)^0*(217846571433984) else 0))) + ((if (5+1)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^1*(1376701634838528) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^1*(93619054706688) else 0) + (if (9+1)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^1*(-48574172233728) else 0)))))

theorem moment10Part18_coeffs : moment10Part18=(((X Coord.U)^0*moment10Part18Coeff 0 + ((X Coord.U)^1*moment10Part18Coeff 1 + (X Coord.U)^2*moment10Part18Coeff 2)) + ((X Coord.U)^3*moment10Part18Coeff 3 + ((X Coord.U)^4*moment10Part18Coeff 4 + (X Coord.U)^5*moment10Part18Coeff 5))) := by
  norm_num [moment10Part18,moment10Part18Coeff] <;> ring

def moment10Part19Coeff (d : ℕ) : Poly := ((((if (6+2)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^2*(140428582060032) else 0) + ((if (8+2)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^2*(-35664401793024) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^0*(32705127157137408) else 0))) + ((if (6+0)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^0*(-8910632371027968) else 0) + ((if (8+0)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^0*(1133703069106176) else 0) + (if (10+0)/2=d then (X Coord.K : Poly)^9*(X Coord.J : Poly)^0*(-51534596210688) else 0)))) + (((if (7+1)/2=d then (X Coord.K : Poly)^10*(X Coord.J : Poly)^1*(-40122452017152) else 0) + ((if (9+1)/2=d then (X Coord.K : Poly)^10*(X Coord.J : Poly)^1*(6687075336192) else 0) + (if (6+0)/2=d then (X Coord.K : Poly)^10*(X Coord.J : Poly)^0*(-229450272473088) else 0))) + ((if (8+0)/2=d then (X Coord.K : Poly)^10*(X Coord.J : Poly)^0*(-19225341591552) else 0) + ((if (10+0)/2=d then (X Coord.K : Poly)^10*(X Coord.J : Poly)^0*(4225860108288) else 0) + (if (8+0)/2=d then (X Coord.K : Poly)^11*(X Coord.J : Poly)^0*(5015306502144) else 0)))))

theorem moment10Part19_coeffs : moment10Part19=(((X Coord.U)^0*moment10Part19Coeff 0 + ((X Coord.U)^1*moment10Part19Coeff 1 + (X Coord.U)^2*moment10Part19Coeff 2)) + ((X Coord.U)^3*moment10Part19Coeff 3 + ((X Coord.U)^4*moment10Part19Coeff 4 + (X Coord.U)^5*moment10Part19Coeff 5))) := by
  norm_num [moment10Part19,moment10Part19Coeff] <;> ring

def moment10Part20Coeff (d : ℕ) : Poly := ((((if (10+0)/2=d then (X Coord.K : Poly)^11*(X Coord.J : Poly)^0*(-557256278016) else 0) + ((if (1+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(160938316815925248) else 0) + (if (3+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-481576059666432) else 0))) + ((if (5+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-327177085648896) else 0) + ((if (7+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(2299011268608) else 0) + (if (9+1)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^1*(-8153726976) else 0)))) + (((if (0+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-149299498311745536) else 0) + ((if (2+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(1744681690202112) else 0) + (if (4+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-2676914685739008) else 0))) + ((if (6+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(100337980538880) else 0) + ((if (8+2)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^2*(-173776306176) else 0) + (if (1+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(107262236326625280) else 0)))))

theorem moment10Part20_coeffs : moment10Part20=(((X Coord.U)^0*moment10Part20Coeff 0 + ((X Coord.U)^1*moment10Part20Coeff 1 + (X Coord.U)^2*moment10Part20Coeff 2)) + ((X Coord.U)^3*moment10Part20Coeff 3 + ((X Coord.U)^4*moment10Part20Coeff 4 + (X Coord.U)^5*moment10Part20Coeff 5))) := by
  norm_num [moment10Part20,moment10Part20Coeff] <;> ring

def moment10Part21Coeff (d : ℕ) : Poly := ((((if (3+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(-13136441311494144) else 0) + ((if (5+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(734567543341056) else 0) + (if (7+3)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^3*(-9730368995328) else 0))) + ((if (0+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(62072707151167488) else 0) + ((if (2+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(-34686602777198592) else 0) + (if (4+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(2807707951300608) else 0)))) + (((if (6+4)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^4*(-62408881078272) else 0) + ((if (1+5)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^5*(-21135383922475008) else 0) + (if (3+5)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^5*(4463867016511488) else 0))) + ((if (5+5)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^5*(-163763975356416) else 0) + ((if (0+6)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^6*(-5108809461792768) else 0) + (if (2+6)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^6*(2867656286011392) else 0)))))

theorem moment10Part21_coeffs : moment10Part21=(((X Coord.U)^0*moment10Part21Coeff 0 + ((X Coord.U)^1*moment10Part21Coeff 1 + (X Coord.U)^2*moment10Part21Coeff 2)) + ((X Coord.U)^3*moment10Part21Coeff 3 + ((X Coord.U)^4*moment10Part21Coeff 4 + (X Coord.U)^5*moment10Part21Coeff 5))) := by
  norm_num [moment10Part21,moment10Part21Coeff] <;> ring

def moment10Part22Coeff (d : ℕ) : Poly := ((((if (4+6)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^6*(-205976998379520) else 0) + ((if (1+7)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^7*(914720701022208) else 0) + (if (3+7)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^7*(-131452284174336) else 0))) + ((if (0+8)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^8*(118649149194240) else 0) + ((if (2+8)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^8*(-48187188707328) else 0) + (if (1+9)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^9*(-9287604633600) else 0)))) + (((if (0+10)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^10*(-743008370688) else 0) + ((if (2+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(10648022001647616) else 0) + (if (4+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(332976678764544) else 0))) + ((if (6+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(-5278009393152) else 0) + ((if (8+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(24461180928) else 0) + (if (0+0)/2=d then (X Coord.K : Poly)^0*(X Coord.J : Poly)^0*(0) else 0)))))

theorem moment10Part22_coeffs : moment10Part22=(((X Coord.U)^0*moment10Part22Coeff 0 + ((X Coord.U)^1*moment10Part22Coeff 1 + (X Coord.U)^2*moment10Part22Coeff 2)) + ((X Coord.U)^3*moment10Part22Coeff 3 + ((X Coord.U)^4*moment10Part22Coeff 4 + (X Coord.U)^5*moment10Part22Coeff 5))) := by
  norm_num [moment10Part22,moment10Part22Coeff] <;> ring

def moment10Coeff0 : Poly := (((((moment10Part0Coeff 0) + (moment10Part1Coeff 0)) + ((moment10Part2Coeff 0) + ((moment10Part3Coeff 0) + (moment10Part4Coeff 0)))) + (((moment10Part5Coeff 0) + ((moment10Part6Coeff 0) + (moment10Part7Coeff 0))) + ((moment10Part8Coeff 0) + ((moment10Part9Coeff 0) + (moment10Part10Coeff 0))))) + ((((moment10Part11Coeff 0) + ((moment10Part12Coeff 0) + (moment10Part13Coeff 0))) + ((moment10Part14Coeff 0) + ((moment10Part15Coeff 0) + (moment10Part16Coeff 0)))) + (((moment10Part17Coeff 0) + ((moment10Part18Coeff 0) + (moment10Part19Coeff 0))) + ((moment10Part20Coeff 0) + ((moment10Part21Coeff 0) + (moment10Part22Coeff 0))))))

def moment10Coeff1 : Poly := (((((moment10Part0Coeff 1) + (moment10Part1Coeff 1)) + ((moment10Part2Coeff 1) + ((moment10Part3Coeff 1) + (moment10Part4Coeff 1)))) + (((moment10Part5Coeff 1) + ((moment10Part6Coeff 1) + (moment10Part7Coeff 1))) + ((moment10Part8Coeff 1) + ((moment10Part9Coeff 1) + (moment10Part10Coeff 1))))) + ((((moment10Part11Coeff 1) + ((moment10Part12Coeff 1) + (moment10Part13Coeff 1))) + ((moment10Part14Coeff 1) + ((moment10Part15Coeff 1) + (moment10Part16Coeff 1)))) + (((moment10Part17Coeff 1) + ((moment10Part18Coeff 1) + (moment10Part19Coeff 1))) + ((moment10Part20Coeff 1) + ((moment10Part21Coeff 1) + (moment10Part22Coeff 1))))))

def moment10Coeff2 : Poly := (((((moment10Part0Coeff 2) + (moment10Part1Coeff 2)) + ((moment10Part2Coeff 2) + ((moment10Part3Coeff 2) + (moment10Part4Coeff 2)))) + (((moment10Part5Coeff 2) + ((moment10Part6Coeff 2) + (moment10Part7Coeff 2))) + ((moment10Part8Coeff 2) + ((moment10Part9Coeff 2) + (moment10Part10Coeff 2))))) + ((((moment10Part11Coeff 2) + ((moment10Part12Coeff 2) + (moment10Part13Coeff 2))) + ((moment10Part14Coeff 2) + ((moment10Part15Coeff 2) + (moment10Part16Coeff 2)))) + (((moment10Part17Coeff 2) + ((moment10Part18Coeff 2) + (moment10Part19Coeff 2))) + ((moment10Part20Coeff 2) + ((moment10Part21Coeff 2) + (moment10Part22Coeff 2))))))

def moment10Coeff3 : Poly := (((((moment10Part0Coeff 3) + (moment10Part1Coeff 3)) + ((moment10Part2Coeff 3) + ((moment10Part3Coeff 3) + (moment10Part4Coeff 3)))) + (((moment10Part5Coeff 3) + ((moment10Part6Coeff 3) + (moment10Part7Coeff 3))) + ((moment10Part8Coeff 3) + ((moment10Part9Coeff 3) + (moment10Part10Coeff 3))))) + ((((moment10Part11Coeff 3) + ((moment10Part12Coeff 3) + (moment10Part13Coeff 3))) + ((moment10Part14Coeff 3) + ((moment10Part15Coeff 3) + (moment10Part16Coeff 3)))) + (((moment10Part17Coeff 3) + ((moment10Part18Coeff 3) + (moment10Part19Coeff 3))) + ((moment10Part20Coeff 3) + ((moment10Part21Coeff 3) + (moment10Part22Coeff 3))))))

def moment10Coeff4 : Poly := (((((moment10Part0Coeff 4) + (moment10Part1Coeff 4)) + ((moment10Part2Coeff 4) + ((moment10Part3Coeff 4) + (moment10Part4Coeff 4)))) + (((moment10Part5Coeff 4) + ((moment10Part6Coeff 4) + (moment10Part7Coeff 4))) + ((moment10Part8Coeff 4) + ((moment10Part9Coeff 4) + (moment10Part10Coeff 4))))) + ((((moment10Part11Coeff 4) + ((moment10Part12Coeff 4) + (moment10Part13Coeff 4))) + ((moment10Part14Coeff 4) + ((moment10Part15Coeff 4) + (moment10Part16Coeff 4)))) + (((moment10Part17Coeff 4) + ((moment10Part18Coeff 4) + (moment10Part19Coeff 4))) + ((moment10Part20Coeff 4) + ((moment10Part21Coeff 4) + (moment10Part22Coeff 4))))))

def moment10Coeff5 : Poly := (((((moment10Part0Coeff 5) + (moment10Part1Coeff 5)) + ((moment10Part2Coeff 5) + ((moment10Part3Coeff 5) + (moment10Part4Coeff 5)))) + (((moment10Part5Coeff 5) + ((moment10Part6Coeff 5) + (moment10Part7Coeff 5))) + ((moment10Part8Coeff 5) + ((moment10Part9Coeff 5) + (moment10Part10Coeff 5))))) + ((((moment10Part11Coeff 5) + ((moment10Part12Coeff 5) + (moment10Part13Coeff 5))) + ((moment10Part14Coeff 5) + ((moment10Part15Coeff 5) + (moment10Part16Coeff 5)))) + (((moment10Part17Coeff 5) + ((moment10Part18Coeff 5) + (moment10Part19Coeff 5))) + ((moment10Part20Coeff 5) + ((moment10Part21Coeff 5) + (moment10Part22Coeff 5))))))

theorem moment10_coeffs : moment10=(((X Coord.U)^0*moment10Coeff0 + ((X Coord.U)^1*moment10Coeff1 + (X Coord.U)^2*moment10Coeff2)) + ((X Coord.U)^3*moment10Coeff3 + ((X Coord.U)^4*moment10Coeff4 + (X Coord.U)^5*moment10Coeff5))) := by
  simp only [moment10,moment10Coeff0,moment10Coeff1,moment10Coeff2,moment10Coeff3,moment10Coeff4,moment10Coeff5,moment10Part0_coeffs,moment10Part1_coeffs,moment10Part2_coeffs,moment10Part3_coeffs,moment10Part4_coeffs,moment10Part5_coeffs,moment10Part6_coeffs,moment10Part7_coeffs,moment10Part8_coeffs,moment10Part9_coeffs,moment10Part10_coeffs,moment10Part11_coeffs,moment10Part12_coeffs,moment10Part13_coeffs,moment10Part14_coeffs,moment10Part15_coeffs,moment10Part16_coeffs,moment10Part17_coeffs,moment10Part18_coeffs,moment10Part19_coeffs,moment10Part20_coeffs,moment10Part21_coeffs,moment10Part22_coeffs]
  ring

def moment10Coeff0Norm : {P : Poly // moment10Coeff0=P} := by
  have h : moment10Coeff0=moment10Coeff0 := rfl
  conv at h =>
    rhs
    norm_num [moment10Coeff0,moment10Part0Coeff,moment10Part1Coeff,moment10Part2Coeff,moment10Part3Coeff,moment10Part4Coeff,moment10Part5Coeff,moment10Part6Coeff,moment10Part7Coeff,moment10Part8Coeff,moment10Part9Coeff,moment10Part10Coeff,moment10Part11Coeff,moment10Part12Coeff,moment10Part13Coeff,moment10Part14Coeff,moment10Part15Coeff,moment10Part16Coeff,moment10Part17Coeff,moment10Part18Coeff,moment10Part19Coeff,moment10Part20Coeff,moment10Part21Coeff,moment10Part22Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment10Coeff1Norm : {P : Poly // moment10Coeff1=P} := by
  have h : moment10Coeff1=moment10Coeff1 := rfl
  conv at h =>
    rhs
    norm_num [moment10Coeff1,moment10Part0Coeff,moment10Part1Coeff,moment10Part2Coeff,moment10Part3Coeff,moment10Part4Coeff,moment10Part5Coeff,moment10Part6Coeff,moment10Part7Coeff,moment10Part8Coeff,moment10Part9Coeff,moment10Part10Coeff,moment10Part11Coeff,moment10Part12Coeff,moment10Part13Coeff,moment10Part14Coeff,moment10Part15Coeff,moment10Part16Coeff,moment10Part17Coeff,moment10Part18Coeff,moment10Part19Coeff,moment10Part20Coeff,moment10Part21Coeff,moment10Part22Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment10Coeff2Norm : {P : Poly // moment10Coeff2=P} := by
  have h : moment10Coeff2=moment10Coeff2 := rfl
  conv at h =>
    rhs
    norm_num [moment10Coeff2,moment10Part0Coeff,moment10Part1Coeff,moment10Part2Coeff,moment10Part3Coeff,moment10Part4Coeff,moment10Part5Coeff,moment10Part6Coeff,moment10Part7Coeff,moment10Part8Coeff,moment10Part9Coeff,moment10Part10Coeff,moment10Part11Coeff,moment10Part12Coeff,moment10Part13Coeff,moment10Part14Coeff,moment10Part15Coeff,moment10Part16Coeff,moment10Part17Coeff,moment10Part18Coeff,moment10Part19Coeff,moment10Part20Coeff,moment10Part21Coeff,moment10Part22Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment10Coeff3Norm : {P : Poly // moment10Coeff3=P} := by
  have h : moment10Coeff3=moment10Coeff3 := rfl
  conv at h =>
    rhs
    norm_num [moment10Coeff3,moment10Part0Coeff,moment10Part1Coeff,moment10Part2Coeff,moment10Part3Coeff,moment10Part4Coeff,moment10Part5Coeff,moment10Part6Coeff,moment10Part7Coeff,moment10Part8Coeff,moment10Part9Coeff,moment10Part10Coeff,moment10Part11Coeff,moment10Part12Coeff,moment10Part13Coeff,moment10Part14Coeff,moment10Part15Coeff,moment10Part16Coeff,moment10Part17Coeff,moment10Part18Coeff,moment10Part19Coeff,moment10Part20Coeff,moment10Part21Coeff,moment10Part22Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment10Coeff4Norm : {P : Poly // moment10Coeff4=P} := by
  have h : moment10Coeff4=moment10Coeff4 := rfl
  conv at h =>
    rhs
    norm_num [moment10Coeff4,moment10Part0Coeff,moment10Part1Coeff,moment10Part2Coeff,moment10Part3Coeff,moment10Part4Coeff,moment10Part5Coeff,moment10Part6Coeff,moment10Part7Coeff,moment10Part8Coeff,moment10Part9Coeff,moment10Part10Coeff,moment10Part11Coeff,moment10Part12Coeff,moment10Part13Coeff,moment10Part14Coeff,moment10Part15Coeff,moment10Part16Coeff,moment10Part17Coeff,moment10Part18Coeff,moment10Part19Coeff,moment10Part20Coeff,moment10Part21Coeff,moment10Part22Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def moment10Coeff5Norm : {P : Poly // moment10Coeff5=P} := by
  have h : moment10Coeff5=moment10Coeff5 := rfl
  conv at h =>
    rhs
    norm_num [moment10Coeff5,moment10Part0Coeff,moment10Part1Coeff,moment10Part2Coeff,moment10Part3Coeff,moment10Part4Coeff,moment10Part5Coeff,moment10Part6Coeff,moment10Part7Coeff,moment10Part8Coeff,moment10Part9Coeff,moment10Part10Coeff,moment10Part11Coeff,moment10Part12Coeff,moment10Part13Coeff,moment10Part14Coeff,moment10Part15Coeff,moment10Part16Coeff,moment10Part17Coeff,moment10Part18Coeff,moment10Part19Coeff,moment10Part20Coeff,moment10Part21Coeff,moment10Part22Coeff]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩


end
end HTGeometry.ThetaRatioSquare
