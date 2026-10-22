import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioSquareFlow
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioReflectionsClean
/-! # Exact squared-coordinate algebra for the full modular third slope. -/

namespace HTGeometry.ThetaRatioSquare
noncomputable section
open MvPolynomial ThetaRatioSource

def moment2Part0 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1152)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-1620)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(1440)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-12)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-5184)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-31104))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(8640)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(576)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-3888)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-3024)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-480)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-1728))))))

theorem moment2Part0_eq : shear reflectionClean2Part0=square moment2Part0 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean2Part0,moment2Part0,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment2Part1 : Poly := ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))

theorem moment2Part1_eq : shear reflectionClean2Part1=square moment2Part1 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean2Part1,moment2Part1,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment2 : Poly := (moment2Part0 + moment2Part1)

theorem moment2_eq : shear (integerReflection 2)=square moment2 := by
  rw [reflectionBalanced2_eq,reflectionClean2_eq]
  simp only [reflectionClean2,moment2,map_add,moment2Part0_eq,moment2Part1_eq]

def moment4Part0 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(819072)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(20481984)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-6697728)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(158976)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(11524032)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(502848))))) + ((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-373248)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-746496)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-312768)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(70368912)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-24603264)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(10368))))))

theorem moment4Part0_eq : shear reflectionClean4Part0=square moment4Part0 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean4Part0,moment4Part0,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment4Part1 : Poly := (((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(559872)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(2177280)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(2239488)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-609120)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(23760)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(25894080))))) + ((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-4478976)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-1866240)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(1679616)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-2426112)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(10435392)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-165888))))))

theorem moment4Part1_eq : shear reflectionClean4Part1=square moment4Part1 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean4Part1,moment4Part1,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment4Part2 : Poly := (((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(11337408)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-3359232)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1119744)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(1399680)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(451008)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(1679616))))) + ((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-186624)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(376704)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-31104)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(3841344)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-164160)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-373248))))))

theorem moment4Part2_eq : shear reflectionClean4Part2=square moment4Part2 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean4Part2,moment4Part2,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment4Part3 : Poly := (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-248832)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(93312)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))

theorem moment4Part3_eq : shear reflectionClean4Part3=square moment4Part3 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean4Part3,moment4Part3,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment4 : Poly := ((moment4Part0 + moment4Part1) + (moment4Part2 + moment4Part3))

theorem moment4_eq : shear (integerReflection 4)=square moment4 := by
  rw [reflectionBalanced4_eq,reflectionClean4_eq]
  simp only [reflectionClean4,moment4,map_add,moment4Part0_eq,moment4Part1_eq,moment4Part2_eq,moment4Part3_eq]

def moment6Part0 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-8338360320)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-90870584832)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(31536096768)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-934861824)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(21026304)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-32045393664))))) + ((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-4303176192)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(149154048)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(3321160704)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(377478144)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(4911197184)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-127650816))))))

theorem moment6Part0_eq : shear reflectionClean6Part0=square moment6Part0 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part0,moment6Part0,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6Part1 : Poly := (((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-232906752)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-107495424)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(1239681024)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-54120960)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-262125911808)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(98870035968))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1579585536)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-73446912)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-6505152768)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-17677398528)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-85536000)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-11663253504))))))

theorem moment6Part1_eq : shear reflectionClean6Part1=square moment6Part1 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part1,moment6Part1,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6Part2 : Poly := (((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(1206337536)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(886837248)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(1155575808)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(537477120)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-5641643520)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(110419200))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(1492992)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-203900763456)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(50993141760)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(15311379456)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-151041024)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-16144468992))))))

theorem moment6Part2_eq : shear reflectionClean6Part2=square moment6Part2 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part2,moment6Part2,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6Part3 : Poly := (((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(7874039808)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-1541514240)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-1370566656)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-1818464256)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(241864704)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-1101828096))))) + ((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-47910346560)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(1067535936)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-18035136)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-122353307136)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(39484412928)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-2002102272))))))

theorem moment6Part3_eq : shear reflectionClean6Part3=square moment6Part3 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part3,moment6Part3,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6Part4 : Poly := (((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(750228480)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-3083774976)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-524040192)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(1350411264)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-967458816)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(1182449664))))) + ((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-15444069120)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-4425228288)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(93747456)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(952342272)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(6167549952)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1612431360))))))

theorem moment6Part4_eq : shear reflectionClean6Part4=square moment6Part4 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part4,moment6Part4,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6Part5 : Poly := (((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-488208384)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(1451188224)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-698720256)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-23657391360)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(915390720)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-151352064))))) + ((((X Coord.K : Poly)^6*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-967458816)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(214990848)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-3083774976)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-604661760)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(69424128)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(241864704))))))

theorem moment6Part5_eq : shear reflectionClean6Part5=square moment6Part5 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part5,moment6Part5,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6Part6 : Poly := (((((X Coord.K : Poly)^7*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-26873856)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(953026560)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(112637952)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-1990656)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-10518875136)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(833836032))))) + ((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-17418240)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(2364152832)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-90160128)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(1547486208)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-211756032)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-137355264))))))

theorem moment6Part6_eq : shear reflectionClean6Part6=square moment6Part6 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part6,moment6Part6,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6Part7 : Poly := ((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-35831808)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-167712768))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(5971968)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))

theorem moment6Part7_eq : shear reflectionClean6Part7=square moment6Part7 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean6Part7,moment6Part7,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment6 : Poly := (((moment6Part0 + moment6Part1) + (moment6Part2 + moment6Part3)) + ((moment6Part4 + moment6Part5) + (moment6Part6 + moment6Part7)))

theorem moment6_eq : shear (integerReflection 6)=square moment6 := by
  rw [reflectionBalanced6_eq,reflectionClean6_eq]
  simp only [reflectionClean6,moment6,map_add,moment6Part0_eq,moment6Part1_eq,moment6Part2_eq,moment6Part3_eq,moment6Part4_eq,moment6Part5_eq,moment6Part6_eq,moment6Part7_eq]

def moment8Part0 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(48721763450880)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(465200636755968)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-208222828609536)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(4892833382400)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-196203036672)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(2516189184))))) + ((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(106607673040896)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(39495108722688)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-1766119956480)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(28747726848)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-30631036059648)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-4672396099584))))))

theorem moment8Part0_eq : shear reflectionClean8Part0=square moment8Part0 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part0,moment8Part0,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part1 : Poly := (((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(175615672320)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-32021435621376)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(3499943510016)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(277618876416)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(3851131060224)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-19707494400))))) + ((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(1500528623616)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-133186830336)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-79976595456)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(-15479341056)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-5043506135040)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(280455561216))))))

theorem moment8Part1_eq : shear reflectionClean8Part1=square moment8Part1 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part1,moment8Part1,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part2 : Poly := (((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-6975258624)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1390654809612288)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-653518510829568)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-15706344517632)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(943376855040)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-18251993088))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(9961318766592)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(161480364963840)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(290179418112)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-114128787456)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(44438285795328)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-18974447271936))))))

theorem moment8Part2_eq : shear reflectionClean8Part2=square moment8Part2 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part2,moment8Part2,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part3 : Poly := (((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-51729186816)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-13697040052224)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-13151151415296)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(909402329088)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-5423574122496)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(976703422464))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(336675667968)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(545646772224)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(108355387392)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(60218694660096)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-1816099356672)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(37381533696))))))

theorem moment8Part3_eq : shear reflectionClean8Part3=square moment8Part3 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part3,moment8Part3,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part4 : Poly := (((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(95551488)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1594560904169472)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-616167263969280)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-114204482150400)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(992594829312)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(39070605312))))) + ((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(43236339148800)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(62404116940800)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(19329491220480)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-81859258368)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(5636415062016)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(14700214222848))))))

theorem moment8Part4_eq : shear reflectionClean8Part4=square moment8Part4 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part4,moment8Part4,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part5 : Poly := (((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-1588280721408)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-6765439500288)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(9166672281600)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-1954051817472)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-1369921683456)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-1377661353984))))) + ((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(34828517376)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-328935997440)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(304304294430720)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-3709196789760)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(12712826880)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-2030469120))))))

theorem moment8Part5_eq : shear reflectionClean8Part5=square moment8Part5 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part5,moment8Part5,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part6 : Poly := (((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1043671487738112)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-374639477501952)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-62359251038208)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-9293006278656)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(118839177216)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-901187887104))))) + ((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(65431174643712)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-10667684634624)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(1263071232000)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(16143017803776)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-10015133663232)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(1932552732672))))))

theorem moment8Part6_eq : shear reflectionClean8Part6=square moment8Part6 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part6,moment8Part6,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part7 : Poly := (((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-914248581120)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(2002639749120)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(1852683632640)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-208971104256)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(564995948544)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(267216539010048))))) + ((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(30406152273408)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-1095470189568)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(17800632576)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(1258724385792)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-8567815274496)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-89526703915008))))))

theorem moment8Part7_eq : shear reflectionClean8Part7=square moment8Part7 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part7,moment8Part7,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part8 : Poly := (((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(7415249338368)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-582911852544)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(33892500971520)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-19133916733440)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(8028456984576)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-1076405428224))))) + ((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(3656994324480)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-1044855521280)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-1458927894528)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(522427760640)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-599824465920)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(320229714622464))))))

theorem moment8Part8_eq : shear reflectionClean8Part8=square moment8Part8 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part8,moment8Part8,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part9 : Poly := (((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-8830480343040)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(3199829723136)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-75026580480)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(25140203394048)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-67785001943040)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(16900538056704))))) + ((((X Coord.K : Poly)^6*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-4563503235072)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(357852266496)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-5485491486720)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-232190115840)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(676576198656)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-696570347520))))))

theorem moment8Part9_eq : shear reflectionClean8Part9=square moment8Part9 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part9,moment8Part9,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part10 : Poly := (((((X Coord.K : Poly)^6*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(402462867456)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-1704420569088)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(34018391549952)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-2749759819776)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(139464115200)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(3656994324480))))) + ((((X Coord.K : Poly)^7*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(417942208512)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-171562696704)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(522427760640)))) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-166402916352)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(33892500971520)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-7144199626752))))))

theorem moment8Part10_eq : shear reflectionClean8Part10=square moment8Part10 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part10,moment8Part10,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part11 : Poly := (((((X Coord.K : Poly)^7*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(1306553131008)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-64765992960)) + ((X Coord.K : Poly)^8*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-208971104256)))) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(38698352640)) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-914248581120)) + ((X Coord.K : Poly)^8*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-110290305024))))) + ((((X Coord.K : Poly)^8*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(18381717504)) + (((X Coord.K : Poly)^9*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(34828517376)) + ((X Coord.K : Poly)^9*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-3869835264)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-14932547665920)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-473768165376)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(18268913664))))))

theorem moment8Part11_eq : shear reflectionClean8Part11=square moment8Part11 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part11,moment8Part11,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part12 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-127401984)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(36181024800768)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-3344970940416)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(260254384128)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-1795571712)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-15123423707136))))) + ((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(1215558254592)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-24953536512)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-9391203348480)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(2944819224576)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-106218418176)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(1838171750400))))))

theorem moment8Part12_eq : shear reflectionClean8Part12=square moment8Part12 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part12,moment8Part12,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8Part13 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-173091520512)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(464057745408))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-117205843968)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-38698352640)))) + ((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(-5159780352)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-293964152832))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-37786632192)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(382205952)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))))

theorem moment8Part13_eq : shear reflectionClean8Part13=square moment8Part13 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean8Part13,moment8Part13,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment8 : Poly := (((moment8Part0 + (moment8Part1 + moment8Part2)) + ((moment8Part3 + moment8Part4) + (moment8Part5 + moment8Part6))) + ((moment8Part7 + (moment8Part8 + moment8Part9)) + ((moment8Part10 + moment8Part11) + (moment8Part12 + moment8Part13))))

theorem moment8_eq : shear (integerReflection 8)=square moment8 := by
  rw [reflectionBalanced8_eq,reflectionClean8_eq]
  simp only [reflectionClean8,moment8,map_add,moment8Part0_eq,moment8Part1_eq,moment8Part2_eq,moment8Part3_eq,moment8Part4_eq,moment8Part5_eq,moment8Part6_eq,moment8Part7_eq,moment8Part8_eq,moment8Part9_eq,moment8Part10_eq,moment8Part11_eq,moment8Part12_eq,moment8Part13_eq]

def moment10Part0 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-312165555505201152)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-2936102282906370048)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(1818995586674982912)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-56594005935390720)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(1534590913609728)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-43083242274816))))) + ((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(266524950528)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-367565196123832320)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-460966580336590848)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(24334188461752320)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-708382995775488)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(4615386365952))))))

theorem moment10Part0_eq : shear reflectionClean10Part0=square moment10Part0 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part0,moment10Part0,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part1 : Poly := (((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(260607039842746368)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(60342327082156032)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-4217261764313088)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(74382549516288)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(207945326055112704)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-57642006020308992))))) + ((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-5306918690930688)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(266907136573440)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-54580396493242368)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(3929776432349184)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(281445092425728)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-17956085932818432))))))

theorem moment10Part1_eq : shear reflectionClean10Part1=square moment10Part1 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part1,moment10Part1,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part2 : Poly := (((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(4715990223814656)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(12592873930752)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(2225170756141056)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(-94841922650112)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(386039286595584)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(-73851936178176))))) + ((((X Coord.K : Poly)^1*(X Coord.U : Poly)^((1+9)/2)*(X Coord.J : Poly)^9*(-21175738564608)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((0+10)/2)*(X Coord.J : Poly)^10*(-2229025112064)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(61684770355347456)))) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-197242493534208)) + (((X Coord.K : Poly)^1*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(80341172158464)) + ((X Coord.K : Poly)^1*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-762883080192))))))

theorem moment10Part2_eq : shear reflectionClean10Part2=square moment10Part2 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part2,moment10Part2,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part3 : Poly := (((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-9455534033560731648)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(6034557931751079936)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(77107829817212928)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-7239659433099264)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(247320885067776)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-3329120010240))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(283490304519241728)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-1830188307339214848)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(25356104889532416)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(1132149688565760)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-27635385434112)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-183915869383655424))))))

theorem moment10Part3_eq : shear reflectionClean10Part3=square moment10Part3 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part3,moment10Part3,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part4 : Poly := (((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(299556403542392832)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-5141271574904832)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-100206207074304)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(29860612486004736)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(145249023007457280)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-30422992425910272))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(244872425963520)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(32470139150401536)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-20769282027159552)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(1027096417271808)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-8705631717752832)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(-10727531636981760))))))

theorem moment10Part4_eq : shear reflectionClean10Part4=square moment10Part4 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part4,moment10Part4,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part5 : Poly := (((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(1085108257751040)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-1743654893912064)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(661215532548096)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(91947285872640)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(185194836393984)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((1+9)/2)*(X Coord.J : Poly)^9*(20061226008576))))) + ((((X Coord.K : Poly)^2*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-412258829129220096)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(19009199682551808)) + ((X Coord.K : Poly)^2*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-403853428260864)))) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(7818213851136)) + (((X Coord.K : Poly)^2*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(6115295232)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-13150464920064589824))))))

theorem moment10Part5_eq : shear reflectionClean10Part5=square moment10Part5 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part5,moment10Part5,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part6 : Poly := (((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(7490578609634623488)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1074125894882033664)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-15869968032301056)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-691019570479104)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(19221849980928)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(93245636404076544))))) + ((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-1594312423014629376)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-240029402699907072)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(4743924629667840)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(67437439377408)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(79758889488580608)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(6742504921595904))))))

theorem moment10Part6_eq : shear reflectionClean10Part6=square moment10Part6 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part6,moment10Part6,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part7 : Poly := (((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(35264505271320576)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-339866777124864)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-162275805732519936)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(37155767614193664)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(20442577957208064)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-1788924764307456))))) + ((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(21372728658886656)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(21837248204636160)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(-2644485466226688)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-2526460650455040)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(3281403593097216)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(-1958740337885184))))))

theorem moment10Part7_eq : shear reflectionClean10Part7=square moment10Part7 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part7,moment10Part7,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part8 : Poly := (((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-573416710078464)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(-648089051332608)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(5015306502144)))) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(-80802160312320)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-2447771852650954752)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(20716788679262208))))) + ((((X Coord.K : Poly)^3*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(1256456716075008)) + (((X Coord.K : Poly)^3*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-27614129209344)) + ((X Coord.K : Poly)^3*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-209066655744)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(-8554127497378209792)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(4188357258535084032)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1578703866224246784))))))

theorem moment10Part8_eq : shear reflectionClean10Part8=square moment10Part8 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part8,moment10Part8,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part9 : Poly := (((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(54261410809724928)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-266793322807296)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-44450211815424)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-518080260483588096)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-801251635915653120)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-151499636071022592))))) + ((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-14721930448404480)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-7410716614656)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(468204878877622272)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-66591881423290368)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-4292773429837824)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(1325204017053696))))))

theorem moment10Part9_eq : shear reflectionClean10Part9=square moment10Part9 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part9,moment10Part9,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part10 : Poly := (((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(-158036696275746816)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(49152197917605888)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(-34257886947311616)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(3518770258575360)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(10641226570924032)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-3685971650936832))))) + ((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(3117090387787776)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-229450272473088)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(1490381915553792)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(1283129018155008)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(-40122452017152)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(191696159637504))))))

theorem moment10Part10_eq : shear reflectionClean10Part10=square moment10Part10 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part10,moment10Part10,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part11 : Poly := (((((X Coord.K : Poly)^4*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-3961660559120695296)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-173128209213800448)) + ((X Coord.K : Poly)^4*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(5898464181780480)))) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-87926724108288)) + (((X Coord.K : Poly)^4*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(2911629017088)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(677116232091085824))))) + ((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(632117280995205120)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(1344442243046768640)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(1706936929468416)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(7781627281932288)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-69760642424832)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-1228382486731505664))))))

theorem moment10Part11_eq : shear reflectionClean10Part11=square moment10Part11 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part11,moment10Part11,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part12 : Poly := (((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-54432845479378944)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-113036754199707648)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(8431935683788800)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-896245999976448)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(633002521774915584)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-236508689461542912))))) + ((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(48716063613517824)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-3315615516721152)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(32705127157137408)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-26210932150173696)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(4425276589277184)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-3051879793754112))))))

theorem moment10Part12_eq : shear reflectionClean10Part12=square moment10Part12 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part12,moment10Part12,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part13 : Poly := (((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(1376701634838528)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-2049588590542848)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(-1604433700454400)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(140428582060032)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(-296460339904512)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-4382336574963588096))))) + ((((X Coord.K : Poly)^5*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-28115931239221248)) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-30272545686878208)) + ((X Coord.K : Poly)^5*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(1220349372668928)))) + (((X Coord.K : Poly)^5*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-21649604520960)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(328311602422530048)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(2303805099558223872))))))

theorem moment10Part13_eq : shear reflectionClean10Part13=square moment10Part13 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part13,moment10Part13,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part14 : Poly := (((((X Coord.K : Poly)^6*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-578663556564123648)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(211281541027430400)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-15769153018920960)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(658392165236736)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(53484012180504576)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(-974558059750490112))))) + ((((X Coord.K : Poly)^6*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(335431848736456704)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-48404603792130048)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(2351529262153728)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(-130820508628549632)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(48960675900555264)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-7059740472115200))))))

theorem moment10Part14_eq : shear reflectionClean10Part14=square moment10Part14 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part14,moment10Part14,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part15 : Poly := (((((X Coord.K : Poly)^6*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(1984745630859264)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-3441754087096320)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(1525489061068800)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(1318886295994368)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(-280857164120064)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(312063515688960))))) + ((((X Coord.K : Poly)^6*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-294241410708922368)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-613251565613383680)) + ((X Coord.K : Poly)^6*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(53149080840781824)))) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-4460464678846464)) + (((X Coord.K : Poly)^6*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(91471564873728)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(383949003059269632))))))

theorem moment10Part15_eq : shear reflectionClean10Part15=square moment10Part15 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part15,moment10Part15,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part16 : Poly := (((((X Coord.K : Poly)^7*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(-106968024361009152)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(682255339279220736)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-212576273746624512)))) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(26346124845121536)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-1070124255608832)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(196230762942824448))))) + ((((X Coord.K : Poly)^7*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-58131790753038336)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(8073877241069568)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-916075143364608)))) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(4589005449461760)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-493171806044160)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-713659540045824))))))

theorem moment10Part16_eq : shear reflectionClean10Part16=square moment10Part16 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part16,moment10Part16,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part17 : Poly := (((((X Coord.K : Poly)^7*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(351071455150080)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-226246048874496)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(-1288727614526312448)))) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(374568440387198976)) + (((X Coord.K : Poly)^7*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-88589516401631232)) + ((X Coord.K : Poly)^7*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(6618583363719168))))) + ((((X Coord.K : Poly)^7*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-213164635115520)) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-130820508628549632)) + ((X Coord.K : Poly)^8*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(36177913453215744)))) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-4810932762181632)) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(298317860831232)) + ((X Coord.K : Poly)^8*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-3441754087096320))))))

theorem moment10Part17_eq : shear reflectionClean10Part17=square moment10Part17 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part17,moment10Part17,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part18 : Poly := (((((X Coord.K : Poly)^8*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(-66034868944896)) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(245239200350208)) + ((X Coord.K : Poly)^8*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(-280857164120064)))) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(111451255603200)) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(53484012180504576)) + ((X Coord.K : Poly)^8*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(-182663105027899392))))) + ((((X Coord.K : Poly)^8*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(51833819612971008)) + (((X Coord.K : Poly)^8*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-5853234192187392)) + ((X Coord.K : Poly)^8*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(217846571433984)))) + (((X Coord.K : Poly)^9*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(1376701634838528)) + (((X Coord.K : Poly)^9*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(93619054706688)) + ((X Coord.K : Poly)^9*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-48574172233728))))))

theorem moment10Part18_eq : shear reflectionClean10Part18=square moment10Part18 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part18,moment10Part18,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part19 : Poly := (((((X Coord.K : Poly)^9*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(140428582060032)) + (((X Coord.K : Poly)^9*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-35664401793024)) + ((X Coord.K : Poly)^9*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(32705127157137408)))) + (((X Coord.K : Poly)^9*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-8910632371027968)) + (((X Coord.K : Poly)^9*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(1133703069106176)) + ((X Coord.K : Poly)^9*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-51534596210688))))) + ((((X Coord.K : Poly)^10*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(-40122452017152)) + (((X Coord.K : Poly)^10*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(6687075336192)) + ((X Coord.K : Poly)^10*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-229450272473088)))) + (((X Coord.K : Poly)^10*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(-19225341591552)) + (((X Coord.K : Poly)^10*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(4225860108288)) + ((X Coord.K : Poly)^11*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(5015306502144))))))

theorem moment10Part19_eq : shear reflectionClean10Part19=square moment10Part19 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part19,moment10Part19,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part20 : Poly := (((((X Coord.K : Poly)^11*(X Coord.U : Poly)^((10+0)/2)*(X Coord.J : Poly)^0*(-557256278016)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+1)/2)*(X Coord.J : Poly)^1*(160938316815925248)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+1)/2)*(X Coord.J : Poly)^1*(-481576059666432)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((5+1)/2)*(X Coord.J : Poly)^1*(-327177085648896)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((7+1)/2)*(X Coord.J : Poly)^1*(2299011268608)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((9+1)/2)*(X Coord.J : Poly)^1*(-8153726976))))) + ((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+2)/2)*(X Coord.J : Poly)^2*(-149299498311745536)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+2)/2)*(X Coord.J : Poly)^2*(1744681690202112)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+2)/2)*(X Coord.J : Poly)^2*(-2676914685739008)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((6+2)/2)*(X Coord.J : Poly)^2*(100337980538880)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((8+2)/2)*(X Coord.J : Poly)^2*(-173776306176)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+3)/2)*(X Coord.J : Poly)^3*(107262236326625280))))))

theorem moment10Part20_eq : shear reflectionClean10Part20=square moment10Part20 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part20,moment10Part20,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part21 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+3)/2)*(X Coord.J : Poly)^3*(-13136441311494144)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((5+3)/2)*(X Coord.J : Poly)^3*(734567543341056)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((7+3)/2)*(X Coord.J : Poly)^3*(-9730368995328)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+4)/2)*(X Coord.J : Poly)^4*(62072707151167488)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+4)/2)*(X Coord.J : Poly)^4*(-34686602777198592)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+4)/2)*(X Coord.J : Poly)^4*(2807707951300608))))) + ((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((6+4)/2)*(X Coord.J : Poly)^4*(-62408881078272)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+5)/2)*(X Coord.J : Poly)^5*(-21135383922475008)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+5)/2)*(X Coord.J : Poly)^5*(4463867016511488)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((5+5)/2)*(X Coord.J : Poly)^5*(-163763975356416)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+6)/2)*(X Coord.J : Poly)^6*(-5108809461792768)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+6)/2)*(X Coord.J : Poly)^6*(2867656286011392))))))

theorem moment10Part21_eq : shear reflectionClean10Part21=square moment10Part21 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part21,moment10Part21,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10Part22 : Poly := (((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+6)/2)*(X Coord.J : Poly)^6*(-205976998379520)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+7)/2)*(X Coord.J : Poly)^7*(914720701022208)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((3+7)/2)*(X Coord.J : Poly)^7*(-131452284174336)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+8)/2)*(X Coord.J : Poly)^8*(118649149194240)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+8)/2)*(X Coord.J : Poly)^8*(-48187188707328)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((1+9)/2)*(X Coord.J : Poly)^9*(-9287604633600))))) + ((((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+10)/2)*(X Coord.J : Poly)^10*(-743008370688)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((2+0)/2)*(X Coord.J : Poly)^0*(10648022001647616)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((4+0)/2)*(X Coord.J : Poly)^0*(332976678764544)))) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((6+0)/2)*(X Coord.J : Poly)^0*(-5278009393152)) + (((X Coord.K : Poly)^0*(X Coord.U : Poly)^((8+0)/2)*(X Coord.J : Poly)^0*(24461180928)) + ((X Coord.K : Poly)^0*(X Coord.U : Poly)^((0+0)/2)*(X Coord.J : Poly)^0*(0))))))

theorem moment10Part22_eq : shear reflectionClean10Part22=square moment10Part22 := by
  apply MvPolynomial.funext
  intro v
  simp [reflectionClean10Part22,moment10Part22,shear,square,shearCoord,squareCoord,map_ofNat] <;> ring

def moment10 : Poly := ((((moment10Part0 + moment10Part1) + (moment10Part2 + (moment10Part3 + moment10Part4))) + ((moment10Part5 + (moment10Part6 + moment10Part7)) + (moment10Part8 + (moment10Part9 + moment10Part10)))) + (((moment10Part11 + (moment10Part12 + moment10Part13)) + (moment10Part14 + (moment10Part15 + moment10Part16))) + ((moment10Part17 + (moment10Part18 + moment10Part19)) + (moment10Part20 + (moment10Part21 + moment10Part22)))))

theorem moment10_eq : shear (integerReflection 10)=square moment10 := by
  rw [reflectionBalanced10_eq,reflectionClean10_eq]
  simp only [reflectionClean10,moment10,map_add,moment10Part0_eq,moment10Part1_eq,moment10Part2_eq,moment10Part3_eq,moment10Part4_eq,moment10Part5_eq,moment10Part6_eq,moment10Part7_eq,moment10Part8_eq,moment10Part9_eq,moment10Part10_eq,moment10Part11_eq,moment10Part12_eq,moment10Part13_eq,moment10Part14_eq,moment10Part15_eq,moment10Part16_eq,moment10Part17_eq,moment10Part18_eq,moment10Part19_eq,moment10Part20_eq,moment10Part21_eq,moment10Part22_eq]

end
end HTGeometry.ThetaRatioSquare
