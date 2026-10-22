import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.SlopeAssembly
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CofactorValues2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CofactorValues4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CofactorValues6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CofactorValues8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CofactorValues10
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare
def boundaryReducedSlope75 (v k : ℂ) : BoundaryAlg v k :=
  boundaryC2 v k*boundaryRT2 v k+boundaryC4 v k*boundaryRT4 v k+
    boundaryC6 v k*boundaryRT6 v k+boundaryC8 v k*boundaryRT8 v k+
      boundaryC10 v k*boundaryRT10 v k

theorem boundarySlope_factor75 (v k : ℂ) : boundarySlope75 v k=
    algebraMap ℂ (BoundaryAlg v k) v*boundaryReducedSlope75 v k := by
  unfold boundarySlope75 boundaryReducedSlope75
  rw [boundaryT2_factor,boundaryT4_factor,boundaryT6_factor,boundaryT8_factor,boundaryT10_factor]
  ring

theorem boundaryReducedSlope_evaluate75 (v k z : ℂ)
    (hz : z^2=boundaryA v k+boundaryB k*z) :
    (((6:ℂ)^24*24^9)⁻¹)*eval (basePoint v k z) ThetaRatioSquare.slope=
      v*((boundaryReducedSlope75 v k).re+z*(boundaryReducedSlope75 v k).im) := by
  rw [boundarySlope_evaluate75 v k z hz,boundarySlope_factor75]
  simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
    zero_mul,mul_zero,zero_add,add_zero]
  ring

end
end HTGeometry.ThetaRatioInfinity
