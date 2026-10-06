import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Cofactor2
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Cofactor4
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Cofactor6
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Cofactor8
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Cofactor10
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def boundarySlope75 (v k : ℂ) : BoundaryAlg v k :=
  boundaryC2 v k*boundaryT2 v k+boundaryC4 v k*boundaryT4 v k+
    boundaryC6 v k*boundaryT6 v k+boundaryC8 v k*boundaryT8 v k+
      boundaryC10 v k*boundaryT10 v k

theorem boundaryHom_seed75 (v k : ℂ) : boundaryHom v k seed=
    algebraMap ℂ (BoundaryAlg v k) (6*k-1) := by
  simp [seed,boundaryCoord,map_ofNat]

theorem boundaryHom_seedFlow75 (v k : ℂ) : boundaryHom v k (squareLie seed)=
    (⟨0,6*(12*k+4)*v⟩ : BoundaryAlg v k) := by
  rw [squareLie_seed75]
  ext <;> norm_num [squareField,boundaryCoord,map_ofNat] <;> ring

theorem boundarySlope_source75 (v k : ℂ) :
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^24*24^9)⁻¹)*boundaryHom v k ThetaRatioSquare.slope=
      boundarySlope75 v k := by
  rw [slope_cofactors75]
  unfold boundarySlope75 boundaryC2 boundaryC4 boundaryC6 boundaryC8 boundaryC10
    boundaryT2 boundaryT4 boundaryT6 boundaryT8 boundaryT10
    cof2_75 cof4_75 cof6_75 cof8_75 cof10_75
  rw [boundaryQM2_eq,boundaryQM4_eq,boundaryQM6_eq,boundaryQM8_eq,boundaryQM10_eq,
    boundaryQF2_eq,boundaryQF4_eq,boundaryQF6_eq,boundaryQF8_eq,boundaryQF10_eq]
  simp only [map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,
    boundaryHom_seed75,boundaryHom_seedFlow75]
  ext <;> norm_num [pow_two] <;> ring

theorem boundarySlope_evaluate75 (v k z : ℂ)
    (hz : z^2=boundaryA v k+boundaryB k*z) :
    (((6:ℂ)^24*24^9)⁻¹)*eval (basePoint v k z) ThetaRatioSquare.slope=
      (boundarySlope75 v k).re+z*(boundarySlope75 v k).im := by
  have he := congrArg (boundaryEval v k z hz) (boundarySlope_source75 v k)
  rw [map_mul,boundaryEval_C] at he
  have hs : boundaryEval v k z hz (boundaryHom v k ThetaRatioSquare.slope)=
      eval (basePoint v k z) ThetaRatioSquare.slope :=
    (boundaryHom_eval ThetaRatioSquare.slope v k z hz).symm
  rw [hs] at he
  exact he

end
end HTGeometry.ThetaRatioInfinity
