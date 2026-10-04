import GaloisForLFunctions.RHTower.ThetaCuspRatioSquareMoments
/-! # Exact squared-coordinate algebra for the full modular third slope. -/

namespace HTGeometry.ThetaRatioSquare
noncomputable section
open MvPolynomial ThetaRatioSource

def minor : Poly :=
  -moment2*moment6*moment10+moment2*moment8^2+moment4^2*moment10-
  2*moment4*moment6*moment8+moment6^3

def seed : Poly := 6*X Coord.K-1

def slope : Poly := seed*squareLie minor-6*minor*squareLie seed

theorem minor_eq : shear integerThirdMinor=square minor := by
  unfold integerThirdMinor integerSignedMoment
  norm_num only
  simp only [map_sub,map_add,map_mul,map_neg,map_pow,map_ofNat,map_one,
    moment2_eq,moment4_eq,moment6_eq,moment8_eq,moment10_eq,minor]
  ring

theorem seed_eq : shear (integerJet 0)=square seed := by
  simp [integerJet,seed,shearCoord,squareCoord,map_ofNat]

/-- Exact polynomial conjugacy for the entire third-minor slope, with all mixed terms. -/
theorem slope_eq : X Coord.U*shear integerThirdSlope=square slope := by
  unfold integerThirdSlope
  simp only [map_sub,map_mul,map_ofNat]
  calc
    X Coord.U*(shear (integerJet 0)*shear (integerLie integerThirdMinor)-
        6*shear integerThirdMinor*shear (integerLie (integerJet 0))) =
      shear (integerJet 0)*chartLie (shear integerThirdMinor)-
        6*shear integerThirdMinor*chartLie (shear (integerJet 0)) := by
          rw [chartLie_shear,chartLie_shear]
          ring
    _ = square seed*square (squareLie minor)-
        6*square minor*square (squareLie seed) := by
          rw [minor_eq,seed_eq,chartLie_square,chartLie_square]
    _ = square slope := by simp [slope,map_ofNat]

end
end HTGeometry.ThetaRatioSquare
