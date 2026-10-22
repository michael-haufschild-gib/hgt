import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CompactRe
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CompactIm
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare
def boundaryCompactA75 (h r : ℂ) : ℂ :=
  (((((boundaryCompactReVC75_0 h) + ((9-r*h^2) ^ Nat.rawCast 1 * (boundaryCompactReVC75_1 h))) + (((9-r*h^2) ^ Nat.rawCast 2 * (boundaryCompactReVC75_2 h)) + ((9-r*h^2) ^ Nat.rawCast 3 * (boundaryCompactReVC75_3 h)))) + ((((9-r*h^2) ^ Nat.rawCast 4 * (boundaryCompactReVC75_4 h)) + ((9-r*h^2) ^ Nat.rawCast 5 * (boundaryCompactReVC75_5 h))) + (((9-r*h^2) ^ Nat.rawCast 6 * (boundaryCompactReVC75_6 h)) + (((9-r*h^2) ^ Nat.rawCast 7 * (boundaryCompactReVC75_7 h)) + ((9-r*h^2) ^ Nat.rawCast 8 * (boundaryCompactReVC75_8 h)))))) + (((((9-r*h^2) ^ Nat.rawCast 9 * (boundaryCompactReVC75_9 h)) + ((9-r*h^2) ^ Nat.rawCast 10 * (boundaryCompactReVC75_10 h))) + (((9-r*h^2) ^ Nat.rawCast 11 * (boundaryCompactReVC75_11 h)) + (((9-r*h^2) ^ Nat.rawCast 12 * (boundaryCompactReVC75_12 h)) + ((9-r*h^2) ^ Nat.rawCast 13 * (boundaryCompactReVC75_13 h))))) + ((((9-r*h^2) ^ Nat.rawCast 14 * (boundaryCompactReVC75_14 h)) + ((9-r*h^2) ^ Nat.rawCast 15 * (boundaryCompactReVC75_15 h))) + (((9-r*h^2) ^ Nat.rawCast 16 * (boundaryCompactReVC75_16 h)) + (((9-r*h^2) ^ Nat.rawCast 17 * (boundaryCompactReVC75_17 h)) + ((9-r*h^2) ^ Nat.rawCast 18 * (boundaryCompactReVC75_18 h)))))))

theorem boundaryCompactA75_eq {h : ℂ} (hh : h≠0) (r : ℂ) :
    h^22*(boundaryReducedSlope75 (9-r*h^2) h⁻¹).re=boundaryCompactA75 h r := by
  rw [boundarySlopeReColumns75_eq]
  dsimp only [boundarySlopeReColumns75,boundaryCompactA75]
  rw [← boundaryCompactReVC75_0_eq hh,← boundaryCompactReVC75_1_eq hh,← boundaryCompactReVC75_2_eq hh,← boundaryCompactReVC75_3_eq hh,← boundaryCompactReVC75_4_eq hh,← boundaryCompactReVC75_5_eq hh,← boundaryCompactReVC75_6_eq hh,← boundaryCompactReVC75_7_eq hh,← boundaryCompactReVC75_8_eq hh,← boundaryCompactReVC75_9_eq hh,← boundaryCompactReVC75_10_eq hh,← boundaryCompactReVC75_11_eq hh,← boundaryCompactReVC75_12_eq hh,← boundaryCompactReVC75_13_eq hh,← boundaryCompactReVC75_14_eq hh,← boundaryCompactReVC75_15_eq hh,← boundaryCompactReVC75_16_eq hh,← boundaryCompactReVC75_17_eq hh,← boundaryCompactReVC75_18_eq hh]
  simp only [mul_add]
  ac_rfl

def boundaryCompactB75 (h r : ℂ) : ℂ :=
  (((((boundaryCompactImVC75_0 h) + ((9-r*h^2) ^ Nat.rawCast 1 * (boundaryCompactImVC75_1 h))) + (((9-r*h^2) ^ Nat.rawCast 2 * (boundaryCompactImVC75_2 h)) + ((9-r*h^2) ^ Nat.rawCast 3 * (boundaryCompactImVC75_3 h)))) + ((((9-r*h^2) ^ Nat.rawCast 4 * (boundaryCompactImVC75_4 h)) + ((9-r*h^2) ^ Nat.rawCast 5 * (boundaryCompactImVC75_5 h))) + (((9-r*h^2) ^ Nat.rawCast 6 * (boundaryCompactImVC75_6 h)) + (((9-r*h^2) ^ Nat.rawCast 7 * (boundaryCompactImVC75_7 h)) + ((9-r*h^2) ^ Nat.rawCast 8 * (boundaryCompactImVC75_8 h)))))) + (((((9-r*h^2) ^ Nat.rawCast 9 * (boundaryCompactImVC75_9 h)) + ((9-r*h^2) ^ Nat.rawCast 10 * (boundaryCompactImVC75_10 h))) + (((9-r*h^2) ^ Nat.rawCast 11 * (boundaryCompactImVC75_11 h)) + (((9-r*h^2) ^ Nat.rawCast 12 * (boundaryCompactImVC75_12 h)) + ((9-r*h^2) ^ Nat.rawCast 13 * (boundaryCompactImVC75_13 h))))) + ((((9-r*h^2) ^ Nat.rawCast 14 * (boundaryCompactImVC75_14 h)) + ((9-r*h^2) ^ Nat.rawCast 15 * (boundaryCompactImVC75_15 h))) + (((9-r*h^2) ^ Nat.rawCast 16 * (boundaryCompactImVC75_16 h)) + (((9-r*h^2) ^ Nat.rawCast 17 * (boundaryCompactImVC75_17 h)) + ((9-r*h^2) ^ Nat.rawCast 18 * (boundaryCompactImVC75_18 h)))))))

theorem boundaryCompactB75_eq {h : ℂ} (hh : h≠0) (r : ℂ) :
    h^21*(boundaryReducedSlope75 (9-r*h^2) h⁻¹).im=boundaryCompactB75 h r := by
  rw [boundarySlopeImColumns75_eq]
  dsimp only [boundarySlopeImColumns75,boundaryCompactB75]
  rw [← boundaryCompactImVC75_0_eq hh,← boundaryCompactImVC75_1_eq hh,← boundaryCompactImVC75_2_eq hh,← boundaryCompactImVC75_3_eq hh,← boundaryCompactImVC75_4_eq hh,← boundaryCompactImVC75_5_eq hh,← boundaryCompactImVC75_6_eq hh,← boundaryCompactImVC75_7_eq hh,← boundaryCompactImVC75_8_eq hh,← boundaryCompactImVC75_9_eq hh,← boundaryCompactImVC75_10_eq hh,← boundaryCompactImVC75_11_eq hh,← boundaryCompactImVC75_12_eq hh,← boundaryCompactImVC75_13_eq hh,← boundaryCompactImVC75_14_eq hh,← boundaryCompactImVC75_15_eq hh,← boundaryCompactImVC75_16_eq hh,← boundaryCompactImVC75_17_eq hh,← boundaryCompactImVC75_18_eq hh]
  simp only [mul_add]
  ac_rfl

theorem boundaryCompactSlope_evaluate75 {h : ℂ} (hh : h≠0) (r z : ℂ)
    (hz : z^2=boundaryA (9-r*h^2) h⁻¹+boundaryB h⁻¹*z) :
    h^22*(((6:ℂ)^24*24^9)⁻¹)*eval (basePoint (9-r*h^2) h⁻¹ z) ThetaRatioSquare.slope=
      (9-r*h^2)*(boundaryCompactA75 h r+h*z*boundaryCompactB75 h r) := by
  have he := boundaryReducedSlope_evaluate75 (9-r*h^2) h⁻¹ z hz
  have ha := boundaryCompactA75_eq hh r
  have hb := boundaryCompactB75_eq hh r
  linear_combination h^22*he+(9-r*h^2)*ha+(9-r*h^2)*h*z*hb

end
end HTGeometry.ThetaRatioInfinity
