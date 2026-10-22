import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.ColumnNorms
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.ReducedAssembly
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundarySlopeReColumns75 (v k : ℂ) : ℂ :=
  (((((boundarySlopeReVC75_0 k) + (v ^ Nat.rawCast 1 * (boundarySlopeReVC75_1 k))) + ((v ^ Nat.rawCast 2 * (boundarySlopeReVC75_2 k)) + (v ^ Nat.rawCast 3 * (boundarySlopeReVC75_3 k)))) + (((v ^ Nat.rawCast 4 * (boundarySlopeReVC75_4 k)) + (v ^ Nat.rawCast 5 * (boundarySlopeReVC75_5 k))) + ((v ^ Nat.rawCast 6 * (boundarySlopeReVC75_6 k)) + ((v ^ Nat.rawCast 7 * (boundarySlopeReVC75_7 k)) + (v ^ Nat.rawCast 8 * (boundarySlopeReVC75_8 k)))))) + ((((v ^ Nat.rawCast 9 * (boundarySlopeReVC75_9 k)) + (v ^ Nat.rawCast 10 * (boundarySlopeReVC75_10 k))) + ((v ^ Nat.rawCast 11 * (boundarySlopeReVC75_11 k)) + ((v ^ Nat.rawCast 12 * (boundarySlopeReVC75_12 k)) + (v ^ Nat.rawCast 13 * (boundarySlopeReVC75_13 k))))) + (((v ^ Nat.rawCast 14 * (boundarySlopeReVC75_14 k)) + (v ^ Nat.rawCast 15 * (boundarySlopeReVC75_15 k))) + ((v ^ Nat.rawCast 16 * (boundarySlopeReVC75_16 k)) + ((v ^ Nat.rawCast 17 * (boundarySlopeReVC75_17 k)) + (v ^ Nat.rawCast 18 * (boundarySlopeReVC75_18 k)))))))

theorem boundarySlopeReColumns75_eq (v k : ℂ) :
    (boundaryReducedSlope75 v k).re=boundarySlopeReColumns75 v k := by
  simp only [boundaryReducedSlope75,QuadraticAlgebra.re_add]
  rw [(boundaryP2ReNorm v k).property,(boundaryP4ReNorm v k).property,(boundaryP6ReNorm v k).property,(boundaryP8ReNorm v k).property,(boundaryP10ReNorm v k).property]
  rw [boundaryP2ReValue75_eq,boundaryP4ReValue75_eq,boundaryP6ReValue75_eq,boundaryP8ReValue75_eq,boundaryP10ReValue75_eq]
  rw [boundaryP2ReColumns75_eq,boundaryP4ReColumns75_eq,boundaryP6ReColumns75_eq,boundaryP8ReColumns75_eq,boundaryP10ReColumns75_eq]
  dsimp only [boundarySlopeReColumns75,boundaryP2ReColumns75,boundaryP4ReColumns75,boundaryP6ReColumns75,boundaryP8ReColumns75,boundaryP10ReColumns75,boundarySlopeReVC75_0,boundarySlopeReVC75_1,boundarySlopeReVC75_2,boundarySlopeReVC75_3,boundarySlopeReVC75_4,boundarySlopeReVC75_5,boundarySlopeReVC75_6,boundarySlopeReVC75_7,boundarySlopeReVC75_8,boundarySlopeReVC75_9,boundarySlopeReVC75_10,boundarySlopeReVC75_11,boundarySlopeReVC75_12,boundarySlopeReVC75_13,boundarySlopeReVC75_14,boundarySlopeReVC75_15,boundarySlopeReVC75_16,boundarySlopeReVC75_17,boundarySlopeReVC75_18]
  simp only [mul_add]
  ac_rfl

def boundarySlopeReNorm75 (v k : ℂ) : {c : ℂ // (boundaryReducedSlope75 v k).re=c} := by
  have he := boundarySlopeReColumns75_eq v k
  conv at he =>
    rhs
    dsimp only [boundarySlopeReColumns75]
    rw [(boundarySlopeReVC75_0Norm k).property,(boundarySlopeReVC75_1Norm k).property,(boundarySlopeReVC75_2Norm k).property,(boundarySlopeReVC75_3Norm k).property,(boundarySlopeReVC75_4Norm k).property,(boundarySlopeReVC75_5Norm k).property,(boundarySlopeReVC75_6Norm k).property,(boundarySlopeReVC75_7Norm k).property,(boundarySlopeReVC75_8Norm k).property,(boundarySlopeReVC75_9Norm k).property,(boundarySlopeReVC75_10Norm k).property,(boundarySlopeReVC75_11Norm k).property,(boundarySlopeReVC75_12Norm k).property,(boundarySlopeReVC75_13Norm k).property,(boundarySlopeReVC75_14Norm k).property,(boundarySlopeReVC75_15Norm k).property,(boundarySlopeReVC75_16Norm k).property,(boundarySlopeReVC75_17Norm k).property,(boundarySlopeReVC75_18Norm k).property]
  exact ⟨_,he⟩

def boundarySlopeImColumns75 (v k : ℂ) : ℂ :=
  (((((boundarySlopeImVC75_0 k) + (v ^ Nat.rawCast 1 * (boundarySlopeImVC75_1 k))) + ((v ^ Nat.rawCast 2 * (boundarySlopeImVC75_2 k)) + (v ^ Nat.rawCast 3 * (boundarySlopeImVC75_3 k)))) + (((v ^ Nat.rawCast 4 * (boundarySlopeImVC75_4 k)) + (v ^ Nat.rawCast 5 * (boundarySlopeImVC75_5 k))) + ((v ^ Nat.rawCast 6 * (boundarySlopeImVC75_6 k)) + ((v ^ Nat.rawCast 7 * (boundarySlopeImVC75_7 k)) + (v ^ Nat.rawCast 8 * (boundarySlopeImVC75_8 k)))))) + ((((v ^ Nat.rawCast 9 * (boundarySlopeImVC75_9 k)) + (v ^ Nat.rawCast 10 * (boundarySlopeImVC75_10 k))) + ((v ^ Nat.rawCast 11 * (boundarySlopeImVC75_11 k)) + ((v ^ Nat.rawCast 12 * (boundarySlopeImVC75_12 k)) + (v ^ Nat.rawCast 13 * (boundarySlopeImVC75_13 k))))) + (((v ^ Nat.rawCast 14 * (boundarySlopeImVC75_14 k)) + (v ^ Nat.rawCast 15 * (boundarySlopeImVC75_15 k))) + ((v ^ Nat.rawCast 16 * (boundarySlopeImVC75_16 k)) + ((v ^ Nat.rawCast 17 * (boundarySlopeImVC75_17 k)) + (v ^ Nat.rawCast 18 * (boundarySlopeImVC75_18 k)))))))

theorem boundarySlopeImColumns75_eq (v k : ℂ) :
    (boundaryReducedSlope75 v k).im=boundarySlopeImColumns75 v k := by
  simp only [boundaryReducedSlope75,QuadraticAlgebra.im_add]
  rw [(boundaryP2ImNorm v k).property,(boundaryP4ImNorm v k).property,(boundaryP6ImNorm v k).property,(boundaryP8ImNorm v k).property,(boundaryP10ImNorm v k).property]
  rw [boundaryP2ImValue75_eq,boundaryP4ImValue75_eq,boundaryP6ImValue75_eq,boundaryP8ImValue75_eq,boundaryP10ImValue75_eq]
  rw [boundaryP2ImColumns75_eq,boundaryP4ImColumns75_eq,boundaryP6ImColumns75_eq,boundaryP8ImColumns75_eq,boundaryP10ImColumns75_eq]
  dsimp only [boundarySlopeImColumns75,boundaryP2ImColumns75,boundaryP4ImColumns75,boundaryP6ImColumns75,boundaryP8ImColumns75,boundaryP10ImColumns75,boundarySlopeImVC75_0,boundarySlopeImVC75_1,boundarySlopeImVC75_2,boundarySlopeImVC75_3,boundarySlopeImVC75_4,boundarySlopeImVC75_5,boundarySlopeImVC75_6,boundarySlopeImVC75_7,boundarySlopeImVC75_8,boundarySlopeImVC75_9,boundarySlopeImVC75_10,boundarySlopeImVC75_11,boundarySlopeImVC75_12,boundarySlopeImVC75_13,boundarySlopeImVC75_14,boundarySlopeImVC75_15,boundarySlopeImVC75_16,boundarySlopeImVC75_17,boundarySlopeImVC75_18]
  simp only [mul_add]
  ac_rfl

def boundarySlopeImNorm75 (v k : ℂ) : {c : ℂ // (boundaryReducedSlope75 v k).im=c} := by
  have he := boundarySlopeImColumns75_eq v k
  conv at he =>
    rhs
    dsimp only [boundarySlopeImColumns75]
    rw [(boundarySlopeImVC75_0Norm k).property,(boundarySlopeImVC75_1Norm k).property,(boundarySlopeImVC75_2Norm k).property,(boundarySlopeImVC75_3Norm k).property,(boundarySlopeImVC75_4Norm k).property,(boundarySlopeImVC75_5Norm k).property,(boundarySlopeImVC75_6Norm k).property,(boundarySlopeImVC75_7Norm k).property,(boundarySlopeImVC75_8Norm k).property,(boundarySlopeImVC75_9Norm k).property,(boundarySlopeImVC75_10Norm k).property,(boundarySlopeImVC75_11Norm k).property,(boundarySlopeImVC75_12Norm k).property,(boundarySlopeImVC75_13Norm k).property,(boundarySlopeImVC75_14Norm k).property,(boundarySlopeImVC75_15Norm k).property,(boundarySlopeImVC75_16Norm k).property,(boundarySlopeImVC75_17Norm k).property,(boundarySlopeImVC75_18Norm k).property]
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
