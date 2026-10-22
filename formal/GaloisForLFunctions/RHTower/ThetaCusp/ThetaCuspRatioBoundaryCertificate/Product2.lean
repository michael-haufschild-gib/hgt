import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CofactorValues2
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryP2ReNorm (v k : ℂ) : {c : ℂ // (boundaryC2 v k*boundaryRT2 v k).re=c} := by
  have he : (boundaryC2 v k*boundaryRT2 v k).re=(boundaryC2 v k*boundaryRT2 v k).re := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.re_mul]
    rw [(boundaryC2ReNorm v k).property,(boundaryC2ImNorm v k).property]
    simp only [boundaryC2ReValue75_eq,boundaryC2ImValue75_eq]
    dsimp only [boundaryRT2]
    norm_num [boundaryC2ReValue75Part0,boundaryC2ReValue75Part1,boundaryC2ReValue75Part2,boundaryC2ReValue75Part3,boundaryC2ReValue75Part4,boundaryC2ReValue75Part5,boundaryC2ReValue75Part6,boundaryC2ReValue75Part7,boundaryC2ReValue75Part8,boundaryC2ReValue75Part9,boundaryC2ReValue75Part10,boundaryC2ReValue75Part11,boundaryC2ReValue75Part12,boundaryC2ReValue75Part13,boundaryC2ReValue75Part14,boundaryC2ReValue75Part15,boundaryC2ReValue75,boundaryC2ImValue75Part0,boundaryC2ImValue75Part1,boundaryC2ImValue75Part2,boundaryC2ImValue75Part3,boundaryC2ImValue75Part4,boundaryC2ImValue75Part5,boundaryC2ImValue75Part6,boundaryC2ImValue75Part7,boundaryC2ImValue75Part8,boundaryC2ImValue75Part9,boundaryC2ImValue75Part10,boundaryC2ImValue75Part11,boundaryC2ImValue75Part12,boundaryC2ImValue75Part13,boundaryC2ImValue75,boundaryRT2ReValue75Part0,boundaryRT2ReValue75Part1,boundaryRT2ReValue75,boundaryRT2ImValue75Part0,boundaryRT2ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryP2ImNorm (v k : ℂ) : {c : ℂ // (boundaryC2 v k*boundaryRT2 v k).im=c} := by
  have he : (boundaryC2 v k*boundaryRT2 v k).im=(boundaryC2 v k*boundaryRT2 v k).im := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.im_mul]
    rw [(boundaryC2ReNorm v k).property,(boundaryC2ImNorm v k).property]
    simp only [boundaryC2ReValue75_eq,boundaryC2ImValue75_eq]
    dsimp only [boundaryRT2]
    norm_num [boundaryC2ReValue75Part0,boundaryC2ReValue75Part1,boundaryC2ReValue75Part2,boundaryC2ReValue75Part3,boundaryC2ReValue75Part4,boundaryC2ReValue75Part5,boundaryC2ReValue75Part6,boundaryC2ReValue75Part7,boundaryC2ReValue75Part8,boundaryC2ReValue75Part9,boundaryC2ReValue75Part10,boundaryC2ReValue75Part11,boundaryC2ReValue75Part12,boundaryC2ReValue75Part13,boundaryC2ReValue75Part14,boundaryC2ReValue75Part15,boundaryC2ReValue75,boundaryC2ImValue75Part0,boundaryC2ImValue75Part1,boundaryC2ImValue75Part2,boundaryC2ImValue75Part3,boundaryC2ImValue75Part4,boundaryC2ImValue75Part5,boundaryC2ImValue75Part6,boundaryC2ImValue75Part7,boundaryC2ImValue75Part8,boundaryC2ImValue75Part9,boundaryC2ImValue75Part10,boundaryC2ImValue75Part11,boundaryC2ImValue75Part12,boundaryC2ImValue75Part13,boundaryC2ImValue75,boundaryRT2ReValue75Part0,boundaryRT2ReValue75Part1,boundaryRT2ReValue75,boundaryRT2ImValue75Part0,boundaryRT2ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
