import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CofactorValues8
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryP8ReNorm (v k : ℂ) : {c : ℂ // (boundaryC8 v k*boundaryRT8 v k).re=c} := by
  have he : (boundaryC8 v k*boundaryRT8 v k).re=(boundaryC8 v k*boundaryRT8 v k).re := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.re_mul]
    rw [(boundaryC8ReNorm v k).property,(boundaryC8ImNorm v k).property]
    simp only [boundaryC8ReValue75_eq,boundaryC8ImValue75_eq]
    dsimp only [boundaryRT8]
    norm_num [boundaryC8ReValue75Part0,boundaryC8ReValue75Part1,boundaryC8ReValue75Part2,boundaryC8ReValue75Part3,boundaryC8ReValue75Part4,boundaryC8ReValue75Part5,boundaryC8ReValue75Part6,boundaryC8ReValue75Part7,boundaryC8ReValue75,boundaryC8ImValue75Part0,boundaryC8ImValue75Part1,boundaryC8ImValue75Part2,boundaryC8ImValue75Part3,boundaryC8ImValue75Part4,boundaryC8ImValue75Part5,boundaryC8ImValue75,boundaryRT8ReValue75Part0,boundaryRT8ReValue75Part1,boundaryRT8ReValue75Part2,boundaryRT8ReValue75Part3,boundaryRT8ReValue75Part4,boundaryRT8ReValue75Part5,boundaryRT8ReValue75,boundaryRT8ImValue75Part0,boundaryRT8ImValue75Part1,boundaryRT8ImValue75Part2,boundaryRT8ImValue75Part3,boundaryRT8ImValue75Part4,boundaryRT8ImValue75Part5,boundaryRT8ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryP8ImNorm (v k : ℂ) : {c : ℂ // (boundaryC8 v k*boundaryRT8 v k).im=c} := by
  have he : (boundaryC8 v k*boundaryRT8 v k).im=(boundaryC8 v k*boundaryRT8 v k).im := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.im_mul]
    rw [(boundaryC8ReNorm v k).property,(boundaryC8ImNorm v k).property]
    simp only [boundaryC8ReValue75_eq,boundaryC8ImValue75_eq]
    dsimp only [boundaryRT8]
    norm_num [boundaryC8ReValue75Part0,boundaryC8ReValue75Part1,boundaryC8ReValue75Part2,boundaryC8ReValue75Part3,boundaryC8ReValue75Part4,boundaryC8ReValue75Part5,boundaryC8ReValue75Part6,boundaryC8ReValue75Part7,boundaryC8ReValue75,boundaryC8ImValue75Part0,boundaryC8ImValue75Part1,boundaryC8ImValue75Part2,boundaryC8ImValue75Part3,boundaryC8ImValue75Part4,boundaryC8ImValue75Part5,boundaryC8ImValue75,boundaryRT8ReValue75Part0,boundaryRT8ReValue75Part1,boundaryRT8ReValue75Part2,boundaryRT8ReValue75Part3,boundaryRT8ReValue75Part4,boundaryRT8ReValue75Part5,boundaryRT8ReValue75,boundaryRT8ImValue75Part0,boundaryRT8ImValue75Part1,boundaryRT8ImValue75Part2,boundaryRT8ImValue75Part3,boundaryRT8ImValue75Part4,boundaryRT8ImValue75Part5,boundaryRT8ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
