import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.CofactorValues6
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryP6ReNorm (v k : ℂ) : {c : ℂ // (boundaryC6 v k*boundaryRT6 v k).re=c} := by
  have he : (boundaryC6 v k*boundaryRT6 v k).re=(boundaryC6 v k*boundaryRT6 v k).re := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.re_mul]
    rw [(boundaryC6ReNorm v k).property,(boundaryC6ImNorm v k).property]
    simp only [boundaryC6ReValue75_eq,boundaryC6ImValue75_eq]
    dsimp only [boundaryRT6]
    norm_num [boundaryC6ReValue75Part0,boundaryC6ReValue75Part1,boundaryC6ReValue75Part2,boundaryC6ReValue75Part3,boundaryC6ReValue75Part4,boundaryC6ReValue75Part5,boundaryC6ReValue75Part6,boundaryC6ReValue75Part7,boundaryC6ReValue75Part8,boundaryC6ReValue75Part9,boundaryC6ReValue75,boundaryC6ImValue75Part0,boundaryC6ImValue75Part1,boundaryC6ImValue75Part2,boundaryC6ImValue75Part3,boundaryC6ImValue75Part4,boundaryC6ImValue75Part5,boundaryC6ImValue75Part6,boundaryC6ImValue75Part7,boundaryC6ImValue75Part8,boundaryC6ImValue75,boundaryRT6ReValue75Part0,boundaryRT6ReValue75Part1,boundaryRT6ReValue75Part2,boundaryRT6ReValue75Part3,boundaryRT6ReValue75,boundaryRT6ImValue75Part0,boundaryRT6ImValue75Part1,boundaryRT6ImValue75Part2,boundaryRT6ImValue75Part3,boundaryRT6ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryP6ImNorm (v k : ℂ) : {c : ℂ // (boundaryC6 v k*boundaryRT6 v k).im=c} := by
  have he : (boundaryC6 v k*boundaryRT6 v k).im=(boundaryC6 v k*boundaryRT6 v k).im := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.im_mul]
    rw [(boundaryC6ReNorm v k).property,(boundaryC6ImNorm v k).property]
    simp only [boundaryC6ReValue75_eq,boundaryC6ImValue75_eq]
    dsimp only [boundaryRT6]
    norm_num [boundaryC6ReValue75Part0,boundaryC6ReValue75Part1,boundaryC6ReValue75Part2,boundaryC6ReValue75Part3,boundaryC6ReValue75Part4,boundaryC6ReValue75Part5,boundaryC6ReValue75Part6,boundaryC6ReValue75Part7,boundaryC6ReValue75Part8,boundaryC6ReValue75Part9,boundaryC6ReValue75,boundaryC6ImValue75Part0,boundaryC6ImValue75Part1,boundaryC6ImValue75Part2,boundaryC6ImValue75Part3,boundaryC6ImValue75Part4,boundaryC6ImValue75Part5,boundaryC6ImValue75Part6,boundaryC6ImValue75Part7,boundaryC6ImValue75Part8,boundaryC6ImValue75,boundaryRT6ReValue75Part0,boundaryRT6ReValue75Part1,boundaryRT6ReValue75Part2,boundaryRT6ReValue75Part3,boundaryRT6ReValue75,boundaryRT6ImValue75Part0,boundaryRT6ImValue75Part1,boundaryRT6ImValue75Part2,boundaryRT6ImValue75Part3,boundaryRT6ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
