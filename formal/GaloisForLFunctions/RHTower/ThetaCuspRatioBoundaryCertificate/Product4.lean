import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.CofactorValues4
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryP4ReNorm (v k : ℂ) : {c : ℂ // (boundaryC4 v k*boundaryRT4 v k).re=c} := by
  have he : (boundaryC4 v k*boundaryRT4 v k).re=(boundaryC4 v k*boundaryRT4 v k).re := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.re_mul]
    rw [(boundaryC4ReNorm v k).property,(boundaryC4ImNorm v k).property]
    simp only [boundaryC4ReValue75_eq,boundaryC4ImValue75_eq]
    dsimp only [boundaryRT4]
    norm_num [boundaryC4ReValue75Part0,boundaryC4ReValue75Part1,boundaryC4ReValue75Part2,boundaryC4ReValue75Part3,boundaryC4ReValue75Part4,boundaryC4ReValue75Part5,boundaryC4ReValue75Part6,boundaryC4ReValue75Part7,boundaryC4ReValue75Part8,boundaryC4ReValue75Part9,boundaryC4ReValue75Part10,boundaryC4ReValue75Part11,boundaryC4ReValue75Part12,boundaryC4ReValue75,boundaryC4ImValue75Part0,boundaryC4ImValue75Part1,boundaryC4ImValue75Part2,boundaryC4ImValue75Part3,boundaryC4ImValue75Part4,boundaryC4ImValue75Part5,boundaryC4ImValue75Part6,boundaryC4ImValue75Part7,boundaryC4ImValue75Part8,boundaryC4ImValue75Part9,boundaryC4ImValue75Part10,boundaryC4ImValue75,boundaryRT4ReValue75Part0,boundaryRT4ReValue75Part1,boundaryRT4ReValue75Part2,boundaryRT4ReValue75,boundaryRT4ImValue75Part0,boundaryRT4ImValue75Part1,boundaryRT4ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryP4ImNorm (v k : ℂ) : {c : ℂ // (boundaryC4 v k*boundaryRT4 v k).im=c} := by
  have he : (boundaryC4 v k*boundaryRT4 v k).im=(boundaryC4 v k*boundaryRT4 v k).im := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.im_mul]
    rw [(boundaryC4ReNorm v k).property,(boundaryC4ImNorm v k).property]
    simp only [boundaryC4ReValue75_eq,boundaryC4ImValue75_eq]
    dsimp only [boundaryRT4]
    norm_num [boundaryC4ReValue75Part0,boundaryC4ReValue75Part1,boundaryC4ReValue75Part2,boundaryC4ReValue75Part3,boundaryC4ReValue75Part4,boundaryC4ReValue75Part5,boundaryC4ReValue75Part6,boundaryC4ReValue75Part7,boundaryC4ReValue75Part8,boundaryC4ReValue75Part9,boundaryC4ReValue75Part10,boundaryC4ReValue75Part11,boundaryC4ReValue75Part12,boundaryC4ReValue75,boundaryC4ImValue75Part0,boundaryC4ImValue75Part1,boundaryC4ImValue75Part2,boundaryC4ImValue75Part3,boundaryC4ImValue75Part4,boundaryC4ImValue75Part5,boundaryC4ImValue75Part6,boundaryC4ImValue75Part7,boundaryC4ImValue75Part8,boundaryC4ImValue75Part9,boundaryC4ImValue75Part10,boundaryC4ImValue75,boundaryRT4ReValue75Part0,boundaryRT4ReValue75Part1,boundaryRT4ReValue75Part2,boundaryRT4ReValue75,boundaryRT4ImValue75Part0,boundaryRT4ImValue75Part1,boundaryRT4ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
