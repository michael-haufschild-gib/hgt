import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.CofactorValues10
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryP10ReNorm (v k : ℂ) : {c : ℂ // (boundaryC10 v k*boundaryRT10 v k).re=c} := by
  have he : (boundaryC10 v k*boundaryRT10 v k).re=(boundaryC10 v k*boundaryRT10 v k).re := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.re_mul]
    rw [(boundaryC10ReNorm v k).property,(boundaryC10ImNorm v k).property]
    simp only [boundaryC10ReValue75_eq,boundaryC10ImValue75_eq]
    dsimp only [boundaryRT10]
    norm_num [boundaryC10ReValue75Part0,boundaryC10ReValue75Part1,boundaryC10ReValue75Part2,boundaryC10ReValue75Part3,boundaryC10ReValue75Part4,boundaryC10ReValue75,boundaryC10ImValue75Part0,boundaryC10ImValue75Part1,boundaryC10ImValue75Part2,boundaryC10ImValue75Part3,boundaryC10ImValue75,boundaryRT10ReValue75Part0,boundaryRT10ReValue75Part1,boundaryRT10ReValue75Part2,boundaryRT10ReValue75Part3,boundaryRT10ReValue75Part4,boundaryRT10ReValue75Part5,boundaryRT10ReValue75Part6,boundaryRT10ReValue75Part7,boundaryRT10ReValue75Part8,boundaryRT10ReValue75,boundaryRT10ImValue75Part0,boundaryRT10ImValue75Part1,boundaryRT10ImValue75Part2,boundaryRT10ImValue75Part3,boundaryRT10ImValue75Part4,boundaryRT10ImValue75Part5,boundaryRT10ImValue75Part6,boundaryRT10ImValue75Part7,boundaryRT10ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryP10ImNorm (v k : ℂ) : {c : ℂ // (boundaryC10 v k*boundaryRT10 v k).im=c} := by
  have he : (boundaryC10 v k*boundaryRT10 v k).im=(boundaryC10 v k*boundaryRT10 v k).im := rfl
  conv at he =>
    rhs
    simp only [QuadraticAlgebra.im_mul]
    rw [(boundaryC10ReNorm v k).property,(boundaryC10ImNorm v k).property]
    simp only [boundaryC10ReValue75_eq,boundaryC10ImValue75_eq]
    dsimp only [boundaryRT10]
    norm_num [boundaryC10ReValue75Part0,boundaryC10ReValue75Part1,boundaryC10ReValue75Part2,boundaryC10ReValue75Part3,boundaryC10ReValue75Part4,boundaryC10ReValue75,boundaryC10ImValue75Part0,boundaryC10ImValue75Part1,boundaryC10ImValue75Part2,boundaryC10ImValue75Part3,boundaryC10ImValue75,boundaryRT10ReValue75Part0,boundaryRT10ReValue75Part1,boundaryRT10ReValue75Part2,boundaryRT10ReValue75Part3,boundaryRT10ReValue75Part4,boundaryRT10ReValue75Part5,boundaryRT10ReValue75Part6,boundaryRT10ReValue75Part7,boundaryRT10ReValue75Part8,boundaryRT10ReValue75,boundaryRT10ImValue75Part0,boundaryRT10ImValue75Part1,boundaryRT10ImValue75Part2,boundaryRT10ImValue75Part3,boundaryRT10ImValue75Part4,boundaryRT10ImValue75Part5,boundaryRT10ImValue75Part6,boundaryRT10ImValue75Part7,boundaryRT10ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
