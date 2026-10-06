import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.AssemblyValues
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar10
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryC10 (v k : ℂ) : BoundaryAlg v k := cof10_75 (boundaryQM2 v k) (boundaryQM4 v k) (boundaryQM6 v k)

def boundaryC10ReNorm (v k : ℂ) : {c : ℂ // (boundaryC10 v k).re=c} := by
  have he : (boundaryC10 v k).re=(boundaryC10 v k).re := rfl
  conv at he =>
    rhs
    norm_num [pow_two,boundaryC10,cof10_75,boundaryQM2,boundaryMoment2ReNorm,boundaryMoment2ImNorm,boundaryQM4,boundaryMoment4ReNorm,boundaryMoment4ImNorm,boundaryQM6,boundaryMoment6ReNorm,boundaryMoment6ImNorm,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryC10ImNorm (v k : ℂ) : {c : ℂ // (boundaryC10 v k).im=c} := by
  have he : (boundaryC10 v k).im=(boundaryC10 v k).im := rfl
  conv at he =>
    rhs
    norm_num [pow_two,boundaryC10,cof10_75,boundaryQM2,boundaryMoment2ReNorm,boundaryMoment2ImNorm,boundaryQM4,boundaryMoment4ReNorm,boundaryMoment4ImNorm,boundaryQM6,boundaryMoment6ReNorm,boundaryMoment6ImNorm,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryT10ReNorm (v k : ℂ) : {c : ℂ // (boundaryT10 v k).re=c} := by
  have he : (boundaryT10 v k).re=(boundaryT10 v k).re := rfl
  conv at he =>
    rhs
    simp only [boundaryT10,QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM10,boundaryQF10]
    simp only [boundaryMoment10ReValue75_eq,boundaryMoment10ImValue75_eq,
      boundaryFlow10ReValue75_eq,boundaryFlow10ImValue75_eq]
    norm_num [boundaryMoment10ReValue75,boundaryMoment10ImValue75,
      boundaryFlow10ReValue75,boundaryFlow10ImValue75,boundaryMoment10ReValue75Part0,boundaryMoment10ReValue75Part1,boundaryMoment10ReValue75Part2,boundaryMoment10ReValue75Part3,boundaryMoment10ReValue75Part4,boundaryMoment10ReValue75Part5,boundaryMoment10ReValue75Part6,boundaryMoment10ImValue75Part0,boundaryMoment10ImValue75Part1,boundaryMoment10ImValue75Part2,boundaryMoment10ImValue75Part3,boundaryMoment10ImValue75Part4,boundaryMoment10ImValue75Part5,boundaryFlow10ReValue75Part0,boundaryFlow10ReValue75Part1,boundaryFlow10ReValue75Part2,boundaryFlow10ReValue75Part3,boundaryFlow10ReValue75Part4,boundaryFlow10ReValue75Part5,boundaryFlow10ReValue75Part6,boundaryFlow10ReValue75Part7,boundaryFlow10ImValue75Part0,boundaryFlow10ImValue75Part1,boundaryFlow10ImValue75Part2,boundaryFlow10ImValue75Part3,boundaryFlow10ImValue75Part4,boundaryFlow10ImValue75Part5,boundaryFlow10ImValue75Part6,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryT10ImNorm (v k : ℂ) : {c : ℂ // (boundaryT10 v k).im=c} := by
  have he : (boundaryT10 v k).im=(boundaryT10 v k).im := rfl
  conv at he =>
    rhs
    simp only [boundaryT10,QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM10,boundaryQF10]
    simp only [boundaryMoment10ReValue75_eq,boundaryMoment10ImValue75_eq,
      boundaryFlow10ReValue75_eq,boundaryFlow10ImValue75_eq]
    norm_num [boundaryMoment10ReValue75,boundaryMoment10ImValue75,
      boundaryFlow10ReValue75,boundaryFlow10ImValue75,boundaryMoment10ReValue75Part0,boundaryMoment10ReValue75Part1,boundaryMoment10ReValue75Part2,boundaryMoment10ReValue75Part3,boundaryMoment10ReValue75Part4,boundaryMoment10ReValue75Part5,boundaryMoment10ReValue75Part6,boundaryMoment10ImValue75Part0,boundaryMoment10ImValue75Part1,boundaryMoment10ImValue75Part2,boundaryMoment10ImValue75Part3,boundaryMoment10ImValue75Part4,boundaryMoment10ImValue75Part5,boundaryFlow10ReValue75Part0,boundaryFlow10ReValue75Part1,boundaryFlow10ReValue75Part2,boundaryFlow10ReValue75Part3,boundaryFlow10ReValue75Part4,boundaryFlow10ReValue75Part5,boundaryFlow10ReValue75Part6,boundaryFlow10ReValue75Part7,boundaryFlow10ImValue75Part0,boundaryFlow10ImValue75Part1,boundaryFlow10ImValue75Part2,boundaryFlow10ImValue75Part3,boundaryFlow10ImValue75Part4,boundaryFlow10ImValue75Part5,boundaryFlow10ImValue75Part6,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
