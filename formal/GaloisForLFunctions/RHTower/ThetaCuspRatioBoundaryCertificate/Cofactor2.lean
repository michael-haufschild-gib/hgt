import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.AssemblyValues
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar2
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar6
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar8
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar10
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryC2 (v k : ℂ) : BoundaryAlg v k := cof2_75 (boundaryQM6 v k) (boundaryQM8 v k) (boundaryQM10 v k)

def boundaryC2ReNorm (v k : ℂ) : {c : ℂ // (boundaryC2 v k).re=c} := by
  have he : (boundaryC2 v k).re=(boundaryC2 v k).re := rfl
  conv at he =>
    rhs
    simp only [boundaryC2,cof2_75,pow_two,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM6,boundaryQM8,boundaryQM10]
    simp only [boundaryMoment6ReValue75_eq,boundaryMoment6ImValue75_eq,boundaryMoment8ReValue75_eq,boundaryMoment8ImValue75_eq,boundaryMoment10ReValue75_eq,boundaryMoment10ImValue75_eq]
    norm_num [boundaryMoment6ReValue75Part0,boundaryMoment6ReValue75Part1,boundaryMoment6ReValue75Part2,boundaryMoment6ReValue75,boundaryMoment6ImValue75Part0,boundaryMoment6ImValue75Part1,boundaryMoment6ImValue75,boundaryMoment8ReValue75Part0,boundaryMoment8ReValue75Part1,boundaryMoment8ReValue75Part2,boundaryMoment8ReValue75Part3,boundaryMoment8ReValue75Part4,boundaryMoment8ReValue75,boundaryMoment8ImValue75Part0,boundaryMoment8ImValue75Part1,boundaryMoment8ImValue75Part2,boundaryMoment8ImValue75Part3,boundaryMoment8ImValue75,boundaryMoment10ReValue75Part0,boundaryMoment10ReValue75Part1,boundaryMoment10ReValue75Part2,boundaryMoment10ReValue75Part3,boundaryMoment10ReValue75Part4,boundaryMoment10ReValue75Part5,boundaryMoment10ReValue75Part6,boundaryMoment10ReValue75,boundaryMoment10ImValue75Part0,boundaryMoment10ImValue75Part1,boundaryMoment10ImValue75Part2,boundaryMoment10ImValue75Part3,boundaryMoment10ImValue75Part4,boundaryMoment10ImValue75Part5,boundaryMoment10ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryC2ImNorm (v k : ℂ) : {c : ℂ // (boundaryC2 v k).im=c} := by
  have he : (boundaryC2 v k).im=(boundaryC2 v k).im := rfl
  conv at he =>
    rhs
    simp only [boundaryC2,cof2_75,pow_two,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM6,boundaryQM8,boundaryQM10]
    simp only [boundaryMoment6ReValue75_eq,boundaryMoment6ImValue75_eq,boundaryMoment8ReValue75_eq,boundaryMoment8ImValue75_eq,boundaryMoment10ReValue75_eq,boundaryMoment10ImValue75_eq]
    norm_num [boundaryMoment6ReValue75Part0,boundaryMoment6ReValue75Part1,boundaryMoment6ReValue75Part2,boundaryMoment6ReValue75,boundaryMoment6ImValue75Part0,boundaryMoment6ImValue75Part1,boundaryMoment6ImValue75,boundaryMoment8ReValue75Part0,boundaryMoment8ReValue75Part1,boundaryMoment8ReValue75Part2,boundaryMoment8ReValue75Part3,boundaryMoment8ReValue75Part4,boundaryMoment8ReValue75,boundaryMoment8ImValue75Part0,boundaryMoment8ImValue75Part1,boundaryMoment8ImValue75Part2,boundaryMoment8ImValue75Part3,boundaryMoment8ImValue75,boundaryMoment10ReValue75Part0,boundaryMoment10ReValue75Part1,boundaryMoment10ReValue75Part2,boundaryMoment10ReValue75Part3,boundaryMoment10ReValue75Part4,boundaryMoment10ReValue75Part5,boundaryMoment10ReValue75Part6,boundaryMoment10ReValue75,boundaryMoment10ImValue75Part0,boundaryMoment10ImValue75Part1,boundaryMoment10ImValue75Part2,boundaryMoment10ImValue75Part3,boundaryMoment10ImValue75Part4,boundaryMoment10ImValue75Part5,boundaryMoment10ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryT2ReNorm (v k : ℂ) : {c : ℂ // (boundaryT2 v k).re=c} := by
  have he : (boundaryT2 v k).re=(boundaryT2 v k).re := rfl
  conv at he =>
    rhs
    simp only [boundaryT2,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM2,boundaryQF2]
    simp only [boundaryMoment2ReValue75_eq,boundaryMoment2ImValue75_eq,boundaryFlow2ReValue75_eq,boundaryFlow2ImValue75_eq]
    norm_num [boundaryMoment2ReValue75Part0,boundaryMoment2ReValue75,boundaryMoment2ImValue75Part0,boundaryMoment2ImValue75,boundaryFlow2ReValue75Part0,boundaryFlow2ReValue75,boundaryFlow2ImValue75Part0,boundaryFlow2ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryT2ImNorm (v k : ℂ) : {c : ℂ // (boundaryT2 v k).im=c} := by
  have he : (boundaryT2 v k).im=(boundaryT2 v k).im := rfl
  conv at he =>
    rhs
    simp only [boundaryT2,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM2,boundaryQF2]
    simp only [boundaryMoment2ReValue75_eq,boundaryMoment2ImValue75_eq,boundaryFlow2ReValue75_eq,boundaryFlow2ImValue75_eq]
    norm_num [boundaryMoment2ReValue75Part0,boundaryMoment2ReValue75,boundaryMoment2ImValue75Part0,boundaryMoment2ImValue75,boundaryFlow2ReValue75Part0,boundaryFlow2ReValue75,boundaryFlow2ImValue75Part0,boundaryFlow2ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
