import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.AssemblyValues
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar2
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar4
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar6
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Scalar8
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryC8 (v k : ℂ) : BoundaryAlg v k := cof8_75 (boundaryQM2 v k) (boundaryQM4 v k) (boundaryQM6 v k) (boundaryQM8 v k)

def boundaryC8ReNorm (v k : ℂ) : {c : ℂ // (boundaryC8 v k).re=c} := by
  have he : (boundaryC8 v k).re=(boundaryC8 v k).re := rfl
  conv at he =>
    rhs
    simp only [boundaryC8,cof8_75,pow_two,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM2,boundaryQM4,boundaryQM6,boundaryQM8]
    simp only [boundaryMoment2ReValue75_eq,boundaryMoment2ImValue75_eq,boundaryMoment4ReValue75_eq,boundaryMoment4ImValue75_eq,boundaryMoment6ReValue75_eq,boundaryMoment6ImValue75_eq,boundaryMoment8ReValue75_eq,boundaryMoment8ImValue75_eq]
    norm_num [boundaryMoment2ReValue75Part0,boundaryMoment2ReValue75,boundaryMoment2ImValue75Part0,boundaryMoment2ImValue75,boundaryMoment4ReValue75Part0,boundaryMoment4ReValue75Part1,boundaryMoment4ReValue75,boundaryMoment4ImValue75Part0,boundaryMoment4ImValue75,boundaryMoment6ReValue75Part0,boundaryMoment6ReValue75Part1,boundaryMoment6ReValue75Part2,boundaryMoment6ReValue75,boundaryMoment6ImValue75Part0,boundaryMoment6ImValue75Part1,boundaryMoment6ImValue75,boundaryMoment8ReValue75Part0,boundaryMoment8ReValue75Part1,boundaryMoment8ReValue75Part2,boundaryMoment8ReValue75Part3,boundaryMoment8ReValue75Part4,boundaryMoment8ReValue75,boundaryMoment8ImValue75Part0,boundaryMoment8ImValue75Part1,boundaryMoment8ImValue75Part2,boundaryMoment8ImValue75Part3,boundaryMoment8ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryC8ImNorm (v k : ℂ) : {c : ℂ // (boundaryC8 v k).im=c} := by
  have he : (boundaryC8 v k).im=(boundaryC8 v k).im := rfl
  conv at he =>
    rhs
    simp only [boundaryC8,cof8_75,pow_two,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM2,boundaryQM4,boundaryQM6,boundaryQM8]
    simp only [boundaryMoment2ReValue75_eq,boundaryMoment2ImValue75_eq,boundaryMoment4ReValue75_eq,boundaryMoment4ImValue75_eq,boundaryMoment6ReValue75_eq,boundaryMoment6ImValue75_eq,boundaryMoment8ReValue75_eq,boundaryMoment8ImValue75_eq]
    norm_num [boundaryMoment2ReValue75Part0,boundaryMoment2ReValue75,boundaryMoment2ImValue75Part0,boundaryMoment2ImValue75,boundaryMoment4ReValue75Part0,boundaryMoment4ReValue75Part1,boundaryMoment4ReValue75,boundaryMoment4ImValue75Part0,boundaryMoment4ImValue75,boundaryMoment6ReValue75Part0,boundaryMoment6ReValue75Part1,boundaryMoment6ReValue75Part2,boundaryMoment6ReValue75,boundaryMoment6ImValue75Part0,boundaryMoment6ImValue75Part1,boundaryMoment6ImValue75,boundaryMoment8ReValue75Part0,boundaryMoment8ReValue75Part1,boundaryMoment8ReValue75Part2,boundaryMoment8ReValue75Part3,boundaryMoment8ReValue75Part4,boundaryMoment8ReValue75,boundaryMoment8ImValue75Part0,boundaryMoment8ImValue75Part1,boundaryMoment8ImValue75Part2,boundaryMoment8ImValue75Part3,boundaryMoment8ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryT8ReNorm (v k : ℂ) : {c : ℂ // (boundaryT8 v k).re=c} := by
  have he : (boundaryT8 v k).re=(boundaryT8 v k).re := rfl
  conv at he =>
    rhs
    simp only [boundaryT8,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM8,boundaryQF8]
    simp only [boundaryMoment8ReValue75_eq,boundaryMoment8ImValue75_eq,boundaryFlow8ReValue75_eq,boundaryFlow8ImValue75_eq]
    norm_num [boundaryMoment8ReValue75Part0,boundaryMoment8ReValue75Part1,boundaryMoment8ReValue75Part2,boundaryMoment8ReValue75Part3,boundaryMoment8ReValue75Part4,boundaryMoment8ReValue75,boundaryMoment8ImValue75Part0,boundaryMoment8ImValue75Part1,boundaryMoment8ImValue75Part2,boundaryMoment8ImValue75Part3,boundaryMoment8ImValue75,boundaryFlow8ReValue75Part0,boundaryFlow8ReValue75Part1,boundaryFlow8ReValue75Part2,boundaryFlow8ReValue75Part3,boundaryFlow8ReValue75Part4,boundaryFlow8ReValue75Part5,boundaryFlow8ReValue75,boundaryFlow8ImValue75Part0,boundaryFlow8ImValue75Part1,boundaryFlow8ImValue75Part2,boundaryFlow8ImValue75Part3,boundaryFlow8ImValue75Part4,boundaryFlow8ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryT8ImNorm (v k : ℂ) : {c : ℂ // (boundaryT8 v k).im=c} := by
  have he : (boundaryT8 v k).im=(boundaryT8 v k).im := rfl
  conv at he =>
    rhs
    simp only [boundaryT8,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      quadratic_re_ofNat,quadratic_im_ofNat,zero_mul,mul_zero,zero_add,add_zero]
    dsimp only [boundaryQM8,boundaryQF8]
    simp only [boundaryMoment8ReValue75_eq,boundaryMoment8ImValue75_eq,boundaryFlow8ReValue75_eq,boundaryFlow8ImValue75_eq]
    norm_num [boundaryMoment8ReValue75Part0,boundaryMoment8ReValue75Part1,boundaryMoment8ReValue75Part2,boundaryMoment8ReValue75Part3,boundaryMoment8ReValue75Part4,boundaryMoment8ReValue75,boundaryMoment8ImValue75Part0,boundaryMoment8ImValue75Part1,boundaryMoment8ImValue75Part2,boundaryMoment8ImValue75Part3,boundaryMoment8ImValue75,boundaryFlow8ReValue75Part0,boundaryFlow8ReValue75Part1,boundaryFlow8ReValue75Part2,boundaryFlow8ReValue75Part3,boundaryFlow8ReValue75Part4,boundaryFlow8ReValue75Part5,boundaryFlow8ReValue75,boundaryFlow8ImValue75Part0,boundaryFlow8ImValue75Part1,boundaryFlow8ImValue75Part2,boundaryFlow8ImValue75Part3,boundaryFlow8ImValue75Part4,boundaryFlow8ImValue75,boundaryA,boundaryB,boundaryMass]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
