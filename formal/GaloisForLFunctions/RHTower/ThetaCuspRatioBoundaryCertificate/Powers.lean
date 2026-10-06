import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Algebra
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

theorem quadraticPower_re_succ (a b : ℂ) (n : ℕ) :
    ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^(n+1)).re=
      a*((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^n).im := by
  rw [pow_succ]
  simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.omega]

theorem quadraticPower_im_succ (a b : ℂ) (n : ℕ) :
    ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^(n+1)).im=
      ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^n).re+
      b*((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^n).im := by
  rw [pow_succ]
  simp [QuadraticAlgebra.im_mul,QuadraticAlgebra.omega]

@[simp] theorem boundaryCoord_pow_re (v k c : ℂ) (n : ℕ) :
    ((algebraMap ℂ (BoundaryAlg v k) c)^n).re=c^n := by rw [←map_pow]; rfl
@[simp] theorem boundaryCoord_pow_im (v k c : ℂ) (n : ℕ) :
    ((algebraMap ℂ (BoundaryAlg v k) c)^n).im=0 := by rw [←map_pow]; rfl

def boundaryPowRe0Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^0).re=c} := ⟨1,rfl⟩

def boundaryPowIm0Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^0).im=c} := ⟨0,rfl⟩

def boundaryPowRe1Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^1).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^1).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^1).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 0]
    rw [(boundaryPowIm0Norm a b).property]
    norm_num [boundaryPowRe0Norm,boundaryPowIm0Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm1Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^1).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^1).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^1).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 0]
    rw [(boundaryPowRe0Norm a b).property,(boundaryPowIm0Norm a b).property]
    norm_num [boundaryPowRe0Norm,boundaryPowIm0Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe2Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^2).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^2).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^2).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 1]
    rw [(boundaryPowIm1Norm a b).property]
    norm_num [boundaryPowRe1Norm,boundaryPowIm1Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm2Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^2).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^2).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^2).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 1]
    rw [(boundaryPowRe1Norm a b).property,(boundaryPowIm1Norm a b).property]
    norm_num [boundaryPowRe1Norm,boundaryPowIm1Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe3Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^3).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^3).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^3).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 2]
    rw [(boundaryPowIm2Norm a b).property]
    norm_num [boundaryPowRe2Norm,boundaryPowIm2Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm3Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^3).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^3).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^3).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 2]
    rw [(boundaryPowRe2Norm a b).property,(boundaryPowIm2Norm a b).property]
    norm_num [boundaryPowRe2Norm,boundaryPowIm2Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe4Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^4).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^4).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^4).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 3]
    rw [(boundaryPowIm3Norm a b).property]
    norm_num [boundaryPowRe3Norm,boundaryPowIm3Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm4Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^4).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^4).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^4).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 3]
    rw [(boundaryPowRe3Norm a b).property,(boundaryPowIm3Norm a b).property]
    norm_num [boundaryPowRe3Norm,boundaryPowIm3Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe5Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^5).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^5).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^5).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 4]
    rw [(boundaryPowIm4Norm a b).property]
    norm_num [boundaryPowRe4Norm,boundaryPowIm4Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm5Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^5).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^5).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^5).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 4]
    rw [(boundaryPowRe4Norm a b).property,(boundaryPowIm4Norm a b).property]
    norm_num [boundaryPowRe4Norm,boundaryPowIm4Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe6Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^6).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^6).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^6).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 5]
    rw [(boundaryPowIm5Norm a b).property]
    norm_num [boundaryPowRe5Norm,boundaryPowIm5Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm6Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^6).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^6).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^6).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 5]
    rw [(boundaryPowRe5Norm a b).property,(boundaryPowIm5Norm a b).property]
    norm_num [boundaryPowRe5Norm,boundaryPowIm5Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe7Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^7).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^7).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^7).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 6]
    rw [(boundaryPowIm6Norm a b).property]
    norm_num [boundaryPowRe6Norm,boundaryPowIm6Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm7Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^7).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^7).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^7).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 6]
    rw [(boundaryPowRe6Norm a b).property,(boundaryPowIm6Norm a b).property]
    norm_num [boundaryPowRe6Norm,boundaryPowIm6Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe8Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^8).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^8).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^8).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 7]
    rw [(boundaryPowIm7Norm a b).property]
    norm_num [boundaryPowRe7Norm,boundaryPowIm7Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm8Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^8).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^8).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^8).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 7]
    rw [(boundaryPowRe7Norm a b).property,(boundaryPowIm7Norm a b).property]
    norm_num [boundaryPowRe7Norm,boundaryPowIm7Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe9Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^9).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^9).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^9).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 8]
    rw [(boundaryPowIm8Norm a b).property]
    norm_num [boundaryPowRe8Norm,boundaryPowIm8Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm9Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^9).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^9).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^9).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 8]
    rw [(boundaryPowRe8Norm a b).property,(boundaryPowIm8Norm a b).property]
    norm_num [boundaryPowRe8Norm,boundaryPowIm8Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe10Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^10).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^10).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^10).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 9]
    rw [(boundaryPowIm9Norm a b).property]
    norm_num [boundaryPowRe9Norm,boundaryPowIm9Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm10Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^10).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^10).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^10).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 9]
    rw [(boundaryPowRe9Norm a b).property,(boundaryPowIm9Norm a b).property]
    norm_num [boundaryPowRe9Norm,boundaryPowIm9Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowRe11Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^11).re=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^11).re=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^11).re := rfl
  conv at he =>
    rhs
    rw [quadraticPower_re_succ a b 10]
    rw [(boundaryPowIm10Norm a b).property]
    norm_num [boundaryPowRe10Norm,boundaryPowIm10Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryPowIm11Norm (a b : ℂ) : {c : ℂ // ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^11).im=c} := by
  have he : ((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^11).im=((QuadraticAlgebra.omega : QuadraticAlgebra ℂ a b)^11).im := rfl
  conv at he =>
    rhs
    rw [quadraticPower_im_succ a b 10]
    rw [(boundaryPowRe10Norm a b).property,(boundaryPowIm10Norm a b).property]
    norm_num [boundaryPowRe10Norm,boundaryPowIm10Norm]
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
