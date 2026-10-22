import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioReflectionsClean
/-! # Exact algebra for the zero-defect, zero-speed source-slope face. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial
def slicePoint (u k : ℂ) : Coord → ℂ
  | .U => u
  | .K => k
  | .J => 0

def sliceValue2 (u k : ℂ) : {a : ℂ // eval (slicePoint u k) (integerReflection 2)=a} := by
  have h : eval (slicePoint u k) (integerReflection 2)=eval (slicePoint u k) (integerReflection 2) := rfl
  conv at h =>
    rhs
    rw [reflectionBalanced2_eq,reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,slicePoint]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def sliceValue4 (u k : ℂ) : {a : ℂ // eval (slicePoint u k) (integerReflection 4)=a} := by
  have h : eval (slicePoint u k) (integerReflection 4)=eval (slicePoint u k) (integerReflection 4) := rfl
  conv at h =>
    rhs
    rw [reflectionBalanced4_eq,reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,slicePoint]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def sliceValue6 (u k : ℂ) : {a : ℂ // eval (slicePoint u k) (integerReflection 6)=a} := by
  have h : eval (slicePoint u k) (integerReflection 6)=eval (slicePoint u k) (integerReflection 6) := rfl
  conv at h =>
    rhs
    rw [reflectionBalanced6_eq,reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,slicePoint]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def sliceValue8 (u k : ℂ) : {a : ℂ // eval (slicePoint u k) (integerReflection 8)=a} := by
  have h : eval (slicePoint u k) (integerReflection 8)=eval (slicePoint u k) (integerReflection 8) := rfl
  conv at h =>
    rhs
    rw [reflectionBalanced8_eq,reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,slicePoint]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def sliceValue10 (u k : ℂ) : {a : ℂ // eval (slicePoint u k) (integerReflection 10)=a} := by
  have h : eval (slicePoint u k) (integerReflection 10)=eval (slicePoint u k) (integerReflection 10) := rfl
  conv at h =>
    rhs
    rw [reflectionBalanced10_eq,reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,slicePoint]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩


private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

/-- On the complete zero-speed face, only the drift component contributes. -/
theorem integerSlope_zeroSpeed (u k : ℂ)
    (hf : k^2*(9-u^2)-6*k-4=0) :
    eval (slicePoint u k) integerThirdSlope =
      (6*k-1)*(6*k*(9-u^2))*eval (slicePoint u k) (pderiv Coord.U integerThirdMinor) := by
  have hF : 6*k^2*(9-u^2)-36*k-24=0 := by linear_combination 6*hf
  simp [integerThirdSlope,integerLie,univ_eq,integerField,integerJet,
    slicePoint,pderiv_X,Pi.single_apply,hF]
  ring

end
end HTGeometry.ThetaRatioSource
