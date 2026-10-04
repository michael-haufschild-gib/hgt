import GaloisForLFunctions.RHTower.ThetaCuspRatioMomentSeam2
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def seamValue8 (k : ℂ) : {a : ℂ // eval (seamPoint k) reflectionBalanced8=a} := by
  have h : eval (seamPoint k) reflectionBalanced8=eval (seamPoint k) reflectionBalanced8 := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamU8 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U reflectionBalanced8)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U reflectionBalanced8)=eval (seamPoint k) (pderiv Coord.U reflectionBalanced8) := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJ8 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J reflectionBalanced8)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J reflectionBalanced8)=eval (seamPoint k) (pderiv Coord.J reflectionBalanced8) := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamK8 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.K reflectionBalanced8)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.K reflectionBalanced8)=eval (seamPoint k) (pderiv Coord.K reflectionBalanced8) := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUU8 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced8))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced8))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced8)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUJ8 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced8))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced8))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced8)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJU8 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced8))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced8))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced8)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJJ8 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced8))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced8))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced8)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean8_eq]
    simp [reflectionClean8,reflectionClean8Part0,reflectionClean8Part1,reflectionClean8Part2,reflectionClean8Part3,reflectionClean8Part4,reflectionClean8Part5,reflectionClean8Part6,reflectionClean8Part7,reflectionClean8Part8,reflectionClean8Part9,reflectionClean8Part10,reflectionClean8Part11,reflectionClean8Part12,reflectionClean8Part13,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
