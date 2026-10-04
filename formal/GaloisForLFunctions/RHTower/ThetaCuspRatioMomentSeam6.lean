import GaloisForLFunctions.RHTower.ThetaCuspRatioMomentSeam2
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def seamValue6 (k : ℂ) : {a : ℂ // eval (seamPoint k) reflectionBalanced6=a} := by
  have h : eval (seamPoint k) reflectionBalanced6=eval (seamPoint k) reflectionBalanced6 := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamU6 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U reflectionBalanced6)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U reflectionBalanced6)=eval (seamPoint k) (pderiv Coord.U reflectionBalanced6) := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJ6 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J reflectionBalanced6)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J reflectionBalanced6)=eval (seamPoint k) (pderiv Coord.J reflectionBalanced6) := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamK6 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.K reflectionBalanced6)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.K reflectionBalanced6)=eval (seamPoint k) (pderiv Coord.K reflectionBalanced6) := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUU6 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced6))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced6))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced6)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUJ6 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced6))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced6))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced6)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJU6 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced6))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced6))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced6)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJJ6 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced6))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced6))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced6)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean6_eq]
    simp [reflectionClean6,reflectionClean6Part0,reflectionClean6Part1,reflectionClean6Part2,reflectionClean6Part3,reflectionClean6Part4,reflectionClean6Part5,reflectionClean6Part6,reflectionClean6Part7,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
