import GaloisForLFunctions.RHTower.ThetaCuspRatioReflectionsClean
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def seamPoint (k : ℂ) : Coord → ℂ
  | .U => 0
  | .K => k
  | .J => 0

def seamValue2 (k : ℂ) : {a : ℂ // eval (seamPoint k) reflectionBalanced2=a} := by
  have h : eval (seamPoint k) reflectionBalanced2=eval (seamPoint k) reflectionBalanced2 := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamU2 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U reflectionBalanced2)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U reflectionBalanced2)=eval (seamPoint k) (pderiv Coord.U reflectionBalanced2) := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJ2 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J reflectionBalanced2)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J reflectionBalanced2)=eval (seamPoint k) (pderiv Coord.J reflectionBalanced2) := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamK2 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.K reflectionBalanced2)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.K reflectionBalanced2)=eval (seamPoint k) (pderiv Coord.K reflectionBalanced2) := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUU2 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced2))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced2))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced2)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUJ2 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced2))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced2))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced2)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJU2 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced2))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced2))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced2)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJJ2 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced2))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced2))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced2)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean2_eq]
    simp [reflectionClean2,reflectionClean2Part0,reflectionClean2Part1,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
