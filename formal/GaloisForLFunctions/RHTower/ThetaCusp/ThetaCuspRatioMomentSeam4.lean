import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioMomentSeam2
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def seamValue4 (k : ℂ) : {a : ℂ // eval (seamPoint k) reflectionBalanced4=a} := by
  have h : eval (seamPoint k) reflectionBalanced4=eval (seamPoint k) reflectionBalanced4 := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamU4 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U reflectionBalanced4)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U reflectionBalanced4)=eval (seamPoint k) (pderiv Coord.U reflectionBalanced4) := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJ4 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J reflectionBalanced4)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J reflectionBalanced4)=eval (seamPoint k) (pderiv Coord.J reflectionBalanced4) := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamK4 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.K reflectionBalanced4)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.K reflectionBalanced4)=eval (seamPoint k) (pderiv Coord.K reflectionBalanced4) := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUU4 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced4))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced4))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced4)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUJ4 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced4))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced4))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced4)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJU4 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced4))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced4))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced4)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJJ4 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced4))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced4))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced4)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean4_eq]
    simp [reflectionClean4,reflectionClean4Part0,reflectionClean4Part1,reflectionClean4Part2,reflectionClean4Part3,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
