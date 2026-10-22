import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioMomentSeam2
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def seamValue10 (k : ℂ) : {a : ℂ // eval (seamPoint k) reflectionBalanced10=a} := by
  have h : eval (seamPoint k) reflectionBalanced10=eval (seamPoint k) reflectionBalanced10 := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamU10 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U reflectionBalanced10)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U reflectionBalanced10)=eval (seamPoint k) (pderiv Coord.U reflectionBalanced10) := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJ10 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J reflectionBalanced10)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J reflectionBalanced10)=eval (seamPoint k) (pderiv Coord.J reflectionBalanced10) := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamK10 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.K reflectionBalanced10)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.K reflectionBalanced10)=eval (seamPoint k) (pderiv Coord.K reflectionBalanced10) := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUU10 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced10))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced10))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U reflectionBalanced10)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamUJ10 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced10))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced10))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J reflectionBalanced10)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJU10 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced10))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced10))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U reflectionBalanced10)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def seamJJ10 (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced10))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced10))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J reflectionBalanced10)) := rfl
  conv at h =>
    rhs
    rw [reflectionClean10_eq]
    simp [reflectionClean10,reflectionClean10Part0,reflectionClean10Part1,reflectionClean10Part2,reflectionClean10Part3,reflectionClean10Part4,reflectionClean10Part5,reflectionClean10Part6,reflectionClean10Part7,reflectionClean10Part8,reflectionClean10Part9,reflectionClean10Part10,reflectionClean10Part11,reflectionClean10Part12,reflectionClean10Part13,reflectionClean10Part14,reflectionClean10Part15,reflectionClean10Part16,reflectionClean10Part17,reflectionClean10Part18,reflectionClean10Part19,reflectionClean10Part20,reflectionClean10Part21,reflectionClean10Part22,seamPoint,pderiv_X,Pi.single_apply,
      pderiv_one,pderiv_C,pderiv_mul,pderiv_pow]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
