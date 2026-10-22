import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioMomentSeam4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioMomentSeam6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioMomentSeam8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioMomentSeam10
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def seamDetModel : Poly :=
  -reflectionBalanced2*reflectionBalanced6*reflectionBalanced10+
  reflectionBalanced2*reflectionBalanced8^2+
  reflectionBalanced4^2*reflectionBalanced10-
  2*reflectionBalanced4*reflectionBalanced6*reflectionBalanced8+reflectionBalanced6^3

theorem integerThirdMinor_model : integerThirdMinor=seamDetModel := by
  norm_num [integerThirdMinor,integerSignedMoment]
  rw [reflectionBalanced2_eq,reflectionBalanced4_eq,reflectionBalanced6_eq,
    reflectionBalanced8_eq,reflectionBalanced10_eq]
  unfold seamDetModel
  ring

@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

def detSeamValue (k : ℂ) : {a : ℂ // eval (seamPoint k) seamDetModel=a} := by
  have h : eval (seamPoint k) seamDetModel=eval (seamPoint k) seamDetModel := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def detSeamU (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U seamDetModel)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U seamDetModel)=eval (seamPoint k) (pderiv Coord.U seamDetModel) := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property,(seamU2 k).property,(seamU4 k).property,(seamU6 k).property,(seamU8 k).property,(seamU10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10,seamU2,seamU4,seamU6,seamU8,seamU10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def detSeamJ (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J seamDetModel)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J seamDetModel)=eval (seamPoint k) (pderiv Coord.J seamDetModel) := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property,(seamJ2 k).property,(seamJ4 k).property,(seamJ6 k).property,(seamJ8 k).property,(seamJ10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10,seamJ2,seamJ4,seamJ6,seamJ8,seamJ10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def detSeamK (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.K seamDetModel)=a} := by
  have h : eval (seamPoint k) (pderiv Coord.K seamDetModel)=eval (seamPoint k) (pderiv Coord.K seamDetModel) := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property,(seamK2 k).property,(seamK4 k).property,(seamK6 k).property,(seamK8 k).property,(seamK10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10,seamK2,seamK4,seamK6,seamK8,seamK10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def detSeamUU (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U seamDetModel))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U seamDetModel))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.U seamDetModel)) := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property,(seamU2 k).property,(seamU4 k).property,(seamU6 k).property,(seamU8 k).property,(seamU10 k).property,(seamUU2 k).property,(seamUU4 k).property,(seamUU6 k).property,(seamUU8 k).property,(seamUU10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10,seamU2,seamU4,seamU6,seamU8,seamU10,seamUU2,seamUU4,seamUU6,seamUU8,seamUU10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def detSeamUJ (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J seamDetModel))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J seamDetModel))=eval (seamPoint k) (pderiv Coord.U (pderiv Coord.J seamDetModel)) := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property,(seamU2 k).property,(seamU4 k).property,(seamU6 k).property,(seamU8 k).property,(seamU10 k).property,(seamJ2 k).property,(seamJ4 k).property,(seamJ6 k).property,(seamJ8 k).property,(seamJ10 k).property,(seamUJ2 k).property,(seamUJ4 k).property,(seamUJ6 k).property,(seamUJ8 k).property,(seamUJ10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10,seamU2,seamU4,seamU6,seamU8,seamU10,seamJ2,seamJ4,seamJ6,seamJ8,seamJ10,seamUJ2,seamUJ4,seamUJ6,seamUJ8,seamUJ10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def detSeamJU (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U seamDetModel))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U seamDetModel))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.U seamDetModel)) := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property,(seamU2 k).property,(seamU4 k).property,(seamU6 k).property,(seamU8 k).property,(seamU10 k).property,(seamJ2 k).property,(seamJ4 k).property,(seamJ6 k).property,(seamJ8 k).property,(seamJ10 k).property,(seamJU2 k).property,(seamJU4 k).property,(seamJU6 k).property,(seamJU8 k).property,(seamJU10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10,seamU2,seamU4,seamU6,seamU8,seamU10,seamJ2,seamJ4,seamJ6,seamJ8,seamJ10,seamJU2,seamJU4,seamJU6,seamJU8,seamJU10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

def detSeamJJ (k : ℂ) : {a : ℂ // eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J seamDetModel))=a} := by
  have h : eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J seamDetModel))=eval (seamPoint k) (pderiv Coord.J (pderiv Coord.J seamDetModel)) := rfl
  conv at h =>
    rhs
    simp [seamDetModel,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,(seamValue2 k).property,(seamValue4 k).property,(seamValue6 k).property,(seamValue8 k).property,(seamValue10 k).property,(seamJ2 k).property,(seamJ4 k).property,(seamJ6 k).property,(seamJ8 k).property,(seamJ10 k).property,(seamJJ2 k).property,(seamJJ4 k).property,(seamJJ6 k).property,(seamJJ8 k).property,(seamJJ10 k).property]
    dsimp only [seamValue2,seamValue4,seamValue6,seamValue8,seamValue10,seamJ2,seamJ4,seamJ6,seamJ8,seamJ10,seamJJ2,seamJJ4,seamJJ6,seamJJ8,seamJJ10]
    ring_nf (config := {ifUnchanged := .silent})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
