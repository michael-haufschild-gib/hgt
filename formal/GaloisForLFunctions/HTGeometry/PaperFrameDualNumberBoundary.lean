import GaloisForLFunctions.HTGeometry.PaperSL2PolynomialFrame
import Mathlib.Algebra.DualNumber

/-!
# An infinitesimal boundary of normalized frame reconstruction

The diagonal matrix with entries `1 + εT` and `1 - εT` has determinant one,
constant frame equal to the identity, and identically zero quadric coordinates.
It is nevertheless nonconstant. Thus the reduced-coefficient condition in the
paper's polynomial frame uniqueness theorem is essential for dual-number
families, the infinitesimal coefficient rings already used by the corpus.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

noncomputable section

/-- The nonzero square-zero polynomial responsible for the hidden motion. -/
def paperDualFrameParameter : MvPolynomial Unit (DualNumber ℂ) :=
  C DualNumber.eps * X ()

@[simp] theorem paperDualFrameParameter_sq : paperDualFrameParameter ^ 2 = 0 := by
  simp [paperDualFrameParameter, mul_pow, ← map_pow]

@[simp] theorem paperDualFrameParameter_constantCoeff :
    constantCoeff paperDualFrameParameter = 0 := by
  simp [paperDualFrameParameter]

theorem paperDualFrameParameter_ne_zero : paperDualFrameParameter ≠ 0 := by
  intro h
  have he := congrArg
    (fun p : MvPolynomial Unit (DualNumber ℂ) =>
      (MvPolynomial.eval (fun _ => 1) p).snd) h
  simp [paperDualFrameParameter] at he

/-- A literal nonconstant special-linear matrix over the dual-number polynomial ring. -/
def paperDualFrameMotion :
    Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial Unit (DualNumber ℂ)) :=
  ⟨!![1 + paperDualFrameParameter, 0; 0, 1 - paperDualFrameParameter], by
    rw [Matrix.det_fin_two]
    change (1 + paperDualFrameParameter) * (1 - paperDualFrameParameter) - 0 * 0 = 1
    calc
      _ = 1 - paperDualFrameParameter ^ 2 := by ring
      _ = 1 := by simp⟩

/-- Every quadratic observable agrees identically with that of the identity matrix. -/
theorem paperDualFrameMotion_quadric :
    paperSL2QuadricPoint paperDualFrameMotion = paperSL2QuadricPoint 1 := by
  funext i
  fin_cases i <;> simp [paperSL2QuadricPoint, paperDualFrameMotion]

/-- The entire frame agrees with the identity at the parameter origin. -/
theorem paperDualFrameMotion_at_zero :
    Matrix.SpecialLinearGroup.map constantCoeff paperDualFrameMotion = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [paperDualFrameMotion, Matrix.SpecialLinearGroup.map]

/-- The polynomial family is still different from the identity. -/
theorem paperDualFrameMotion_ne_one : paperDualFrameMotion ≠ 1 := by
  intro h
  have ha := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial Unit (DualNumber ℂ)) =>
      g 0 0 - 1) h
  apply paperDualFrameParameter_ne_zero
  simpa [paperDualFrameMotion] using ha

/-- Quadratic data and origin normalization fail to reconstruct dual-number families. -/
theorem paperDualFrameNormalizedData_not_injective :
    ¬ Function.Injective
      (fun g : Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial Unit (DualNumber ℂ)) =>
        (paperSL2QuadricPoint g, Matrix.SpecialLinearGroup.map constantCoeff g)) := by
  intro h
  apply paperDualFrameMotion_ne_one
  apply h
  exact Prod.ext paperDualFrameMotion_quadric
    (paperDualFrameMotion_at_zero.trans (map_one _).symm)

end

end GaloisForLFunctions.HTGeometry
