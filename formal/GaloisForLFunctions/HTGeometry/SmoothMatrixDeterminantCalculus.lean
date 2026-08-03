import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Smoothness of determinants, adjugates, matrix inverses and metric densities

A matrix-valued map with smooth entries has a smooth determinant, smooth adjugate entries and,
away from the vanishing locus of the determinant, smooth inverse entries.  Combined with
smoothness of `t ↦ √|t|` off the origin this produces the smooth Riemannian volume density
`x ↦ √|det g x|` of a nondegenerate smooth metric field.

The determinant is expanded by the Leibniz permutation formula, so every statement is a finite
sum of finite products of entries; the adjugate is a determinant of a row-updated matrix, whose
entries are either entries of the original matrix or constants.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : WithTop ℕ∞}

/-- A matrix field with smooth entries has a smooth determinant. -/
theorem contDiff_matrix_det {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ n fun x => A x i j) :
    ContDiff ℝ n fun x => (A x).det := by
  have hexp : (fun x => (A x).det) =
      fun x => ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i := by
    funext x
    simpa using (Matrix.det_apply' (A x))
  rw [hexp]
  refine ContDiff.sum ?_
  intro σ _
  refine contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hA (σ i) i

/-- A matrix field with smooth entries has smooth adjugate entries. -/
theorem contDiff_matrix_adjugate_apply {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ n fun x => A x i j) (i j : ι) :
    ContDiff ℝ n fun x => (A x).adjugate i j := by
  have hexp : (fun x => (A x).adjugate i j) =
      fun x => ((A x).updateRow j (Pi.single i 1)).det := by
    funext x
    exact Matrix.adjugate_apply (A x) i j
  rw [hexp]
  refine contDiff_matrix_det ?_
  intro k l
  by_cases hk : k = j
  · have : (fun x => ((A x).updateRow j (Pi.single i 1)) k l) =
        fun _ : E => ((Pi.single i (1 : ℝ) : ι → ℝ) l) := by
      funext x
      simp [Matrix.updateRow_apply, hk]
    rw [this]
    exact contDiff_const
  · have : (fun x => ((A x).updateRow j (Pi.single i 1)) k l) = fun x => A x k l := by
      funext x
      simp [Matrix.updateRow_apply, hk]
    rw [this]
    exact hA k l

/-- Off the vanishing locus of the determinant, a smooth matrix field has smooth inverse
entries. -/
theorem contDiff_matrix_inv_apply {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ n fun x => A x i j)
    (hdet : ∀ x, (A x).det ≠ 0) (i j : ι) :
    ContDiff ℝ n fun x => (A x)⁻¹ i j := by
  have hexp : (fun x => (A x)⁻¹ i j) =
      fun x => ((A x).det)⁻¹ * (A x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  refine ContDiff.mul ?_ (contDiff_matrix_adjugate_apply hA i j)
  exact ContDiff.inv (contDiff_matrix_det hA) hdet

/-- `√|u|` is as smooth as `u` wherever `u` does not vanish; the absolute value is locally one
of the two smooth branches `u` or `-u`. -/
theorem contDiff_sqrt_abs {u : E → ℝ} (hu : ContDiff ℝ n u) (hne : ∀ x, u x ≠ 0) :
    ContDiff ℝ n fun x => Real.sqrt |u x| := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have habs : ContDiffAt ℝ n (fun y => |u y|) x := by
    rcases lt_or_gt_of_ne (hne x) with hneg | hpos
    · have hopen : IsOpen {y : E | u y < 0} := isOpen_lt hu.continuous continuous_const
      have hmem : {y : E | u y < 0} ∈ nhds x := hopen.mem_nhds hneg
      refine ContDiffAt.congr_of_eventuallyEq (f := fun y => -u y) ?_ ?_
      · exact hu.neg.contDiffAt
      · filter_upwards [hmem] with y hy
        exact abs_of_neg hy
    · have hopen : IsOpen {y : E | 0 < u y} := isOpen_lt continuous_const hu.continuous
      have hmem : {y : E | 0 < u y} ∈ nhds x := hopen.mem_nhds hpos
      refine ContDiffAt.congr_of_eventuallyEq (f := fun y => u y) ?_ ?_
      · exact hu.contDiffAt
      · filter_upwards [hmem] with y hy
        exact abs_of_pos hy
  have hpos : |u x| ≠ 0 := abs_ne_zero.mpr (hne x)
  exact (Real.contDiffAt_sqrt hpos).comp x habs

end GaloisForLFunctions.HTGeometry
