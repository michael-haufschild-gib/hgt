import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


/-!
# The unitary matrix model of the hexablock boundary

The coordinates `(U₁₀,U₀₀,U₁₁,det U)` give a homeomorphism from `U(2)`
onto the locus `|a|²+|x₁|²=1`, `x₂=det(U) conjugate(x₁)`, `|det(U)|=1`.
The inverse reconstructs the missing entry as `-det(U) conjugate(a)`.
This is the explicit algebraic boundary realization of Proposition 6.1 in
Pal–Su–Tomar, *Hardy Spaces and Toeplitz operators on the Hexablock*.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.HexablockBoundary
open Matrix

abbrev U2 := Matrix.unitaryGroup (Fin 2) ℂ
abbrev Coordinates := ℂ × ℂ × ℂ × ℂ

def project (U : U2) : Coordinates := (U.1 1 0, U.1 0 0, U.1 1 1, U.1.det)
def reconstruct (q : Coordinates) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![q.2.1, -(q.2.2.2 * star q.1); q.1, q.2.2.1]

theorem adjugate_eq_det_smul_star (U : U2) : U.1.adjugate = U.1.det • star U.1 := by
  have hu : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  calc
    U.1.adjugate = (star U.1 * U.1) * U.1.adjugate := by rw [hu, one_mul]
    _ = U.1.det • star U.1 := by rw [mul_assoc, Matrix.mul_adjugate, mul_smul_comm, mul_one]

theorem missing_entry (U : U2) : U.1 0 1 = -(U.1.det * star (U.1 1 0)) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1)
    (adjugate_eq_det_smul_star U)
  rw [Matrix.adjugate_fin_two] at h
  change -U.1 0 1 = U.1.det * star (U.1 1 0) at h
  exact neg_eq_iff_eq_neg.mp h

theorem reconstruct_project (U : U2) : reconstruct (project U) = U.1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact (missing_entry U).symm
  · rfl
  · rfl

theorem project_injective : Function.Injective project := by
  intro U V h
  apply Subtype.ext
  rw [← reconstruct_project U, ← reconstruct_project V, h]

theorem continuous_project : Continuous project := by
  unfold project
  exact ((continuous_apply 0).comp ((continuous_apply 1).comp continuous_subtype_val)).prodMk
    (((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)).prodMk
      (((continuous_apply 1).comp ((continuous_apply 1).comp continuous_subtype_val)).prodMk
        continuous_subtype_val.matrix_det))

/-- The fourth coordinate and first diagonal entry force the second diagonal entry. -/
theorem second_diagonal (U : U2) : U.1 1 1 = U.1.det * star (U.1 0 0) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    (adjugate_eq_det_smul_star U)
  rw [Matrix.adjugate_fin_two] at h
  exact h

/-- Algebraic boundary equations: a unit first column and a unit determinant. -/
def boundary : Set Coordinates := {q |
  star q.1 * q.1 + star q.2.1 * q.2.1 = 1 ∧
  q.2.2.1 = q.2.2.2 * star q.2.1 ∧
  star q.2.2.2 * q.2.2.2 = 1}

theorem project_mem_boundary (U : U2) : project U ∈ boundary := by
  have hu := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    (Matrix.mem_unitaryGroup_iff'.mp U.2)
  have hc : star (U.1 1 0) * U.1 1 0 + star (U.1 0 0) * U.1 0 0 = 1 := by
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_eq, add_comm] using hu
  exact ⟨hc, second_diagonal U, (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1⟩

theorem reconstruct_unitary (q : boundary) : reconstruct q.1 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  obtain ⟨hc, hd, hp⟩ := q.2
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · change star q.1.2.1 * q.1.2.1 + star q.1.1 * q.1.1 = 1
    linear_combination hc
  · change star q.1.2.1 * (-(q.1.2.2.2 * star q.1.1)) + star q.1.1 * q.1.2.2.1 = 0
    rw [hd]
    ring
  · change star (-(q.1.2.2.2 * star q.1.1)) * q.1.2.1 + star q.1.2.2.1 * q.1.1 = 0
    rw [hd]
    simp only [star_neg, star_mul, star_star]
    ring
  · change star (-(q.1.2.2.2 * star q.1.1)) * (-(q.1.2.2.2 * star q.1.1)) +
      star q.1.2.2.1 * q.1.2.2.1 = 1
    rw [hd]
    simp only [star_neg, star_mul, star_star]
    calc
      _ = (star q.1.2.2.2 * q.1.2.2.2) *
        (star q.1.1 * q.1.1 + star q.1.2.1 * q.1.2.1) := by ring
      _ = 1 := by rw [hp, hc, mul_one]

def inverse (q : boundary) : U2 := ⟨reconstruct q.1, reconstruct_unitary q⟩

theorem project_inverse (q : boundary) : project (inverse q) = q.1 := by
  obtain ⟨hc, hd, hp⟩ := q.2
  have hdet : (reconstruct q.1).det = q.1.2.2.2 := by
    rw [Matrix.det_fin_two]
    change q.1.2.1 * q.1.2.2.1 - (-(q.1.2.2.2 * star q.1.1)) * q.1.1 = q.1.2.2.2
    rw [hd]
    calc
      _ = q.1.2.2.2 * (star q.1.1 * q.1.1 + star q.1.2.1 * q.1.2.1) := by ring
      _ = q.1.2.2.2 := by rw [hc, mul_one]
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hdet))

theorem continuous_reconstruct : Continuous reconstruct := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · change Continuous (fun q : Coordinates => q.2.1)
    fun_prop
  · change Continuous (fun q : Coordinates => -(q.2.2.2 * star q.1))
    fun_prop
  · change Continuous (fun q : Coordinates => q.1)
    fun_prop
  · change Continuous (fun q : Coordinates => q.2.2.1)
    fun_prop

/-- The unitary projection is a homeomorphism onto the algebraic hexablock boundary. -/
def homeomorph : U2 ≃ₜ boundary where
  toFun U := ⟨project U, project_mem_boundary U⟩
  invFun := inverse
  left_inv U := Subtype.ext (reconstruct_project U)
  right_inv q := Subtype.ext (project_inverse q)
  continuous_toFun := continuous_project.subtype_mk _
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_reconstruct.comp continuous_subtype_val

/-- The boundary equations characterize the unitary image, including singular coordinate strata. -/
theorem range_project : Set.range project = boundary := by
  ext q
  constructor
  · rintro ⟨U, rfl⟩
    exact project_mem_boundary U
  · intro hq
    exact ⟨inverse ⟨q, hq⟩, project_inverse ⟨q, hq⟩⟩

end GaloisForLFunctions.HTGeometry.HexablockBoundary

#print axioms GaloisForLFunctions.HTGeometry.HexablockBoundary.homeomorph
#print axioms GaloisForLFunctions.HTGeometry.HexablockBoundary.range_project
#print axioms GaloisForLFunctions.HTGeometry.HexablockBoundary.project_injective
