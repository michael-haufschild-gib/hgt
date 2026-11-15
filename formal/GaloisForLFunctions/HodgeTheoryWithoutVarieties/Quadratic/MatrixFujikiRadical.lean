import GaloisForLFunctions.HodgeTheoryWithoutVarieties.Quadratic.FujikiDegreeRigidity
import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianFormsAtDegreeTwo

/-!
# Fujiki degree tests for real matrix forms

The affine-line power test detects the radical of the symmetric part of any
real matrix, including singular and indefinite matrices. No positivity or
nondegeneracy premise is required.
-/

noncomputable section
open Polynomial Matrix
open GaloisForLFunctions.ArithmeticLorentzianGeometry
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- The formal quadratic line polynomial evaluates to the actual quadratic form. -/
theorem quadraticLine_eval {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : QuadraticForm ℝ V) (x h : V) (t : ℝ) :
    (quadraticLine q x h).eval t = q (x + t • h) := by
  simp only [quadraticLine, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    QuadraticMap.map_add, QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
    QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  ring

variable {ι : Type*} [Fintype ι]

/-- The polynomial obtained by restricting `qf W` to an affine line. -/
def matrixQuadraticLine (W : Matrix ι ι ℝ) (x h : ι → ℝ) : ℝ[X] :=
  C (qf W x) + C (bil W x h + bil W h x) * X + C (qf W h) * X ^ 2

theorem matrixQuadraticLine_eval (W : Matrix ι ι ℝ) (x h : ι → ℝ) (t : ℝ) :
    (matrixQuadraticLine W x h).eval t = qf W (x + t • h) := by
  simp only [matrixQuadraticLine, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    qf, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right]
  ring

/-- The weak degree threshold detects the isotropic cone of the matrix form. -/
theorem matrixQuadraticLine_isotropic_iff (W : Matrix ι ι ℝ) (x h : ι → ℝ) (n : ℕ) :
    ((matrixQuadraticLine W x h) ^ (n + 1)).natDegree ≤ n + 1 ↔ qf W h = 0 :=
  quadratic_power_degree_le_exponent_iff _ _ _ _

/-- Affine degree of every higher power characterizes the symmetric radical. -/
theorem matrixQuadraticLine_radical_iff (W : Matrix ι ι ℝ) (h : ι → ℝ) (n : ℕ) :
    (∀ x, ((matrixQuadraticLine W x h) ^ (n + 2)).natDegree ≤ 1) ↔
      ∀ x, bil W x h + bil W h x = 0 := by
  simp only [matrixQuadraticLine, quadratic_power_affine_iff]
  constructor
  · exact fun H x => (H x).1
  · intro H x
    refine ⟨H x, ?_⟩
    have hh := H h
    change bil W h h = 0
    linarith only [hh]

/-- The test is unchanged by adding an alternating matrix: only its symmetric part matters. -/
theorem matrixQuadraticLine_radical_symmetrize (W : Matrix ι ι ℝ) (h : ι → ℝ) (n : ℕ) :
    (∀ x, ((matrixQuadraticLine W x h) ^ (n + 2)).natDegree ≤ 1) ↔
      ∀ x, bil (W + W.transpose) x h = 0 := by
  rw [matrixQuadraticLine_radical_iff]
  have he (x : ι → ℝ) : bil (W + W.transpose) x h = bil W x h + bil W h x := by
    simp only [bil, add_mulVec, dotProduct_add]
    rw [dotProduct_transpose_mulVec]
  simp only [he]

/-- The affine-power locus is the ordinary kernel of the symmetric matrix part. -/
theorem matrixQuadraticLine_kernel_iff (W : Matrix ι ι ℝ) (h : ι → ℝ) (n : ℕ) :
    (∀ x, ((matrixQuadraticLine W x h) ^ (n + 2)).natDegree ≤ 1) ↔
      (W + W.transpose) *ᵥ h = 0 := by
  classical
  rw [matrixQuadraticLine_radical_symmetrize]
  constructor
  · intro H
    funext i
    simpa [bil, dotProduct, Pi.single_apply] using H (Pi.single i 1)
  · intro H x
    simp [bil, H]

#print axioms matrixQuadraticLine_radical_iff
#print axioms matrixQuadraticLine_isotropic_iff
#print axioms matrixQuadraticLine_radical_symmetrize
#print axioms matrixQuadraticLine_kernel_iff
#print axioms quadraticLine_eval
#print axioms matrixQuadraticLine_eval
end GaloisForLFunctions.HodgeTheoryWithoutVarieties
