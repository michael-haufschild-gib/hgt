import GaloisForLFunctions.HTGeometry.BelinskiZakharovConfocalLorentzBridge
import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Four-dimensional smooth-metric lift of flat Belinski--Zakharov dressing

The existing BZ interface acts on the stationary two-Killing block. Here its unipotent dressing
is lifted to the full flat Kerr--Newman metric. The resulting four-metric is an explicit
nondegenerate smooth pseudo-metric whose `t--φ` submatrix is exactly the dressed BZ block.

This identifies the constant and one-pole constructions as flat-frame congruences. It does not
calculate curvature, establish an Einstein--Maxwell solution, or prove that a general BZ dressing
is a diffeomorphism of a curved Kerr--Newman spacetime.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- Extension of the two-Killing BZ unipotent to coordinates `(t, r, θ, φ)`. -/
def belinskiZakharovKillingLift (parameter : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, parameter;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The lifted BZ unipotent is upper triangular in the full coordinate order. -/
theorem belinskiZakharovKillingLift_blockTriangular (parameter : ℝ) :
    (belinskiZakharovKillingLift parameter).BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [belinskiZakharovKillingLift]

/-- The full-coordinate lift of the BZ unipotent remains unimodular. -/
theorem belinskiZakharovKillingLift_det (parameter : ℝ) :
    (belinskiZakharovKillingLift parameter).det = 1 := by
  rw [Matrix.det_of_upperTriangular (belinskiZakharovKillingLift_blockTriangular parameter)]
  norm_num [belinskiZakharovKillingLift, Fin.prod_univ_succ]

/-- The full flat Kerr--Newman metric after the constant BZ two-Killing congruence. -/
def kerrNewmanFlatBZDressedMetric (parameter : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1 + parameter ^ 2, 0, 0, parameter;
     0, 1, 0, 0;
     0, 0, 1, 0;
     parameter, 0, 0, 1]

/-- Explicit inverse of the four-dimensional flat BZ-dressed metric. -/
def kerrNewmanFlatBZDressedMetricInverse (parameter : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, parameter;
     0, 1, 0, 0;
     0, 0, 1, 0;
     parameter, 0, 0, 1 - parameter ^ 2]

/-- The full metric is the congruence of Minkowski space by the lifted BZ unipotent. -/
theorem kerrNewmanFlatBZDressedMetric_eq_liftCongruence (parameter : ℝ) :
    kerrNewmanFlatBZDressedMetric parameter =
      belinskiZakharovKillingLift parameter * minkowskiMetric4 *
        Matrix.transpose (belinskiZakharovKillingLift parameter) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrNewmanFlatBZDressedMetric, belinskiZakharovKillingLift,
      minkowskiMetric4, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

/-- The corpus's flat Kerr--Newman representative has Minkowski determinant. -/
theorem minkowskiMetric4_det : minkowskiMetric4.det = -1 := by
  have htri : minkowskiMetric4.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [minkowskiMetric4]
  rw [Matrix.det_of_upperTriangular htri]
  norm_num [minkowskiMetric4, Fin.prod_univ_succ]

/-- Full constant BZ dressing preserves the flat Kerr--Newman determinant exactly. -/
theorem kerrNewmanFlatBZDressedMetric_det (parameter : ℝ) :
    (kerrNewmanFlatBZDressedMetric parameter).det = -1 := by
  rw [kerrNewmanFlatBZDressedMetric_eq_liftCongruence, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, belinskiZakharovKillingLift_det,
    minkowskiMetric4_det]
  ring

/-- The full flat BZ-dressed metric remains symmetric. -/
theorem kerrNewmanFlatBZDressedMetric_transpose (parameter : ℝ) :
    Matrix.transpose (kerrNewmanFlatBZDressedMetric parameter) =
      kerrNewmanFlatBZDressedMetric parameter := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Explicit nondegeneracy witness for the full flat BZ-dressed metric. -/
theorem kerrNewmanFlatBZDressedMetric_mul_inverse (parameter : ℝ) :
    kerrNewmanFlatBZDressedMetric parameter *
        kerrNewmanFlatBZDressedMetricInverse parameter = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrNewmanFlatBZDressedMetric, kerrNewmanFlatBZDressedMetricInverse,
      Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

/-- The full metric's stationary two-Killing block is the existing BZ-dressed flat
Kerr--Newman block. -/
theorem kerrNewmanFlatBZDressedMetric_killingBlock (parameter : ℝ) :
    Matrix.submatrix (kerrNewmanFlatBZDressedMetric parameter)
      kerrNewmanKillingIndices kerrNewmanKillingIndices =
      belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
        (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2)) := by
  rw [belinskiZakharov_flatKillingBlock]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrNewmanFlatBZDressedMetric, belinskiZakharovDressing,
      belinskiZakharovUnipotentDressing, kerrNewmanKillingIndices,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- The constant flat BZ lift is a smooth nondegenerate pseudo-metric. -/
noncomputable def kerrNewmanFlatBZDressedSmoothMetric (parameter : ℝ) :
    SmoothPseudoMetric 4 where
  metric := fun _ => kerrNewmanFlatBZDressedMetric parameter
  contDiff_metric := fun _ _ => contDiff_const
  metric_symm := fun _ => kerrNewmanFlatBZDressedMetric_transpose parameter
  det_ne_zero := fun _ => Matrix.det_ne_zero_of_right_inverse
    (kerrNewmanFlatBZDressedMetric_mul_inverse parameter)

/-- Evaluation of the smooth flat BZ lift is its constant matrix representative. -/
@[simp] theorem kerrNewmanFlatBZDressedSmoothMetric_metric
    (parameter : ℝ) (x : Fin 4 → ℝ) :
    (kerrNewmanFlatBZDressedSmoothMetric parameter).metric x =
      kerrNewmanFlatBZDressedMetric parameter := rfl

/-- The smooth metric's Killing block is the BZ-dressed flat Kerr--Newman block. -/
theorem kerrNewmanFlatBZDressedSmoothMetric_killingBlock
    (parameter : ℝ) (x : Fin 4 → ℝ) :
    Matrix.submatrix ((kerrNewmanFlatBZDressedSmoothMetric parameter).metric x)
      kerrNewmanKillingIndices kerrNewmanKillingIndices =
      belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
        (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2)) :=
  kerrNewmanFlatBZDressedMetric_killingBlock parameter

/-- Full four-dimensional one-pole BZ dressing of the flat Kerr--Newman representative. -/
noncomputable def kerrNewmanFlatOnePoleBZDressedMetric
    (spectral pole residue : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  kerrNewmanFlatBZDressedMetric (residue / (spectral - pole))

/-- The totalized one-pole full BZ dressing also preserves the flat determinant exactly. -/
theorem kerrNewmanFlatOnePoleBZDressedMetric_det
    (spectral pole residue : ℝ) :
    (kerrNewmanFlatOnePoleBZDressedMetric spectral pole residue).det = -1 := by
  exact kerrNewmanFlatBZDressedMetric_det _

/-- The one-pole full metric carries the existing one-pole BZ Killing block exactly. -/
theorem kerrNewmanFlatOnePoleBZDressedMetric_killingBlock
    (spectral pole residue : ℝ) :
    Matrix.submatrix (kerrNewmanFlatOnePoleBZDressedMetric spectral pole residue)
      kerrNewmanKillingIndices kerrNewmanKillingIndices =
      belinskiZakharovDressing (belinskiZakharovOnePoleDressing spectral pole residue)
        (kerrNewmanKillingBlock 0 0 0 1 (Real.pi / 2)) := by
  exact kerrNewmanFlatBZDressedMetric_killingBlock _

/-- The full one-pole flat BZ lift is also a smooth nondegenerate pseudo-metric. -/
noncomputable def kerrNewmanFlatOnePoleBZDressedSmoothMetric
    (spectral pole residue : ℝ) : SmoothPseudoMetric 4 :=
  kerrNewmanFlatBZDressedSmoothMetric (residue / (spectral - pole))

end GaloisForLFunctions.HTGeometry
