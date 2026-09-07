import GaloisForLFunctions.HTGeometry.MatrixInverseCurveDerivative
import Mathlib.Tactic.NoncommRing

/-!
# Exact cubic expansion of an affine inverse metric

For an invertible background matrix `A`, the cubic polynomial in the perturbation `t H`
has coefficients fixed by ordered products of `A⁻¹` and `H`. Its error is exactly a fourth-order
matrix product against the actual perturbed inverse. No commutativity of matrix factors or
convergence of an infinite series is assumed.
-/

namespace GaloisForLFunctions.HTGeometry
open Matrix
noncomputable section

variable {d : ℕ} {𝕜 : Type*} [Field 𝕜]

/-- The inverse-metric polynomial through cubic perturbative order. -/
def matrixAffineInverseCubic (A H : Matrix (Fin d) (Fin d) 𝕜) (t : 𝕜) :
    Matrix (Fin d) (Fin d) 𝕜 :=
  (1 - t • (A⁻¹ * H) + (t • (A⁻¹ * H)) ^ 2 - (t • (A⁻¹ * H)) ^ 3) * A⁻¹

/-- Explicit ordered coefficients of the affine inverse through order three. -/
theorem matrixAffineInverseCubic_coefficients (A H : Matrix (Fin d) (Fin d) 𝕜) (t : 𝕜) :
    matrixAffineInverseCubic A H t =
      A⁻¹ - t • (A⁻¹ * H * A⁻¹) +
        t ^ 2 • ((A⁻¹ * H) ^ 2 * A⁻¹) - t ^ 3 • ((A⁻¹ * H) ^ 3 * A⁻¹) := by
  simp only [matrixAffineInverseCubic, sub_mul, add_mul, one_mul,
    smul_pow, smul_mul_assoc]

/-- The polynomial's right product defect is exactly quartic. -/
theorem matrixAffineInverseCubic_mul (A H : Matrix (Fin d) (Fin d) 𝕜) (t : 𝕜)
    (hA : IsUnit A.det) :
    matrixAffineInverseCubic A H t * (A + t • H) =
      1 - (t • (A⁻¹ * H)) ^ 4 := by
  have hfactor : A⁻¹ * (A + t • H) = 1 + t • (A⁻¹ * H) := by
    rw [mul_add, Matrix.nonsing_inv_mul A hA, mul_smul_comm]
  rw [matrixAffineInverseCubic, mul_assoc, hfactor]
  have hpoly (X : Matrix (Fin d) (Fin d) 𝕜) :
      (1 - X + X ^ 2 - X ^ 3) * (1 + X) = 1 - X ^ 4 := by noncomm_ring
  exact hpoly _

/-- Exact finite inverse expansion with its actual fourth-order remainder. -/
theorem matrixAffineInverse_eq_cubic_add_remainder
    (A H : Matrix (Fin d) (Fin d) 𝕜) (t : 𝕜)
    (hA : IsUnit A.det) (hAt : IsUnit (A + t • H).det) :
    (A + t • H)⁻¹ = matrixAffineInverseCubic A H t +
      t ^ 4 • ((A⁻¹ * H) ^ 4 * (A + t • H)⁻¹) := by
  have heq := congrArg (fun M : Matrix (Fin d) (Fin d) 𝕜 => M * (A + t • H)⁻¹)
    (matrixAffineInverseCubic_mul A H t hA)
  rw [mul_assoc, Matrix.mul_nonsing_inv _ hAt, mul_one, sub_mul, one_mul,
    smul_pow, smul_mul_assoc] at heq
  exact (eq_sub_iff_add_eq.mp heq).symm

section RealDerivatives

/-- The first derivative of the affine inverse, as an explicit matrix function. -/
def matrixAffineInverseFirstDerivative (A H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    Matrix (Fin d) (Fin d) ℝ := -((A + t • H)⁻¹ * H * (A + t • H)⁻¹)

/-- The second derivative retains both ordered inverse-product contributions. -/
def matrixAffineInverseSecondDerivative (A H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (2 : ℝ) • ((A + t • H)⁻¹ * H * (A + t • H)⁻¹ * H * (A + t • H)⁻¹)

/-- The third derivative of the affine inverse, with its exact factorial coefficient. -/
def matrixAffineInverseThirdDerivative (A H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (-6 : ℝ) • ((A + t • H)⁻¹ * H * (A + t • H)⁻¹ * H * (A + t • H)⁻¹ * H * (A + t • H)⁻¹)

private theorem matrixDerivative_const (A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    MatrixHasDerivAt (fun _ => A) 0 t := fun i j => hasDerivAt_const t (A i j)

private theorem matrixDerivative_neg {F : ℝ → Matrix (Fin d) (Fin d) ℝ}
    {F' : Matrix (Fin d) (Fin d) ℝ} {t : ℝ} (h : MatrixHasDerivAt F F' t) :
    MatrixHasDerivAt (fun s => -(F s)) (-F') t := fun i j => (h i j).neg

private theorem matrixDerivative_const_smul {F : ℝ → Matrix (Fin d) (Fin d) ℝ}
    {F' : Matrix (Fin d) (Fin d) ℝ} {t : ℝ} (h : MatrixHasDerivAt F F' t) (c : ℝ) :
    MatrixHasDerivAt (fun s => c • F s) (c • F') t := fun i j => (h i j).const_mul c

/-- Actual first derivative of the inverse curve at every nondegenerate affine metric value. -/
theorem matrixHasDerivAt_affineInverse (A H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hAt : (A + t • H).det ≠ 0) :
    MatrixHasDerivAt (fun s => (A + s • H)⁻¹) (matrixAffineInverseFirstDerivative A H t) t := by
  apply matrixHasDerivAt_inv (J' := H) _ hAt
  intro i j
  simpa using ((hasDerivAt_id t).mul_const (H i j)).const_add (A i j)

/-- The displayed first derivative has the exact second derivative from the cubic expansion. -/
theorem matrixHasDerivAt_affineInverseFirstDerivative
    (A H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (hAt : (A + t • H).det ≠ 0) :
    MatrixHasDerivAt (matrixAffineInverseFirstDerivative A H)
      (matrixAffineInverseSecondDerivative A H t) t := by
  have hF := matrixHasDerivAt_affineInverse A H t hAt
  have hH := matrixDerivative_const H t
  have hd := matrixDerivative_neg ((hF.mul hH).mul hF)
  have heq : -((matrixAffineInverseFirstDerivative A H t * H + (A + t • H)⁻¹ * 0) *
      (A + t • H)⁻¹ + ((A + t • H)⁻¹ * H) * matrixAffineInverseFirstDerivative A H t) =
      matrixAffineInverseSecondDerivative A H t := by
    simp only [matrixAffineInverseFirstDerivative, matrixAffineInverseSecondDerivative,
      mul_zero, add_zero, neg_mul, mul_neg, neg_add, neg_neg, mul_assoc]
    module
  rw [heq] at hd
  exact hd

/-- Actual third derivative of the inverse curve; no convergence of an infinite expansion is used. -/
theorem matrixHasDerivAt_affineInverseSecondDerivative
    (A H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (hAt : (A + t • H).det ≠ 0) :
    MatrixHasDerivAt (matrixAffineInverseSecondDerivative A H)
      (matrixAffineInverseThirdDerivative A H t) t := by
  have hF := matrixHasDerivAt_affineInverse A H t hAt
  have hH := matrixDerivative_const H t
  have hd := matrixDerivative_const_smul ((((hF.mul hH).mul hF).mul hH).mul hF) 2
  let F := (A + t • H)⁻¹
  let D := matrixAffineInverseFirstDerivative A H t
  have heq : (2 : ℝ) •
      ((((D * H + F * 0) * F + F * H * D) * H + F * H * F * 0) * F + F * H * F * H * D) =
      matrixAffineInverseThirdDerivative A H t := by
    dsimp only [F, D, matrixAffineInverseFirstDerivative, matrixAffineInverseThirdDerivative]
    simp only [mul_zero, add_zero, neg_mul, mul_neg, add_mul, mul_assoc]
    module
  rw [heq] at hd
  exact hd

/-- The inverse's cubic derivative vanishes precisely for a cube-nilpotent relative perturbation.
Affine dependence of the metric itself does not remove this third-order contribution. -/
theorem matrixAffineInverseThirdDerivative_zero_iff
    (A H : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    matrixAffineInverseThirdDerivative A H 0 = 0 ↔ (A⁻¹ * H) ^ 3 = 0 := by
  have hword : A⁻¹ * H * A⁻¹ * H * A⁻¹ * H * A⁻¹ = (A⁻¹ * H) ^ 3 * A⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [matrixAffineInverseThirdDerivative, zero_smul, add_zero, hword]
  have hsix : (-6 : ℝ) ≠ 0 := by norm_num
  rw [smul_eq_zero, or_iff_right hsix]
  constructor
  · intro h
    have heq := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M * A) h
    simpa only [mul_assoc, Matrix.nonsing_inv_mul A hA, mul_one, zero_mul] using heq
  · intro h
    rw [h, zero_mul]

end RealDerivatives

end
end GaloisForLFunctions.HTGeometry
