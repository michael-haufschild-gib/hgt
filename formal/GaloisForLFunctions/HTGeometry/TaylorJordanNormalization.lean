import GaloisForLFunctions.HTGeometry.SharpJordanMetricBudget
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.Rev

/-!
# The exact Taylor norm behind the sharp Jordan metric budget

Derivative jets have subdiagonal coefficients `k`. Dividing by `k!` and
reversing indices gives the canonical unit superdiagonal chain. This explicit
invertible frame specifies the reference norm; raw derivative coordinates do
not have the same conditioning budget.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Matrix

def derivativeJordanBlock (d : ℕ) (a : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = j then a else if j.val + 1 = i.val then (i.val : ℂ) else 0

def factorialTaylorFrame (d : ℕ) : (Matrix (Fin d) (Fin d) ℂ)ˣ where
  val := Matrix.diagonal fun i => (i.val.factorial : ℂ)⁻¹
  inv := Matrix.diagonal fun i => (i.val.factorial : ℂ)
  val_inv := by
    have hf : ∀ i : Fin d, (i.val.factorial : ℂ) ≠ 0 := by
      intro i; exact_mod_cast Nat.factorial_ne_zero i.val
    rw [Matrix.diagonal_mul_diagonal]
    simp [hf]
  inv_val := by
    have hf : ∀ i : Fin d, (i.val.factorial : ℂ) ≠ 0 := by
      intro i; exact_mod_cast Nat.factorial_ne_zero i.val
    rw [Matrix.diagonal_mul_diagonal]
    simp [hf]

def permutationMetricFrame {d : ℕ} (e : Equiv.Perm (Fin d)) :
    (Matrix (Fin d) (Fin d) ℂ)ˣ where
  val := e.permMatrix ℂ
  inv := e⁻¹.permMatrix ℂ
  val_inv := by rw [← Matrix.permMatrix_mul]; simp
  inv_val := by rw [← Matrix.permMatrix_mul]; simp

def reversedTaylorFrame (d : ℕ) : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
  permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin d)) * factorialTaylorFrame d

theorem factorialTaylorFrame_conjugate (d : ℕ) (a : ℂ) :
    (factorialTaylorFrame d).val * derivativeJordanBlock d a * (factorialTaylorFrame d).inv =
      (metricJordanBlock d a)ᵀ := by
  have hf : ∀ i : Fin d, (i.val.factorial : ℂ) ≠ 0 := by
    intro i; exact_mod_cast Nat.factorial_ne_zero i.val
  ext i j
  change ((Matrix.diagonal (fun i : Fin d => (i.val.factorial : ℂ)⁻¹) *
    derivativeJordanBlock d a) * Matrix.diagonal (fun i : Fin d => (i.val.factorial : ℂ))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    simp [derivativeJordanBlock, metricJordanBlock, mul_comm, hf]
  · have hji : j ≠ i := fun h => hij h.symm
    simp only [derivativeJordanBlock, metricJordanBlock, Matrix.transpose_apply,
      if_neg hij, if_neg hji]
    by_cases h : j.val + 1 = i.val
    · simp only [if_pos h]
      rw [← h, Nat.factorial_succ]
      push_cast
      have hj : (j.val.factorial : ℂ) ≠ 0 := hf j
      have hj1 : (j.val : ℂ) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero j.val
      field_simp
    · simp [h]

theorem permutationMetricFrame_conjugate_apply {d : ℕ}
    (e : Equiv.Perm (Fin d)) (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    ((permutationMetricFrame e).val * M * (permutationMetricFrame e).inv) i j =
      M (e i) (e j) := by
  change ((e.permMatrix ℂ * M) * (e⁻¹).permMatrix ℂ) i j = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem reversal_conjugate_transpose_jordan (d : ℕ) (a : ℂ) :
    (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin d))).val *
        (metricJordanBlock d a)ᵀ *
        (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin d))).inv =
      metricJordanBlock d a := by
  ext i j
  rw [permutationMetricFrame_conjugate_apply]
  change metricJordanBlock d a j.rev i.rev = metricJordanBlock d a i j
  by_cases hij : i = j
  · subst j; simp [metricJordanBlock]
  · have hrev : j.rev ≠ i.rev := fun h => hij (Fin.rev_injective h).symm
    have hadj : j.rev.val + 1 = i.rev.val ↔ i.val + 1 = j.val := by
      simp only [Fin.val_rev]
      have := i.isLt
      have := j.isLt
      omega
    simp only [metricJordanBlock, if_neg hij, if_neg hrev]
    simp only [hadj]

theorem reversedTaylorFrame_conjugate (d : ℕ) (a : ℂ) :
    (reversedTaylorFrame d).val * derivativeJordanBlock d a * (reversedTaylorFrame d).inv =
      metricJordanBlock d a := by
  change ((permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin d))).val *
      (factorialTaylorFrame d).val) * derivativeJordanBlock d a *
        ((factorialTaylorFrame d).inv *
          (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin d))).inv) = _
  calc
    _ = (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin d))).val *
        ((factorialTaylorFrame d).val * derivativeJordanBlock d a *
          (factorialTaylorFrame d).inv) *
            (permutationMetricFrame (Fin.revPerm : Equiv.Perm (Fin d))).inv := by
      simp only [Matrix.mul_assoc]
    _ = metricJordanBlock d a := by
      rw [factorialTaylorFrame_conjugate, reversal_conjugate_transpose_jordan]

theorem matrixMetricFrame_gram_posDef {d : ℕ} (P : (Matrix (Fin d) (Fin d) ℂ)ˣ) :
    ((P : Matrix (Fin d) (Fin d) ℂ)ᴴ * (P : Matrix (Fin d) (Fin d) ℂ)).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.mpr P.isUnit)

/-- The positive Gram metric has the square of its frame's operator condition number. -/
theorem matrixMetricFrame_gram_conditionNumber {d : ℕ}
    (P : (Matrix (Fin d) (Fin d) ℂ)ˣ) :
    HilbertMetric.similarityConditionNumber (star P * P) =
      HilbertMetric.similarityConditionNumber P ^ 2 := by
  simp only [HilbertMetric.similarityConditionNumber, Units.val_mul, mul_inv_rev,
    Units.coe_star, Units.coe_star_inv, CStarRing.norm_star_mul_self,
    CStarRing.norm_self_mul_star]
  ring

end
end GaloisForLFunctions.HTGeometry
