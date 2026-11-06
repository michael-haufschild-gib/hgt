import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Determinant weights of invariant tensors

For the standard complex plane, every `SL₂`-invariant multilinear form of degree `2k`
transforms under an invertible matrix `A` by `det(A)^k`. Odd-degree invariant forms
vanish. Split `A` into a scalar and a determinant-one matrix to obtain the even law;
the central element `-1` gives the odd law.

These weights depend only on the determinant, not on the moduli of the two eigenvalues.
-/

open Matrix
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

abbrev Plane := Fin 2 → ℂ
abbrev TensorForm (n : ℕ) := MultilinearMap ℂ (fun _ : Fin n => Plane) ℂ

/-- Multilinear forms fixed by every determinant-one change of frame. -/
def invariantForms (n : ℕ) : Submodule ℂ (TensorForm n) where
  carrier := { f | ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 →
    ∀ v, f (fun i => A.mulVec (v i)) = f v }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg A hA v
    simp only [_root_.add_apply, hf A hA, hg A hA]
  smul_mem' := by
    intro c f hf A hA v
    simp only [_root_.smul_apply, hf A hA]

/-- Scalar changes of frame act with the tensor degree. -/
theorem invariant_scalar_mul (n : ℕ) (f : invariantForms n) (c : ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (v : Fin n → Plane) :
    f.val (fun i => (c • A).mulVec (v i)) = c ^ n * f.val v := by
  simp_rw [Matrix.smul_mulVec]
  rw [f.val.map_smul_univ, f.property A hA v]
  simp

/-- In even degree the full invertible-frame action is exactly the determinant character. -/
theorem invariant_even_det (k : ℕ) (f : invariantForms (2 * k))
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) (v : Fin (2 * k) → Plane) :
    f.val (fun i => A.mulVec (v i)) = A.det ^ k * f.val v := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) A.det (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    intro h
    apply hA
    simpa [h] using hc.symm
  have hd : (c⁻¹ • A).det = 1 := by
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin, inv_pow, hc]
    exact inv_mul_cancel₀ hA
  have he := invariant_scalar_mul (2 * k) f c (c⁻¹ • A) hd v
  rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, pow_mul, hc] at he
  exact he

/-- Determinant covariance on invertible matrices characterizes the invariant forms. -/
theorem mem_invariantForms_even_iff (k : ℕ) (f : TensorForm (2 * k)) :
    f ∈ invariantForms (2 * k) ↔
      ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.det ≠ 0 → ∀ v,
        f (fun i => A.mulVec (v i)) = A.det ^ k * f v := by
  refine ⟨fun hf A hA v => invariant_even_det k ⟨f, hf⟩ A hA v, ?_⟩
  intro hf A hA v
  simpa only [hA, one_pow, one_mul] using hf A (by rw [hA]; exact one_ne_zero) v

/-- Odd-degree invariant forms vanish: the central element `-1` reverses their sign. -/
theorem invariant_odd_eq_zero (k : ℕ) (f : invariantForms (2 * k + 1)) : f.val = 0 := by
  ext v
  have hdet : (-(1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 1 := by
    rw [Matrix.det_neg]
    simp
  have hf := f.property (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) hdet v
  have hs := invariant_scalar_mul (2 * k + 1) f (-1) 1 Matrix.det_one v
  simp only [neg_one_smul] at hs
  rw [hf] at hs
  have hp : (-1 : ℂ) ^ (2 * k + 1) = -1 := by simp [pow_add, pow_mul]
  rw [hp, neg_one_mul] at hs
  change f.val v = 0
  linear_combination (1 / 2 : ℂ) * hs

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
