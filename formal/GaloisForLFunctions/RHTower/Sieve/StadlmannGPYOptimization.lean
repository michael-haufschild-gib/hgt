import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Stadlmann GPY optimization algebra

Section 5.1 of arXiv:2608.31126 replaces Proposition 1's functional ratio by a ratio of
quadratic forms in exact basis matrices.  This file formalizes that reduction without assuming
either matrix is positive definite: only the chosen denominator must be positive when an
inequality is inferred.
-/

namespace RHTower.Sieve.StadlmannGPYOptimization

open scoped BigOperators Matrix

noncomputable section

variable {ι V : Type*} [Fintype ι] [AddCommMonoid V] [Module ℝ V]

/-- Real quadratic form used in the paper's equation (5.1). -/
def quadraticForm (M : Matrix ι ι ℝ) (c : ι → ℝ) : ℝ :=
  c ⬝ᵥ (M *ᵥ c)

/-- Matrix of a bilinear functional in a chosen finite family. -/
def gramMatrix (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : ι → V) : Matrix ι ι ℝ :=
  fun i j => B (G i) (G j)

/-- Linear combination represented by a coefficient vector. -/
def basisCombination (G : ι → V) (c : ι → ℝ) : V :=
  ∑ i, c i • G i

/-- Exact quadratic-form expansion of a bilinear functional in an arbitrary finite family. -/
theorem bilinear_basisCombination_eq_quadraticForm
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : ι → V) (c : ι → ℝ) :
    B (basisCombination G c) (basisCombination G c) =
      quadraticForm (gramMatrix B G) c := by
  simp only [basisCombination, map_sum, LinearMapClass.map_smul, gramMatrix, quadraticForm,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Numerator matrix `k(1-c₁)J - kc₂K` from Proposition 1 and equation (5.1). -/
def rewardMatrix (k : ℕ) (c₁ c₂ : ℝ) (J K : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ((k : ℝ) * (1 - c₁)) • J - ((k : ℝ) * c₂) • K

/-- Quadratic form of the reward matrix is the corresponding linear combination of forms. -/
theorem quadraticForm_rewardMatrix
    (k : ℕ) (c₁ c₂ : ℝ) (J K : Matrix ι ι ℝ) (c : ι → ℝ) :
    quadraticForm (rewardMatrix k c₁ c₂ J K) c =
      (k : ℝ) * (1 - c₁) * quadraticForm J c -
        (k : ℝ) * c₂ * quadraticForm K c := by
  simp only [quadraticForm, rewardMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul]
  ring

/-- **Paper equation (5.1).**  Basis matrices reproduce the functional ratio exactly. -/
theorem matrix_ratio_eq_functional_ratio
    (I J K : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : ι → V) (c : ι → ℝ)
    (k : ℕ) (c₁ c₂ : ℝ) :
    quadraticForm
          (rewardMatrix k c₁ c₂ (gramMatrix J G) (gramMatrix K G)) c /
        quadraticForm (gramMatrix I G) c =
      ((k : ℝ) * (1 - c₁) * J (basisCombination G c) (basisCombination G c) -
          (k : ℝ) * c₂ * K (basisCombination G c) (basisCombination G c)) /
        I (basisCombination G c) (basisCombination G c) := by
  rw [quadraticForm_rewardMatrix]
  simp only [← bilinear_basisCombination_eq_quadraticForm]

/-- A ratio exceeds one exactly when numerator exceeds its positive denominator. -/
theorem ratio_gt_one_iff {M₁ M₂ : Matrix ι ι ℝ} {c : ι → ℝ}
    (hden : 0 < quadraticForm M₁ c) :
    quadraticForm M₂ c / quadraticForm M₁ c > 1 ↔
      quadraticForm M₁ c < quadraticForm M₂ c := by
  rw [gt_iff_lt, lt_div_iff₀ hden]
  simp

/-- A generalized eigenvector gives its eigenvalue as the exact quadratic-form ratio.
No definiteness of either matrix is required. -/
theorem ratio_eq_generalizedEigenvalue {M₁ M₂ : Matrix ι ι ℝ} {c : ι → ℝ}
    {eigenvalue : ℝ}
    (hden : quadraticForm M₁ c ≠ 0)
    (heigen : M₂ *ᵥ c = eigenvalue • (M₁ *ᵥ c)) :
    quadraticForm M₂ c / quadraticForm M₁ c = eigenvalue := by
  have hquad : quadraticForm M₂ c = eigenvalue * quadraticForm M₁ c := by
    rw [quadraticForm, heigen, quadraticForm]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hquad]
  calc
    eigenvalue * quadraticForm M₁ c / quadraticForm M₁ c =
        quadraticForm M₁ c * eigenvalue / quadraticForm M₁ c := by ring
    _ = eigenvalue := mul_div_cancel_left₀ eigenvalue hden

/-- A generalized eigenvalue above one is a valid Proposition 1 matrix certificate whenever its
chosen denominator is positive. -/
theorem ratio_gt_one_of_generalizedEigenvalue {M₁ M₂ : Matrix ι ι ℝ}
    {c : ι → ℝ} {eigenvalue : ℝ}
    (hden : 0 < quadraticForm M₁ c)
    (heigen : M₂ *ᵥ c = eigenvalue • (M₁ *ᵥ c))
    (heigenvalue : 1 < eigenvalue) :
    quadraticForm M₂ c / quadraticForm M₁ c > 1 := by
  rw [ratio_eq_generalizedEigenvalue hden.ne' heigen]
  exact heigenvalue

omit [Fintype ι] in
/-- With the final proof's prime-indicator choice `c₁=c₂=0`, the correction matrix vanishes and
the reward is simply `kJ`. -/
theorem rewardMatrix_primeIndicator (k : ℕ) (J K : Matrix ι ι ℝ) :
    rewardMatrix k 0 0 J K = (k : ℝ) • J := by
  ext i j
  simp [rewardMatrix]

/-- The final `k=49`, `c₁=c₂=0` certificate is exactly the scalar inequality `I(c)<49J(c)`.
This is the non-numerical closed target that an exact rational witness must discharge. -/
theorem finalFortyNine_ratio_gt_one_iff
    {I J K : Matrix ι ι ℝ} {c : ι → ℝ}
    (hden : 0 < quadraticForm I c) :
    quadraticForm (rewardMatrix 49 0 0 J K) c / quadraticForm I c > 1 ↔
      quadraticForm I c < 49 * quadraticForm J c := by
  rw [ratio_gt_one_iff hden, quadraticForm_rewardMatrix]
  norm_num

end

end RHTower.Sieve.StadlmannGPYOptimization
