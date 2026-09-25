import GaloisForLFunctions.RHTower.HadamardRegularizationLaw
import GaloisForLFunctions.RHTower.VonMangoldtGammaFactorialNormalizationNoGo

/-!
# The factorial trace-normalization destroys positivity as a map

The first factorial trace-normalization sends `A` to `!![A₀₀, A₀₁/6; A₁₀/6, A₁₁/120]`, which is the
entrywise product with the multiplier `!![1, 1/6; 1/6, 1/120]` of reciprocal odd factorials.  That
multiplier has determinant `−7/360`, so by the regularization criterion the normalization fails to
preserve positive semidefiniteness — and the witness is the all-ones matrix, the most degenerate
positive Gram there is.

The failure therefore has nothing to do with the arithmetic of the source: the source-specific
no-go for the von Mangoldt Gram is an instance of a property of the normalization map alone.
-/

open Matrix

namespace RHTower

/-- The entrywise multiplier of the first factorial trace-normalization: the reciprocal odd
factorials `1/1!, 1/3!, 1/5!`. -/
noncomputable def oddFactorialMultiplier : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / 6; 1 / 6, 1 / 120]

theorem vonMangoldtGammaFirstFactorialNormalize_eq_hadamard (A : Matrix (Fin 2) (Fin 2) ℝ) :
    vonMangoldtGammaFirstFactorialNormalize A = A.hadamard oddFactorialMultiplier := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vonMangoldtGammaFirstFactorialNormalize, oddFactorialMultiplier, Matrix.hadamard,
      div_eq_mul_inv]

theorem oddFactorialMultiplier_det : oddFactorialMultiplier.det = -(7 / 360) := by
  rw [oddFactorialMultiplier, Matrix.det_fin_two]
  norm_num

/-- **The multiplier is not a positive kernel.** -/
theorem oddFactorialMultiplier_not_posSemidef : ¬ oddFactorialMultiplier.PosSemidef := by
  intro h
  have hdet := h.det_nonneg
  rw [oddFactorialMultiplier_det] at hdet
  norm_num at hdet

/-- **The normalization is not positivity-preserving, independently of the source.**  The all-ones
Gram already breaks. -/
theorem exists_posSemidef_factorialNormalize_not_posSemidef :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosSemidef ∧
      ¬ (vonMangoldtGammaFirstFactorialNormalize A).PosSemidef := by
  refine ⟨Matrix.of (fun _ _ : Fin 2 => (1 : ℝ)), posSemidef_allOnes (Fin 2), ?_⟩
  rw [vonMangoldtGammaFirstFactorialNormalize_eq_hadamard]
  have heq : (Matrix.of (fun _ _ : Fin 2 => (1 : ℝ))).hadamard oddFactorialMultiplier
      = oddFactorialMultiplier := by
    ext i j
    simp [Matrix.hadamard]
  rw [heq]
  exact oddFactorialMultiplier_not_posSemidef

/-- **The criterion, applied.**  The normalization preserves positivity on every input exactly when
its multiplier is a positive kernel, and here it is not. -/
theorem not_forall_posSemidef_factorialNormalize :
    ¬ (∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosSemidef →
        (vonMangoldtGammaFirstFactorialNormalize A).PosSemidef) := by
  intro h
  refine oddFactorialMultiplier_not_posSemidef ?_
  refine (hadamard_preserves_posSemidef_iff oddFactorialMultiplier).mp ?_
  intro A hA
  rw [← vonMangoldtGammaFirstFactorialNormalize_eq_hadamard]
  exact h A hA

end RHTower
