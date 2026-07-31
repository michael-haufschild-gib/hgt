import GaloisForLFunctions.RHTower.FiniteRankOperatorAlgebra

/-!
# Diagonal operators on the square-summable sequence space

The approximation-number sandwich needs a concrete operator whose approximation numbers can be
read off.  The canonical one is diagonal on `ℓ²(ℕ)`, and the corpus had no such operator: nothing
constructed a bounded operator on that space at all.

Here the diagonal multiplication by a bounded sequence is built end to end: square-summability is
preserved by comparison with the multiplier bound, the map is linear, its operator norm is at most
the multiplier bound, and it is therefore a bounded operator on the space.
-/

open scoped ENNReal

noncomputable section

namespace RHTower

/-- The square-summable complex sequence space. -/
abbrev EllTwo := lp (fun _ : ℕ => ℂ) 2

/-- Multiplying a square-summable sequence by a bounded sequence keeps it square summable. -/
theorem memℓp_diagonal {lam : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (f : EllTwo) :
    Memℓp (fun n => lam n * f n) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun n => ‖f n‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro n
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (hC n) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

/-- Diagonal multiplication by a bounded sequence, as a linear map. -/
def diagonalLinearMap (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) :
    EllTwo →ₗ[ℂ] EllTwo where
  toFun f := ⟨fun n => lam n * f n, memℓp_diagonal hC f⟩
  map_add' := by
    intro f g
    ext n
    simp [mul_add]
  map_smul' := by
    intro c f
    ext n
    simp [mul_left_comm]

@[simp] theorem diagonalLinearMap_apply (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (f : EllTwo) (n : ℕ) :
    (diagonalLinearMap lam hC f : ℕ → ℂ) n = lam n * f n := rfl

/-- The diagonal map is bounded by the multiplier bound. -/
theorem norm_diagonalLinearMap_le (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (f : EllTwo) :
    ‖diagonalLinearMap lam hC f‖ ≤ C * ‖f‖ := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hnn : (0 : ℝ) ≤ ‖diagonalLinearMap lam hC f‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ C * ‖f‖ := mul_nonneg hCnn (norm_nonneg _)
  have htsumD : ‖diagonalLinearMap lam hC f‖ ^ (2 : ℝ)
      = ∑' n, ‖(diagonalLinearMap lam hC f) n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num)
      (diagonalLinearMap lam hC f)
  have htsumf : ‖f‖ ^ (2 : ℝ) = ∑' n, ‖f n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num) f
  have hsumf : Summable fun n => ‖f n‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hsumD : Summable fun n => ‖(diagonalLinearMap lam hC f) n‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ n, ‖(diagonalLinearMap lam hC f) n‖ ^ (2 : ℝ)
      ≤ C ^ (2 : ℝ) * ‖f n‖ ^ (2 : ℝ) := by
    intro n
    rw [diagonalLinearMap_apply, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hC n) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : ‖diagonalLinearMap lam hC f‖ ^ (2 : ℝ) ≤ (C * ‖f‖) ^ (2 : ℝ) := by
    rw [htsumD, Real.mul_rpow hCnn (norm_nonneg _), htsumf, ← tsum_mul_left]
    exact tsum_le_tsum hterm hsumD (hsumf.mul_left (C ^ (2 : ℝ)))
  have hx2 : ‖diagonalLinearMap lam hC f‖ ^ (2 : ℝ)
      = ‖diagonalLinearMap lam hC f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (C * ‖f‖) ^ (2 : ℝ) = (C * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

/-- Diagonal multiplication by a bounded sequence, as a bounded operator. -/
def diagonalOperator (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) :
    EllTwo →L[ℂ] EllTwo :=
  LinearMap.mkContinuous (diagonalLinearMap lam hC) C (norm_diagonalLinearMap_le lam hC)

@[simp] theorem diagonalOperator_apply (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (f : EllTwo) (n : ℕ) :
    (diagonalOperator lam hC f) n = lam n * f n := rfl

theorem norm_diagonalOperator_le (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) :
    ‖diagonalOperator lam hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (norm_nonneg _) (hC 0)) _

end RHTower

end
