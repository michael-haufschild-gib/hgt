import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovAntipodes

/-!
The two-step critical Gibbs transition contains an exact uniform-refresh component
of weight1/6. Its remainder is another literal corpus FiniteMarkovKernel.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Residual transition after removing the uniform-refresh component from two Gibbs steps. -/
def egbFixedChargeACriticalMarkovRefreshWeight (n : ℕ) (i j : Fin (2 ^ (n + 3))) : ℝ :=
  (6 / 5) * (((egbFixedChargeACriticalMarkovMatrix n ^ 2) i j).re -
    1 / (6 * (2 : ℝ) ^ (n + 3)))

/-- The sharp positive floor makes the residual weights nonnegative. -/
theorem egbFixedChargeACriticalMarkovRefreshWeight_nonneg
    (n : ℕ) (i j : Fin (2 ^ (n + 3))) :
    0 ≤ egbFixedChargeACriticalMarkovRefreshWeight n i j := by
  unfold egbFixedChargeACriticalMarkovRefreshWeight
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr (egbFixedChargeACriticalMarkovMatrix_two_step_minorization n 0 i j))

/-- The residual transition remains symmetric. -/
theorem egbFixedChargeACriticalMarkovRefreshWeight_symm
    (n : ℕ) (i j : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalMarkovRefreshWeight n i j =
      egbFixedChargeACriticalMarkovRefreshWeight n j i := by
  unfold egbFixedChargeACriticalMarkovRefreshWeight
  rw [egbFixedChargeACriticalMarkovMatrix_pow_symm n 2 i j]

/-- The residual transition preserves total probability. -/
theorem egbFixedChargeACriticalMarkovRefreshWeight_column_sum
    (n : ℕ) (j : Fin (2 ^ (n + 3))) :
    ∑ i : Fin (2 ^ (n + 3)), egbFixedChargeACriticalMarkovRefreshWeight n i j = 1 := by
  simp only [egbFixedChargeACriticalMarkovRefreshWeight, ← Finset.mul_sum,
    Finset.sum_sub_distrib, egbFixedChargeACriticalMarkovMatrix_pow_column_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp <;> ring

/-- The residual transition as an existing corpus finite Markov kernel. -/
def egbFixedChargeACriticalMarkovRefreshKernel (n : ℕ) :
    FiniteMarkovKernel (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) where
  weight := egbFixedChargeACriticalMarkovRefreshWeight n
  nonneg := egbFixedChargeACriticalMarkovRefreshWeight_nonneg n
  column_sum := egbFixedChargeACriticalMarkovRefreshWeight_column_sum n

/-- Exact two-step decomposition into uniform refresh and residual Markov transition. -/
theorem egbFixedChargeACriticalMarkovRefresh_decomposition
    (n : ℕ) (i j : Fin (2 ^ (n + 3))) :
    ((egbFixedChargeACriticalMarkovMatrix n ^ 2) i j).re =
      (1 / 6) * ((2 : ℝ) ^ (n + 3))⁻¹ +
        (5 / 6) * egbFixedChargeACriticalMarkovRefreshWeight n i j := by
  unfold egbFixedChargeACriticalMarkovRefreshWeight
  ring

/-- The refresh decomposition acts on arbitrary real profiles with their own total mass. -/
theorem egbFixedChargeACriticalMarkovRefresh_action
    (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n 2).toFinitePositiveKernel.applyReal f =
      fun i => (1 / (6 * (2 : ℝ) ^ (n + 3))) * (∑ j, f j) +
        (5 / 6) * (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal f i := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ 2) i j).re * f j) = _
  simp only [egbFixedChargeACriticalMarkovRefresh_decomposition, add_mul,
    Finset.sum_add_distrib]
  change (∑ j, (1 / 6 * ((2 : ℝ) ^ (n + 3))⁻¹) * f j) +
      (∑ j, (5 / 6 * egbFixedChargeACriticalMarkovRefreshWeight n i j) * f j) =
    _ + (5 / 6) * ∑ j, egbFixedChargeACriticalMarkovRefreshWeight n i j * f j
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

end

end GaloisForLFunctions.HTGeometry
