import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsRelativeUniform

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Matrix

/-- The residual transition left after removing the exact uniform refresh preserves constants. -/
theorem egbFixedChargeACriticalMarkovRefreshWeight_row_sum (n : ℕ)
    (i : Fin (2 ^ (n + 3))) :
    ∑ j, egbFixedChargeACriticalMarkovRefreshWeight n i j = 1 := by
  simp_rw [egbFixedChargeACriticalMarkovRefreshWeight_symm n i]
  exact egbFixedChargeACriticalMarkovRefreshWeight_column_sum n i

/-- The residual part of the two-step refresh decomposition is itself bistochastic. -/
def egbFixedChargeACriticalRefreshBistochastic (n : ℕ) :
    doublyStochastic ℝ (Fin (2 ^ (n + 3))) :=
  ⟨Matrix.of (egbFixedChargeACriticalMarkovRefreshWeight n),
    mem_doublyStochastic_iff_sum.mpr
      ⟨egbFixedChargeACriticalMarkovRefreshWeight_nonneg n,
        egbFixedChargeACriticalMarkovRefreshWeight_row_sum n,
        egbFixedChargeACriticalMarkovRefreshWeight_column_sum n⟩⟩

/-- Matrix action and the corpus positive-kernel action agree for the residual transition. -/
theorem egbFixedChargeACriticalRefreshBistochastic_action (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalRefreshBistochastic n).val *ᵥ f =
      (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal f := rfl

/-- Removing the stationary component commutes with the residual transition. -/
theorem egbFixedChargeACriticalMarkovRefresh_center (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) (c : ℝ) :
    (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal
      (fun i => f i - c) = fun i =>
        (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal f i - c := by
  funext i
  change ∑ j, egbFixedChargeACriticalMarkovRefreshWeight n i j * (f j - c) =
    (∑ j, egbFixedChargeACriticalMarkovRefreshWeight n i j * f j) - c
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    egbFixedChargeACriticalMarkovRefreshWeight_row_sum, one_mul]

/-- The residual transition cannot increase the squared norm of any real profile. -/
theorem egbFixedChargeACriticalMarkovRefresh_sum_sq_le (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i, ((egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal f i) ^ 2 ≤
      ∑ i, (f i) ^ 2 := by
  have h := bistochasticMixing_sum_sq_le (egbFixedChargeACriticalRefreshBistochastic n) f
  rw [egbFixedChargeACriticalRefreshBistochastic_action] at h
  exact h

/-- The residual transition also contracts the corpus total-variation observable. -/
theorem egbFixedChargeACriticalMarkovRefresh_totalVariation_le (n : ℕ)
    (f g : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i, |(egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal f i -
      (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal g i| ≤
      ∑ i, |f i - g i| := by
  have h := bistochasticMixing_abs_sub_sum_le (egbFixedChargeACriticalRefreshBistochastic n) f g
  rw [egbFixedChargeACriticalRefreshBistochastic_action,
    egbFixedChargeACriticalRefreshBistochastic_action] at h
  exact h

end
end GaloisForLFunctions.HTGeometry
