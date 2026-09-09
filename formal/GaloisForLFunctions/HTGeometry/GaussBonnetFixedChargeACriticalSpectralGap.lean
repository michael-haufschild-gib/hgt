import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalCenteredEnergy

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem nonzero_frequency_bound (n : ℕ) (j : Fin (2 ^ (n + 3))) (hj : j ≠ 0) :
    ‖egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j‖ ^ 2 ≤ 4 / 9 := by
  by_cases hs : ∃ k : Fin 5, j = egbFixedChargeAFiveFourierModes n k
  · obtain ⟨k, rfl⟩ := hs
    rw [egbFixedChargeAFiveModeSpectrum_mode]
    fin_cases k
    · exact (hj rfl).elim
    all_goals norm_num [egbFixedChargeACriticalMarkovEigenvalues,
      Complex.norm_real, Real.norm_eq_abs]
  · rw [(egbFixedChargeACriticalMarkovSpectrum_zero_iff n j).mpr hs]
    norm_num

private theorem centered_sum_sq_step (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i, ((egbFixedChargeACriticalMarkovIteratedKernel n 1).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalCenteredProfile n f) i) ^ 2 ≤
        (4 / 9) * ∑ i, egbFixedChargeACriticalCenteredProfile n f i ^ 2 := by
  have he := egbFixedChargeACriticalMarkovMatrix_spectral_energy n 1
    (fun i => (egbFixedChargeACriticalCenteredProfile n f i : ℂ))
  rw [egbFixedChargeACriticalMarkov_complex_lift] at he
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_one] at he
  rw [he]
  have hp := egbFixedChargeACriticalFourierCoordinates_parseval n
    (fun i => (egbFixedChargeACriticalCenteredProfile n f i : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp
  rw [← hp, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j = 0
  · subst j
    rw [egbFixedChargeACriticalCenteredProfile_zero_frequency]
    simp
  · rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (nonzero_frequency_bound n j hj) (sq_nonneg _)

/-- Removing the invariant mean exposes a squared-norm contraction by four ninths at each step. -/
theorem egbFixedChargeACriticalCenteredEnergy_step (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalCenteredEnergy n
      ((egbFixedChargeACriticalMarkovIteratedKernel n 1).toFinitePositiveKernel.applyReal f) ≤
        (4 / 9) * egbFixedChargeACriticalCenteredEnergy n f := by
  unfold egbFixedChargeACriticalCenteredEnergy
  rw [← egbFixedChargeACriticalCenteredProfile_action]
  exact centered_sum_sq_step n f

/-- The centered squared norm has a geometric bound at every finite transition count. -/
theorem egbFixedChargeACriticalCenteredEnergy_geometric (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalCenteredEnergy n
      ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) ≤
        (4 / 9 : ℝ) ^ m * egbFixedChargeACriticalCenteredEnergy n f := by
  induction m with
  | zero => rw [egbFixedChargeACriticalMarkovIteratedKernel_zero]; simp
  | succ m ih =>
      have ha := egbFixedChargeACriticalMarkovIteratedKernel_add n 1 m f
      rw [Nat.add_comm 1 m] at ha
      rw [ha]
      calc
        _ ≤ (4 / 9) * egbFixedChargeACriticalCenteredEnergy n
            ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) :=
          egbFixedChargeACriticalCenteredEnergy_step n _
        _ ≤ (4 / 9) * ((4 / 9 : ℝ) ^ m * egbFixedChargeACriticalCenteredEnergy n f) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ (4 / 9 : ℝ) m]; ring

end
end GaloisForLFunctions.HTGeometry
