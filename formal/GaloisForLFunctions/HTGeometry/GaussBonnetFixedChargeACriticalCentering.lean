import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAFiveModeEnergy

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The uniform mean of an arbitrary real profile on the critical grid. -/
def egbFixedChargeACriticalRealMean (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ((2 : ℝ) ^ (n + 3))⁻¹ * ∑ i, f i

/-- Removing the invariant constant component of a real profile. -/
def egbFixedChargeACriticalCenteredProfile (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => f i - egbFixedChargeACriticalRealMean n f

/-- Centering cancels total mass exactly. -/
theorem egbFixedChargeACriticalCenteredProfile_mass_zero (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i, egbFixedChargeACriticalCenteredProfile n f i = 0 := by
  unfold egbFixedChargeACriticalCenteredProfile
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  unfold egbFixedChargeACriticalRealMean
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- Every transition power preserves the uniform mean. -/
theorem egbFixedChargeACriticalRealMean_invariant (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalRealMean n
      ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) =
        egbFixedChargeACriticalRealMean n f := by
  unfold egbFixedChargeACriticalRealMean
  rw [FiniteMarkovKernel.sum_applyReal]

/-- Removing the invariant component commutes with every transition power. -/
theorem egbFixedChargeACriticalCenteredProfile_action (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalCenteredProfile n f) =
        egbFixedChargeACriticalCenteredProfile n
          ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) := by
  have h := egbFixedChargeACriticalMarkov_affine_action n m f
    (-egbFixedChargeACriticalRealMean n f) 1
  simp only [one_mul] at h
  have hi : (fun i => -egbFixedChargeACriticalRealMean n f + f i) =
      egbFixedChargeACriticalCenteredProfile n f := by
    funext i
    unfold egbFixedChargeACriticalCenteredProfile
    ring
  rw [hi] at h
  rw [h]
  funext i
  unfold egbFixedChargeACriticalCenteredProfile
  rw [egbFixedChargeACriticalRealMean_invariant]
  ring

/-- Centering respects arbitrary real scaling. -/
theorem egbFixedChargeACriticalCenteredProfile_scale (n : ℕ) (c : ℝ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalCenteredProfile n (fun i => c * f i) =
      fun i => c * egbFixedChargeACriticalCenteredProfile n f i := by
  funext i
  simp only [egbFixedChargeACriticalCenteredProfile, egbFixedChargeACriticalRealMean,
    ← Finset.mul_sum]
  ring

/-- The centering operator is an exact projection. -/
theorem egbFixedChargeACriticalCenteredProfile_idempotent (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalCenteredProfile n f) =
      egbFixedChargeACriticalCenteredProfile n f := by
  funext i
  change egbFixedChargeACriticalCenteredProfile n f i -
    egbFixedChargeACriticalRealMean n (egbFixedChargeACriticalCenteredProfile n f) = _
  rw [egbFixedChargeACriticalRealMean, egbFixedChargeACriticalCenteredProfile_mass_zero,
    mul_zero, sub_zero]

end
end GaloisForLFunctions.HTGeometry
