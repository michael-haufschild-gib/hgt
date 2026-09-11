import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalUnitHidden
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMixedModes

/-! # Three independent real energy coordinates for the full thermal history -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The erased coordinate completes the existing normalized slow/fast plane. -/
def egbFixedChargeACriticalFullMixedProfile (n : ℕ) (c a b : ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => c * egbFixedChargeACriticalUnitHidden n i + egbFixedChargeACriticalMixedProfile n a b i

/-- The erased unit direction is orthogonal to the entire surviving two-mode plane. -/
theorem egbFixedChargeACriticalUnitHidden_mixed_orthogonal (n : ℕ) (a b : ℝ) :
    ∑ i, egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalMixedProfile n a b i = 0 := by
  unfold egbFixedChargeACriticalMixedProfile
  calc
    _ = a * (∑ i, egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalUnitSlow n i) +
        b * (∑ i, egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalUnitFast n i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      rw [(egbFixedChargeACriticalUnitHidden_orthogonal n).1,
        (egbFixedChargeACriticalUnitHidden_orthogonal n).2]
      ring

/-- All three independent profile coordinates preserve zero total mass. -/
theorem egbFixedChargeACriticalFullMixedProfile_mass_zero (n : ℕ) (c a b : ℝ) :
    ∑ i, egbFixedChargeACriticalFullMixedProfile n c a b i = 0 := by
  simp only [egbFixedChargeACriticalFullMixedProfile, Finset.sum_add_distrib, ← Finset.mul_sum,
    egbFixedChargeACriticalUnitHidden_mass_zero, egbFixedChargeACriticalMixedProfile_mass_zero,
    mul_zero, add_zero]

/-- The full three-coordinate profile is already centered. -/
theorem egbFixedChargeACriticalFullMixedProfile_centered (n : ℕ) (c a b : ℝ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalFullMixedProfile n c a b) =
      egbFixedChargeACriticalFullMixedProfile n c a b := by
  funext i
  simp only [egbFixedChargeACriticalCenteredProfile, egbFixedChargeACriticalRealMean,
    egbFixedChargeACriticalFullMixedProfile_mass_zero, mul_zero, sub_zero]

/-- Erased, slow, and fast coefficients are exact Euclidean energy coordinates. -/
theorem egbFixedChargeACriticalFullMixedProfile_energy (n : ℕ) (c a b : ℝ) :
    egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFullMixedProfile n c a b) =
      c ^ 2 + a ^ 2 + b ^ 2 := by
  have hh : (∑ i, egbFixedChargeACriticalUnitHidden n i ^ 2) = 1 := by
    simpa only [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalUnitHidden_centered] using
      egbFixedChargeACriticalUnitHidden_energy_one n
  have hm : (∑ i, egbFixedChargeACriticalMixedProfile n a b i ^ 2) = a ^ 2 + b ^ 2 := by
    simpa only [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalMixedProfile_centered] using
      egbFixedChargeACriticalMixedProfile_energy n a b
  have hp (i : Fin (2 ^ (n + 3))) :
      (c * egbFixedChargeACriticalUnitHidden n i + egbFixedChargeACriticalMixedProfile n a b i) ^ 2 =
        c ^ 2 * egbFixedChargeACriticalUnitHidden n i ^ 2 + egbFixedChargeACriticalMixedProfile n a b i ^ 2 +
          (2 * c) * (egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalMixedProfile n a b i) := by ring
  rw [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalFullMixedProfile_centered]
  simp only [egbFixedChargeACriticalFullMixedProfile, hp, Finset.sum_add_distrib, ← Finset.mul_sum,
    hh, hm, egbFixedChargeACriticalUnitHidden_mixed_orthogonal, mul_zero, mul_one, add_zero]
  ring

/-- One action evolves all three coordinates by their own amplitude rates, with the erased coordinate killed after time zero. -/
theorem egbFixedChargeACriticalFullMixedProfile_evolution (n m : ℕ) (c a b : ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalFullMixedProfile n c a b) =
        egbFixedChargeACriticalFullMixedProfile n (c * (0 : ℝ) ^ m)
          (a * (2 / 3 : ℝ) ^ m) (b * (1 / 6 : ℝ) ^ m) := by
  have hh := egbFixedChargeACriticalMarkov_affine_action n m (egbFixedChargeACriticalUnitHidden n) 0 c
  simp only [zero_add, egbFixedChargeACriticalUnitHidden_evolution] at hh
  unfold egbFixedChargeACriticalFullMixedProfile
  rw [FinitePositiveKernel.applyReal_add, hh, egbFixedChargeACriticalMixedProfile_evolution]
  funext i
  change c * ((0 : ℝ) ^ m * egbFixedChargeACriticalUnitHidden n i) + _ = _
  ring

/-- The complete three-rate energy law retains the initial erased mass exactly. -/
theorem egbFixedChargeACriticalFullMixedProfile_evolved_energy (n m : ℕ) (c a b : ℝ) :
    egbFixedChargeACriticalCenteredEnergy n
      ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
        (egbFixedChargeACriticalFullMixedProfile n c a b)) =
      (0 : ℝ) ^ m * c ^ 2 + (4 / 9 : ℝ) ^ m * a ^ 2 + (1 / 36 : ℝ) ^ m * b ^ 2 := by
  rw [egbFixedChargeACriticalFullMixedProfile_evolution, egbFixedChargeACriticalFullMixedProfile_energy]
  have hh : ((0 : ℝ) ^ m) ^ 2 = (0 : ℝ) ^ m := by cases m <;> simp
  have hs : ((2 / 3 : ℝ) ^ m) ^ 2 = (4 / 9 : ℝ) ^ m := by rw [pow_two, ← mul_pow]; norm_num
  have hf : ((1 / 6 : ℝ) ^ m) ^ 2 = (1 / 36 : ℝ) ^ m := by rw [pow_two, ← mul_pow]; norm_num
  rw [mul_pow c _ 2, mul_pow a _ 2, mul_pow b _ 2, hh, hs, hf]
  ring

/-- Zero initial energy identifies exactly the origin of the full three-mode space. -/
theorem egbFixedChargeACriticalFullMixedProfile_energy_zero_iff (n : ℕ) (c a b : ℝ) :
    egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFullMixedProfile n c a b) = 0 ↔
      c = 0 ∧ a = 0 ∧ b = 0 := by
  rw [egbFixedChargeACriticalFullMixedProfile_energy]
  constructor
  · intro h
    exact ⟨by nlinarith [sq_nonneg c, sq_nonneg a, sq_nonneg b],
      by nlinarith [sq_nonneg c, sq_nonneg a, sq_nonneg b],
      by nlinarith [sq_nonneg c, sq_nonneg a, sq_nonneg b]⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

end
end GaloisForLFunctions.HTGeometry
