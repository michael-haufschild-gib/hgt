import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalUnitModes

/-! # A normalized two-mode plane inside the critical thermal dynamics -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

def egbFixedChargeACriticalMixedProfile (n : ℕ) (a b : ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => a * egbFixedChargeACriticalUnitSlow n i + b * egbFixedChargeACriticalUnitFast n i

/-- Every point of the normalized two-mode plane has zero invariant mean. -/
theorem egbFixedChargeACriticalMixedProfile_mass_zero (n : ℕ) (a b : ℝ) :
    ∑ i, egbFixedChargeACriticalMixedProfile n a b i = 0 := by
  simp only [egbFixedChargeACriticalMixedProfile, Finset.sum_add_distrib, ← Finset.mul_sum,
    (egbFixedChargeACriticalUnitModes_mass_zero n).1,
    (egbFixedChargeACriticalUnitModes_mass_zero n).2, mul_zero, add_zero]

/-- The whole two-mode plane is already centered. -/
theorem egbFixedChargeACriticalMixedProfile_centered (n : ℕ) (a b : ℝ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalMixedProfile n a b) =
      egbFixedChargeACriticalMixedProfile n a b := by
  funext i
  simp only [egbFixedChargeACriticalCenteredProfile, egbFixedChargeACriticalRealMean,
    egbFixedChargeACriticalMixedProfile_mass_zero, mul_zero, sub_zero]

/-- The two profile coefficients are exact Euclidean energy coordinates. -/
theorem egbFixedChargeACriticalMixedProfile_energy (n : ℕ) (a b : ℝ) :
    egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalMixedProfile n a b) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  have hs : (∑ i, egbFixedChargeACriticalUnitSlow n i ^ (2 : ℕ)) = 1 := by
    simpa only [egbFixedChargeACriticalCenteredEnergy, (egbFixedChargeACriticalUnitModes_centered n).1] using
      (egbFixedChargeACriticalUnitModes_energy_one n).1
  have hf : (∑ i, egbFixedChargeACriticalUnitFast n i ^ (2 : ℕ)) = 1 := by
    simpa only [egbFixedChargeACriticalCenteredEnergy, (egbFixedChargeACriticalUnitModes_centered n).2] using
      (egbFixedChargeACriticalUnitModes_energy_one n).2
  have hp (i : Fin (2 ^ (n + 3))) :
      (a * egbFixedChargeACriticalUnitSlow n i + b * egbFixedChargeACriticalUnitFast n i) ^ (2 : ℕ) =
        a ^ (2 : ℕ) * egbFixedChargeACriticalUnitSlow n i ^ (2 : ℕ) + b ^ (2 : ℕ) * egbFixedChargeACriticalUnitFast n i ^ (2 : ℕ) +
        (2 * a * b) * (egbFixedChargeACriticalUnitSlow n i * egbFixedChargeACriticalUnitFast n i) := by ring
  rw [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalMixedProfile_centered]
  simp only [egbFixedChargeACriticalMixedProfile, hp, Finset.sum_add_distrib, ← Finset.mul_sum,
    hs, hf, egbFixedChargeACriticalUnitModes_orthogonal, mul_zero, mul_one, add_zero]

/-- The normalized mode plane is invariant and its two coordinates decay independently. -/
theorem egbFixedChargeACriticalMixedProfile_evolution (n m : ℕ) (a b : ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalMixedProfile n a b) =
      egbFixedChargeACriticalMixedProfile n (a * (2 / 3 : ℝ) ^ m) (b * (1 / 6 : ℝ) ^ m) := by
  have hs := egbFixedChargeACriticalMarkov_affine_action n m (egbFixedChargeACriticalUnitSlow n) 0 a
  have hf := egbFixedChargeACriticalMarkov_affine_action n m (egbFixedChargeACriticalUnitFast n) 0 b
  simp only [zero_add, egbFixedChargeACriticalUnitSlow_evolution] at hs
  simp only [zero_add, egbFixedChargeACriticalUnitFast_evolution] at hf
  unfold egbFixedChargeACriticalMixedProfile
  rw [FinitePositiveKernel.applyReal_add, hs, hf]
  funext i
  change a * ((2 / 3 : ℝ) ^ m * egbFixedChargeACriticalUnitSlow n i) +
    b * ((1 / 6 : ℝ) ^ m * egbFixedChargeACriticalUnitFast n i) = _
  ring

/-- Arbitrary normalized mixtures have an exact two-rate energy law at every time. -/
theorem egbFixedChargeACriticalMixedProfile_evolved_energy (n m : ℕ) (a b : ℝ) :
    egbFixedChargeACriticalCenteredEnergy n
      ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
        (egbFixedChargeACriticalMixedProfile n a b)) =
      (4 / 9 : ℝ) ^ m * a ^ (2 : ℕ) + (1 / 36 : ℝ) ^ m * b ^ (2 : ℕ) := by
  rw [egbFixedChargeACriticalMixedProfile_evolution, egbFixedChargeACriticalMixedProfile_energy]
  have hs : ((2 / 3 : ℝ) ^ m) ^ (2 : ℕ) = (4 / 9 : ℝ) ^ m := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hf : ((1 / 6 : ℝ) ^ m) ^ (2 : ℕ) = (1 / 36 : ℝ) ^ m := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [mul_pow, mul_pow, hs, hf]
  ring

/-- Vanishing mixed-profile energy identifies precisely the origin of the two-mode plane. -/
theorem egbFixedChargeACriticalMixedProfile_energy_zero_iff (n : ℕ) (a b : ℝ) :
    egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalMixedProfile n a b) = 0 ↔ a = 0 ∧ b = 0 := by
  rw [egbFixedChargeACriticalMixedProfile_energy]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · rintro ⟨rfl, rfl⟩
    norm_num

end
end GaloisForLFunctions.HTGeometry
