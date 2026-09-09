import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalFourierMean

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squared norm after removing the invariant uniform mean. -/
def egbFixedChargeACriticalCenteredEnergy (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ∑ i, egbFixedChargeACriticalCenteredProfile n f i ^ 2

/-- Centered energy is nonnegative for every real profile. -/
theorem egbFixedChargeACriticalCenteredEnergy_nonneg (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeACriticalCenteredEnergy n f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Scaling the input scales its centered energy by the scalar square. -/
theorem egbFixedChargeACriticalCenteredEnergy_scale (n : ℕ) (c : ℝ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalCenteredEnergy n (fun i => c * f i) =
      c ^ 2 * egbFixedChargeACriticalCenteredEnergy n f := by
  simp only [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalCenteredProfile_scale,
    mul_pow, Finset.mul_sum]

/-- Total squared norm splits exactly into centered energy and the invariant constant component. -/
theorem egbFixedChargeACriticalCenteredEnergy_decomposition (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, f i ^ 2) = egbFixedChargeACriticalCenteredEnergy n f +
      (2 : ℝ) ^ (n + 3) * egbFixedChargeACriticalRealMean n f ^ 2 := by
  have hp (x : ℝ) : (x - egbFixedChargeACriticalRealMean n f) ^ 2 =
      x ^ 2 - (2 * egbFixedChargeACriticalRealMean n f) * x +
        egbFixedChargeACriticalRealMean n f ^ 2 := by ring
  simp only [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalCenteredProfile,
    hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  unfold egbFixedChargeACriticalRealMean
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  <;> ring

end
end GaloisForLFunctions.HTGeometry
