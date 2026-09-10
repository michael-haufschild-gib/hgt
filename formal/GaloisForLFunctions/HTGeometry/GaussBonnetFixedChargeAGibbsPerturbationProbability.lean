import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpectralInformation

/-!
A symbolic positive Gibbs realization of every centered real input on the critical
grid. This turns the spectral consequences of arXiv:2609.00025 into actual Gibbs
probabilities without imposing positivity or normalization premises.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An explicit amplitude keeping every centered perturbation strictly positive. -/
def egbFixedChargeAGibbsPerturbationScale (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  (2 * (1 + ∑ i, |egbFixedChargeACriticalCenteredProfile n f i|))⁻¹

/-- The perturbation amplitude is always strictly positive. -/
theorem egbFixedChargeAGibbsPerturbationScale_pos (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) : 0 < egbFixedChargeAGibbsPerturbationScale n f := by
  unfold egbFixedChargeAGibbsPerturbationScale
  have hs : 0 ≤ ∑ i, |egbFixedChargeACriticalCenteredProfile n f i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  positivity

/-- Every scaled coordinate has absolute value strictly below one half. -/
theorem egbFixedChargeAGibbsPerturbationScale_coordinate_bound (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    |egbFixedChargeAGibbsPerturbationScale n f * egbFixedChargeACriticalCenteredProfile n f i| < 1 / 2 := by
  have hc := egbFixedChargeAGibbsPerturbationScale_pos n f
  have hs : 0 ≤ ∑ j, |egbFixedChargeACriticalCenteredProfile n f j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hi := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
      abs_nonneg (egbFixedChargeACriticalCenteredProfile n f j)) (Finset.mem_univ i)
  have he : egbFixedChargeAGibbsPerturbationScale n f *
      (2 * (1 + ∑ j, |egbFixedChargeACriticalCenteredProfile n f j|)) = 1 := by
    unfold egbFixedChargeAGibbsPerturbationScale
    field_simp
  rw [abs_mul, abs_of_pos hc]
  nlinarith [mul_le_mul_of_nonneg_left hi hc.le]

/-- A normalized full-support probability law encoding the centered input profile. -/
def egbFixedChargeAGibbsPerturbationProbability (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (1 + egbFixedChargeAGibbsPerturbationScale n f *
    egbFixedChargeACriticalCenteredProfile n f i) / (2 : ℝ) ^ (n + 3)

/-- Every probability is between one half and three halves of the uniform mass. -/
theorem egbFixedChargeAGibbsPerturbationProbability_envelope (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    (1 / 2 : ℝ) / (2 : ℝ) ^ (n + 3) < egbFixedChargeAGibbsPerturbationProbability n f i ∧
      egbFixedChargeAGibbsPerturbationProbability n f i < (3 / 2 : ℝ) / (2 : ℝ) ^ (n + 3) := by
  have h := egbFixedChargeAGibbsPerturbationScale_coordinate_bound n f i
  have hl := neg_abs_le (egbFixedChargeAGibbsPerturbationScale n f *
    egbFixedChargeACriticalCenteredProfile n f i)
  have hu := le_abs_self (egbFixedChargeAGibbsPerturbationScale n f *
    egbFixedChargeACriticalCenteredProfile n f i)
  have hn : 0 < (2 : ℝ) ^ (n + 3) := pow_pos (by norm_num) _
  unfold egbFixedChargeAGibbsPerturbationProbability
  constructor <;> apply div_lt_div_of_pos_right _ hn <;> linarith

/-- Positivity is guaranteed by the construction for every real input. -/
theorem egbFixedChargeAGibbsPerturbationProbability_pos (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    0 < egbFixedChargeAGibbsPerturbationProbability n f i :=
  lt_trans (by positivity) (egbFixedChargeAGibbsPerturbationProbability_envelope n f i).1

/-- The encoded probability has total mass one for every real input. -/
theorem egbFixedChargeAGibbsPerturbationProbability_mass (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) : ∑ i, egbFixedChargeAGibbsPerturbationProbability n f i = 1 := by
  unfold egbFixedChargeAGibbsPerturbationProbability
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    egbFixedChargeACriticalCenteredProfile_mass_zero]
  simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (pow_ne_zero _ (by norm_num))

end
end GaloisForLFunctions.HTGeometry
