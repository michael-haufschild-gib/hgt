import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHellingerMixing

/-!
Explicit, dimension-independent information-contraction bounds for finite Gibbs
populations under the critical Markov kernel derived from arXiv:2609.00025.
The refresh rate is a certified bound, not a claim of the optimal Hellinger coefficient.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two transitions contract Hellinger distance by at most sqrt(5/6). -/
theorem egbFixedChargeAGibbsHellinger_two_step_distance
    (n m : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n (m + 2) β E)
      (egbFixedChargeAGibbsMarkovPopulation n (m + 2) γ F) ≤
        Real.sqrt (5 / 6) * finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
          (egbFixedChargeAGibbsMarkovPopulation n m γ F) := by
  apply (sq_le_sq₀ (finitePacketHellinger_nonneg _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (finitePacketHellinger_nonneg _ _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6)]
  exact egbFixedChargeAGibbsHellinger_two_step_square n m β γ E F

/-- Every even number of transitions has a global geometric squared-distance bound. -/
theorem egbFixedChargeAGibbsHellinger_even_square_bound
    (n m : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n (2 * m) β E)
      (egbFixedChargeAGibbsMarkovPopulation n (2 * m) γ F) ^ (2 : ℕ) ≤
        (5 / 6 : ℝ) ^ m * finitePacketHellinger
          (_root_.HTGeometry.finiteGibbsStateWeight β E)
          (_root_.HTGeometry.finiteGibbsStateWeight γ F) ^ (2 : ℕ) := by
  induction m with
  | zero =>
    simp only [mul_zero, egbFixedChargeAGibbsMarkovPopulation_zero, pow_zero, one_mul, le_refl]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    calc
      _ ≤ (5 / 6 : ℝ) * finitePacketHellinger
        (egbFixedChargeAGibbsMarkovPopulation n (2 * m) β E)
        (egbFixedChargeAGibbsMarkovPopulation n (2 * m) γ F) ^ (2 : ℕ) :=
          egbFixedChargeAGibbsHellinger_two_step_square n (2 * m) β γ E F
      _ ≤ (5 / 6 : ℝ) * ((5 / 6 : ℝ) ^ m * finitePacketHellinger
        (_root_.HTGeometry.finiteGibbsStateWeight β E)
        (_root_.HTGeometry.finiteGibbsStateWeight γ F) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ (5 / 6 : ℝ) m]; ring

/-- The extra transition in every odd step count cannot worsen the even-step bound. -/
theorem egbFixedChargeAGibbsHellinger_odd_square_bound
    (n m : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n (2 * m + 1) β E)
      (egbFixedChargeAGibbsMarkovPopulation n (2 * m + 1) γ F) ^ (2 : ℕ) ≤
        (5 / 6 : ℝ) ^ m * finitePacketHellinger
          (_root_.HTGeometry.finiteGibbsStateWeight β E)
          (_root_.HTGeometry.finiteGibbsStateWeight γ F) ^ (2 : ℕ) := by
  have h := egbFixedChargeAGibbsHellinger_antitone n β γ E F (show 2 * m ≤ 2 * m + 1 by omega)
  have hs := (sq_le_sq₀ (finitePacketHellinger_nonneg _ _) (finitePacketHellinger_nonneg _ _)).mpr h
  exact hs.trans (egbFixedChargeAGibbsHellinger_even_square_bound n m β γ E F)

/-- A direct Hellinger-distance bound at every even step count. -/
theorem egbFixedChargeAGibbsHellinger_even_distance_bound
    (n m : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n (2 * m) β E)
      (egbFixedChargeAGibbsMarkovPopulation n (2 * m) γ F) ≤
        Real.sqrt ((5 / 6 : ℝ) ^ m) * finitePacketHellinger
          (_root_.HTGeometry.finiteGibbsStateWeight β E)
          (_root_.HTGeometry.finiteGibbsStateWeight γ F) := by
  apply (sq_le_sq₀ (finitePacketHellinger_nonneg _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (finitePacketHellinger_nonneg _ _))).mp
  rw [mul_pow, Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 6) m)]
  exact egbFixedChargeAGibbsHellinger_even_square_bound n m β γ E F

end

end GaloisForLFunctions.HTGeometry
