import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalRefreshBistochastic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squared deviation of a Gibbs population from the uniform stationary law. -/
def egbFixedChargeAGibbsCollisionExcess (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ∑ i, (egbFixedChargeAGibbsMarkovPopulation n m β E i - ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ)

/-- Squared deviation is precisely collision probability above its uniform floor. -/
theorem egbFixedChargeAGibbsCollisionExcess_identity (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E =
      (∑ i, egbFixedChargeAGibbsMarkovPopulation n m β E i ^ (2 : ℕ)) -
        ((2 : ℝ) ^ (n + 3))⁻¹ := by
  have hpoint (x : ℝ) : (x - ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ) =
      x ^ (2 : ℕ) - (2 * ((2 : ℝ) ^ (n + 3))⁻¹) * x + (((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ) := by ring
  simp only [egbFixedChargeAGibbsCollisionExcess, hpoint, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, egbFixedChargeAGibbsMarkovPopulation_mass,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  <;> ring

/-- Collision excess is always nonnegative. -/
theorem egbFixedChargeAGibbsCollisionExcess_nonneg (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsCollisionExcess n m β E :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Zero excess exactly classifies the equilibrium population. -/
theorem egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E = 0 ↔
      ∀ i, egbFixedChargeAGibbsMarkovPopulation n m β E i = ((2 : ℝ) ^ (n + 3))⁻¹ := by
  constructor
  · intro h i
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
        sq_nonneg (egbFixedChargeAGibbsMarkovPopulation n m β E j - ((2 : ℝ) ^ (n + 3))⁻¹))
      (Finset.mem_univ i)
    change (_ - _) ^ (2 : ℕ) ≤ egbFixedChargeAGibbsCollisionExcess n m β E at hi
    rw [h] at hi
    nlinarith [sq_nonneg (egbFixedChargeAGibbsMarkovPopulation n m β E i -
      ((2 : ℝ) ^ (n + 3))⁻¹)]
  · intro h
    simp [egbFixedChargeAGibbsCollisionExcess, h]

/-- Every block of transitions decreases collision excess. -/
theorem egbFixedChargeAGibbsCollisionExcess_block_le (n a b : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (a + b) β E ≤
      egbFixedChargeAGibbsCollisionExcess n b β E := by
  simp only [egbFixedChargeAGibbsCollisionExcess_identity]
  rw [egbFixedChargeAGibbsMarkovPopulation_add]
  exact sub_le_sub_right
    (egbFixedChargeACriticalMarkov_sum_sq_le n a (egbFixedChargeAGibbsMarkovPopulation n b β E)) _

/-- Collision excess is a Lyapunov function for all Gibbs energy landscapes. -/
theorem egbFixedChargeAGibbsCollisionExcess_antitone (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Antitone (fun m => egbFixedChargeAGibbsCollisionExcess n m β E) := by
  have h : Monotone (fun m => -egbFixedChargeAGibbsCollisionExcess n m β E) := by
    apply monotone_nat_of_le_succ
    intro m
    have hm := egbFixedChargeAGibbsCollisionExcess_block_le n 1 m β E
    rw [Nat.add_comm 1 m] at hm
    linarith
  intro a b hab
  linarith [h hab]

end
end GaloisForLFunctions.HTGeometry
