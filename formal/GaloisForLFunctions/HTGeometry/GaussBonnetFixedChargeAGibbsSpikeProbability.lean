import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsPerturbationRealization

/-!
# A positive Gibbs law exciting every nonzero Fourier mode

Half the probability is uniform and half is concentrated at the first state.
The positive uniform component makes its logarithmic energy finite everywhere.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A strictly positive half-uniform, half-point-mass probability law. -/
def egbFixedChargeAGibbsSpikeProbability (n : ℕ) (i : Fin (2 ^ (n + 3))) : ℝ :=
  ((2 : ℝ) ^ (n + 3))⁻¹ / 2 + if i = 0 then 1 / 2 else 0

/-- Every state has positive probability, including all states outside the distinguished point. -/
theorem egbFixedChargeAGibbsSpikeProbability_pos (n : ℕ) (i : Fin (2 ^ (n + 3))) :
    0 < egbFixedChargeAGibbsSpikeProbability n i := by
  unfold egbFixedChargeAGibbsSpikeProbability
  split_ifs <;> positivity

/-- The spike construction is exactly normalized on every symbolic dyadic grid. -/
theorem egbFixedChargeAGibbsSpikeProbability_mass (n : ℕ) :
    ∑ i, egbFixedChargeAGibbsSpikeProbability n i = 1 := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold egbFixedChargeAGibbsSpikeProbability
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  simp
  <;> field_simp [hn]
  <;> ring

/-- A finite real energy landscape realizing the spike law at unit inverse temperature. -/
def egbFixedChargeAGibbsSpikeEnergy (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => -Real.log (egbFixedChargeAGibbsSpikeProbability n i)

/-- The logarithmic spike energy has partition function exactly one. -/
theorem egbFixedChargeAGibbsSpike_partition (n : ℕ) :
    _root_.HTGeometry.finiteGibbsPartition 1 (egbFixedChargeAGibbsSpikeEnergy n) = 1 := by
  unfold _root_.HTGeometry.finiteGibbsPartition egbFixedChargeAGibbsSpikeEnergy
  simp only [neg_mul, one_mul, neg_neg]
  simp_rw [Real.exp_log (egbFixedChargeAGibbsSpikeProbability_pos n _)]
  exact egbFixedChargeAGibbsSpikeProbability_mass n

/-- The corpus Gibbs construction recovers the spike law exactly. -/
theorem egbFixedChargeAGibbsSpike_realization (n : ℕ) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      egbFixedChargeAGibbsSpikeProbability n := by
  funext i
  rw [_root_.HTGeometry.finiteGibbsStateWeight, egbFixedChargeAGibbsSpike_partition, div_one]
  simp only [egbFixedChargeAGibbsSpikeEnergy, neg_mul, one_mul, neg_neg]
  exact Real.exp_log (egbFixedChargeAGibbsSpikeProbability_pos n i)

/-- The initial population of the new energy landscape is the exact positive spike law. -/
theorem egbFixedChargeAGibbsSpike_initial (n : ℕ) :
    egbFixedChargeAGibbsMarkovPopulation n 0 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      egbFixedChargeAGibbsSpikeProbability n := by
  rw [egbFixedChargeAGibbsMarkovPopulation_zero, egbFixedChargeAGibbsSpike_realization]

end
end GaloisForLFunctions.HTGeometry
