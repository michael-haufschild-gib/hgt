import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsMarkovPopulationActions
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAHellingerCommonRefresh

/-!
Information loss for existing finite Gibbs probabilities under the critical Gibbs
Markov kernel derived from arXiv:2609.00025. All input probabilities are constructed
from arbitrary real inverse temperatures and energy arrays, with no probability premises.
-/
namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- Any number of critical-kernel transitions can only reduce Gibbs-state distinguishability. -/
theorem egbFixedChargeAGibbsHellinger_nonincrease
    (n m : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (egbFixedChargeAGibbsMarkovPopulation n m γ F) ≤
        finitePacketHellinger (_root_.HTGeometry.finiteGibbsStateWeight β E)
          (_root_.HTGeometry.finiteGibbsStateWeight γ F) := by
  exact finitePacketHellinger_markovDataProcessing
    (egbFixedChargeACriticalMarkovIteratedKernel n m)
    (fun i => (_root_.HTGeometry.finiteGibbsStateWeight_pos β E i).le)
    (fun i => (_root_.HTGeometry.finiteGibbsStateWeight_pos γ F i).le)
    (_root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one β E)
    (_root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one γ F)

/-- Distinguishability decreases monotonically at every individual transition. -/
theorem egbFixedChargeAGibbsHellinger_antitone
    (n : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    Antitone (fun m : ℕ => finitePacketHellinger
      (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (egbFixedChargeAGibbsMarkovPopulation n m γ F)) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [egbFixedChargeAGibbsMarkovPopulation_step, egbFixedChargeAGibbsMarkovPopulation_step]
  exact finitePacketHellinger_markovDataProcessing (egbFixedChargeACriticalMarkovKernel n)
    (egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E)
    (egbFixedChargeAGibbsMarkovPopulation_nonneg n m γ F)
    (egbFixedChargeAGibbsMarkovPopulation_mass n m β E)
    (egbFixedChargeAGibbsMarkovPopulation_mass n m γ F)

/-- Every pair of finite Gibbs inputs eventually becomes indistinguishable in Hellinger distance. -/
theorem egbFixedChargeAGibbsHellinger_zero_limit
    (n : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => finitePacketHellinger
      (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (egbFixedChargeAGibbsMarkovPopulation n m γ F)) atTop (𝓝 0) := by
  have hp := (egbFixedChargeAGibbsMarkovPopulation_limit n β E).prodMk_nhds
    (egbFixedChargeAGibbsMarkovPopulation_limit n γ F)
  have h := (egbFixedChargeAHellinger_continuous (2 ^ (n + 3))).continuousAt.tendsto.comp hp
  have hz : finitePacketHellinger
      (fun _ : Fin (2 ^ (n + 3)) => ((2 : ℝ) ^ (n + 3))⁻¹)
      (fun _ : Fin (2 ^ (n + 3)) => ((2 : ℝ) ^ (n + 3))⁻¹) = 0 := by
    simp [finitePacketHellinger]
  rw [hz] at h
  simpa only [Function.comp_def] using h

/-- The exact uniform refresh contracts squared Hellinger distance by5/6 every two steps. -/
theorem egbFixedChargeAGibbsHellinger_two_step_square
    (n m : ℕ) (β γ : ℝ) (E F : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n (m + 2) β E)
      (egbFixedChargeAGibbsMarkovPopulation n (m + 2) γ F) ^ (2 : ℕ) ≤
        (5 / 6 : ℝ) * finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
          (egbFixedChargeAGibbsMarkovPopulation n m γ F) ^ (2 : ℕ) := by
  let R := (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel
  let u := egbFixedChargeAGibbsMarkovPopulation n m β E
  let v := egbFixedChargeAGibbsMarkovPopulation n m γ F
  have hu : ∀ i, 0 ≤ u i := egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E
  have hv : ∀ i, 0 ≤ v i := egbFixedChargeAGibbsMarkovPopulation_nonneg n m γ F
  have hRu (i : Fin (2 ^ (n + 3))) : Real.sqrt (R.applyReal u i) ^ (2 : ℕ) = R.applyReal u i :=
    Real.sq_sqrt (R.applyReal_nonneg hu i)
  have hRv (i : Fin (2 ^ (n + 3))) : Real.sqrt (R.applyReal v i) ^ (2 : ℕ) = R.applyReal v i :=
    Real.sq_sqrt (R.applyReal_nonneg hv i)
  have h := egbFixedChargeAHellinger_common_refresh (2 ^ (n + 3)) (Real.sqrt (5 / 6))
    (fun _ => Real.sqrt (1 / (6 * (2 : ℝ) ^ (n + 3))))
    (fun i => Real.sqrt (R.applyReal u i)) (fun i => Real.sqrt (R.applyReal v i))
  simp only [hRu, hRv, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (6 * (2 : ℝ) ^ (n + 3)))] at h
  have hd := finitePacketHellinger_markovDataProcessing (egbFixedChargeACriticalMarkovRefreshKernel n)
    hu hv (egbFixedChargeAGibbsMarkovPopulation_mass n m β E)
      (egbFixedChargeAGibbsMarkovPopulation_mass n m γ F)
  have hs : finitePacketHellinger (R.applyReal u) (R.applyReal v) ^ (2 : ℕ) ≤
      finitePacketHellinger u v ^ (2 : ℕ) :=
    (sq_le_sq₀ (finitePacketHellinger_nonneg _ _) (finitePacketHellinger_nonneg _ _)).mpr hd
  rw [egbFixedChargeAGibbsMarkovPopulation_refresh, egbFixedChargeAGibbsMarkovPopulation_refresh]
  exact h.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

end

end GaloisForLFunctions.HTGeometry
