import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.WeightedMoments
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.MomentInversion

/-! # Individual occupation probabilities from high moments -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

private theorem tail_ratio_limit (v : MissingWave) (N : ℕ) :
    Tendsto (fun m : ℕ => ∑' k, (occupationWeight (k+N)/occupationWeight N)^m*heatedMass v (k+N))
      atTop (𝓝 (heatedMass v N)) := by
  let g (k : ℕ) := if k = 0 then heatedMass v N else 0
  have hg : ∑' k, g k = heatedMass v N := by rw [tsum_eq_single 0 (fun k hk => if_neg hk)]; simp only [g,if_pos rfl]
  rw [← hg]
  apply tendsto_tsum_of_dominated_convergence ((summable_nat_add_iff N).mpr (heatedMass_sum v).summable)
  · intro k
    by_cases hk : k = 0
    · subst k
      simp only [Nat.zero_add,div_self (occupationWeight_pos N).ne',one_pow,one_mul,g,if_pos rfl]
      exact tendsto_const_nhds
    · have hlt : occupationWeight (k+N)/occupationWeight N < 1 := (div_lt_one (occupationWeight_pos N)).mpr
          (occupationWeight_strictAnti (show N < k+N by omega))
      simpa only [g,if_neg hk,zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (occupationWeight_pos _).le (occupationWeight_pos _).le) hlt).mul_const (heatedMass v (k+N))
  · apply Eventually.of_forall
    intro m k
    have hr : 0 ≤ occupationWeight (k+N)/occupationWeight N := (div_pos (occupationWeight_pos _) (occupationWeight_pos _)).le
    have hu : occupationWeight (k+N)/occupationWeight N ≤ 1 :=
      (div_le_one (occupationWeight_pos N)).mpr (occupationWeight_antitone (Nat.le_add_left _ _))
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr _) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hr hu)

/-- Subtract the already resolved labels and divide by the current heat level to isolate one Born mass. -/
theorem heatedMass_from_moments (v : MissingWave) (N : ℕ) :
    Tendsto (fun m : ℕ => ((nativeVectorMoment v m).re-
      ∑ k ∈ Finset.range N, occupationWeight k^m*heatedMass v k)/occupationWeight N^m)
      atTop (𝓝 (heatedMass v N)) := by
  apply (tail_ratio_limit v N).congr
  intro m
  have ht := ((hasSum_nat_add_iff' N).mpr (heatedMoment_summable v m).hasSum).tsum_eq
  rw [nativeVectorMoment_eq_sum,Complex.ofReal_re,← ht]
  rw [← tsum_div_const]
  apply tsum_congr
  intro k
  rw [div_pow]
  ring

/-- Isospectral exterior omissions give the same normalized probability at each individual occupation. -/
theorem occupationProbability_eq_of_spectrum {v w : MissingWave} (he : missingSpectrum v = missingSpectrum w) :
    occupationProbability v = occupationProbability w := by
  have hm := nativeVectorMoments_of_spectrum he
  have hw (N : ℕ) : heatedMass v N = heatedMass w N := by
    induction N using Nat.strong_induction_on with
    | h N ih =>
      have ht := heatedMass_from_moments w N
      apply tendsto_nhds_unique (heatedMass_from_moments v N)
      apply ht.congr
      intro m
      have hf : ∑ k ∈ Finset.range N, occupationWeight k^m*heatedMass v k =
          ∑ k ∈ Finset.range N, occupationWeight k^m*heatedMass w k :=
        Finset.sum_congr rfl (fun k hk => by rw [ih k (Finset.mem_range.mp hk)])
      rw [hm m,hf]
  funext n
  obtain ⟨k,rfl⟩ := number_surjective n
  exact mul_left_cancel₀ (occupationWeight_pos k).ne' (by simpa only [heatedMass_eq] using hw k)

#print axioms heatedMass_from_moments
#print axioms occupationProbability_eq_of_spectrum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
