import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTunedMinLogAsymptotic

/-!
# A uniform bound for every real linear Selberg cutoff

The linear Selberg asymptotic controls large logarithmic cutoffs.
The elementary finite-sum envelope controls the remaining compact interval.
The resulting constant is independent of the cutoff, as needed when
integrating linear cutoffs to represent smooth mollifier profiles.
-/

open Filter Set Topology
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The real-cutoff linear Selberg energy is uniformly at most linear in its logarithmic length. -/
theorem exists_linear_selberg_energy_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u →
      |selbergOriginalLogMonomialReal 1 1 (Real.exp u)| ≤ C * (1 + u) := by
  have hlim : Tendsto (fun u : ℝ =>
      selbergOriginalLogMonomialReal 1 1 (Real.exp u) / u) atTop (𝓝 1) := by
    simpa using tendsto_selbergOriginalLogMonomialReal_exp_div_pow
      (by norm_num : 0 < (1 : ℕ)) (by norm_num : 0 < (1 : ℕ))
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.mp hlim) 1 zero_lt_one
  let B : ℝ := max A 1
  let C : ℝ := 2 + (1 + B) ^ 5
  have hB1 : 1 ≤ B := le_max_right _ _
  have hC2 : 2 ≤ C := by
    have hp : 0 ≤ (1 + B) ^ 5 := pow_nonneg (by linarith only [hB1]) _
    dsimp only [C]
    linarith only [hp]
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  refine ⟨C, hC, fun u hu => ?_⟩
  by_cases huB : B ≤ u
  · have hu0 : 0 < u := zero_lt_one.trans_le (hB1.trans huB)
    have hh := hA u ((le_max_left A 1).trans huB)
    rw [Real.dist_eq] at hh
    have hratio : |selbergOriginalLogMonomialReal 1 1 (Real.exp u) / u| ≤ 2 := by
      have ht := abs_add_le (selbergOriginalLogMonomialReal 1 1 (Real.exp u) / u - 1) (1 : ℝ)
      rw [sub_add_cancel, abs_one] at ht
      linarith only [hh, ht]
    rw [abs_div, abs_of_pos hu0] at hratio
    calc
      _ ≤ 2 * u := (div_le_iff₀ hu0).mp hratio
      _ ≤ C * u := mul_le_mul_of_nonneg_right hC2 hu
      _ ≤ C * (1 + u) := mul_le_mul_of_nonneg_left (by linarith) hC.le
  · have hlocal := abs_selbergOriginalLogMonomialReal_exp_le 1 1 hu
    calc
      _ ≤ (1 + u) ^ 5 := by simpa only [Nat.reduceAdd] using hlocal
      _ ≤ (1 + B) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith only [le_of_not_ge huB]) 5
      _ ≤ C := by dsimp only [C]; linarith
      _ ≤ C * (1 + u) := le_mul_of_one_le_right hC.le (by linarith only [hu])

end GaloisForLFunctions.MultiscaleMollifiedZetaField
