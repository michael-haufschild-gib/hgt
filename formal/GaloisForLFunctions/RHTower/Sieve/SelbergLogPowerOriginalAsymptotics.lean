import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedMinLogForms
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerCorrectionAsymptotics

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Euler-correction convolution for every ordinary logarithmic monomial. -/
theorem selbergOriginalLogMonomial_eq_correction_scaled
    (i j N : ℕ) :
    selbergOriginalLogMonomial i j N =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          selbergPrincipalScaledLogPowerModel i j a b N := by
  rw [selbergOriginalLogMonomial, Finset.sum_product]
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      selbergOriginalCoeff m n *
        (Real.log ((N : ℝ) / (m : ℝ)) ^ i *
          Real.log ((N : ℝ) / (n : ℝ)) ^ j)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergPrincipalCoeff m n *
            (Real.log ((N : ℝ) / (m : ℝ)) ^ i *
              Real.log ((N : ℝ) / (n : ℝ)) ^ j) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [selbergEulerCorrection_convolution_principal]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
            selbergPrincipalCoeff r s *
              (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) ^ i *
                Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ j)) :=
      sum_Icc_bivariateDirichletConvolution_mul _ _ _ N N
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [selbergPrincipalCoeff_weighted_logPower_eq_scaledModel i j a b N
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1]

/-- Normalized original ordinary forms are exactly the correction `tsum`. -/
theorem selbergOriginalLogMonomial_succ_succ_div_log_pow_eq_tsum
    (q r : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    selbergOriginalLogMonomial (q + 1) (r + 1) N /
        Real.log N ^ (q + r + 1) =
      ∑' mn : ℕ × ℕ, selbergCorrectionScaledLogPowerTerm q r N mn := by
  rw [tsum_selbergCorrectionScaledLogPowerTerm,
    selbergOriginalLogMonomial_eq_correction_scaled]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  have hlog : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]

/-- The original `(log, log⁴)` Selberg form has leading coefficient one. -/
theorem tendsto_selbergOriginalLogMonomial_one_four_div_log_fourth_one :
    Tendsto (fun N : ℕ =>
      selbergOriginalLogMonomial 1 4 N / Real.log N ^ (4 : ℕ))
      atTop (𝓝 1) := by
  refine tendsto_tsum_selbergCorrectionScaledLogPowerTerm_zero_three_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  simpa using (selbergOriginalLogMonomial_succ_succ_div_log_pow_eq_tsum
    0 3 hN).symm

/-- The original `(log², log³)` Selberg form has leading coefficient `3/2`. -/
theorem tendsto_selbergOriginalLogMonomial_two_three_div_log_fourth_three_halves :
    Tendsto (fun N : ℕ =>
      selbergOriginalLogMonomial 2 3 N / Real.log N ^ (4 : ℕ))
      atTop (𝓝 (3 / 2 : ℝ)) := by
  refine
    tendsto_tsum_selbergCorrectionScaledLogPowerTerm_one_two_three_halves.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  simpa using (selbergOriginalLogMonomial_succ_succ_div_log_pow_eq_tsum
    1 2 hN).symm

end

end RHTower.Sieve
