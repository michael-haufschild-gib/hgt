import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogCorrectionAsymptotics

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Original Möbius/gcd `(log, log²)` bilinear form. -/
def selbergOriginalLogOneTwo (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    selbergOriginalCoeff m n *
      (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2)

theorem selbergOriginalLogOneTwo_eq_correction_scaled (N : ℕ) :
    selbergOriginalLogOneTwo N =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b * selbergPrincipalScaledMixedModel a b N := by
  rw [selbergOriginalLogOneTwo]
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      selbergOriginalCoeff m n *
        (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergPrincipalCoeff m n *
            (Real.log ((N : ℝ) / (m : ℝ)) *
              Real.log ((N : ℝ) / (n : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [selbergEulerCorrection_convolution_principal]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
            selbergPrincipalCoeff r s *
              (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) *
                Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ 2)) :=
      sum_Icc_bivariateDirichletConvolution_mul _ _ _ N N
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [selbergPrincipalCoeff_weighted_one_two_eq_scaledMixedModel a b N
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1]

theorem selbergOriginalLogOneTwo_div_log_sq_eq_tsum
    {N : ℕ} (hN : 2 ≤ N) :
    selbergOriginalLogOneTwo N / Real.log N ^ 2 =
      ∑' mn : ℕ × ℕ, selbergCorrectionScaledMixedTerm N mn := by
  rw [tsum_selbergCorrectionScaledMixedTerm,
    selbergOriginalLogOneTwo_eq_correction_scaled]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]

theorem tendsto_selbergOriginalLogOneTwo_div_log_sq_one :
    Tendsto (fun N : ℕ => selbergOriginalLogOneTwo N / Real.log N ^ 2)
      atTop (𝓝 1) := by
  refine tendsto_tsum_selbergCorrectionScaledMixedTerm_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (selbergOriginalLogOneTwo_div_log_sq_eq_tsum hN).symm

/-- Original Möbius/gcd `(log², log²)` bilinear form. -/
def selbergOriginalLogTwoTwo (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    selbergOriginalCoeff m n *
      (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 * Real.log ((N : ℝ) / (n : ℝ)) ^ 2)

theorem selbergOriginalLogTwoTwo_eq_correction_scaled (N : ℕ) :
    selbergOriginalLogTwoTwo N =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          selbergPrincipalScaledQuadraticModel a b N := by
  rw [selbergOriginalLogTwoTwo]
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      selbergOriginalCoeff m n *
        (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
          Real.log ((N : ℝ) / (n : ℝ)) ^ 2)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergPrincipalCoeff m n *
            (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
              Real.log ((N : ℝ) / (n : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [selbergEulerCorrection_convolution_principal]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
            selbergPrincipalCoeff r s *
              (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) ^ 2 *
                Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ 2)) :=
      sum_Icc_bivariateDirichletConvolution_mul _ _ _ N N
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [selbergPrincipalCoeff_weighted_two_two_eq_scaledQuadraticModel a b N
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1]

theorem selbergOriginalLogTwoTwo_div_log_cube_eq_tsum
    {N : ℕ} (hN : 2 ≤ N) :
    selbergOriginalLogTwoTwo N / Real.log N ^ 3 =
      ∑' mn : ℕ × ℕ, selbergCorrectionScaledQuadraticTerm N mn := by
  rw [tsum_selbergCorrectionScaledQuadraticTerm,
    selbergOriginalLogTwoTwo_eq_correction_scaled]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]

theorem tendsto_selbergOriginalLogTwoTwo_div_log_cube_four_thirds :
    Tendsto (fun N : ℕ => selbergOriginalLogTwoTwo N / Real.log N ^ 3)
      atTop (𝓝 (4 / 3 : ℝ)) := by
  refine tendsto_tsum_selbergCorrectionScaledQuadraticTerm_four_thirds.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (selbergOriginalLogTwoTwo_div_log_cube_eq_tsum hN).symm

end

end RHTower.Sieve
