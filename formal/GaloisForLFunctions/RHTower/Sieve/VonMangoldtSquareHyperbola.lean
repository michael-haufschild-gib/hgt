import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareConvolution
import GaloisForLFunctions.RHTower.SelbergWeightEvaluation

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

/-- Harmonic hyperbola mass of the pointwise von Mangoldt square. -/
def vonMangoldtSquareHyperbolaMass (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (Λ d) ^ 2 / (d : ℝ) *
    ∑ m ∈ Finset.Icc 1 (N / d), (Λ m) ^ 2 / (m : ℝ)

/-- Harmonic partial sum of the Dirichlet self-convolution of the pointwise square. -/
def vonMangoldtSquareConvHarmonicSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    (vonMangoldtSquare * vonMangoldtSquare) k / (k : ℝ)

theorem vonMangoldtSquareHyperbolaMass_eq_convHarmonicSum (N : ℕ) :
    vonMangoldtSquareHyperbolaMass N = vonMangoldtSquareConvHarmonicSum N := by
  let g : ℕ → ℝ := fun d => (Λ d) ^ 2 / (d : ℝ)
  have hregroup := RHTower.hyperbola_bilinear_regroup g g (fun _ => 1) N
  have hleft :
      ∑ d ∈ Finset.Icc 1 N, g d *
          ∑ m ∈ Finset.Icc 1 (N / d), g m * (1 : ℝ) =
        vonMangoldtSquareHyperbolaMass N := by
    rw [vonMangoldtSquareHyperbolaMass]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [g]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hright :
      ∑ k ∈ Finset.Icc 1 N,
          (∑ p ∈ k.divisorsAntidiagonal, g p.1 * g p.2) * (1 : ℝ) =
        vonMangoldtSquareConvHarmonicSum N := by
    rw [vonMangoldtSquareConvHarmonicSum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    rw [mul_one, ArithmeticFunction.mul_apply]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hprod : p.1 * p.2 = k := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hp1 : (0 : ℝ) < p.1 := by
      have hp10 : p.1 ≠ 0 := by
        intro hzero
        rw [hzero, zero_mul] at hprod
        omega
      exact_mod_cast Nat.pos_of_ne_zero hp10
    have hp2 : (0 : ℝ) < p.2 := by
      have hp20 : p.2 ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at hprod
        omega
      exact_mod_cast Nat.pos_of_ne_zero hp20
    dsimp only [g]
    simp only [vonMangoldtSquare_apply]
    rw [← hprod]
    push_cast
    field_simp
  rw [← hleft, ← hright]
  exact hregroup

/-- Prime-power correction between the squared self-convolution and its square-weight hyperbola
main term. -/
def vonMangoldtSelfConvSquareCorrection (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N,
    (((Λ * Λ) k) ^ 2 -
      2 * (vonMangoldtSquare * vonMangoldtSquare) k) / (k : ℝ)

theorem vonMangoldtSelfConvHarmonicSquareSum_eq_hyperbola_add_correction
    (N : ℕ) :
    vonMangoldtSelfConvHarmonicSquareSum N =
      2 * vonMangoldtSquareHyperbolaMass N +
        vonMangoldtSelfConvSquareCorrection N := by
  by_cases hN0 : N = 0
  · subst N
    norm_num [vonMangoldtSelfConvHarmonicSquareSum, vonMangoldtSquareHyperbolaMass,
      vonMangoldtSelfConvSquareCorrection]
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  rw [vonMangoldtSelfConvHarmonicSquareSum, vonMangoldtSelfConvSquareCorrection,
    vonMangoldtSquareHyperbolaMass_eq_convHarmonicSum,
    vonMangoldtSquareConvHarmonicSum]
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  have hone : (vonMangoldtSquare * vonMangoldtSquare) 1 = 0 := by
    norm_num [vonMangoldtSquare, ArithmeticFunction.mul_apply]
  rw [hone]
  simp only [Nat.cast_one, zero_div, zero_add]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two (Finset.mem_Icc.mp hk).1)
  field_simp
  ring

def primePowerLogFourthHarmonicSum (N : ℕ) : ℝ :=
  ∑ k ∈ {k ∈ Finset.Icc 2 N | IsPrimePow k}, Real.log k ^ 4 / (k : ℝ)

theorem abs_vonMangoldtSelfConvSquareCorrection_le (N : ℕ) :
    |vonMangoldtSelfConvSquareCorrection N| ≤
      primePowerLogFourthHarmonicSum N := by
  rw [vonMangoldtSelfConvSquareCorrection]
  calc
    |∑ k ∈ Finset.Icc 2 N,
        (((Λ * Λ) k) ^ 2 -
          2 * (vonMangoldtSquare * vonMangoldtSquare) k) / (k : ℝ)| ≤
        ∑ k ∈ Finset.Icc 2 N,
          |(((Λ * Λ) k) ^ 2 -
            2 * (vonMangoldtSquare * vonMangoldtSquare) k) / (k : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ {k ∈ Finset.Icc 2 N | IsPrimePow k},
          |(((Λ * Λ) k) ^ 2 -
            2 * (vonMangoldtSquare * vonMangoldtSquare) k) / (k : ℝ)| := by
      symm
      apply Finset.sum_subset (Finset.filter_subset IsPrimePow (Finset.Icc 2 N))
      intro k hk hknot
      have hkIcc := Finset.mem_Icc.mp hk
      have hpp : ¬ IsPrimePow k := by
        intro hprimepow
        exact hknot (Finset.mem_filter.mpr ⟨hk, hprimepow⟩)
      have heq := vonMangoldtSelfConv_sq_eq_two_mul_squareConv_of_not_isPrimePow
        k (by omega) hpp
      have hnum : ((Λ * Λ) k) ^ 2 -
          2 * (vonMangoldtSquare * vonMangoldtSquare) k = 0 := sub_eq_zero.mpr heq
      rw [hnum, zero_div, abs_zero]
    _ ≤ primePowerLogFourthHarmonicSum N := by
      rw [primePowerLogFourthHarmonicSum]
      apply Finset.sum_le_sum
      intro k hk
      have hpp : IsPrimePow k := (Finset.mem_filter.mp hk).2
      have hkpos : (0 : ℝ) < k := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1)
      rw [abs_div, abs_of_pos hkpos]
      exact div_le_div_of_nonneg_right
        (abs_vonMangoldtSelfConv_sq_sub_two_mul_squareConv_le_of_isPrimePow hpp) hkpos.le

end RHTower.Sieve
