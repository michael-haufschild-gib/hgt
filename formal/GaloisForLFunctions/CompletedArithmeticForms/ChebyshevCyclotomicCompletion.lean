import GaloisForLFunctions.CompletedArithmeticForms.DivisorCovariance
import GaloisForLFunctions.RHTower.QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!
# Cyclotomic completion of the actual normalized Chebyshev energy

The discrete derivative of the literal normalized Chebyshev Cesàro source feeds
the completed arithmetic Gram. Accumulation changes its energy by a factor at
most four thirds. The explicit coefficient channels cost at most a linear term;
every superlinear exponent is therefore carried by the actual nonnegative
cyclotomic remainder, with the same zero-strip consequences.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open GaloisForLFunctions.RHTower _root_.RHTower
open _root_.RHTower.DeletionAveragedDivisor

/-- The literal arithmetic increment before covariance accumulation. -/
def chebyshevCesaroIncrement (j : ℕ) : ℝ :=
  chebyshevNormalizedCesaroSum j - chebyshevNormalizedCesaroSum (j - 1)

/-- The coefficient in the completed conductor Gram. -/
def chebyshevConductorCoeff (j : ℕ) : ℝ := chebyshevCesaroIncrement j / j

/-- Complete accumulated energy at its exact telescoping carrier. -/
def chebyshevCompletedEnergy (N : ℕ) : ℝ := cumulativeEnergy chebyshevCesaroIncrement N

/-- The actual cyclic remainder, normalized by its conductor. -/
def chebyshevCyclotomicRemainder (N : ℕ) : ℝ :=
  cyclotomicRemainder (N + 1) chebyshevConductorCoeff / ((N : ℝ) + 1)

theorem chebyshevCesaro_zero_of_le_two {j : ℕ} (hj : j ≤ 2) :
    chebyshevNormalizedCesaroSum j = 0 := by
  simp only [chebyshevNormalizedCesaroSum, Nat.sub_eq_zero_of_le hj, range_zero, sum_empty]

theorem chebyshevCesaroIncrement_zero_of_le_two {j : ℕ} (hj : j ≤ 2) :
    chebyshevCesaroIncrement j = 0 := by
  rw [chebyshevCesaroIncrement, chebyshevCesaro_zero_of_le_two hj,
    chebyshevCesaro_zero_of_le_two (by omega), sub_self]

/-- The increment is the normalized actual Chebyshev error at the preceding integer. -/
theorem chebyshevCesaroIncrement_eq {j : ℕ} (hj : 3 ≤ j) :
    chebyshevCesaroIncrement j =
      (Chebyshev.psi ((j - 1 : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ)) /
        Real.sqrt ((j - 1 : ℕ) : ℝ) := by
  unfold chebyshevCesaroIncrement chebyshevNormalizedCesaroSum
  rw [show j - 2 = (j - 3) + 1 by omega, Finset.sum_range_succ,
    show j - 1 - 2 = j - 3 by omega,
    show j - 3 + 2 = j - 1 by omega]
  ring

theorem chebyshevCesaroIncrement_prefix (N : ℕ) :
    ∑ j ∈ Icc 1 N, chebyshevCesaroIncrement j = chebyshevNormalizedCesaroSum N := by
  induction N with
  | zero => simp [chebyshevNormalizedCesaroSum]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, chebyshevCesaroIncrement, Nat.add_sub_cancel]
    ring

/-- The arithmetic completion retains the exact normalized Chebyshev prefix at every coordinate. -/
theorem chebyshevCompletedEnergy_eq_sum (N : ℕ) :
    chebyshevCompletedEnergy N =
      ∑ n ∈ Icc 1 N, chebyshevNormalizedCesaroSum n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  unfold chebyshevCompletedEnergy cumulativeEnergy
  simp_rw [chebyshevCesaroIncrement_prefix]

theorem chebyshevCompletedEnergy_eq_divisorGram (N : ℕ) :
    chebyshevCompletedEnergy N =
      divisorGramEnergy (N + 1) chebyshevConductorCoeff / ((N : ℝ) + 1) := by
  change cumulativeEnergy chebyshevCesaroIncrement N =
    divisorGramEnergy (N + 1) (fun j => chebyshevCesaroIncrement j / j) / ((N : ℝ) + 1)
  rw [divisorGramEnergy_eq_cumulativeEnergy,
    mul_div_cancel_left₀ _ (by positivity)]

/-- Both coefficient channels and the nonnegative cyclic remainder occur in the literal source. -/
theorem chebyshevCompletedEnergy_completion (N : ℕ) :
    4 * chebyshevCompletedEnergy N =
      (∑ j ∈ Icc 1 N, chebyshevConductorCoeff j) ^ 2 +
        (∑ j ∈ Icc 1 N, chebyshevConductorCoeff j ^ 2) + chebyshevCyclotomicRemainder N :=
  cumulativeEnergy_completion chebyshevCesaroIncrement N

theorem chebyshevCyclotomicRemainder_nonneg (N : ℕ) : 0 ≤ chebyshevCyclotomicRemainder N :=
  div_nonneg (cyclotomicRemainder_nonneg _ _) (by positivity)

private theorem chebyshevMeanSquare_eq_sum_one (N : ℕ) :
    chebyshevNormalizedCesaroMeanSquareEnergy N =
      ∑ n ∈ Icc 1 N, (chebyshevNormalizedCesaroSum n / (n : ℝ)) ^ 2 := by
  unfold chebyshevNormalizedCesaroMeanSquareEnergy
  apply sum_subset
  · intro n hn
    have h := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega, h.2⟩
  · intro n hn hnot
    have h := mem_Icc.mp hn
    have hn1 : n = 1 := by
      have : ¬ (2 ≤ n ∧ n ≤ N) := by simpa only [mem_Icc] using hnot
      omega
    subst n
    rw [chebyshevCesaro_zero_of_le_two (by omega), zero_div, zero_pow (by omega : (2 : ℕ) ≠ 0)]

private theorem chebyshevEnergy_term_bounds {n : ℕ} (hn : 1 ≤ n) :
    chebyshevNormalizedCesaroSum n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (chebyshevNormalizedCesaroSum n / (n : ℝ)) ^ 2 ∧
    (chebyshevNormalizedCesaroSum n / (n : ℝ)) ^ 2 ≤
      (4 / 3 : ℝ) * (chebyshevNormalizedCesaroSum n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
  by_cases hn2 : n ≤ 2
  · simp only [chebyshevCesaro_zero_of_le_two hn2, zero_pow (by omega : (2 : ℕ) ≠ 0),
      zero_div, mul_zero, le_refl, and_self]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hnp : (0 : ℝ) < n := by linarith only [hn3]
  have hq : 0 ≤ chebyshevNormalizedCesaroSum n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by positivity
  have he : (chebyshevNormalizedCesaroSum n / (n : ℝ)) ^ 2 =
      (1 + 1 / (n : ℝ)) *
        (chebyshevNormalizedCesaroSum n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    field_simp [hnp.ne', show (n : ℝ) + 1 ≠ 0 by positivity]
  have hl : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) := by
    linarith only [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hnp.le]
  have hu : 1 + 1 / (n : ℝ) ≤ (4 / 3 : ℝ) := by
    have h : (1 : ℝ) / n ≤ 1 / 3 := (div_le_iff₀ hnp).mpr (by linarith only [hn3])
    linarith only [h]
  rw [he]
  exact ⟨by simpa only [one_mul] using mul_le_mul_of_nonneg_right hl hq,
    mul_le_mul_of_nonneg_right hu hq⟩

/-- Accumulation retains an explicit nonnegative one-order-smaller denominator defect. -/
theorem chebyshevEnergy_covariance_defect (N : ℕ) :
    chebyshevNormalizedCesaroMeanSquareEnergy N - chebyshevCompletedEnergy N =
      ∑ n ∈ Icc 1 N,
        chebyshevNormalizedCesaroSum n ^ 2 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
  rw [chebyshevMeanSquare_eq_sum_one, chebyshevCompletedEnergy_eq_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1)
  field_simp [hnp.ne', show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

/-- Actual Chebyshev mean-square energy and its arithmetic completion differ by at most four thirds. -/
theorem chebyshevCompletedEnergy_comparison (N : ℕ) :
    chebyshevCompletedEnergy N ≤ chebyshevNormalizedCesaroMeanSquareEnergy N ∧
      chebyshevNormalizedCesaroMeanSquareEnergy N ≤ (4 / 3 : ℝ) * chebyshevCompletedEnergy N := by
  rw [chebyshevCompletedEnergy_eq_sum, chebyshevMeanSquare_eq_sum_one]
  constructor
  · exact sum_le_sum fun n hn => (chebyshevEnergy_term_bounds (mem_Icc.mp hn).1).1
  · rw [mul_sum]
    exact sum_le_sum fun n hn => (chebyshevEnergy_term_bounds (mem_Icc.mp hn).1).2

/-- The literal conductor coefficient has a reciprocal-square-root envelope. -/
theorem abs_chebyshevConductorCoeff_le {j : ℕ} (hj : 1 ≤ j) :
    |chebyshevConductorCoeff j| ≤ 6 / Real.sqrt (j : ℝ) := by
  by_cases hj2 : j ≤ 2
  · rw [chebyshevConductorCoeff, chebyshevCesaroIncrement_zero_of_le_two hj2, zero_div, abs_zero]
    positivity
  have hj3 : 3 ≤ j := by omega
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hdp : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < j - 1 by omega)
  have hsdp := Real.sqrt_pos.mpr hdp
  have hsjp := Real.sqrt_pos.mpr hjp
  have hψ : |Chebyshev.psi ((j - 1 : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ)| ≤
      6 * ((j - 1 : ℕ) : ℝ) := by
    have hu := psi_nat_le_six_mul (j - 1)
    have hl := psi_nat_nonneg (j - 1)
    exact abs_le.mpr ⟨by linarith only [hl, hdp], by linarith only [hu, hdp]⟩
  have hc : |chebyshevCesaroIncrement j| ≤ 6 * Real.sqrt ((j - 1 : ℕ) : ℝ) := by
    rw [chebyshevCesaroIncrement_eq hj3, abs_div, abs_of_pos hsdp]
    apply (div_le_iff₀ hsdp).mpr
    nlinarith only [hψ, Real.sq_sqrt hdp.le]
  rw [chebyshevConductorCoeff, abs_div, abs_of_pos hjp]
  calc
    _ ≤ (6 * Real.sqrt ((j - 1 : ℕ) : ℝ)) / j := div_le_div_of_nonneg_right hc hjp.le
    _ ≤ (6 * Real.sqrt (j : ℝ)) / j :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le j 1))
          (by norm_num)) hjp.le
    _ = 6 / Real.sqrt (j : ℝ) := by
      apply (div_eq_div_iff hjp.ne' hsjp.ne').mpr
      nlinarith only [Real.sq_sqrt hjp.le]

/-- The explicit weighted total-mass channel has a square-root payment. -/
theorem abs_sum_chebyshevConductorCoeff_le (N : ℕ) :
    |∑ j ∈ Icc 1 N, chebyshevConductorCoeff j| ≤ 12 * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Icc 1 N, |chebyshevConductorCoeff j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Icc 1 N, 6 / Real.sqrt (j : ℝ) :=
      sum_le_sum fun j hj => abs_chebyshevConductorCoeff_le (mem_Icc.mp hj).1
    _ = 6 * ∑ j ∈ Icc 1 N, 1 / Real.sqrt (j : ℝ) := by rw [mul_sum]; simp only [mul_one_div]
    _ ≤ 6 * (2 * Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left (_root_.RHTower.sum_inv_sqrt_le N)
      (by norm_num)
    _ = _ := by ring

/-- The explicit coefficient square-mass channel is at most linear in conductor. -/
theorem sum_sq_chebyshevConductorCoeff_le (N : ℕ) :
    ∑ j ∈ Icc 1 N, chebyshevConductorCoeff j ^ 2 ≤ 36 * (N : ℝ) := by
  have hterm (j : ℕ) (hj : 1 ≤ j) : chebyshevConductorCoeff j ^ 2 ≤ 36 := by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hjp : (0 : ℝ) < j := by linarith only [hj1]
    have hs : 1 ≤ Real.sqrt (j : ℝ) := by
      nlinarith only [Real.sq_sqrt hjp.le, Real.sqrt_nonneg (j : ℝ), hj1]
    have habs : |chebyshevConductorCoeff j| ≤ 6 :=
      (abs_chebyshevConductorCoeff_le hj).trans
        ((div_le_iff₀ (Real.sqrt_pos.mpr hjp)).mpr (by linarith only [hs]))
    have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
    norm_num only [sq_abs] at h
    exact h
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h := hterm (N + 1) (by omega)
    push_cast
    linarith only [ih, h]

/-- Both explicit coefficient channels together cost at most one hundred eighty times rank. -/
theorem chebyshevConductor_channels_le (N : ℕ) :
    (∑ j ∈ Icc 1 N, chebyshevConductorCoeff j) ^ 2 +
      (∑ j ∈ Icc 1 N, chebyshevConductorCoeff j ^ 2) ≤ 180 * (N : ℝ) := by
  have hmass := pow_le_pow_left₀ (abs_nonneg _) (abs_sum_chebyshevConductorCoeff_le N) 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at hmass
  have hsquare := sum_sq_chebyshevConductorCoeff_le N
  norm_num only at hmass
  linarith only [hmass, hsquare]

/-- Every superlinear Chebyshev energy cost lies in the actual cyclic remainder. -/
theorem chebyshevEnergy_cyclotomic_bounds (N : ℕ) :
    chebyshevCyclotomicRemainder N ≤ 4 * chebyshevNormalizedCesaroMeanSquareEnergy N ∧
      chebyshevNormalizedCesaroMeanSquareEnergy N ≤
        60 * (N : ℝ) + chebyshevCyclotomicRemainder N / 3 := by
  obtain ⟨hl, hu⟩ := chebyshevCompletedEnergy_comparison N
  have he := chebyshevCompletedEnergy_completion N
  have hbase := chebyshevConductor_channels_le N
  have hn : 0 ≤ (∑ j ∈ Icc 1 N, chebyshevConductorCoeff j) ^ 2 +
      (∑ j ∈ Icc 1 N, chebyshevConductorCoeff j ^ 2) :=
    add_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
  constructor <;> linarith only [hl, hu, he, hbase, hn]

/-- A fixed exponent at least one is preserved exactly by the actual cyclic-remainder reduction. -/
theorem chebyshevEnergy_power_bound_iff_cyclotomic {r : ℝ} (hr : 1 ≤ r) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevNormalizedCesaroMeanSquareEnergy N ≤ C * (N : ℝ) ^ r) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicRemainder N ≤ C * (N : ℝ) ^ r) := by
  constructor
  · rintro ⟨C, hC, hb⟩
    refine ⟨4 * C, by positivity, fun N hN => ?_⟩
    have h := (chebyshevEnergy_cyclotomic_bounds N).1.trans
      (mul_le_mul_of_nonneg_left (hb N hN) (by norm_num : (0 : ℝ) ≤ 4))
    simpa only [mul_assoc] using h
  · rintro ⟨C, hC, hb⟩
    refine ⟨60 + C / 3, by positivity, fun N hN => ?_⟩
    have hNp : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hpow : (N : ℝ) ≤ (N : ℝ) ^ r := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNp hr
    have h := (chebyshevEnergy_cyclotomic_bounds N).2
    have he := hb N hN
    nlinarith only [h, he, hpow]

/-- The five-sixths strip is precisely the corresponding upper exponent for the actual cyclic remainder. -/
theorem five_sixths_strip_iff_chebyshevCyclotomicRemainder_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 6 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 5 / 6) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevCyclotomicRemainder N ≤ C * (N : ℝ) ^ ((5 / 3 : ℝ) + ε) := by
  rw [five_sixths_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower]
  constructor <;> intro h ε hε
  · exact (chebyshevEnergy_power_bound_iff_cyclotomic (by linarith only [hε])).mp (h ε hε)
  · exact (chebyshevEnergy_power_bound_iff_cyclotomic (by linarith only [hε])).mpr (h ε hε)

/-- The three-quarters strip has the same exact arithmetic remainder normalization. -/
theorem three_quarters_strip_iff_chebyshevCyclotomicRemainder_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3 / 4) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevCyclotomicRemainder N ≤ C * (N : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
  rw [three_quarters_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower]
  constructor <;> intro h ε hε
  · exact (chebyshevEnergy_power_bound_iff_cyclotomic (by linarith only [hε])).mp (h ε hε)
  · exact (chebyshevEnergy_power_bound_iff_cyclotomic (by linarith only [hε])).mpr (h ε hε)

#print axioms chebyshevCompletedEnergy_eq_divisorGram
#print axioms chebyshevCompletedEnergy_comparison
#print axioms chebyshevConductor_channels_le
#print axioms chebyshevEnergy_cyclotomic_bounds
#print axioms five_sixths_strip_iff_chebyshevCyclotomicRemainder_subpower
#print axioms three_quarters_strip_iff_chebyshevCyclotomicRemainder_subpower

end GaloisForLFunctions.CompletedArithmeticForms
