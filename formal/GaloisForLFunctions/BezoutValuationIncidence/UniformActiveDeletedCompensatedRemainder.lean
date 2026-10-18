import GaloisForLFunctions.BezoutValuationIncidence.CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget

/-!
# Uniform active-deleted compensated remainder

The existing divisor-square moment estimates discharge the logarithmic coefficient
conditions for the actual power-damped field and its shifted-exponent product.
The existing regularized divisor-harmonic theorem then yields a uniform bound for
the active-deleted diagonal after its canonical compensated drift is removed.
This supplies the diagonal part of the interior-energy remainder problem; adjacent
correlations and strict interior contraction are separate conclusions.
-/

open Finset Filter Topology ArithmeticFunction RHTower
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem summable_logWeight_of_divisor_rpow_bound
    {a : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (ha : ∀ n, |a n| ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (-ε)) :
    Summable (RegularizedDivisorHarmonic.logWeight a) := by
  have hσ : (1 : ℝ) / 2 < (1 + ε) / 2 := by linarith
  have hs := ((summable_divisor_sq_rpow hσ).mul_left (2 : ℝ)).add
    (summable_divisor_sq_log_rpow hσ)
  refine Summable.of_nonneg_of_le
    (RegularizedDivisorHarmonic.logWeight_nonneg a) ?_ hs
  intro n
  by_cases hn : n = 0
  · subst n
    simp [RegularizedDivisorHarmonic.logWeight]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hd1 : (1 : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr
      ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩⟩
  have hd2 : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by nlinarith
  have hl2 : 1 + Real.log n ≤ 2 + (Real.log n) ^ 2 := by
    nlinarith [sq_nonneg (Real.log n - 1)]
  have hr : (n : ℝ) ^ (-ε) / n = (n : ℝ) ^ (-2 * ((1 + ε) / 2)) := by
    rw [← Real.rpow_sub_one hnpos.ne']
    congr 1
    ring
  calc
    RegularizedDivisorHarmonic.logWeight a n
      ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ (-ε)) * (1 + Real.log n) / n := by
        unfold RegularizedDivisorHarmonic.logWeight
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ha n) (by linarith)) hnpos.le
    _ = ((n.divisors.card : ℝ) * (1 + Real.log n)) * ((n : ℝ) ^ (-ε) / n) := by ring
    _ ≤ ((n.divisors.card : ℝ) ^ 2 * (2 + (Real.log n) ^ 2)) *
        ((n : ℝ) ^ (-ε) / n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hd2 hl2 (by linarith) (sq_nonneg _)
    _ = _ := by rw [hr]; ring

/-- The actual power-damped Möbius coefficients satisfy the logarithmic moment
needed by the existing uniform divisor-harmonic theorem. -/
theorem summable_pmPowerDampedMobius_logWeight {ε : ℝ} (hε : 0 < ε) :
    Summable (RegularizedDivisorHarmonic.logWeight
      (fun n : ℕ => (moebius n : ℝ) * (n : ℝ) ^ (-ε))) := by
  apply summable_logWeight_of_divisor_rpow_bound hε
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  have hd1 : (1 : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr
      ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩⟩
  have hmu : |(moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (-ε))]
  exact mul_le_mul_of_nonneg_right (hmu.trans hd1) (by positivity)

/-- The exact coefficient of the shifted-exponent product has the same
logarithmic summability for every positive damping. -/
theorem summable_pmShiftedExponentSecondCoeff_logWeight {ε : ℝ} (hε : 0 < ε) :
    Summable (RegularizedDivisorHarmonic.logWeight (pmShiftedExponentSecondCoeff ε)) :=
  summable_logWeight_of_divisor_rpow_bound hε
    (abs_pmShiftedExponentSecondCoeff_le hε.le)

private theorem pm_real_coeffDensity_eq {ε : ℝ} (hε : 0 < ε) :
    RegularizedDivisorHarmonic.coeffDensity
      (fun n : ℕ => (moebius n : ℝ) * (n : ℝ) ^ (-ε)) =
      (pmPowerDampedDivisorDensity ε).re := by
  have hm := pm_tendsto_divisor_average (pm_summable_real_mobius_reciprocal hε)
  exact tendsto_nhds_unique hm (by
    simpa only [pmPowerDampedDivisorSum, pmPowerDampedDivisorCoeff] using
      tendsto_pmPowerDampedDivisorSum_div_real hε)

private theorem exists_divisorHarmonic_compensated_bound {a : ℕ → ℝ}
    (ha : Summable (RegularizedDivisorHarmonic.logWeight a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(∑ n ∈ Icc 1 N, (∑ d ∈ n.divisors, a d) / (n : ℝ)) -
        RegularizedDivisorHarmonic.coeffDensity a * pmCompensatedHarmonicSum N| ≤ C := by
  let C : ℝ :=
    |RegularizedDivisorHarmonic.coeffDensity a * Real.eulerMascheroniConstant -
      RegularizedDivisorHarmonic.coeffLogMass a| +
    (6 + |Real.eulerMascheroniConstant|) *
      ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d +
    |RegularizedDivisorHarmonic.coeffDensity a| * (|Real.eulerMascheroniConstant| + 3)
  refine ⟨max C 0, le_max_right _ _, fun N => ?_⟩
  by_cases hN : N = 0
  · subst N
    simp [pmCompensatedHarmonicSum, le_max_right C 0]
  · exact (abs_divisorHarmonic_sub_coeffDensity_mul_compensated_le ha
      (Nat.one_le_iff_ne_zero.mpr hN)).trans (le_max_left C 0)

/-- Uniform compensated harmonic remainder of the actual divisor field. -/
theorem exists_pmPowerDampedDivisor_harmonic_compensated_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff ε n / (n : ℝ)) -
        (pmPowerDampedDivisorDensity ε).re * pmCompensatedHarmonicSum N| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_divisorHarmonic_compensated_bound
    (summable_pmPowerDampedMobius_logWeight hε)
  refine ⟨C, hC0, fun N => ?_⟩
  simpa only [pmPowerDampedDivisorCoeff, pm_real_coeffDensity_eq hε] using hC N

/-- Uniform compensated harmonic remainder of the same-node shifted product. -/
theorem exists_pmShiftedExponentProduct_harmonic_compensated_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(∑ n ∈ Icc 1 N,
        pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n / (n : ℝ)) -
        pmShiftedExponentSecondDensity ε * pmCompensatedHarmonicSum N| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_divisorHarmonic_compensated_bound
    (summable_pmShiftedExponentSecondCoeff_logWeight hε)
  refine ⟨C, hC0, fun N => ?_⟩
  simpa only [← pmPowerDampedDivisorCoeff_mul_add_one,
    RegularizedDivisorHarmonic.coeffDensity, pmShiftedExponentSecondDensity] using hC N

private theorem exists_pmActiveDeletedDiagonal_harmonic_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(∑ n ∈ Icc 1 N, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum N| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_pmPowerDampedDivisor_harmonic_compensated_bound hε
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    exists_pmPowerDampedDivisor_harmonic_compensated_bound (show 0 < 1 + ε by linarith)
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_pmShiftedExponentProduct_harmonic_compensated_bound hε
  let ρ := (pmPowerDampedDivisorDensity ε).re
  refine ⟨C₃ + |ρ| * C₁ + |ρ| * C₂ + 2 * ρ ^ 2, by positivity, fun N => ?_⟩
  have hexpand :
      (∑ n ∈ Icc 1 N, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) =
      (∑ n ∈ Icc 1 N,
        pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n / (n : ℝ)) -
      ρ * (∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff ε n / (n : ℝ)) -
      ρ * (∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff (1 + ε) n / (n : ℝ)) +
      ρ ^ 2 * (harmonic N : ℝ) := by
    rw [RegularizedDivisorHarmonic.harmonic_cast_eq_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [pmActiveDeletedDiagonalCoeff, pmPowerDampedCenteredDivisorCoeff, ρ]
    ring
  let r₁ := (∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff ε n / (n : ℝ)) -
    ρ * pmCompensatedHarmonicSum N
  let r₂ := (∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff (1 + ε) n / (n : ℝ)) -
    (pmPowerDampedDivisorDensity (1 + ε)).re * pmCompensatedHarmonicSum N
  let r₃ := (∑ n ∈ Icc 1 N,
    pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n / (n : ℝ)) -
    pmShiftedExponentSecondDensity ε * pmCompensatedHarmonicSum N
  have hid :
      (∑ n ∈ Icc 1 N, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum N =
      r₃ - ρ * r₁ - ρ * r₂ + ρ ^ 2 * ((harmonic N : ℝ) - pmCompensatedHarmonicSum N) := by
    rw [hexpand]
    dsimp only [r₁, r₂, r₃, ρ, pmShiftedExponentCovariance]
    ring
  have hH : |(harmonic N : ℝ) - pmCompensatedHarmonicSum N| ≤ 2 := by
    obtain ⟨h0, h2⟩ := harmonic_sub_pmCompensatedHarmonicSum_bounds N
    simpa only [abs_of_nonneg h0] using h2
  have hr₁ : |r₁| ≤ C₁ := hC₁ N
  have hr₂ : |r₂| ≤ C₂ := hC₂ N
  have hr₃ : |r₃| ≤ C₃ := hC₃ N
  rw [hid]
  calc
    _ ≤ |r₃ - ρ * r₁ - ρ * r₂| +
        |ρ ^ 2 * ((harmonic N : ℝ) - pmCompensatedHarmonicSum N)| := abs_add_le _ _
    _ ≤ (|r₃ - ρ * r₁| + |ρ * r₂|) +
        |ρ ^ 2 * ((harmonic N : ℝ) - pmCompensatedHarmonicSum N)| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((|r₃| + |ρ * r₁|) + |ρ * r₂|) +
        |ρ ^ 2 * ((harmonic N : ℝ) - pmCompensatedHarmonicSum N)| :=
      add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
    _ = |r₃| + |ρ| * |r₁| + |ρ| * |r₂| +
        ρ ^ 2 * |(harmonic N : ℝ) - pmCompensatedHarmonicSum N| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ρ)]
    _ ≤ C₃ + |ρ| * C₁ + |ρ| * C₂ + 2 * ρ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hr₁ (abs_nonneg ρ),
        mul_le_mul_of_nonneg_left hr₂ (abs_nonneg ρ),
        mul_le_mul_of_nonneg_left hH (sq_nonneg ρ)]

private theorem abs_sum_div_succ_le {f : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ n, |f n| ≤ B) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, f n) / ((N : ℝ) + 1)| ≤ B := by
  have hs : |∑ n ∈ Icc 1 N, f n| ≤ (N : ℝ) * B := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |f n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, B := Finset.sum_le_sum fun n _ => hf n
      _ = _ := by simp
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

/-- For every positive damping, the actual active-deleted diagonal differs
from its canonical compensated drift by a horizon-independent constant.
All coefficient moment conditions are discharged for the arithmetic field. -/
theorem exists_pmActiveDeletedCovarianceDiagonal_compensated_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_pmActiveDeletedDiagonal_harmonic_bound hε
  let ρ := (pmPowerDampedDivisorDensity ε).re
  have hcoeff (n : ℕ) : |pmActiveDeletedDiagonalCoeff ε n| ≤ (1 + |ρ|) ^ 2 := by
    have hF₁ : |pmPowerDampedDivisorCoeff ε n| ≤ 1 := by
      rw [abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε.le n)]
      exact pmPowerDampedDivisorCoeff_le_one hε.le n
    have hF₂ : |pmPowerDampedDivisorCoeff (1 + ε) n| ≤ 1 := by
      have hη : 0 ≤ 1 + ε := by linarith
      rw [abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hη n)]
      exact pmPowerDampedDivisorCoeff_le_one hη n
    have h₁ : |pmPowerDampedDivisorCoeff ε n - ρ| ≤ 1 + |ρ| :=
      (abs_sub _ _).trans (add_le_add hF₁ le_rfl)
    have h₂ : |pmPowerDampedDivisorCoeff (1 + ε) n - ρ| ≤ 1 + |ρ| :=
      (abs_sub _ _).trans (add_le_add hF₂ le_rfl)
    change |(pmPowerDampedDivisorCoeff ε n - ρ) *
      (pmPowerDampedDivisorCoeff (1 + ε) n - ρ)| ≤ _
    rw [abs_mul, sq]
    exact mul_le_mul h₁ h₂ (abs_nonneg _) (by positivity)
  refine ⟨C + (1 + |ρ|) ^ 2, by positivity, fun T => ?_⟩
  have ht := abs_sum_div_succ_le (sq_nonneg (1 + |ρ|)) hcoeff T
  calc
    _ = |((∑ n ∈ Icc 1 T, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T) -
        (∑ n ∈ Icc 1 T, pmActiveDeletedDiagonalCoeff ε n) / ((T : ℝ) + 1)| := by
      rw [pmActiveDeletedCovarianceDiagonal_eq]
      congr 1
      ring
    _ ≤ |(∑ n ∈ Icc 1 T, pmActiveDeletedDiagonalCoeff ε n / (n : ℝ)) -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T| +
        |(∑ n ∈ Icc 1 T, pmActiveDeletedDiagonalCoeff ε n) / ((T : ℝ) + 1)| :=
      abs_sub _ _
    _ ≤ C + (1 + |ρ|) ^ 2 := add_le_add (hC T) ht

end GaloisForLFunctions.BezoutValuationIncidence
