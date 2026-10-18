import GaloisForLFunctions.BezoutValuationIncidence.UniformActiveDeletedCompensatedRemainder
import GaloisForLFunctions.BezoutValuationIncidence.UniformAdjacentDivisorCompensatedRemainder

/-!
# Uniform renormalized interior-energy remainder

The existing compensated pronic-shift identity transfers the single-field
harmonic bound to the actual kernel at a uniform cost of two. Combining this
with the adjacent compensated bounds gives a uniform predecessor-peak remainder.
The canonical energy budget then bounds the compensated interior bracket minus
the actual energy for every positive damping.

Strict interior contraction is consequently equivalent to bounded actual energy.
This module proves that equivalence, without asserting either side.
-/

open Finset RHTower
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem abs_compensated_sum_sub_harmonic_le_two
    {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1) (T : ℕ) :
    |(∑ n ∈ Icc 1 (T - 1), f n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
      (∑ n ∈ Icc 1 T, f n / (n : ℝ))| ≤ 2 := by
  have hp0 : 0 ≤ ∑ n ∈ Icc 1 T, f n / (pronicSeq n : ℝ) :=
    sum_nonneg fun n _ => div_nonneg (hf0 n) (Nat.cast_nonneg _)
  have hp1 : (∑ n ∈ Icc 1 T, f n / (pronicSeq n : ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ n ∈ Icc 1 T, (1 : ℝ) / (pronicSeq n : ℝ) :=
        sum_le_sum fun n _ => div_le_div_of_nonneg_right (hf1 n) (Nat.cast_nonneg _)
      _ ≤ 1 := sum_one_div_pronicSeq_le_one T
  have ht0 : 0 ≤ (∑ n ∈ Icc 1 T, f n) / ((T : ℝ) + 1) := by
    exact div_nonneg (sum_nonneg fun n _ => hf0 n) (by positivity)
  have ht1 : (∑ n ∈ Icc 1 T, f n) / ((T : ℝ) + 1) ≤ 1 := by
    have hs : (∑ n ∈ Icc 1 T, f n) ≤ (T : ℝ) := by
      calc
        _ ≤ ∑ n ∈ Icc 1 T, (1 : ℝ) := sum_le_sum fun n _ => hf1 n
        _ = _ := by simp
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  by_cases hT : T = 0
  · subst T
    simp
  have he := sum_Icc_pred_compensated_add_sum_pronicSeq_eq f
    (show 1 ≤ T by omega)
  simp only [mul_sub, mul_one_div, sum_sub_distrib, ← sum_div] at he ⊢
  apply abs_le.mpr
  constructor <;> linarith

/-- The actual single divisor field has a uniform centered remainder with
the exact compensated kernel used by the predecessor-peak martingale. -/
theorem exists_pmPowerDampedDivisor_compensated_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |∑ n ∈ Icc 1 (T - 1),
        (pmPowerDampedDivisorCoeff ε n - (pmPowerDampedDivisorDensity ε).re) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_pmPowerDampedDivisor_harmonic_compensated_bound hε
  refine ⟨C + 2, by positivity, fun T => ?_⟩
  have hshift := abs_compensated_sum_sub_harmonic_le_two
    (pmPowerDampedDivisorCoeff_nonneg hε.le) (pmPowerDampedDivisorCoeff_le_one hε.le) T
  have he :
      (∑ n ∈ Icc 1 (T - 1),
        (pmPowerDampedDivisorCoeff ε n - (pmPowerDampedDivisorDensity ε).re) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      ((∑ n ∈ Icc 1 (T - 1), pmPowerDampedDivisorCoeff ε n *
        (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        (∑ n ∈ Icc 1 T, pmPowerDampedDivisorCoeff ε n / (n : ℝ))) +
      ((∑ n ∈ Icc 1 T, pmPowerDampedDivisorCoeff ε n / (n : ℝ)) -
        (pmPowerDampedDivisorDensity ε).re * pmCompensatedHarmonicSum T) := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, pmCompensatedHarmonicSum]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith [add_le_add hshift (hC T)])

/-- Every positive damping has a horizon-independent predecessor-peak
remainder after its exact canonical drift is removed. -/
theorem exists_pmPredecessorPeak_compensated_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T| ≤ C := by
  have hη : 0 < 1 + ε := by linarith
  obtain ⟨C₁, hC₁, h₁⟩ := exists_pm_adjacent_divisor_compensated_bound hε hε
  obtain ⟨C₂, hC₂, h₂⟩ := exists_pm_adjacent_divisor_compensated_bound hε hη
  obtain ⟨C₃, hC₃, h₃⟩ := exists_pmPowerDampedDivisor_compensated_bound hε
  obtain ⟨C₄, hC₄, h₄⟩ := exists_pmPowerDampedDivisor_compensated_bound hη
  let ρ := (pmPowerDampedDivisorDensity ε).re
  refine ⟨(C₁ + C₂ + |ρ| * (C₄ + C₃)) / 2, by positivity, fun T => ?_⟩
  let w : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)
  let A : ℝ := ∑ n ∈ Icc 1 (T - 1),
    (pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff ε n -
      pmAdjacentDivisorDensity ε ε) * w n
  let B : ℝ := ∑ n ∈ Icc 1 (T - 1),
    (pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff (1 + ε) n -
      pmAdjacentDivisorDensity ε (1 + ε)) * w n
  let U : ℝ := ∑ n ∈ Icc 1 (T - 1),
    (pmPowerDampedDivisorCoeff ε n - ρ) * w n
  let V : ℝ := ∑ n ∈ Icc 1 (T - 1),
    (pmPowerDampedDivisorCoeff (1 + ε) n - (pmPowerDampedDivisorDensity (1 + ε)).re) * w n
  have he : pmPredecessorPeakMartingaleSum ε T -
      pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T =
      (A - B + ρ * (V - U)) / 2 := by
    rw [pmPredecessorPeakLogDrift_eq_adjacent]
    dsimp only [pmPredecessorPeakMartingaleSum, pmCompensatedHarmonicSum,
      A, B, U, V, w, ρ, pmPowerDampedCenteredDivisorCoeff, pmActiveSawtoothComponent]
    simp only [mul_sum, sum_div, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    ring
  have hA : |A| ≤ C₁ := h₁ T
  have hB : |B| ≤ C₂ := h₂ T
  have hU : |U| ≤ C₃ := h₃ T
  have hV : |V| ≤ C₄ := h₄ T
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ |A - B| + |ρ * (V - U)| := abs_add_le _ _
    _ = |A - B| + |ρ| * |V - U| := by rw [abs_mul]
    _ ≤ (|A| + |B|) + |ρ| * (|V| + |U|) :=
      add_le_add (abs_sub _ _) (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg ρ))
    _ ≤ _ := add_le_add (add_le_add hA hB)
      (mul_le_mul_of_nonneg_left (add_le_add hV hU) (abs_nonneg ρ))

/-- The compensated interior bracket tracks the actual energy to O(1)
for every positive damping. This is a coefficient-one comparison. -/
theorem exists_pmBezoutInterior_compensated_energy_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T -
        pmPowerDampedDivisorDiscreteEnergy ε T| ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_pmActiveDeletedCovarianceDiagonal_compensated_bound hε
  obtain ⟨C₂, hC₂, h₂⟩ := exists_pmPredecessorPeak_compensated_bound hε
  refine ⟨C₁ + 2 * C₂, by positivity, fun T => ?_⟩
  have he : 2 * pmBezoutInteriorMartingaleSum ε T +
      2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T -
      pmPowerDampedDivisorDiscreteEnergy ε T =
      -(pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T) -
      2 * (pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T) := by
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_canonical_compensated_budget]
    ring
  rw [he]
  calc
    _ ≤ |-(pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T)| +
      |2 * (pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T)| := abs_sub _ _
    _ = |pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T| +
      2 * |pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T| := by
      rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := add_le_add (h₁ T) (mul_le_mul_of_nonneg_left (h₂ T) (by norm_num))

/-- At every positive damping, strict interior contraction is equivalent
to bounded actual energy. Neither side is assumed or asserted here. -/
theorem pmInterior_strict_contraction_iff_bounded_energy
    {ε : ℝ} (hε : 0 < ε) :
    (∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
      2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
        (1 - δ) * pmPowerDampedDivisorDiscreteEnergy ε T + C) ↔
    (∃ K : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ K) := by
  obtain ⟨B, _, hB⟩ := exists_pmBezoutInterior_compensated_energy_bound hε
  constructor
  · rintro ⟨δ, hδ, C, hC⟩
    refine ⟨(C + B) / δ, fun T => ?_⟩
    have hh := (abs_le.mp (hB T)).1
    apply (le_div_iff₀ hδ).mpr
    nlinarith [hC T]
  · rintro ⟨K, hK⟩
    refine ⟨1, by norm_num, K + B, fun T => ?_⟩
    have hh := (abs_le.mp (hB T)).2
    nlinarith [hK T]

end GaloisForLFunctions.BezoutValuationIncidence

