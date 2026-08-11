import GaloisForLFunctions.RHTower.XiHeatCassiniPrimeGapMomentThreshold

/-!
# Asymptotic import bridge for the consecutive-prime-gap moment

Published prime-gap moment theorems are stated with an eventual Vinogradov/Big-O bound.  Route T's
Abel theorem was initially packaged with one global constant.  This module closes that mismatch:
an eventual ordered-prefix `IsBigO` estimate absorbs its finite exceptional prefix and feeds the
critical `3/2` Abel threshold directly.
-/

open Complex Filter Set Topology Asymptotics

namespace RHTower

noncomputable section

/-- An eventual Big-O prefix moment admits one nonnegative global constant.  The finite exceptional
prefix is absorbed by the sum of its exact positive-weight ratios. -/
theorem exists_global_primeGapSquarePrefix_bound_of_isBigO
    {theta : ℝ}
    (hmoment : xiHeatCassiniPrimeGapSquarePrefix =O[atTop]
      fun M : ℕ => Real.exp (theta * xiMassNthPrimeLogHeight M)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      xiHeatCassiniPrimeGapSquarePrefix M ≤
        C * Real.exp (theta * xiMassNthPrimeLogHeight M) := by
  obtain ⟨C, hC, hbound⟩ := hmoment.exists_nonneg
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp hbound.bound
  let g : ℕ → ℝ := fun M => Real.exp (theta * xiMassNthPrimeLogHeight M)
  let D : ℝ := ∑ M ∈ Finset.range M₀,
    xiHeatCassiniPrimeGapSquarePrefix M / g M
  let C' : ℝ := C + D
  have hg (M : ℕ) : 0 < g M := Real.exp_pos _
  have hratio (M : ℕ) :
      0 ≤ xiHeatCassiniPrimeGapSquarePrefix M / g M :=
    div_nonneg (xiHeatCassiniPrimeGapSquarePrefix_nonneg M) (hg M).le
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact Finset.sum_nonneg fun M _ => hratio M
  refine ⟨C', add_nonneg hC hD, fun M => ?_⟩
  by_cases hlarge : M₀ ≤ M
  · have htail := hM₀ M hlarge
    have hprefix :
        ‖xiHeatCassiniPrimeGapSquarePrefix M‖ =
          xiHeatCassiniPrimeGapSquarePrefix M :=
      by rw [Real.norm_eq_abs,
        abs_of_nonneg (xiHeatCassiniPrimeGapSquarePrefix_nonneg M)]
    have hgNorm : ‖g M‖ = g M :=
      by rw [Real.norm_eq_abs, abs_of_pos (hg M)]
    rw [hprefix, hgNorm] at htail
    calc
      xiHeatCassiniPrimeGapSquarePrefix M ≤ C * g M := htail
      _ ≤ C' * g M := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp only [C']; linarith) (hg M).le
      _ = C' * Real.exp (theta * xiMassNthPrimeLogHeight M) := rfl
  · have hMmem : M ∈ Finset.range M₀ := Finset.mem_range.mpr (Nat.lt_of_not_ge hlarge)
    have hratioD : xiHeatCassiniPrimeGapSquarePrefix M / g M ≤ D := by
      dsimp only [D]
      exact Finset.single_le_sum (fun j _ => hratio j) hMmem
    calc
      xiHeatCassiniPrimeGapSquarePrefix M =
          (xiHeatCassiniPrimeGapSquarePrefix M / g M) * g M := by
        field_simp [(hg M).ne']
      _ ≤ D * g M :=
        mul_le_mul_of_nonneg_right hratioD (hg M).le
      _ ≤ C' * g M := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp only [C']; linarith) (hg M).le
      _ = C' * Real.exp (theta * xiMassNthPrimeLogHeight M) := rfl

/-- **Literature-shaped critical-energy receiver.**  Any Big-O ordered-prefix second moment with
exponent strictly below `3/2` forces the critical Route-T mesh energy. -/
theorem summable_primeGapCriticalEnergy_of_prefix_moment_isBigO_lt_three_halves
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta : theta < 3 / 2)
    (hmoment : xiHeatCassiniPrimeGapSquarePrefix =O[atTop]
      fun M : ℕ => Real.exp (theta * xiMassNthPrimeLogHeight M)) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_global_primeGapSquarePrefix_bound_of_isBigO hmoment
  exact summable_primeGapCriticalEnergy_of_prefix_moment_lt_three_halves
    htheta0 htheta hC hglobal

/-- Concrete import point for Maynard--Peck: choose `epsilon = 1/8`, so
`5/4 + epsilon = 11/8 < 3/2`. -/
theorem summable_primeGapCriticalEnergy_of_eleven_eighth_prefix_moment_isBigO
    (hmoment : xiHeatCassiniPrimeGapSquarePrefix =O[atTop]
      fun M : ℕ => Real.exp ((11 / 8 : ℝ) * xiMassNthPrimeLogHeight M)) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  exact summable_primeGapCriticalEnergy_of_prefix_moment_isBigO_lt_three_halves
    (by norm_num) (by norm_num) hmoment

end

end RHTower
