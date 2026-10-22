import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalProperPrimePowerReduction
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalAbsoluteVariationPressure

/-!
# Absolute variation remains impossible after the proper-prime-power reduction

The critical FU codiagonal left after proper-prime-power removal is still not amenable to a
cellwise absolute-value argument.  This module proves that statement on the literal moving
triangular aperture: the absolute variation of the valuation-one-prime-minus-polar cells diverges
on the same canonical cofinal clock as the mixed von Mangoldt source.

The result does not estimate the signed reporter.  Its purpose is to identify exactly where a
successful producer must retain cancellation: among valuation-one prime and polar cells.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One valuation-one-prime-minus-polar cell of the literal critical FU source. -/
def suzukiCheckpointCriticalPrimeOnlyPolarCell (n : ℕ) : ℝ :=
  (if Nat.Prime n then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) -
    (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))

/-- Total cellwise absolute variation of the literal valuation-one prime--polar codiagonal. -/
def suzukiCheckpointCriticalPrimeOnlyAbsoluteVariationCore (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (⌊Real.exp H⌋₊ - 2),
    |suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
      suzukiCheckpointCriticalTriangularMultiplier H j|

private theorem abs_fullCriticalCell_le_primeOnly_add_proper
    (H : ℝ) (j : ℕ) :
    |(suzukiCheckpointCriticalMertensDeviationCore (j + 1) -
        suzukiCheckpointCriticalMertensDeviationCore j) *
      suzukiCheckpointCriticalTriangularMultiplierCore H j| ≤
      |suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
        suzukiCheckpointCriticalTriangularMultiplier H j| +
      |(if IsProperPrimePow (j + 3) then
          ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
        else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| := by
  rw [suzukiCheckpointCriticalMertensDeviationCore_succ_sub]
  unfold suzukiCheckpointCriticalTriangularMultiplierCore
  change |(ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
      (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
      suzukiCheckpointCriticalTriangularMultiplier H j| ≤ _
  have hsplit :=
    suzukiCheckpointCriticalPrimePolarIncrement_eq_primeOnly_add_properPrimePower (j + 3)
  rw [show (j + 3 - 1 : ℕ) = j + 2 by omega] at hsplit
  unfold suzukiCheckpointCriticalPrimeOnlyPolarCell
  rw [hsplit, add_mul]
  exact abs_add_le _ _

/-- Exact mixed-to-valuation-one absolute comparison.  The only discarded sector is the already
uniformly summable proper-prime-power absolute mass. -/
theorem suzukiCheckpointCriticalAbsoluteVariationCore_le_primeOnly_add_proper
    (H : ℝ) :
    suzukiCheckpointCriticalAbsoluteVariationCore H ≤
      suzukiCheckpointCriticalPrimeOnlyAbsoluteVariationCore H +
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          |(if IsProperPrimePow (j + 3) then
              ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
            else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| := by
  unfold suzukiCheckpointCriticalAbsoluteVariationCore
    suzukiCheckpointCriticalPrimeOnlyAbsoluteVariationCore
  rw [show (⌊Real.exp H⌋₊ - 2) = suzukiCheckpointEventIndex H - 2 by
    rw [suzukiCheckpointEventIndex]]
  calc
    ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        |(suzukiCheckpointCriticalMertensDeviationCore (j + 1) -
            suzukiCheckpointCriticalMertensDeviationCore j) *
          suzukiCheckpointCriticalTriangularMultiplierCore H j| ≤
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (|suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
              suzukiCheckpointCriticalTriangularMultiplier H j| +
            |(if IsProperPrimePow (j + 3) then
                ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
              else 0) * suzukiCheckpointCriticalTriangularMultiplier H j|) := by
          apply Finset.sum_le_sum
          intro j _
          exact abs_fullCriticalCell_le_primeOnly_add_proper H j
    _ = _ := Finset.sum_add_distrib

private theorem two_le_suzukiCheckpointCriticalPressureSchedule
    {N : ℕ} (hN : 1 ≤ N) :
    2 ≤ suzukiCheckpointCriticalPressureSchedule N := by
  have hlog3 : 1 < Real.log (3 : ℝ) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hthree : (3 : ℝ) ≤ (4 * N : ℕ) := by
    exact_mod_cast (show 3 ≤ 4 * N by omega)
  have hlog : 1 ≤ Real.log ((4 * N : ℕ) : ℝ) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) hthree)
  unfold suzukiCheckpointCriticalPressureSchedule
  linarith

/-- **Valuation-one absolute-variation no-go.**  Even after proper prime powers are removed,
the literal true-prime-minus-polar codiagonal has divergent cellwise absolute variation on the
canonical critical moving clock.  Hence any RH-bearing cancellation proof must be collective and
signed already in this reduced source. -/
theorem tendsto_suzukiCheckpointCriticalPrimeOnlyAbsoluteVariation_schedule_atTop :
    Tendsto (fun N : ℕ =>
      suzukiCheckpointCriticalPrimeOnlyAbsoluteVariationCore
        (suzukiCheckpointCriticalPressureSchedule N)) atTop atTop := by
  obtain ⟨C, hC⟩ :=
    exists_suzukiCheckpointCriticalProperPrimePowerAbsoluteVariation_uniform_bound
  refine tendsto_atTop.2 fun r => ?_
  filter_upwards [
      (tendsto_suzukiCheckpointCriticalAbsoluteVariation_schedule_atTop.eventually
        (eventually_ge_atTop (r + C))),
      eventually_ge_atTop (1 : ℕ)] with N hfull hN
  have hH : 2 ≤ suzukiCheckpointCriticalPressureSchedule N :=
    two_le_suzukiCheckpointCriticalPressureSchedule hN
  have hproper := hC (suzukiCheckpointCriticalPressureSchedule N) hH
  have hcomparison :=
    suzukiCheckpointCriticalAbsoluteVariationCore_le_primeOnly_add_proper
      (suzukiCheckpointCriticalPressureSchedule N)
  linarith

end

end RHTower
