import GaloisForLFunctions.RHTower.MobiusDivisorCriticalChildAbelMellinWeld
import GaloisForLFunctions.RHTower.BakerGeneralConsequences

noncomputable section
open Finset Complex
namespace RHTower

theorem criticalContinuousAbel_nat_formula (k : ℕ) :
    criticalContinuousAbel (k : ℝ) =
      ∑ n ∈ Ico 1 k,
        (Real.sqrt (n + 1 : ℕ) - Real.sqrt n) * psiDefect n := by
  unfold criticalContinuousAbel
  rw [squareRootSummatoryPrimitive_nat]
  have hsets : Icc 1 (k - 1) = Ico 1 k := by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hsets, Complex.re_sum]
  apply sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (mem_Ico.mp hn).1
  rw [criticalSourceCoeff_cumulative n hn1]
  simp

end RHTower
