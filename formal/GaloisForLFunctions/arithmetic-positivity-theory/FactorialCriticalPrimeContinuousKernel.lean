import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelDensity
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Continuous representative of the critical prime kernel

The arithmetic cumulative charges are uniformly bounded. A summable inverse-square
majorant gives a continuous one-sided periodization branch on the closed unit cell.
Its reflected average has matching endpoints and agrees with the real L1 kernel
on the open cell. Hence it represents every complete translated prime form.

This removes the endpoint ambiguity without asserting a sign for the kernel.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private def kernelCellBudget : ℝ :=
  ∑' m : ℕ, |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ)^3

private theorem kernel_cell_budget_nonneg : 0 ≤ kernelCellBudget :=
  (abs_nonneg (factorialCriticalPrimeCumulativeCharge 0)).trans
    (abs_factorialCriticalPrimeCumulativeCharge_le 0)

private def kernelCellMajorant (k : ℕ) : ℝ :=
  2 * kernelCellBudget / ((k + 1 : ℕ) : ℝ)^2

private theorem kernel_cell_majorant_summable : Summable kernelCellMajorant := by
  refine ((HTGeometry.summable_inv_sq_shift (σ := 1) zero_lt_one).mul_left
    (2 * kernelCellBudget)).congr ?_
  intro k
  simp only [kernelCellMajorant, Nat.cast_add, Nat.cast_one]
  rw [add_comm (k : ℝ) 1]
  ring

/-- The continuous one-sided branch of the native unit-cell periodization. -/
def factorialCriticalPrimeCellKernel (t : ℝ) : ℝ :=
  ∑' k : ℕ, factorialCriticalPrimeCumulativeCharge (k + 1) *
    factorialCriticalPrimeKernelWeight (((k + 1 : ℕ) : ℝ) + t)

private theorem kernel_cell_term_bound (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖factorialCriticalPrimeCumulativeCharge (k + 1) *
      factorialCriticalPrimeKernelWeight (((k + 1 : ℕ) : ℝ) + t)‖ ≤ kernelCellMajorant k := by
  have hj : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hu : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + t := by linarith [ht.1]
  have hsq : (((k + 1 : ℕ) : ℝ))^2 ≤ (((k + 1 : ℕ) : ℝ) + t)^2 := by
    nlinarith [ht.1]
  have hinv : ((((k + 1 : ℕ) : ℝ) + t)^2)⁻¹ ≤ ((((k + 1 : ℕ) : ℝ))^2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hj) hsq
  have hγ : |factorialCriticalPrimeKernelWeight (((k + 1 : ℕ) : ℝ) + t)| ≤
      2 / ((k + 1 : ℕ) : ℝ)^2 := by
    rw [factorialCriticalPrimeKernelWeight, Real.rpow_neg hu.le, Real.rpow_two,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),
      abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    calc
      ((((k + 1 : ℕ) : ℝ) + t)^2)⁻¹ *
          (1 - Real.cos (2 * Real.pi * (((k + 1 : ℕ) : ℝ) + t) / 12))
          ≤ ((((k + 1 : ℕ) : ℝ) + t)^2)⁻¹ * 2 := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
        linarith [Real.neg_one_le_cos (2 * Real.pi * (((k + 1 : ℕ) : ℝ) + t) / 12)]
      _ ≤ ((((k + 1 : ℕ) : ℝ))^2)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_right hinv (by norm_num)
      _ = _ := by ring
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |factorialCriticalPrimeCumulativeCharge (k + 1)| *
        |factorialCriticalPrimeKernelWeight (((k + 1 : ℕ) : ℝ) + t)|
        ≤ kernelCellBudget * (2 / ((k + 1 : ℕ) : ℝ)^2) :=
      mul_le_mul (abs_factorialCriticalPrimeCumulativeCharge_le _) hγ
        (abs_nonneg _) kernel_cell_budget_nonneg
    _ = kernelCellMajorant k := by unfold kernelCellMajorant; ring

private theorem kernel_cell_term_continuous (k : ℕ) :
    ContinuousOn (fun t : ℝ => factorialCriticalPrimeCumulativeCharge (k + 1) *
      factorialCriticalPrimeKernelWeight (((k + 1 : ℕ) : ℝ) + t)) (Icc (0 : ℝ) 1) := by
  have hu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < ((k + 1 : ℕ) : ℝ) + t := by
    have hj : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => factorialCriticalPrimeCumulativeCharge (k + 1) *
      ((1 - Real.cos (2 * Real.pi * (((k + 1 : ℕ) : ℝ) + t) / 12)) /
        (((k + 1 : ℕ) : ℝ) + t)^2)) (Icc (0 : ℝ) 1) := by
    apply continuousOn_const.mul
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact ne_of_gt (sq_pos_of_pos (hu t ht))
  apply hcont.congr
  intro t ht
  dsimp only
  rw [factorialCriticalPrimeKernelWeight, Real.rpow_neg (hu t ht).le, Real.rpow_two]
  ring

/-- The native one-sided unit-cell series is continuous up to both endpoints. -/
theorem continuousOn_factorialCriticalPrimeCellKernel :
    ContinuousOn factorialCriticalPrimeCellKernel (Icc (0 : ℝ) 1) := by
  exact continuousOn_tsum kernel_cell_term_continuous kernel_cell_majorant_summable
    (fun k t ht => kernel_cell_term_bound k ht)

private theorem kernel_cell_summable {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun k : ℕ => factorialCriticalPrimeCumulativeCharge (k + 1) *
      factorialCriticalPrimeKernelWeight (((k + 1 : ℕ) : ℝ) + t)) :=
  kernel_cell_majorant_summable.of_norm_bounded (fun k => kernel_cell_term_bound k ht)

private theorem kernel_cell_floor {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (j : ℕ) :
    ⌊(j : ℝ) + t⌋₊ = j := by
  have hu : 0 ≤ (j : ℝ) + t := by positivity
  have hlo : j ≤ ⌊(j : ℝ) + t⌋₊ := (Nat.le_floor_iff hu).mpr (by linarith)
  have hup : (⌊(j : ℝ) + t⌋₊ : ℝ) < (j : ℝ) + 1 :=
    (Nat.floor_le hu).trans_lt (by linarith)
  have hupN : ⌊(j : ℝ) + t⌋₊ < j + 1 := by exact_mod_cast hup
  omega

/-- Away from integer endpoints, the native L1 periodization is its continuous cell branch. -/
theorem factorialCriticalPrimePeriodizedKernel_eq_cell {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    factorialCriticalPrimePeriodizedKernel t = factorialCriticalPrimeCellKernel t := by
  let f : ℤ → ℝ := fun z => factorialCriticalPrimeKernelDensity (t + z)
  have hterm (n : ℕ) : f ((n + 1 : ℕ) : ℤ) =
      factorialCriticalPrimeCumulativeCharge (n + 1) *
        factorialCriticalPrimeKernelWeight (((n + 1 : ℕ) : ℝ) + t) := by
    change factorialCriticalPrimeKernelDensity (t + ((n + 1 : ℕ) : ℝ)) = _
    rw [add_comm t _, factorialCriticalPrimeKernelDensity, kernel_cell_floor ht ht1]
    ring
  have hzero : f 0 = 0 := by
    have hf0 : ⌊t⌋₊ = 0 := by simpa only [Nat.cast_zero, zero_add] using kernel_cell_floor ht ht1 0
    simp [f, factorialCriticalPrimeKernelDensity, hf0, factorialCriticalPrimeCumulativeCharge]
  have hneg (n : ℕ) : f (-((n : ℤ) + 1)) = 0 := by
    have hu : t + (-((n : ℝ) + 1)) ≤ 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      factorialCriticalPrimeKernelDensity, Nat.floor_of_nonpos hu]
    simp [factorialCriticalPrimeCumulativeCharge]
  have hpostail : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)) :=
    (kernel_cell_summable ⟨ht.le, ht1.le⟩).congr (fun n => (hterm n).symm)
  have hpos : Summable (fun n : ℕ => f (n : ℤ)) := (summable_nat_add_iff 1).mp hpostail
  have hnegative : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    simp only [hneg]
    exact summable_zero
  change (∑' z : ℤ, f z) = _
  rw [tsum_of_nat_of_neg_add_one hpos hnegative]
  simp_rw [hneg]
  rw [tsum_zero, add_zero, ← hpos.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, Int.natCast_zero, hzero, zero_add]
  exact tsum_congr hterm

/-- The endpoint-correct continuous real kernel on the closed unit cell. -/
def factorialCriticalPrimeContinuousRealKernel (t : ℝ) : ℝ :=
  (factorialCriticalPrimeCellKernel t + factorialCriticalPrimeCellKernel (1 - t)) / 2

/-- Reflection produces a continuous real kernel on the closed unit cell. -/
theorem continuousOn_factorialCriticalPrimeContinuousRealKernel :
    ContinuousOn factorialCriticalPrimeContinuousRealKernel (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div_const
  apply continuousOn_factorialCriticalPrimeCellKernel.add
  apply continuousOn_factorialCriticalPrimeCellKernel.comp (by fun_prop)
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

/-- The continuous representative has matching endpoint values. -/
theorem factorialCriticalPrimeContinuousRealKernel_endpoints :
    factorialCriticalPrimeContinuousRealKernel 0 = factorialCriticalPrimeContinuousRealKernel 1 := by
  simp only [factorialCriticalPrimeContinuousRealKernel, sub_zero, sub_self]
  ring

/-- The continuous representative agrees with the real L1 kernel throughout the open cell. -/
theorem factorialCriticalPrimeRealKernel_eq_continuous {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    factorialCriticalPrimeRealKernel t = factorialCriticalPrimeContinuousRealKernel t := by
  unfold factorialCriticalPrimeRealKernel factorialCriticalPrimeContinuousRealKernel
  rw [factorialCriticalPrimePeriodizedKernel_eq_cell ht ht1,
    factorialCriticalPrimePeriodizedKernel_eq_cell (by linarith : 0 < 1 - t) (by linarith : 1 - t < 1)]

/-- The exact complete prime form is represented by the continuous real unit-cell kernel. -/
theorem factorialCriticalTranslatedPrimeLimit_eq_continuous_kernel_integral
    (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit S b = (4 / Real.pi^4) *
      ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t *
        factorialCriticalPatternDensity S b t := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_real_kernel_integral,
    intervalIntegral.integral_of_le zero_le_one]
  congr 1
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [factorialCriticalPrimeRealKernel_eq_continuous ht.1 ht.2]

end GaloisForLFunctions.ArithmeticPositivityTheory
