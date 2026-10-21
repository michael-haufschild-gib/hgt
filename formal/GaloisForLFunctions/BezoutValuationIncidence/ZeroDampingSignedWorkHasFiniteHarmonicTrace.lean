import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver
import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# The zero-damping signed work has a finite harmonic trace

At each fixed horizon, the complete source–tangent pairing tends to the harmonic
Chebyshev-error pairing as damping decreases to zero. The latter is absolutely
summable and has total work `-4γ`, by the existing Mertens Abel-tail evaluation.

The limits are ordered: first damping at a fixed horizon, then the horizon.
No infinite-horizon energy derivative or positive-damping work bound is asserted.
-/

open Finset Filter Topology RHTower ArithmeticFunction
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The complete finite-horizon source–tangent work, with centering retained. -/
def pmPowerDampedSignedWork (ε : ℝ) (T : ℕ) : ℝ :=
  2 * ∑ n ∈ Icc 1 T,
    pmPowerDampedCenteredDivisorPrefix ε n * dampedChebyshevError ε n /
      ((n : ℝ) * ((n : ℝ) + 1))

/-- The finite-horizon zero-damping trace; this uses the right limit of the source. -/
def zeroDampingSignedWork (T : ℕ) : ℝ :=
  2 * ∑ n ∈ Icc 1 T,
    (∑ k ∈ Icc 1 n, vonMangoldt k - (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1))

/-- Damping is sent to zero before varying the horizon. -/
theorem tendsto_pmPowerDampedSignedWork_zero (T : ℕ) :
    Tendsto (fun ε => pmPowerDampedSignedWork ε T) (𝓝[>] 0)
      (𝓝 (zeroDampingSignedWork T)) := by
  unfold pmPowerDampedSignedWork zeroDampingSignedWork
  simpa only [one_mul] using
    (tendsto_finsetSum (Icc 1 T) fun n hn =>
      ((tendsto_pmPowerDampedCenteredDivisorPrefix_zero (mem_Icc.mp hn).1).mul
        (tendsto_dampedChebyshevError_zero n)).div_const
          ((n : ℝ) * ((n : ℝ) + 1))).const_mul 2

/-- The complete zero-damping work is absolutely summable, with total `-4γ`. -/
theorem hasSum_zeroDampingSignedWork :
    HasSum (fun n : ℕ =>
      2 * ((∑ k ∈ Icc 1 (n + 1), vonMangoldt k - ((n + 1 : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))))
      (-4 * Real.eulerMascheroniConstant) := by
  have h := summable_psiError_increment.hasSum
  change HasSum (fun k : ℕ =>
    psiError k * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))) mertensAbelTail at h
  rw [mertensAbelTail_eq] at h
  have hterm (n : ℕ) :
      2 * ((∑ k ∈ Icc 1 (n + 1), vonMangoldt k - ((n + 1 : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) =
      2 * (psiError n * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2))) := by
    rw [psiError_eq, sum_Icc_eq_sum_range_shift]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h1, h2]
    ring
  have hsum := (h.mul_left (2 : ℝ)).congr_fun hterm
  have hconstant : 2 * (-2 * Real.eulerMascheroniConstant) =
      -4 * Real.eulerMascheroniConstant := by ring
  rw [hconstant] at hsum
  exact hsum

/-- Absolute convergence is part of the trace, rather than a conditional regrouping. -/
theorem summable_abs_zeroDampingSignedWork :
    Summable (fun n : ℕ =>
      |2 * ((∑ k ∈ Icc 1 (n + 1), vonMangoldt k - ((n + 1 : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)))|) := by
  simpa only [Real.norm_eq_abs] using hasSum_zeroDampingSignedWork.summable.norm

/-- The horizon limit is taken only after forming the zero-damping trace. -/
theorem tendsto_zeroDampingSignedWork :
    Tendsto zeroDampingSignedWork atTop (𝓝 (-4 * Real.eulerMascheroniConstant)) := by
  refine hasSum_zeroDampingSignedWork.tendsto_sum_nat.congr fun T => ?_
  rw [zeroDampingSignedWork, sum_Icc_eq_sum_range_shift, mul_sum]

/-- The two limits are supplied in their valid order; they are not interchanged. -/
theorem zeroDampingSignedWork_iterated_limits :
    (∀ T : ℕ, Tendsto (fun ε => pmPowerDampedSignedWork ε T) (𝓝[>] 0)
      (𝓝 (zeroDampingSignedWork T))) ∧
      Tendsto zeroDampingSignedWork atTop (𝓝 (-4 * Real.eulerMascheroniConstant)) :=
  ⟨tendsto_pmPowerDampedSignedWork_zero, tendsto_zeroDampingSignedWork⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
