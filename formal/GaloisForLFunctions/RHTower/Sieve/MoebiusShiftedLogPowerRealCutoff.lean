import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogRealCutoff
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogPowerRealCutoff

/-!
# Arbitrary shifted logarithmic Möbius kernels

Minimum-logarithmic Selberg forms introduce an affine shift in every logarithmic Möbius
kernel.  This file packages all powers in one definition and proves the exact finite binomial
expansion into the existing unshifted kernels.  The former linear and quadratic definitions are
recovered exactly.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Logarithmic-power Möbius kernel after an affine logarithmic shift. -/
def moebiusShiftedLogPowerKernelReal (p : ℕ) (t Y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
    ((moebius d : ℤ) : ℝ) / (d : ℝ) *
      (t + Real.log (Y / (d : ℝ))) ^ p

/-- Exact binomial reduction of every shifted kernel to the existing unshifted log-power
kernels. -/
theorem moebiusShiftedLogPowerKernelReal_eq_sum
    (p : ℕ) (t Y : ℝ) :
    moebiusShiftedLogPowerKernelReal p t Y =
      ∑ q ∈ Finset.range (p + 1),
        (p.choose q : ℝ) * t ^ q *
          moebiusLogPowerKernelReal (p - q) Y := by
  simp only [moebiusShiftedLogPowerKernelReal, moebiusLogPowerKernelReal]
  calc
    (∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
        ((moebius d : ℤ) : ℝ) / (d : ℝ) *
          (t + Real.log (Y / (d : ℝ))) ^ p) =
      ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
        ∑ q ∈ Finset.range (p + 1),
          ((moebius d : ℤ) : ℝ) / (d : ℝ) *
            (t ^ q * Real.log (Y / (d : ℝ)) ^ (p - q) *
              (p.choose q : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [add_pow, Finset.mul_sum]
    _ = ∑ q ∈ Finset.range (p + 1),
        ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
          ((moebius d : ℤ) : ℝ) / (d : ℝ) *
            (t ^ q * Real.log (Y / (d : ℝ)) ^ (p - q) *
              (p.choose q : ℝ)) := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Finset.range (p + 1),
        (p.choose q : ℝ) * t ^ q *
          (∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
            ((moebius d : ℤ) : ℝ) / (d : ℝ) *
              Real.log (Y / (d : ℝ)) ^ (p - q)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- The generic degree-one shifted kernel is the existing linear kernel. -/
theorem moebiusShiftedLogPowerKernelReal_one (t Y : ℝ) :
    moebiusShiftedLogPowerKernelReal 1 t Y =
      moebiusShiftedLogKernelReal t Y := by
  simp [moebiusShiftedLogPowerKernelReal, moebiusShiftedLogKernelReal,
    pow_one]

/-- The generic degree-two shifted kernel is the existing quadratic kernel. -/
theorem moebiusShiftedLogPowerKernelReal_two (t Y : ℝ) :
    moebiusShiftedLogPowerKernelReal 2 t Y =
      moebiusShiftedLogSqKernelReal t Y := by
  simp [moebiusShiftedLogPowerKernelReal, moebiusShiftedLogSqKernelReal]

end

end RHTower.Sieve
