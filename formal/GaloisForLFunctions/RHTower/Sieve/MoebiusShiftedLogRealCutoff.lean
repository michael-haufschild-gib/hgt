import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff

/-!
# Affine shifts of the real-cutoff logarithmic Möbius kernels

Layer-cake truncation replaces `log(X/d)` by `t + log(Y/d)`, where `Y = X exp(-t)`.
The linear and quadratic shifted sums below reduce exactly to the existing unshifted kernels and
the Möbius harmonic boundary.  No new analytic estimate is introduced.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Linear logarithmic Möbius kernel after an affine logarithmic shift. -/
def moebiusShiftedLogKernelReal (t Y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
    ((moebius d : ℤ) : ℝ) / (d : ℝ) *
      (t + Real.log (Y / (d : ℝ)))

/-- Quadratic logarithmic Möbius kernel after an affine logarithmic shift. -/
def moebiusShiftedLogSqKernelReal (t Y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
    ((moebius d : ℤ) : ℝ) / (d : ℝ) *
      (t + Real.log (Y / (d : ℝ))) ^ 2

/-- Exact affine-shift identity for the linear logarithmic Möbius kernel. -/
theorem moebiusShiftedLogKernelReal_eq
    (t Y : ℝ) :
    moebiusShiftedLogKernelReal t Y =
      coprimeLogMoebius 1 Y +
        t * RHTower.deningerHarmonicPartial ⌊Y⌋₊ := by
  have hpartial : RHTower.deningerHarmonicPartial ⌊Y⌋₊ =
      ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
        ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [RHTower.deningerHarmonicPartial, Finset.sum_range_succ']
    simp
    convert RHTower.sum_range_succ_eq_sum_Icc
      (fun d : ℕ => ((moebius d : ℤ) : ℝ) / (d : ℝ)) ⌊Y⌋₊ using 1
    all_goals push_cast
    all_goals ring
  rw [moebiusShiftedLogKernelReal, coprimeLogMoebius,
    Finset.filter_true_of_mem (fun d _ => Nat.coprime_one_left d),
    hpartial, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Exact affine-shift identity for the quadratic logarithmic Möbius kernel. -/
theorem moebiusShiftedLogSqKernelReal_eq
    (t Y : ℝ) :
    moebiusShiftedLogSqKernelReal t Y =
      moebiusDoubleLogKernelReal Y + 2 * t * coprimeLogMoebius 1 Y +
        t ^ 2 * RHTower.deningerHarmonicPartial ⌊Y⌋₊ := by
  have hpartial : RHTower.deningerHarmonicPartial ⌊Y⌋₊ =
      ∑ d ∈ Finset.Icc 1 ⌊Y⌋₊,
        ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [RHTower.deningerHarmonicPartial, Finset.sum_range_succ']
    simp
    convert RHTower.sum_range_succ_eq_sum_Icc
      (fun d : ℕ => ((moebius d : ℤ) : ℝ) / (d : ℝ)) ⌊Y⌋₊ using 1
    all_goals push_cast
    all_goals ring
  rw [moebiusShiftedLogSqKernelReal, moebiusDoubleLogKernelReal,
    coprimeLogMoebius,
    Finset.filter_true_of_mem (fun d _ => Nat.coprime_one_left d),
    hpartial, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end

end RHTower.Sieve
