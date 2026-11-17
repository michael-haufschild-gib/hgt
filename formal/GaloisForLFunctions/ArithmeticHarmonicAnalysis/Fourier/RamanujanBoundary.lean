import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Fourier.DivisibilityHarmonics
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-!
# Fourier boundary values of Ramanujan lag coefficients

The divisor expansion of a Ramanujan coefficient cancels the reciprocal scale
introduced by decimation. Its harmonic sine series is a finite integer Möbius
combination of dilated sawtooths, at every phase including rational resonances.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset Filter Topology
open BezoutValuationIncidence

noncomputable section

/-- The existing Ramanujan lag coefficient is a finite divisibility filter. -/
theorem ramanujanLagCoefficient_eq_divisorFilter (q n : ℕ) :
    ramanujanLagCoefficient q n =
      divisorFilter q.divisors (fun d => BezoutValuationIncidence.moebiusReal (q / d) * d) n := by
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp only [mul_zero]

/-- Exact finite decimation of the Ramanujan-weighted sine sum. -/
theorem sum_ramanujan_harmonicSine (q N : ℕ) (x : ℝ) :
    (∑ n ∈ Icc 1 N, ramanujanLagCoefficient q n *
      (Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ))) =
      ∑ d ∈ q.divisors, BezoutValuationIncidence.moebiusReal (q / d) *
        harmonicSine (N / d + 1) ((d : ℝ) * x) := by
  simp_rw [ramanujanLagCoefficient_eq_divisorFilter]
  rw [sum_divisorFilter_harmonicSine _ _ (fun _ hd => Nat.pos_of_mem_divisors hd)]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [mul_div_cancel_right₀ _ hd0]

/-- Ramanujan harmonic sine sums converge to an explicit finite sawtooth transform. -/
theorem tendsto_ramanujan_harmonicSine (q : ℕ) (x : ℝ) :
    Tendsto (fun N => ∑ n ∈ Icc 1 N, ramanujanLagCoefficient q n *
      (Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ))) atTop
      (𝓝 (-Real.pi * ∑ d ∈ q.divisors,
        BezoutValuationIncidence.moebiusReal (q / d) * sawtooth ((d : ℝ) * x))) := by
  have h := tendsto_divisorFilter_harmonicSine q.divisors
    (fun d => BezoutValuationIncidence.moebiusReal (q / d) * d)
    (fun _ hd => Nat.pos_of_mem_divisors hd) x
  have hvalue : (∑ d ∈ q.divisors,
      BezoutValuationIncidence.moebiusReal (q / d) * d / d * sawtooth ((d : ℝ) * x)) =
      ∑ d ∈ q.divisors, BezoutValuationIncidence.moebiusReal (q / d) * sawtooth ((d : ℝ) * x) := by
    apply sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [mul_div_cancel_right₀ _ hd0]
  rw [hvalue] at h
  simpa only [ramanujanLagCoefficient_eq_divisorFilter] using h

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.sum_ramanujan_harmonicSine
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.tendsto_ramanujan_harmonicSine
