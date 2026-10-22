import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeStieltjesAutocorrelation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The growing half-density reads the unnormalized Chebyshev error

The critical Mellin Stieltjes carrier is normally tested against bounded Fourier phases or the
constant function.  The Poisson-center cross term instead produces the growing test
`exp(h/2)`.  On every finite aperture this test cancels the square-root weight at each von
Mangoldt atom.  The resulting cumulative value is exactly

`h - 1 - (Psi(exp h) - exp h)`.

This identity is the source bridge needed to keep the Poisson center coupled to the polar--prime
carrier.  It is unconditional and contains no zero location, Weil positivity, or RH hypothesis.
-/

open scoped BigOperators
open Real MeasureTheory Set Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- The critical square-root atom becomes the ordinary von Mangoldt atom after multiplication by
the growing half-density at its logarithmic location. -/
lemma criticalMellinAtomWeight_mul_exp_log_half
    {k : ℕ} (hk : 0 < k) :
    criticalMellinAtomWeight k * Real.exp (Real.log k / 2) =
      ArithmeticFunction.vonMangoldt k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [criticalMellinAtomWeight]
  have hexp : Real.exp (Real.log k / 2) = (k : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hkR]
    congr 1
    ring
  rw [hexp]
  calc
    (k : ℝ) ^ (-1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt k *
        (k : ℝ) ^ (1 / 2 : ℝ) =
      ((k : ℝ) ^ (-1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ)) *
        ArithmeticFunction.vonMangoldt k := by ring_nf
    _ = (k : ℝ) ^ ((-1 / 2 : ℝ) + (1 / 2 : ℝ)) *
        ArithmeticFunction.vonMangoldt k := by rw [Real.rpow_add hkR]
    _ = ArithmeticFunction.vonMangoldt k := by norm_num

/-- The growing half-density test of the finite critical Mellin carrier. -/
def criticalMellinGrowingCumulative (a : ℝ) : ℝ :=
  (∫ h in Set.Ioc (0 : ℝ) (2 * a),
      Real.exp (h / 2) * (2 * Real.cosh (h / 2))) -
    ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
      criticalMellinAtomWeight k * Real.exp (Real.log k / 2)

/-- The growing cumulative is the continuous exponential-plus-constant mass minus the ordinary
Chebyshev cumulative sum. -/
theorem criticalMellinGrowingCumulative_eq
    {a : ℝ} (ha : 0 ≤ a) :
    criticalMellinGrowingCumulative a =
      Real.exp (2 * a) - 1 + 2 * a -
        criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k)
          (Real.exp (2 * a)) := by
  have h2a : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha
  have hint :
      (∫ h in Set.Ioc (0 : ℝ) (2 * a),
        Real.exp (h / 2) * (2 * Real.cosh (h / 2))) =
          Real.exp (2 * a) - 1 + 2 * a := by
    rw [← intervalIntegral.integral_of_le h2a]
    have hfun :
        (fun h : ℝ => Real.exp (h / 2) * (2 * Real.cosh (h / 2))) =
          fun h => Real.exp h + 1 := by
      funext h
      rw [Real.cosh_eq]
      calc
        Real.exp (h / 2) *
            (2 * ((Real.exp (h / 2) + Real.exp (-(h / 2))) / 2)) =
            Real.exp (h / 2) * Real.exp (h / 2) +
              Real.exp (h / 2) * Real.exp (-(h / 2)) := by ring
        _ = Real.exp h + Real.exp 0 := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2 <;> ring
        _ = Real.exp h + 1 := by simp
    rw [hfun]
    rw [intervalIntegral.integral_add
      (Real.continuous_exp.intervalIntegrable 0 (2 * a))
      intervalIntegrable_const]
    rw [integral_exp, intervalIntegral.integral_const]
    simp
  have hsum :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        criticalMellinAtomWeight k * Real.exp (Real.log k / 2)) =
        criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k)
          (Real.exp (2 * a)) := by
    rw [criticalCumulative]
    let N : ℕ := ⌊Real.exp (2 * a)⌋₊
    have hsub : Finset.Icc 2 N ⊆ Finset.Icc 0 N := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    calc
      (∑ k ∈ Finset.Icc 2 N,
          criticalMellinAtomWeight k * Real.exp (Real.log k / 2)) =
          ∑ k ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact criticalMellinAtomWeight_mul_exp_log_half (by
          simp only [Finset.mem_Icc] at hk
          omega)
      _ = ∑ k ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt k := by
        apply Finset.sum_subset hsub
        intro k hk hnot
        simp only [Finset.mem_Icc] at hk
        have hklt : k < 2 := Nat.lt_of_not_ge fun hk2 =>
          hnot (Finset.mem_Icc.mpr ⟨hk2, hk.2⟩)
        interval_cases k <;> simp
  rw [criticalMellinGrowingCumulative, hint, hsum]

/-- In logarithmic coordinates the growing cumulative is exactly `h - 1` minus the
unnormalized Chebyshev error. -/
theorem criticalMellinGrowingCumulative_eq_chebyshevError
    {a : ℝ} (ha : 0 ≤ a) :
    criticalMellinGrowingCumulative a =
      2 * a - 1 -
        criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k)
          (Real.exp (2 * a)) := by
  rw [criticalMellinGrowingCumulative_eq ha, criticalMellinError]
  ring

/-- The real growing cumulative is literally the existing complex Stieltjes carrier evaluated on
the growing half-density. -/
theorem criticalMellinStieltjesPairing_exp_half_eq
    (a : ℝ) :
    criticalMellinStieltjesPairing a
      (fun h => (Real.exp (h / 2) : ℂ)) =
        (criticalMellinGrowingCumulative a : ℂ) := by
  rw [criticalMellinStieltjesPairing, criticalMellinGrowingCumulative]
  have hint :
      (∫ h in Set.Ioc (0 : ℝ) (2 * a),
        (Real.exp (h / 2) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)) =
      ((∫ h in Set.Ioc (0 : ℝ) (2 * a),
        Real.exp (h / 2) * (2 * Real.cosh (h / 2))) : ℂ) := by
    rfl
  have hsum :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) *
          (Real.exp (Real.log k / 2) : ℂ)) =
      ((∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        criticalMellinAtomWeight k * Real.exp (Real.log k / 2)) : ℂ) := by
    rfl
  rw [hint, hsum]
  norm_cast

end RHTower
