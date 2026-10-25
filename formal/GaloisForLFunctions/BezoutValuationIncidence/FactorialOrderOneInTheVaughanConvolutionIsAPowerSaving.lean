import GaloisForLFunctions.HTGeometry.FactorialLogarithmicBoundsArePowerBounds
import GaloisForLFunctions.BezoutValuationIncidence.UniformVaughanPowerBoundsAreFixedStrips

/-!
A common-threshold factorial logarithmic envelope for the actual Vaughan
convolution error is equivalent to a uniform power saving. The actual
power-rate criterion identifies both properties with a fixed zero-free strip.
-/

open Filter RHTower
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A common-threshold factorial logarithmic envelope for the actual Vaughan error is a power saving. -/
theorem uniform_pmUndampedVaughan_factorial_bounds_iff_power_bound :
    (∃ A C : ℝ, 0 < A ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V q : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| * Real.log (n : ℝ) ^ q ≤
          C * A ^ q * (q.factorial : ℝ) * n) ↔
    (∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
          C * (n : ℝ) ^ (1 - η)) := by
  let f : (ℕ × ℕ) → ℕ → ℝ := fun a n =>
    (pmUndampedVaughanConvolutionPrefix a.1 a.2 n -
      (n : ℝ) * deningerHarmonicPartial a.1 * deningerHarmonicPartial a.2) / n
  constructor
  · rintro ⟨A, C, hA, hC, h⟩
    have hfactorial : ∃ A C : ℝ, 0 < A ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
        ∀ i : ℕ × ℕ, ∀ q : ℕ,
        |f i n| * Real.log (n : ℝ) ^ q ≤ C * A ^ q * (q.factorial : ℝ) := by
      refine ⟨A, C, hA, hC, ?_⟩
      filter_upwards [h, eventually_ge_atTop 1] with n hn hn1 a q
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      dsimp only [f]
      rw [abs_div, abs_of_pos hn0, div_mul_eq_mul_div]
      exact (div_le_iff₀ hn0).mpr (hn a.1 a.2 q)
    obtain ⟨η, K, hη, hK, hbound⟩ :=
      (HTGeometry.uniform_log_factorial_bounds_iff_power_bound f).mp hfactorial
    refine ⟨η, K, hη, hK, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1 U V
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h := hn (U, V)
    dsimp only [f] at h
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0] at h
    refine h.trans_eq ?_
    rw [show 1 - η = -η + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    ring
  · rintro ⟨η, C, hη, hC, h⟩
    refine ⟨1 / η, C, by positivity, hC, ?_⟩
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1 U V q
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hratio : |f (U, V) n| ≤ C * (n : ℝ) ^ (-η) := by
      dsimp only [f]
      rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
      refine (hn U V).trans_eq ?_
      rw [show 1 - η = -η + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
      ring
    have hlog := HTGeometry.log_factorial_bound_of_abs_le_rpow
      (by exact_mod_cast hn1) hC hη hratio q
    dsimp only [f] at hlog
    rw [abs_div, abs_of_pos hn0, div_mul_eq_mul_div, div_le_iff₀ hn0] at hlog
    exact hlog

/-- Factorial order one at a common threshold in the actual Vaughan error is exactly a fixed strip. -/
theorem zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_factorial_bounds :
    zetaZeroAbscissa < 1 ↔
      ∃ A C : ℝ, 0 < A ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V q : ℕ,
        |pmUndampedVaughanConvolutionPrefix U V n -
          (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| * Real.log (n : ℝ) ^ q ≤
            C * A ^ q * (q.factorial : ℝ) * n :=
  zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power.trans
    uniform_pmUndampedVaughan_factorial_bounds_iff_power_bound.symm

#print axioms uniform_pmUndampedVaughan_factorial_bounds_iff_power_bound
#print axioms zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_factorial_bounds
end GaloisForLFunctions.BezoutValuationIncidence
