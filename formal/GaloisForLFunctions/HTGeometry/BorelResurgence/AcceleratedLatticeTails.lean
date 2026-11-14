import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration
import GaloisForLFunctions.HTGeometry.GaussianLatticeTheta
import Mathlib.Analysis.PSeries

/-!
# The harmonic boundary of accelerated Gaussian lattice tails

Each fixed positive Gaussian bandwidth has a summable lattice theta series. Integrating that
bandwidth against the acceleration kernel changes its lattice tail to inverse-square-root
decay. Exact two-sided harmonic bounds quantify the resulting loss of summability and control
every finite lattice window.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Accelerated Gaussian weight at a nonzero point of the positive integer lattice. -/
def acceleratedLatticeTerm (s : ℝ) (n : ℕ) : ℝ :=
  gaussianAcceleration
    (fun x => RiemannGaussian.translatedGaussian (((n : ℝ) + 1) ^ 2) 0 x) (Real.exp s)

theorem acceleratedLatticeTerm_eq (s : ℝ) (n : ℕ) :
    acceleratedLatticeTerm s n =
      (Real.sqrt (1 + 4 * Real.exp s * ((n : ℝ) + 1) ^ 2))⁻¹ :=
  gaussianAcceleration_gaussian s ((n : ℝ) + 1)

/-- Uniform harmonic bounds identify the exact decay order of the accelerated lattice. -/
theorem acceleratedLatticeTerm_harmonic_bounds (s : ℝ) (n : ℕ) :
    (Real.sqrt (1 + 4 * Real.exp s))⁻¹ / ((n : ℝ) + 1) ≤
        acceleratedLatticeTerm s n ∧
      acceleratedLatticeTerm s n ≤
        (Real.sqrt (4 * Real.exp s))⁻¹ / ((n : ℝ) + 1) := by
  rw [acceleratedLatticeTerm_eq]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hn1 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  have hlo : Real.sqrt (4 * Real.exp s) * ((n : ℝ) + 1) ≤
      Real.sqrt (1 + 4 * Real.exp s * ((n : ℝ) + 1) ^ 2) := by
    rw [← Real.sqrt_sq hn.le, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hhi : Real.sqrt (1 + 4 * Real.exp s * ((n : ℝ) + 1) ^ 2) ≤
      Real.sqrt (1 + 4 * Real.exp s) * ((n : ℝ) + 1) := by
    rw [← Real.sqrt_sq hn.le, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith only [hn1]
  constructor
  · rw [div_eq_mul_inv, ← mul_inv_rev]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr hhi
  · rw [div_eq_mul_inv, ← mul_inv_rev]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr hlo

/-- Every finite accelerated lattice window lies between explicit multiples of its harmonic mass. -/
theorem acceleratedLatticeWindow_harmonic_bounds (s : ℝ) (S : Finset ℕ) :
    (Real.sqrt (1 + 4 * Real.exp s))⁻¹ * ∑ n ∈ S, 1 / ((n : ℝ) + 1) ≤
        ∑ n ∈ S, acceleratedLatticeTerm s n ∧
      (∑ n ∈ S, acceleratedLatticeTerm s n) ≤
        (Real.sqrt (4 * Real.exp s))⁻¹ * ∑ n ∈ S, 1 / ((n : ℝ) + 1) := by
  simp only [Finset.mul_sum, mul_one_div]
  exact ⟨Finset.sum_le_sum fun n _ => (acceleratedLatticeTerm_harmonic_bounds s n).1,
    Finset.sum_le_sum fun n _ => (acceleratedLatticeTerm_harmonic_bounds s n).2⟩

/-- Bandwidth acceleration destroys Gaussian lattice summability: the exact surviving tail is harmonic. -/
theorem not_summable_acceleratedLatticeTerm (s : ℝ) :
    ¬ Summable (acceleratedLatticeTerm s) := by
  intro h
  have hl : Summable (fun n : ℕ =>
      (Real.sqrt (1 + 4 * Real.exp s))⁻¹ * (1 / ((n : ℝ) + 1))) :=
    h.of_nonneg_of_le (fun n => by positivity)
      (fun n => by simpa only [mul_one_div] using
        (acceleratedLatticeTerm_harmonic_bounds s n).1)
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) :=
    (summable_mul_left_iff (by positivity :
      (Real.sqrt (1 + 4 * Real.exp s))⁻¹ ≠ 0)).mp hl
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using hh)

end

end GaloisForLFunctions.HTGeometry
