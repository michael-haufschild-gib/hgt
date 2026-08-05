import GaloisForLFunctions.RHTower.Sieve.WeylDifferencing

/-!
# Autocorrelations of smooth phases

The `h`-shifted autocorrelation of the phase sequence `n ↦ e(g(x₀+n))` is the exponential
sum of the difference phase `x ↦ g(x+h) − g(x)` over the truncated range.  This is the
bridge between the Weyl–van der Corput inequality and the iterated derivative tests: a
correlation of a smooth phase is again a smooth phase, one derivative order down.
-/

namespace RHTower.Sieve

/-- Phases multiply against conjugate phases by phase subtraction. -/
theorem exp_mul_conj_exp (y z : ℝ) :
    Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)
      * (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * z : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((2 * Real.pi * (y - z) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The shifted autocorrelation of a smooth phase is the exponential sum of the
difference phase. -/
theorem weylCorr_phase (g : ℝ → ℝ) (x₀ : ℝ) (N h : ℕ) :
    weylCorr (fun n => Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)) N h
      = ∑ n ∈ Finset.range (N - h),
          Complex.exp (((2 * Real.pi * (g (x₀ + n + h) - g (x₀ + n)) : ℝ) : ℂ)
            * Complex.I) := by
  simp only [weylCorr]
  refine Finset.sum_congr rfl fun n _ => ?_
  have harg : x₀ + ((n + h : ℕ) : ℝ) = x₀ + (n : ℝ) + (h : ℝ) := by push_cast; ring
  rw [harg, exp_mul_conj_exp]

/-- Trivial bound for a shifted autocorrelation of bounded coefficients. -/
theorem norm_weylCorr_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (N h : ℕ) :
    ‖weylCorr a N h‖ ≤ (N : ℝ) := by
  rw [weylCorr]
  refine le_trans (norm_sum_le _ _) ?_
  have hpt : ∀ n ∈ Finset.range (N - h), ‖a (n + h) * (starRingEnd ℂ) (a n)‖ ≤ 1 := by
    intro n _
    rw [norm_mul, RCLike.norm_conj]
    have h1 := ha (n + h)
    have h2 := ha n
    nlinarith [norm_nonneg (a (n + h)), norm_nonneg (a n)]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact_mod_cast Nat.sub_le N h

/-- Trivial bound for a phase sum. -/
theorem norm_phase_sum_le_card (g : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ ≤ (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hpt : ∀ n ∈ Finset.range N,
      ‖Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 :=
    fun n _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

end RHTower.Sieve
