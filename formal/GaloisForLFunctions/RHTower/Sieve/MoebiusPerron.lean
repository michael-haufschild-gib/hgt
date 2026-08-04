import GaloisForLFunctions.RHTower.Sieve.ZeroFreeCombination
import GaloisForLFunctions.HTGeometry.SmoothWeightPerron

/-!
# The smoothed Möbius sum, bounded by the reciprocal of zeta

The corpus's smoothed Perron formula turns a smoothed sum with unit-bounded coefficients into a
vertical integral of the Dirichlet series.  For `μ` the Dirichlet series is `1/ζ`, and the zero-free
machinery bounds it uniformly in the height, so the smoothed Möbius sum is controlled by the mass of
the Mellin transform of the cutoff:

`‖∑' μ(n)·w(n)‖ ≤ e^{11/2}(1 + 1/(σ−1))·∫‖mellin w(σ+iy)‖ dy / 2π`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The Perron series is the `L`-series. -/
theorem tsum_cpow_neg_eq_LSeries {a : ℕ → ℂ} (ha0 : a 0 = 0) (s : ℂ) :
    (∑' n : ℕ, a n * (n : ℂ) ^ (-s)) = LSeries a s := by
  rw [LSeries]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ha0, zero_mul, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, ← div_eq_mul_inv]

/-- **The smoothed Möbius sum, bounded.**  The Perron formula against the uniform `1/ζ` bound. -/
theorem norm_tsum_moebius_smoothWeight_le {N H σ : ℝ} (hN : 0 < N) (hH : 0 < H) (hσ : 1 < σ) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1))
          * ∫ y : ℝ, ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := by
  have ha : ∀ n : ℕ, ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    intro n
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have ha0 : (ArithmeticFunction.moebius 0 : ℂ) = 0 := by simp
  have hperron := tsum_mul_smoothWeight_eq_integral
    (a := fun n => (ArithmeticFunction.moebius n : ℂ)) ha ha0 hN hH hσ
  rw [hperron]
  have hpt : ∀ y : ℝ,
      ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
            * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I)))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1))
          * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := by
    intro y
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [tsum_cpow_neg_eq_LSeries ha0]
    exact norm_LSeries_moebius_le_uniform hσ
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hInt : Integrable (fun y : ℝ =>
      Real.exp (22 / 4) * (1 + 1 / (σ - 1))
        * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I)‖) :=
    ((verticalIntegrable_mellin_smoothWeight hN hH (by linarith)).norm).const_mul _
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    hInt (Filter.Eventually.of_forall hpt)) ?_
  rw [integral_const_mul]

end RHTower.Sieve
