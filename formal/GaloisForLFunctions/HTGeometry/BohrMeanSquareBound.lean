import GaloisForLFunctions.HTGeometry.BohrCoefficientBound

/-!
# Two bounds on mean squares

The mean square of a bounded function is at most the square of its sup norm, and the mean square of
the spectral partial sum is at most the mean square of the function — the latter being Bessel's
inequality read through the mean square of a trigonometric polynomial.

Both are needed to turn a mean-square approximation into a bound on the coefficients of a product.
-/

open MeasureTheory ComplexConjugate

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- The mean square is at most the squared sup norm. -/
theorem bohrMean_mul_conj_re_le_norm_sq {f : ℝ →ᵇ ℂ}
    (hap : IsBohrAlmostPeriodic (fun x => f x)) :
    (bohrMean (fun t => f t * conj (f t))).re ≤ ‖f‖ ^ 2 := by
  have hcont : Continuous (fun x => f x) := f.continuous
  have hc : Continuous fun t : ℝ => (f : ℝ → ℂ) t * conj ((f : ℝ → ℂ) t) :=
    hcont.mul (Complex.continuous_conj.comp hcont)
  have ha : IsBohrAlmostPeriodic fun t : ℝ => (f : ℝ → ℂ) t * conj ((f : ℝ → ℂ) t) :=
    isBohrAlmostPeriodic_mul hcont hap (Complex.continuous_conj.comp hcont)
      (isBohrAlmostPeriodic_conj hap)
  refine le_trans (Complex.re_le_norm _) ?_
  refine norm_bohrMean_le hc ha fun t => ?_
  rw [norm_mul, RCLike.norm_conj, ← pow_two]
  exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm t) 2

/-- **Bessel's inequality in mean-square form.**  The spectral partial sum has mean square at most
that of the function. -/
theorem bohrMean_trigPoly_mul_conj_self_re_le {f : ℝ →ᵇ ℂ}
    (hap : IsBohrAlmostPeriodic (fun x => f x)) (S : Finset ℝ) :
    (bohrMean (fun t => trigPoly S (bohrCoefficient (fun x => f x)) t *
      conj (trigPoly S (bohrCoefficient (fun x => f x)) t))).re
      ≤ (bohrMean (fun t => f t * conj (f t))).re := by
  have hval := bohrMean_trigPoly_mul_conj_self S (bohrCoefficient (fun x => f x))
  rw [hval, Complex.re_sum]
  have hterm : ∀ lam ∈ S, (bohrCoefficient (fun x => f x) lam *
      conj (bohrCoefficient (fun x => f x) lam)).re
      = ‖bohrCoefficient (fun x => f x) lam‖ ^ 2 := by
    intro lam _
    rw [Complex.mul_conj']
    norm_cast
  rw [Finset.sum_congr rfl hterm]
  exact bohr_bessel f.continuous hap S

end

end GaloisForLFunctions
