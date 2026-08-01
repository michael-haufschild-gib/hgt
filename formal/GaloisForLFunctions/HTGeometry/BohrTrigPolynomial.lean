import GaloisForLFunctions.HTGeometry.BohrUniqueness

/-!
# Bohr coefficients of a trigonometric polynomial

The Bohr coefficient of `∑ a i e^{iμ_i t}` at a frequency `λ` is the sum of the `a i` over the
indices with `μ_i = λ`: the characters are orthonormal for the Bohr mean.

This is the bookkeeping lemma behind both Parseval and the spectral product rule, where a function
is replaced by a trigonometric approximant and the coefficients of the approximant have to be read
off.
-/

open MeasureTheory

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- **The Bohr coefficients of a trigonometric polynomial.** -/
theorem bohrCoefficient_trigPoly {ι : Type*} (S : Finset ι) (a : ι → ℂ) (mu : ι → ℝ) (lam : ℝ) :
    bohrCoefficient (fun t => ∑ i ∈ S, a i * bohrExp (mu i) t) lam
      = ∑ i ∈ S, if mu i = lam then a i else 0 := by
  classical
  have hsplit : (fun t : ℝ => (∑ i ∈ S, a i * bohrExp (mu i) t) * bohrChar lam t)
      = fun t : ℝ => ∑ i ∈ S, a i * (bohrExp (mu i) t * bohrChar lam t) := by
    funext t
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmean : bohrMean (fun t : ℝ => ∑ i ∈ S, a i * (bohrExp (mu i) t * bohrChar lam t))
      = ∑ i ∈ S, bohrMean (fun t : ℝ => a i * (bohrExp (mu i) t * bohrChar lam t)) := by
    refine bohrMean_sum (F := fun i => fun t : ℝ => a i * (bohrExp (mu i) t * bohrChar lam t)) S
      (fun i _ => continuous_const.mul ((continuous_bohrExp _).mul (continuous_bohrChar _)))
      (fun i _ => isBohrAlmostPeriodic_const_mul _
        (isBohrAlmostPeriodic_mul (continuous_bohrExp _) (isBohrAlmostPeriodic_bohrExp _)
          (continuous_bohrChar _) (isBohrAlmostPeriodic_bohrChar _)))
  have hterm : ∀ i ∈ S, bohrMean (fun t : ℝ => a i * (bohrExp (mu i) t * bohrChar lam t))
      = if mu i = lam then a i else 0 := by
    intro i _
    rw [bohrMean_const_mul (f := fun t : ℝ => bohrExp (mu i) t * bohrChar lam t) _
      ((continuous_bohrExp _).mul (continuous_bohrChar _))
      (isBohrAlmostPeriodic_mul (continuous_bohrExp _) (isBohrAlmostPeriodic_bohrExp _)
        (continuous_bohrChar _) (isBohrAlmostPeriodic_bohrChar _))]
    have hfun : (fun t : ℝ => bohrExp (mu i) t * bohrChar lam t) = bohrChar (lam - mu i) :=
      funext fun t => bohrExp_mul_bohrChar (mu i) lam t
    rw [hfun, bohrMean_bohrChar]
    by_cases h : mu i = lam
    · rw [if_pos (by rw [h]; ring), if_pos h, mul_one]
    · rw [if_neg (fun hz => h (by linarith [sub_eq_zero.mp hz])), if_neg h, mul_zero]
  show bohrMean (fun t : ℝ => (∑ i ∈ S, a i * bohrExp (mu i) t) * bohrChar lam t) = _
  rw [hsplit, hmean]
  exact Finset.sum_congr rfl hterm

/-- On a finite family of *distinct* frequencies, the Bohr coefficient of a trigonometric polynomial
is the corresponding coefficient. -/
theorem bohrCoefficient_trigPoly_of_injective {ι : Type*} [Fintype ι] (a : ι → ℂ) {mu : ι → ℝ}
    (hmu : Function.Injective mu) (j : ι) :
    bohrCoefficient (fun t => ∑ i, a i * bohrExp (mu i) t) (mu j) = a j := by
  classical
  rw [bohrCoefficient_trigPoly]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro i _ hij
    rw [if_neg (fun h => hij (hmu h))]
  · intro h
    exact absurd (Finset.mem_univ j) h

end

end GaloisForLFunctions
