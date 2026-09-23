import GaloisForLFunctions.RHTower.GaussianWindowMomentRescaling

/-!
# Shifted polynomial moments of the standard Gaussian

A shifted monomial `(a + |v|)^N` expands binomially into ordinary monomials, so it too is integrable
against `exp(-v²)`.  This is the majorant every polynomial-times-Gaussian domination argument needs
when the polynomial is centred away from the origin.
-/

open MeasureTheory

noncomputable section

namespace RHTower

theorem integrable_abs_pow_mul_exp_neg_sq (m : ℕ) :
    Integrable (fun v : ℝ => |v| ^ m * Real.exp (-v ^ (2 : ℕ))) := by
  refine ((integrable_pow_mul_exp_neg_sq m).abs).congr ?_
  filter_upwards with v
  rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

/-- **Shifted polynomial Gaussian moments.** -/
theorem integrable_shifted_pow_mul_exp_neg_sq (a : ℝ) (N : ℕ) :
    Integrable (fun v : ℝ => (a + |v|) ^ N * Real.exp (-v ^ (2 : ℕ))) := by
  classical
  have hcongr : (fun v : ℝ => (a + |v|) ^ N * Real.exp (-v ^ (2 : ℕ)))
      = fun v : ℝ => ∑ j ∈ Finset.range (N + 1),
          (a ^ j * (N.choose j : ℝ)) * (|v| ^ (N - j) * Real.exp (-v ^ (2 : ℕ))) := by
    funext v
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hcongr]
  refine integrable_finsetSum _ fun j _ => Integrable.const_mul ?_ _
  exact integrable_abs_pow_mul_exp_neg_sq (N - j)

end RHTower

end
