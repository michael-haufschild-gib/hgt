import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The extremal law has a model

At the zero of maximal angle, `t ↦ Q(t w₀)` satisfies `‖Q(t̄ w₀)‖ < ‖Q(t w₀)‖` for `Im t > 0` (`norm_squaredXi_conj_lt`). Every order of this
inequality at `t = 1` is a necessary law of a counterexample to RH. The first order is the Stieltjes sign (`im_stieltjes_nonpos`).

**No law derived from this inequality alone contradicts an off-axis zero.** The real quadratic `F(w) = w² − 2w + 2` has the zeros
`1 ± i`, the zero `w₀ = 1 + i` has maximal angle, and `F` satisfies the full inequality (`norm_model_conj_lt`). So any contradiction
must use more of `Q` than its extremal position: growth, log-concavity of the coefficients, or arithmetic.

The mechanism is the factor identity: `F(t w₀) = w₀ (t − 1) · w₀ (t + i)`, and `‖t + i‖ > ‖t̄ + i‖` for `Im t > 0`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The model `F(w) = w² − 2w + 2`, real, with zeros `1 ± i`. -/
def extremalModel (w : ℂ) : ℂ := w ^ 2 - 2 * w + 2

theorem extremalModel_eq_zero_iff (w : ℂ) : extremalModel w = 0 ↔ w = 1 + I ∨ w = 1 - I := by
  have hfac : extremalModel w = (w - (1 + I)) * (w - (1 - I)) := by
    have hI : I ^ 2 = -1 := Complex.I_sq
    rw [extremalModel]
    linear_combination hI
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The zero `1 + i` lies at the larger angle: `(1 + i)/(1 − i) = i` has positive imaginary part. -/
theorem extremalModel_angle : (1 + I : ℂ) / (1 - I) = I := by
  have hne : (1 - I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hI : I ^ 2 = -1 := Complex.I_sq
  rw [div_eq_iff hne]
  linear_combination hI

/-- **The model satisfies the extremal inequality.** For `Im t > 0`, `‖F(t̄ w₀)‖ < ‖F(t w₀)‖` at `w₀ = 1 + i`. -/
theorem norm_model_conj_lt {t : ℂ} (ht : 0 < t.im) :
    ‖extremalModel (star t * (1 + I))‖ < ‖extremalModel (t * (1 + I))‖ := by
  have hfac : ∀ u : ℂ, extremalModel (u * (1 + I)) = (1 + I) ^ 2 * ((u - 1) * (u + I)) := by
    intro u
    have hI : I ^ 2 = -1 := Complex.I_sq
    rw [extremalModel]
    linear_combination (-u + 2 - I * u + I) * hI
  rw [hfac, hfac, norm_mul, norm_mul, norm_mul, norm_mul]
  have hw : 0 < ‖(1 + I : ℂ) ^ 2‖ := by
    refine norm_pos_iff.mpr (pow_ne_zero 2 fun h => ?_)
    have := congrArg Complex.im h
    simp at this
  have h1 : ‖star t - 1‖ = ‖t - 1‖ := by
    rw [← norm_star (t - 1), star_sub, star_one]
  have h2 : ‖star t + I‖ < ‖t + I‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp
    nlinarith
  have h3 : 0 < ‖t - 1‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [h1]
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h2 h3) hw

end GaloisForLFunctions.RigidArithmeticOfCuts
