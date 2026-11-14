import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic bounds for signed generating products

The local ratio `(1 + 2t)/(1 - t)` has logarithm at most `3t` on `[0, 1/2]`.
This controls the Rankin tail after the negative local factors of a generating polynomial
have been combined into a positive product. The linear coefficient three cannot be replaced
by eleven quarters, even on `[0, 1/3]`.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence.Sieve

open Set

/-- A quadratic lower bound for the logarithm, valid throughout the positive half-line. -/
theorem quadratic_le_log_one_add (t : NNReal) :
    (t : ℝ) - (t : ℝ) ^ 2 / 2 ≤ Real.log (1 + (t : ℝ)) := by
  have hd (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun x : ℝ => Real.log (1 + x) - x + x ^ 2 / 2)
        (1 / (1 + x) - 1 + 2 * x / 2) x := by
    convert ((((hasDerivAt_id x).const_add 1).log (by positivity)).sub
      (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      (try funext y) <;> ring
  have hm : MonotoneOn (fun x : ℝ => Real.log (1 + x) - x + x ^ 2 / 2) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun x => 1 / (1 + x) - 1 + 2 * x / 2)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      have heq : 1 / (1 + x) - 1 + 2 * x / 2 = x ^ 2 / (1 + x) := by
        field_simp
        ring
      rw [heq]
      positivity
  have hh := hm (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
    (mem_Ici.mpr t.property) t.property
  simp only [add_zero, Real.log_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, zero_add] at hh
  linarith only [hh]

/-- A uniform linear bound for the logarithm of the doubled-parameter Rankin ratio. -/
theorem log_rankin_ratio_le_three (t : Icc (0 : ℝ) (1 / 2)) :
    Real.log ((1 + 2 * t.1) / (1 - t.1)) ≤ 3 * t.1 := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
      HasDerivAt (fun x : ℝ => 3 * x - Real.log (1 + 2 * x) + Real.log (1 - x))
        (3 - 2 / (1 + 2 * x) + (-1) / (1 - x)) x := by
    have hp : 0 < 1 + 2 * x := by linarith only [hx.1]
    have hn : 0 < 1 - x := by linarith only [hx.2]
    convert (((hasDerivAt_id x).const_mul 3).sub
      ((((hasDerivAt_id x).const_mul 2).const_add 1).log hp.ne')).add
        (((hasDerivAt_id x).const_sub 1).log hn.ne') using 1 <;> (try funext y) <;> ring
  have hm : MonotoneOn
      (fun x : ℝ => 3 * x - Real.log (1 + 2 * x) + Real.log (1 - x))
      (Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
      (f' := fun x => 3 - 2 / (1 + 2 * x) + (-1) / (1 - x))
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := interior_subset hx
      have hp : 0 < 1 + 2 * x := by linarith only [hx'.1]
      have hn : 0 < 1 - x := by linarith only [hx'.2]
      have heq : 3 - 2 / (1 + 2 * x) + (-1) / (1 - x) =
          3 * x * (1 - 2 * x) / ((1 + 2 * x) * (1 - x)) := by
        field_simp
        ring
      rw [heq]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx'.1)
        (by linarith only [hx'.2])) (mul_pos hp hn).le
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := ⟨le_rfl, by norm_num⟩
  have hh := hm h0 t.property t.property.1
  have hp : 0 < 1 + 2 * t.1 := by linarith only [t.property.1]
  have hn : 0 < 1 - t.1 := by linarith only [t.property.2]
  rw [Real.log_div hp.ne' hn.ne']
  norm_num only [mul_zero, add_zero, sub_zero, Real.log_one, zero_sub, neg_zero] at hh
  linarith only [hh]

/-- Eleven quarters is too small a uniform linear coefficient for the Rankin ratio. -/
theorem log_rankin_ratio_counterexample :
    (11 / 4 : ℝ) * (1 / 12) < Real.log ((1 + 2 * (1 / 12 : ℝ)) / (1 - 1 / 12)) := by
  have hlo := quadratic_le_log_one_add (⟨1 / 6, by positivity⟩ : NNReal)
  have hneg := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - 1 / 12 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)]
  norm_num only [NNReal.coe_mk] at hlo
  have harg : (1 + 2 * (1 / 12 : ℝ)) = 1 + 1 / 6 := by ring
  rw [harg]
  linarith only [hlo, hneg]

end GaloisForLFunctions.BezoutValuationIncidence.Sieve
