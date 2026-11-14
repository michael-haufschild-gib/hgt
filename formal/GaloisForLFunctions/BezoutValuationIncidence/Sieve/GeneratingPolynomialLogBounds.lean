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
    have hbase : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x :=
      hbase.log (by positivity)
    have hquad : HasDerivAt (fun y : ℝ => y ^ 2 / 2) (2 * x / 2) x := by
      simpa only [id_eq, pow_one, mul_one, Nat.cast_ofNat] using
        ((hasDerivAt_id x).pow 2).div_const 2
    exact (hlog.sub (hasDerivAt_id x)).add hquad
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
  norm_num at hh
  linarith only [hh]

/-- A uniform linear bound for the logarithm of the doubled-parameter Rankin ratio. -/
theorem log_rankin_ratio_le_three (t : Icc (0 : ℝ) (1 / 2)) :
    Real.log ((1 + 2 * t.1) / (1 - t.1)) ≤ 3 * t.1 := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
      HasDerivAt (fun x : ℝ => 3 * x - Real.log (1 + 2 * x) + Real.log (1 - x))
        (3 - 2 / (1 + 2 * x) + (-1) / (1 - x)) x := by
    have hp : 0 < 1 + 2 * x := by linarith only [hx.1]
    have hn : 0 < 1 - x := by linarith only [hx.2]
    have hlinear : HasDerivAt (fun y : ℝ => 3 * y) 3 x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 3
    have hpos : HasDerivAt (fun y : ℝ => 1 + 2 * y) 2 x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul 2).const_add 1
    have hneg : HasDerivAt (fun y : ℝ => 1 - y) (-1) x :=
      (hasDerivAt_id x).const_sub 1
    exact (hlinear.sub (hpos.log hp.ne')).add (hneg.log hn.ne')
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
  have hlo := quadratic_le_log_one_add (NNReal.mk (1 / 6) (by positivity))
  have hneg := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - 1 / 12 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)]
  simp only [NNReal.coe_mk] at hlo
  have harg : (1 + 2 * (1 / 12 : ℝ)) = 1 + 1 / 6 := by ring
  rw [harg]
  linarith only [hlo, hneg]

/-- A rational lower bound for `log 2` sufficient for the fourth-degree Rankin threshold. -/
theorem log_two_ge_forty_seven_over_seventy_two : (47 / 72 : ℝ) ≤ Real.log 2 := by
  have h₁ := quadratic_le_log_one_add (NNReal.mk (1 / 2) (by positivity))
  have h₂ := quadratic_le_log_one_add (NNReal.mk (1 / 3) (by positivity))
  have heq : Real.log 2 = Real.log (1 + 1 / 2) + Real.log (1 + 1 / 3) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    ring
  rw [heq]
  simp only [NNReal.coe_mk] at h₁ h₂
  linarith only [h₁, h₂]

/-- The adaptive degree still makes the corrected Rankin exponent at most `-log 2`. -/
theorem corrected_rankin_exponent (t : Icc (0 : ℝ) (1 / 3)) (S : NNReal) :
    -((⌈4 * t.1 * (S : ℝ)⌉₊ + 1 : ℕ) : ℝ) * Real.log 2 +
      ((S : ℝ) / 2) * Real.log ((1 + 2 * t.1) / (1 - t.1)) + t.1 * S ≤
        -Real.log 2 := by
  have hlog := log_rankin_ratio_le_three
    (⟨t.1, t.property.1, by linarith only [t.property.2]⟩ : Icc (0 : ℝ) (1 / 2))
  have hlocal := mul_le_mul_of_nonneg_left hlog (div_nonneg S.property (by norm_num : (0 : ℝ) ≤ 2))
  have hceil := Nat.le_ceil (4 * t.1 * (S : ℝ))
  have hlower := log_two_ge_forty_seven_over_seventy_two
  have hlogpos : 0 ≤ Real.log 2 := by linarith only [hlower]
  have hdegree := mul_le_mul_of_nonneg_right hceil hlogpos
  have hmass : 0 ≤ t.1 * (S : ℝ) := mul_nonneg t.property.1 S.property
  have hmain : (S : ℝ) / 2 * Real.log ((1 + 2 * t.1) / (1 - t.1)) + t.1 * S ≤
      4 * t.1 * S * Real.log 2 := by
    calc
      _ ≤ (S : ℝ) / 2 * (3 * t.1) + t.1 * S := add_le_add_right hlocal _
      _ = (5 / 2 : ℝ) * (t.1 * S) := by ring
      _ ≤ (4 * Real.log 2) * (t.1 * S) :=
        mul_le_mul_of_nonneg_right (by linarith only [hlower]) hmass
      _ = _ := by ring
  have hcombined := hmain.trans hdegree
  push_cast
  linarith only [hcombined]

/-- The proposed quadratic coefficient involving `log (3/2)` also fails on the stated interval. -/
theorem quadratic_log_counterexample :
    (1 / 4 : ℝ) + (3 * Real.log (3 / 2) - 1) * (1 / 4 : ℝ) ^ 2 <
      -Real.log (1 - 1 / 4 : ℝ) := by
  have hlow := quadratic_le_log_one_add (NNReal.mk (1 / 3) (by positivity))
  have h₁ := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  have h₂ := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have hsum : Real.log (3 / 2 : ℝ) = Real.log (9 / 8) + Real.log (4 / 3) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    ring
  have hinv : -Real.log (1 - 1 / 4 : ℝ) = Real.log (1 + 1 / 3) := by
    rw [← Real.log_inv]
    congr 1
    norm_num
  rw [hsum, hinv]
  simp only [NNReal.coe_mk] at hlow
  have harg : (1 + 1 / 3 : ℝ) = 4 / 3 := by ring
  rw [harg] at hlow ⊢
  linarith only [hlow, h₁, h₂]

end GaloisForLFunctions.BezoutValuationIncidence.Sieve

#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.quadratic_le_log_one_add
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.log_rankin_ratio_le_three
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.log_rankin_ratio_counterexample
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.corrected_rankin_exponent
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.quadratic_log_counterexample
