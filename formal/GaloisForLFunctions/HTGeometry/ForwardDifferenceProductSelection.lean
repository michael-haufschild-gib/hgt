import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Product selection on an interval by forward differences

For finitely many reals `a_1, …, a_m` and an interval `[c, c + L]`, some grid point
`X = c + kL/m` satisfies `Π |X - a_i| ≥ (L/(2e))^m` (`exists_mem_Icc_prod_abs_sub_ge`).

The `m`-th forward difference of a monic polynomial of degree `m` is `m!`, and it equals the
alternating binomial sum of the values at `0, 1, …, m`; hence one of these values has modulus at
least `m!/2^m` (`exists_le_abs_eval_nat_of_monic`).  Rescaling the grid to `[c, c + L]` and
`m! ≥ (m/e)^m` give the bound.  The base `L/(2e)` does not depend on `m`: the bound is a
product version of the fact that `m` points cannot crowd every point of an interval.
-/

open Polynomial Finset
open scoped fwdDiff Nat

namespace HTGeometry

/-- For a monic real polynomial `Q` of degree `m`, some integer `k ∈ [0, m]` has
`|Q(k)| ≥ m!/2^m`: the `m`-th forward difference of `Q` at `0` is `m!`, and it is
`Σ_k (-1)^{m-k} C(m,k) Q(k)`. -/
theorem exists_le_abs_eval_nat_of_monic {Q : ℝ[X]} (hQ : Q.Monic) :
    ∃ k ∈ range (Q.natDegree + 1),
      (Q.natDegree ! : ℝ) / 2 ^ Q.natDegree ≤ |Q.eval (k : ℝ)| := by
  set m := Q.natDegree with hm
  have hfd := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial Q) 0
  rw [fwdDiff_iter_eq_sum_shift, hQ.leadingCoeff] at hfd
  simp only [zero_add, nsmul_eq_mul, mul_one, Pi.smul_apply, one_smul, Pi.natCast_apply] at hfd
  by_contra hcon
  push Not at hcon
  have hlt : |∑ k ∈ range (m + 1), ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ)) • Q.eval (k : ℝ)| <
      ∑ k ∈ range (m + 1), (m.choose k : ℝ) * ((m ! : ℝ) / 2 ^ m) := by
    refine lt_of_le_of_lt (abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun k hk => ?_
    rw [zsmul_eq_mul, abs_mul]
    have hc : |(((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) : ℝ)| = (m.choose k : ℝ) := by
      push_cast
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    rw [hc]
    have hpos : (0 : ℝ) < m.choose k := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp (mem_range.mp hk))
    exact mul_lt_mul_of_pos_left (hcon k hk) hpos
  rw [← Finset.sum_mul] at hlt
  have hsum : ∑ k ∈ range (m + 1), (m.choose k : ℝ) = 2 ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  rw [hsum, mul_div_cancel₀ _ (by positivity), hfd] at hlt
  rw [abs_of_nonneg (by positivity)] at hlt
  exact lt_irrefl _ hlt

/-- **Product selection on an interval.**  For finitely many reals `a_i`, some point `X` of any
interval `[c, c + L]` has `Π |X - a_i| ≥ (L/(2e))^m`, `m` the number of points.  The point is on
the grid `c + kL/m`: apply the forward-difference bound to the monic polynomial
`Π (y - (a_i - c)m/L)`. -/
theorem exists_mem_Icc_prod_abs_sub_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ) (c : ℝ) {L : ℝ}
    (hL : 0 < L) :
    ∃ X ∈ Set.Icc c (c + L), (L / (2 * Real.exp 1)) ^ s.card ≤ ∏ i ∈ s, |X - a i| := by
  classical
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · refine ⟨c, ⟨le_rfl, by linarith⟩, ?_⟩
    rw [h0, pow_zero, Finset.card_eq_zero.mp h0, Finset.prod_empty]
  set m := s.card with hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos
  set h := L / m with hh
  have hh0 : 0 < h := div_pos hL hm0
  set Q : ℝ[X] := ∏ i ∈ s, (X - C ((a i - c) / h)) with hQ
  have hmon : Q.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hdeg : Q.natDegree = m := by
    rw [hQ, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, hm]
  obtain ⟨k, hk, hQk⟩ := exists_le_abs_eval_nat_of_monic hmon
  rw [hdeg] at hk hQk
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
  refine ⟨c + h * k, ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) k], ?_⟩, ?_⟩
  · have : h * k ≤ h * m := mul_le_mul_of_nonneg_left hkm hh0.le
    rw [hh, div_mul_cancel₀ _ hm0.ne'] at this
    linarith
  have heval : |Q.eval (k : ℝ)| * h ^ m = ∏ i ∈ s, |c + h * k - a i| := by
    rw [hQ, eval_prod, Finset.abs_prod, hm, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [eval_sub, eval_X, eval_C, ← abs_of_pos hh0, ← abs_mul, abs_of_pos hh0]
    congr 1
    field_simp
    ring
  rw [← heval]
  have hfact : (m : ℝ) ^ m / (m ! : ℝ) ≤ Real.exp m := Real.pow_div_factorial_le_exp _ hm0.le m
  have hfac0 : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by rw [← Real.exp_nat_mul, mul_one]
  rw [hexp] at hfact
  have key : (L / (2 * Real.exp 1)) ^ m ≤ (m ! : ℝ) / 2 ^ m * h ^ m := by
    rw [hh, div_pow, div_pow, mul_pow]
    rw [div_le_iff₀ (by positivity)]
    have e1 : (m ! : ℝ) / 2 ^ m * (L ^ m / (m : ℝ) ^ m) * (2 ^ m * Real.exp 1 ^ m) =
        L ^ m * ((m ! : ℝ) * Real.exp 1 ^ m / (m : ℝ) ^ m) := by
      field_simp
    rw [e1]
    have : 1 ≤ (m ! : ℝ) * Real.exp 1 ^ m / (m : ℝ) ^ m := by
      rw [le_div_iff₀ (by positivity), one_mul]
      rw [div_le_iff₀ hfac0] at hfact
      linarith
    nlinarith [pow_pos hL m]
  exact key.trans (mul_le_mul_of_nonneg_right hQk (by positivity))

end HTGeometry
