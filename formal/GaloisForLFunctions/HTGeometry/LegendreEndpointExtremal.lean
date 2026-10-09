import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# The endpoint extremal polynomial on `[0, 1]`

For `m ≥ 1` put `r_j = (−1)^j C(m, j+1) C(m+j, j)` and `c_j = r_j/m` (`j < m`), and let
`p_m(x) = Σ_{j<m} c_j x^j`. Then

* `p_m(0) = 1` (`endpointExtremalPoly_eval_zero`);
* `∫_0^1 x^i p_m(x) dx = Σ_j c_j/(i+j+1) = δ_{i0}/m²` for `i < m` (`sum_endpointExtremalCoeff_div`);
* `∫_0^1 p_m² = Σ_{i,j} c_i c_j/(i+j+1) = 1/m²` (`sum_sum_endpointExtremalCoeff`,
  `integral_endpointExtremalPoly_sq`).

So `p_m` is the minimiser of `∫_0^1 p²` among polynomials of degree `< m` with `p(0) = 1`, with
minimum `1/m²`.

The proof is a partial-fraction identity. The polynomials
`Σ_j r_j ∏_{k<m, k≠j}(X + k + 1)` and `∏_{k=1}^{m−1}(k − X)` have degree `< m` and agree at the
`m` nodes `−(l+1)`, where both equal `(m+l)!/(l+1)!` (`partialFraction_eq`). Evaluating at
`X = i` gives `Σ_j r_j/(i+j+1) = ∏_{k=1}^{m−1}(k − i)/∏_{k<m}(i+k+1)`, which is `1/m` at
`i = 0` and `0` for `1 ≤ i < m`.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LegendreEndpoint

/-- The partial-fraction numerators `r_j = (−1)^j C(m, j+1) C(m+j, j)`. -/
def endpointExtremalNumer (m j : ℕ) : ℝ := (-1) ^ j * (m.choose (j + 1) : ℝ) * ((m + j).choose j : ℝ)

/-- The coefficients `c_j = (−1)^j C(m, j+1) C(m+j, j)/m`. -/
def endpointExtremalCoeff (m j : ℕ) : ℝ := endpointExtremalNumer m j / m

/-- The endpoint extremal polynomial `p_m = Σ_{j<m} c_j X^j`. -/
def endpointExtremalPoly (m : ℕ) : ℝ[X] := ∑ j ∈ range m, C (endpointExtremalCoeff m j) * X ^ j

theorem endpointExtremalPoly_eval_zero {m : ℕ} (hm : 1 ≤ m) : (endpointExtremalPoly m).eval 0 = 1 := by
  rw [endpointExtremalPoly, eval_finsetSum]
  rw [Finset.sum_eq_single 0]
  · simp only [eval_C, pow_zero, mul_one, endpointExtremalCoeff,
      endpointExtremalNumer, zero_add, Nat.choose_one_right, add_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul]
    have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    field_simp
  · intro j _ hj
    simp [hj]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ### Factorial products -/

/-- `∏_{k<m, k≠l} (k − l) = (−1)^l l! (m−1−l)!`. -/
theorem prod_erase_sub {m l : ℕ} (hl : l < m) :
    ∏ k ∈ (range m).erase l, ((k : ℝ) - l) =
      (-1) ^ l * (l.factorial : ℝ) * ((m - 1 - l).factorial : ℝ) := by
  have hsplit : (range m).erase l = range l ∪ Ico (l + 1) m := by
    ext k; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range l) (Ico (l + 1) m) := by
    rw [Finset.disjoint_left]; intro k hk hk'
    simp only [mem_range] at hk; simp only [mem_Ico] at hk'; omega
  rw [hsplit, prod_union hdisj]
  have h1 : ∏ k ∈ range l, ((k : ℝ) - l) = (-1) ^ l * (l.factorial : ℝ) := by
    have e : ∀ k ∈ range l, ((k : ℝ) - l) = -1 * (((l - 1 - k : ℕ) : ℝ) + 1) := by
      intro k hk
      simp only [mem_range] at hk
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range]
    congr 1
    rw [prod_range_reflect (fun j => ((j : ℕ) : ℝ) + 1) l]
    have hf : ((∏ j ∈ range l, (j + 1) : ℕ) : ℝ) = (l.factorial : ℝ) := by
      rw [prod_range_add_one_eq_factorial]
    rw [← hf]; push_cast; rfl
  have h2 : ∏ k ∈ Ico (l + 1) m, ((k : ℝ) - l) = ((m - 1 - l).factorial : ℝ) := by
    rw [prod_Ico_eq_prod_range]
    have e : ∀ t ∈ range (m - (l + 1)), (((l + 1 + t : ℕ) : ℝ) - l) = ((t : ℝ) + 1) := by
      intro t _; push_cast; ring
    rw [prod_congr rfl e, show m - (l + 1) = m - 1 - l by omega]
    exact_mod_cast prod_range_add_one_eq_factorial (m - 1 - l)
  rw [h1, h2]

/-- `(l+1)! ∏_{k=1}^{m−1}(k + l + 1) = (m+l)!`. -/
theorem factorial_mul_prod_Ico {m l : ℕ} (hm : 1 ≤ m) :
    ((l + 1).factorial : ℝ) * ∏ k ∈ Ico 1 m, ((k : ℝ) + l + 1) = ((m + l).factorial : ℝ) := by
  rw [prod_Ico_eq_prod_range]
  have e : ∀ t ∈ range (m - 1), (((1 + t : ℕ) : ℝ) + l + 1) = (((l + 2 + t : ℕ) : ℝ)) := by
    intro t _; push_cast; ring
  rw [prod_congr rfl e, ← Nat.cast_prod, ← Nat.ascFactorial_eq_prod_range]
  have h := Nat.factorial_mul_ascFactorial (l + 1) (m - 1)
  rw [show l + 1 + (m - 1) = m + l by omega] at h
  exact_mod_cast h

/-- The node identity `r_l (−1)^l l! (m−1−l)! (l+1)! = (m+l)!`. -/
theorem endpointExtremalNumer_node {m l : ℕ} (hl : l < m) :
    endpointExtremalNumer m l * ((-1) ^ l * (l.factorial : ℝ) * ((m - 1 - l).factorial : ℝ)) *
      ((l + 1).factorial : ℝ) = ((m + l).factorial : ℝ) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show l + 1 ≤ m by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show l ≤ m + l by omega)
  rw [show m - (l + 1) = m - 1 - l by omega] at h1
  rw [show m + l - l = m by omega] at h2
  have h1' : (m.choose (l + 1) : ℝ) * ((l + 1).factorial : ℝ) * ((m - 1 - l).factorial : ℝ) =
      (m.factorial : ℝ) := by exact_mod_cast h1
  have h2' : ((m + l).choose l : ℝ) * (l.factorial : ℝ) * (m.factorial : ℝ) =
      ((m + l).factorial : ℝ) := by exact_mod_cast h2
  have hsq : ((-1 : ℝ) ^ l) * (-1) ^ l = 1 := by rw [← mul_pow]; norm_num
  rw [endpointExtremalNumer, ← h2', ← h1']
  linear_combination ((m + l).choose l : ℝ) * (m.choose (l + 1) : ℝ) * (l.factorial : ℝ) *
    ((m - 1 - l).factorial : ℝ) * ((l + 1).factorial : ℝ) * hsq

/-! ### The partial-fraction identity -/

/-- The polynomial `Σ_j r_j ∏_{k<m, k≠j}(X + k + 1)`. -/
def pfLeft (m : ℕ) : ℝ[X] :=
  ∑ j ∈ range m, C (endpointExtremalNumer m j) * ∏ k ∈ (range m).erase j, (X + C ((k : ℝ) + 1))

/-- The polynomial `∏_{k=1}^{m−1}(k − X)`. -/
def pfRight (m : ℕ) : ℝ[X] := ∏ k ∈ Ico 1 m, (C (k : ℝ) - X)

theorem natDegree_pfLeft_le (m : ℕ) : (pfLeft m).natDegree ≤ m - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  have : ∀ k ∈ (range m).erase j, (X + C ((k : ℝ) + 1)).natDegree ≤ 1 := fun k _ =>
    (natDegree_X_add_C _).le
  refine (sum_le_sum this).trans ?_
  rw [sum_const, card_erase_of_mem hj, card_range, smul_eq_mul, mul_one]

theorem natDegree_pfRight_le (m : ℕ) : (pfRight m).natDegree ≤ m - 1 := by
  refine (natDegree_prod_le _ _).trans ?_
  have : ∀ k ∈ Ico 1 m, (C (k : ℝ) - X).natDegree ≤ 1 := fun k _ =>
    (natDegree_sub_le _ _).trans (by simp)
  refine (sum_le_sum this).trans ?_
  rw [sum_const, Nat.card_Ico, smul_eq_mul, mul_one]

theorem eval_pfLeft_node {m l : ℕ} (hl : l < m) :
    (pfLeft m).eval (-((l : ℝ) + 1)) = endpointExtremalNumer m l * ∏ k ∈ (range m).erase l, ((k : ℝ) - l) := by
  rw [pfLeft, eval_finsetSum, sum_eq_single l]
  · rw [eval_mul, eval_C, eval_prod]
    congr 1
    refine prod_congr rfl fun k _ => ?_
    simp only [eval_add, eval_X, eval_C]; ring
  · intro j _ hjl
    rw [eval_mul, eval_prod]
    have hmem : l ∈ (range m).erase j := mem_erase.mpr ⟨Ne.symm hjl, mem_range.mpr hl⟩
    rw [prod_eq_zero hmem (by simp only [eval_add, eval_X, eval_C]; ring), mul_zero]
  · intro h; exact absurd (mem_range.mpr hl) h

theorem eval_pfRight_node {m l : ℕ} :
    (pfRight m).eval (-((l : ℝ) + 1)) = ∏ k ∈ Ico 1 m, ((k : ℝ) + l + 1) := by
  rw [pfRight, eval_prod]
  refine prod_congr rfl fun k _ => ?_
  simp only [eval_sub, eval_C, eval_X]; ring

/-- **Partial fractions.** `Σ_j r_j ∏_{k≠j}(X + k + 1) = ∏_{k=1}^{m−1}(k − X)`. -/
theorem partialFraction_eq {m : ℕ} (hm : 1 ≤ m) : pfLeft m = pfRight m := by
  set s : Finset ℝ := (range m).image fun l : ℕ => -((l : ℝ) + 1) with hs
  have hcard : s.card = m := by
    rw [hs, card_image_of_injective _ (fun a b h => by
      simpa using h), card_range]
  refine eq_of_degree_sub_lt_of_eval_finset_eq s ?_ ?_
  · rw [hcard]
    refine (degree_sub_le _ _).trans_lt ?_
    rw [max_lt_iff]
    constructor
    · refine (degree_le_natDegree).trans_lt ?_
      exact_mod_cast (natDegree_pfLeft_le m).trans_lt (by omega)
    · refine (degree_le_natDegree).trans_lt ?_
      exact_mod_cast (natDegree_pfRight_le m).trans_lt (by omega)
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
    have hl' := mem_range.mp hl
    rw [eval_pfLeft_node hl', eval_pfRight_node, prod_erase_sub hl']
    have hf : ((l + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h1 := endpointExtremalNumer_node hl'
    have h2 := factorial_mul_prod_Ico (l := l) hm
    apply mul_right_cancel₀ hf
    linarith

/-- **Evaluation at the integers.** `Σ_j r_j/(i+j+1) · ∏_{k<m}(i+k+1) = ∏_{k=1}^{m−1}(k − i)`. -/
theorem sum_endpointExtremalNumer_div_mul_prod {m : ℕ} (hm : 1 ≤ m) (i : ℕ) :
    (∑ j ∈ range m, endpointExtremalNumer m j / ((i : ℝ) + j + 1)) *
      ∏ k ∈ range m, ((i : ℝ) + k + 1) = ∏ k ∈ Ico 1 m, ((k : ℝ) - i) := by
  have h := congrArg (eval (i : ℝ)) (partialFraction_eq hm)
  rw [pfLeft, pfRight, eval_finsetSum, eval_prod] at h
  rw [sum_mul]
  have e : ∀ j ∈ range m, endpointExtremalNumer m j / ((i : ℝ) + j + 1) *
      ∏ k ∈ range m, ((i : ℝ) + k + 1) =
      eval (i : ℝ) (C (endpointExtremalNumer m j) * ∏ k ∈ (range m).erase j, (X + C ((k : ℝ) + 1))) := by
    intro j hj
    rw [eval_mul, eval_C, eval_prod, ← mul_prod_erase (range m) (fun k => (i : ℝ) + k + 1) hj]
    have hne : (i : ℝ) + j + 1 ≠ 0 := by positivity
    have e2 : ∏ k ∈ (range m).erase j, eval (i : ℝ) (X + C ((k : ℝ) + 1)) =
        ∏ k ∈ (range m).erase j, ((i : ℝ) + k + 1) :=
      prod_congr rfl fun k _ => by simp only [eval_add, eval_X, eval_C]; ring
    rw [e2]
    field_simp
  rw [sum_congr rfl e, h]
  exact prod_congr rfl fun k _ => by simp only [eval_sub, eval_C, eval_X]

/-- **The reproducing identity.** `Σ_j c_j/(i+j+1) = δ_{i0}/m²` for `i < m`. -/
theorem sum_endpointExtremalCoeff_div {m i : ℕ} (hm : 1 ≤ m) (hi : i < m) :
    ∑ j ∈ range m, endpointExtremalCoeff m j / ((i : ℝ) + j + 1) = if i = 0 then 1 / (m : ℝ) ^ 2 else 0 := by
  have h := sum_endpointExtremalNumer_div_mul_prod hm i
  have hP : ∏ k ∈ range m, ((i : ℝ) + k + 1) ≠ 0 :=
    prod_ne_zero_iff.mpr fun k _ => by positivity
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have e : ∑ j ∈ range m, endpointExtremalCoeff m j / ((i : ℝ) + j + 1) =
      (∑ j ∈ range m, endpointExtremalNumer m j / ((i : ℝ) + j + 1)) / m := by
    rw [sum_div]
    exact sum_congr rfl fun j _ => by rw [endpointExtremalCoeff]; ring
  rw [e]
  split_ifs with hi0
  · subst hi0
    have hI : ∏ k ∈ Ico 1 m, k = (m - 1).factorial := by
      have := prod_Ico_id_eq_factorial (m - 1)
      rwa [show m - 1 + 1 = m by omega] at this
    have hR : ∏ k ∈ Ico 1 m, ((k : ℝ) - ((0 : ℕ) : ℝ)) = ((m - 1).factorial : ℝ) := by
      rw [← hI]; push_cast; simp
    have hL : ∏ k ∈ range m, (((0 : ℕ) : ℝ) + k + 1) = (m.factorial : ℝ) := by
      simp only [Nat.cast_zero, zero_add]
      exact_mod_cast prod_range_add_one_eq_factorial m
    rw [hR, hL] at h
    have hfm : (m.factorial : ℝ) = m * ((m - 1).factorial : ℝ) := by
      have := Nat.mul_factorial_pred (show m ≠ 0 by omega)
      exact_mod_cast this.symm
    have hf1 : ((m - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [hfm] at h
    have hs : ∑ j ∈ range m, endpointExtremalNumer m j / (((0 : ℕ) : ℝ) + j + 1) = 1 / m := by
      have h' : (∑ j ∈ range m, endpointExtremalNumer m j / (((0 : ℕ) : ℝ) + j + 1)) * m *
          ((m - 1).factorial : ℝ) = 1 * ((m - 1).factorial : ℝ) := by linear_combination h
      have h'' := mul_right_cancel₀ hf1 h'
      rw [eq_div_iff hmR]; exact h''
    rw [hs]; field_simp
  · have hR : ∏ k ∈ Ico 1 m, ((k : ℝ) - i) = 0 :=
      prod_eq_zero (mem_Ico.mpr ⟨by omega, hi⟩) (by ring)
    rw [hR] at h
    have := (mul_eq_zero.mp h).resolve_right hP
    rw [this, zero_div]

/-- **The Gram sum.** `Σ_{i,j<m} c_i c_j/(i+j+1) = 1/m²`. -/
theorem sum_sum_endpointExtremalCoeff {m : ℕ} (hm : 1 ≤ m) :
    ∑ i ∈ range m, ∑ j ∈ range m, endpointExtremalCoeff m i * endpointExtremalCoeff m j / ((i : ℝ) + j + 1) =
      1 / (m : ℝ) ^ 2 := by
  have e : ∀ i ∈ range m, ∑ j ∈ range m, endpointExtremalCoeff m i * endpointExtremalCoeff m j / ((i : ℝ) + j + 1)
      = endpointExtremalCoeff m i * (if i = 0 then 1 / (m : ℝ) ^ 2 else 0) := by
    intro i hi
    rw [← sum_endpointExtremalCoeff_div hm (mem_range.mp hi), mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [sum_congr rfl e, sum_eq_single 0]
  · simp only [if_true]
    have h0 : endpointExtremalCoeff m 0 = 1 := by
      have := endpointExtremalPoly_eval_zero hm
      rw [endpointExtremalPoly, eval_finsetSum, sum_eq_single 0] at this
      · simpa using this
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (mem_range.mpr (by omega)) h
    rw [h0, one_mul]
  · intro i _ hi; rw [if_neg hi, mul_zero]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- **The endpoint extremal.** `∫_0^1 p_m² = 1/m²`. -/
theorem integral_endpointExtremalPoly_sq {m : ℕ} (hm : 1 ≤ m) :
    ∫ x in (0 : ℝ)..1, ((endpointExtremalPoly m).eval x) ^ 2 = 1 / (m : ℝ) ^ 2 := by
  have hexp : ∀ x : ℝ, ((endpointExtremalPoly m).eval x) ^ 2 =
      ∑ i ∈ range m, ∑ j ∈ range m, endpointExtremalCoeff m i * endpointExtremalCoeff m j * x ^ (i + j) := by
    intro x
    rw [endpointExtremalPoly, eval_finsetSum, sq, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [eval_mul, eval_C, eval_pow, eval_X]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (continuous_finsetSum _ fun j _ => by fun_prop).intervalIntegrable _ _]
  rw [← sum_sum_endpointExtremalCoeff hm]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => (by fun_prop : Continuous fun x : ℝ =>
    endpointExtremalCoeff m i * endpointExtremalCoeff m j * x ^ (i + j)).intervalIntegrable _ _]
  refine sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  simp only [one_pow, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    sub_zero]
  ring

end GaloisForLFunctions.HTGeometry.LegendreEndpoint
