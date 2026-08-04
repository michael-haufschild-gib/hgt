import Mathlib

/-!
# The pointwise algebraic root estimate

A root of a polynomial relation is bounded by the sum of the moduli of the normalised coefficients.
Unlike Cauchy's bound this form is *pointwise in the coefficients*, so it integrates directly over a
circle: no supremum over the circle is taken anywhere, and therefore no Poisson--Jensen input is
needed to convert a maximum-modulus bound back into a characteristic.

This is the shape the Clunie induction uses: at a first algebraic dependence one regards the relation
as a polynomial in the dependent state with coefficients built from the previous states, and the
estimate bounds the growth of that state by the growth of the coefficients.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **The pointwise algebraic root estimate.**  If `∑_{i ≤ n} c_i g^i = 0` with `c_n ≠ 0` and
`n ≥ 1`, then `g` is at most the sum of the moduli of the normalised lower coefficients, or one. -/
theorem norm_le_max_sum_of_root {n : ℕ} (hn : 1 ≤ n) {g : ℂ} {c : ℕ → ℂ} (hcn : c n ≠ 0)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * g ^ i = 0) :
    ‖g‖ ≤ max 1 (∑ i ∈ Finset.range n, ‖c i / c n‖) := by
  rcases le_or_gt ‖g‖ 1 with hg | hg
  · exact le_trans hg (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  have hg1 : (1 : ℝ) ≤ ‖g‖ := le_of_lt hg
  have hgpos : (0 : ℝ) < ‖g‖ := by linarith
  have hcnpos : (0 : ℝ) < ‖c n‖ := norm_pos_iff.mpr hcn
  -- isolate the top monomial
  rw [Finset.sum_range_succ] at hrel
  have hsplit : c n * g ^ n = -∑ i ∈ Finset.range n, c i * g ^ i :=
    eq_neg_of_add_eq_zero_right hrel
  -- bound the lower monomials
  have hlow : ‖∑ i ∈ Finset.range n, c i * g ^ i‖
      ≤ (∑ i ∈ Finset.range n, ‖c i‖) * ‖g‖ ^ (n - 1) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hile : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hpow : ‖g‖ ^ i ≤ ‖g‖ ^ (n - 1) := pow_le_pow_right₀ hg1 hile
    calc ‖c i * g ^ i‖ = ‖c i‖ * ‖g‖ ^ i := by rw [norm_mul, norm_pow]
      _ ≤ ‖c i‖ * ‖g‖ ^ (n - 1) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  -- compare with the top monomial
  have htop : ‖c n‖ * (‖g‖ ^ (n - 1) * ‖g‖) ≤ (∑ i ∈ Finset.range n, ‖c i‖) * ‖g‖ ^ (n - 1) := by
    have hn1 : ‖g‖ ^ (n - 1) * ‖g‖ = ‖g‖ ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    have hnorm : ‖c n * g ^ n‖ = ‖c n‖ * ‖g‖ ^ n := by rw [norm_mul, norm_pow]
    rw [hn1]
    calc ‖c n‖ * ‖g‖ ^ n = ‖c n * g ^ n‖ := hnorm.symm
      _ = ‖∑ i ∈ Finset.range n, c i * g ^ i‖ := by rw [hsplit, norm_neg]
      _ ≤ (∑ i ∈ Finset.range n, ‖c i‖) * ‖g‖ ^ (n - 1) := hlow
  -- divide
  have hpowpos : (0 : ℝ) < ‖g‖ ^ (n - 1) := pow_pos hgpos _
  have hcancel : ‖c n‖ * ‖g‖ ≤ ∑ i ∈ Finset.range n, ‖c i‖ := by
    have hmul : (‖c n‖ * ‖g‖) * ‖g‖ ^ (n - 1)
        ≤ (∑ i ∈ Finset.range n, ‖c i‖) * ‖g‖ ^ (n - 1) := by
      calc (‖c n‖ * ‖g‖) * ‖g‖ ^ (n - 1) = ‖c n‖ * (‖g‖ ^ (n - 1) * ‖g‖) := by ring
        _ ≤ (∑ i ∈ Finset.range n, ‖c i‖) * ‖g‖ ^ (n - 1) := htop
    exact le_of_mul_le_mul_right hmul hpowpos
  have hsumdiv : ∑ i ∈ Finset.range n, ‖c i / c n‖
      = (∑ i ∈ Finset.range n, ‖c i‖) / ‖c n‖ := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [norm_div]
  rw [hsumdiv, le_div_iff₀ hcnpos]
  linarith [hcancel]

/-- The positive logarithm of a root is bounded by that of the normalised coefficient sum. -/
theorem posLog_norm_le_of_root {n : ℕ} (hn : 1 ≤ n) {g : ℂ} {c : ℕ → ℂ} (hcn : c n ≠ 0)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * g ^ i = 0) :
    Real.posLog ‖g‖ ≤ Real.posLog (∑ i ∈ Finset.range n, ‖c i / c n‖) := by
  have hbase := norm_le_max_sum_of_root hn hcn hrel
  have hsum0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, ‖c i / c n‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hmax : Real.posLog (max 1 (∑ i ∈ Finset.range n, ‖c i / c n‖))
      = Real.posLog (∑ i ∈ Finset.range n, ‖c i / c n‖) := by
    rcases le_total (∑ i ∈ Finset.range n, ‖c i / c n‖) 1 with hle | hle
    · have h1 : max 1 (∑ i ∈ Finset.range n, ‖c i / c n‖) = 1 := max_eq_left hle
      rw [h1]
      have h2 : Real.posLog (∑ i ∈ Finset.range n, ‖c i / c n‖) = 0 := by
        rw [Real.posLog, max_eq_left]
        exact Real.log_nonpos hsum0 hle
      rw [h2, Real.posLog, Real.log_one, max_self]
    · rw [max_eq_right hle]
  calc Real.posLog ‖g‖
      ≤ Real.posLog (max 1 (∑ i ∈ Finset.range n, ‖c i / c n‖)) :=
        Real.posLog_le_posLog (norm_nonneg _) hbase
    _ = Real.posLog (∑ i ∈ Finset.range n, ‖c i / c n‖) := hmax

/-- **The positive logarithm of a finite sum.**  Splitting a sum costs one `log 2` per term. -/
theorem posLog_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    Real.posLog (∑ i ∈ s, x i)
      ≤ (∑ i ∈ s, Real.posLog (x i)) + (s.card : ℝ) * Real.log 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp [Real.posLog]
  | insert j t hj ih =>
      have hxj : 0 ≤ x j := hx j (Finset.mem_insert_self j t)
      have hxt : ∀ i ∈ t, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have hstep := ih hxt
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.card_insert_of_notMem hj]
      have hadd : Real.posLog (x j + ∑ i ∈ t, x i)
          ≤ Real.log 2 + Real.posLog (x j) + Real.posLog (∑ i ∈ t, x i) := Real.posLog_add
      push_cast
      linarith

end GaloisForLFunctions.HTGeometry
