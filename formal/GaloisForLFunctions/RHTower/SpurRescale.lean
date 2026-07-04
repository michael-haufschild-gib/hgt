/-
(E5) of the MWM lane (doc 25 §1; task #143): the first-order heat expansion of the
Jensen rescaling multipliers, with explicit quadratic remainder.

`φ_d(j) := ∏_{i<j} (1 − i/d)` is the rescaled-section multiplier (`Ã_d = Σ φ_d(j) c_j z^j`,
doc 25 (E3)/(E4)). Main result (`phi_first_order`): for every `j` and `d ≥ 1`,

    |φ_d(j) − (1 − C(j,2)/d)| ≤ (C(j,2)/d)² / 2.

The two sides are the Weierstrass product bound (below) and `∏(1−x) ≤ exp(−Σx) ≤
1 − S + S²/2`; for `j > d` the product vanishes (zero factor at `i = d`) and the bound
holds because then `S ≥ 1`. This is the elementary estimate behind the cluster analysis
(doc 25 Thm B, m ≤ 3): sections are a backward-heat smoothing of the carrier to first
order in `1/d`.
-/
import Mathlib

namespace RHTower

/-- Weierstrass product inequality: for `f i ∈ [0,1]`,
`1 − ∑ f ≤ ∏ (1 − f)`. -/
theorem one_sub_sum_le_prod_one_sub (s : Finset ℕ) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons]
      have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_cons_of_mem hi)
      have h1s : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_cons_of_mem hi)
      have hih := ih h0s h1s
      have ha0 : 0 ≤ f a := h0 a (Finset.mem_cons_self ..)
      have ha1 : f a ≤ 1 := h1 a (Finset.mem_cons_self ..)
      have hsum0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg h0s
      have hmul : (1 - f a) * (1 - ∑ i ∈ s, f i) ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) :=
        mul_le_mul_of_nonneg_left hih (by linarith)
      nlinarith [hmul]

/-- `∏ (1 − f) ≤ exp (−∑ f)` for `f i ∈ [0,1]`. -/
theorem prod_one_sub_le_exp_neg_sum (s : Finset ℕ) (f : ℕ → ℝ)
    (h1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, (1 - f i) ≤ Real.exp (-∑ i ∈ s, f i) := by
  have hstep : ∏ i ∈ s, (1 - f i) ≤ ∏ i ∈ s, Real.exp (-f i) := by
    refine Finset.prod_le_prod (fun i hi => by linarith [h1 i hi]) (fun i hi => ?_)
    have := Real.add_one_le_exp (-f i)
    linarith
  calc ∏ i ∈ s, (1 - f i) ≤ ∏ i ∈ s, Real.exp (-f i) := hstep
    _ = Real.exp (∑ i ∈ s, -f i) := (Real.exp_sum s fun i => -f i).symm
    _ = Real.exp (-∑ i ∈ s, f i) := by rw [Finset.sum_neg_distrib]

/-- `exp(−x) ≤ 1 − x + x²/2` for `x ≥ 0`. -/
theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have key : MonotoneOn (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) ?_
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y))
        (-1 + y + Real.exp (-y)) y := by
      have ha : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
        simpa using (hasDerivAt_id y).const_sub 1
      have hb : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
        have := (hasDerivAt_pow 2 y).div_const 2
        norm_num at this
        simpa using this
      have hc : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
        simpa using (Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)
      have := (ha.add hb).sub hc
      convert this using 1
      ring
    rw [h1.deriv]
    have := Real.add_one_le_exp (-y)
    linarith
  have h0x := key Set.self_mem_Ici (Set.mem_Ici.mpr hx) hx
  simp only [neg_zero, Real.exp_zero] at h0x
  linarith [h0x]

/-- Gauss sum, cast through the binomial coefficient:
`∑_{i<j} i = C(j,2)` in `ℝ`. -/
theorem sum_range_id_cast (j : ℕ) :
    (∑ i ∈ Finset.range j, (i : ℝ)) = (j.choose 2 : ℝ) := by
  rcases j with _ | j
  · simp
  · rw [Nat.cast_choose_two]
    have h := Finset.sum_range_id_mul_two (j + 1)
    have hc : ((∑ i ∈ Finset.range (j + 1), i : ℕ) : ℝ) * 2
        = ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) - 1) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at this ⊢
      simpa using this
    push_cast at hc ⊢
    linarith [hc]

/-- The rescaling product has a zero factor once `j > d`. -/
theorem phi_product_eq_zero_of_d_lt_j {j d : ℕ} (hd : 0 < d) (hjd : d < j) :
    ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hjd) (by rw [div_self hd0]; norm_num)

/-- **(E5).** The rescaling multiplier `φ_d(j) = ∏_{i<j}(1 − i/d)` matches its
first-order heat expansion `1 − C(j,2)/d` to quadratic accuracy, for ALL `j, d ≥ 1`. -/
theorem phi_first_order (j : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    |∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) - (1 - (j.choose 2 : ℝ) / d)|
      ≤ ((j.choose 2 : ℝ) / d) ^ 2 / 2 := by
  have hd0 : (0 : ℝ) < d := by positivity
  set S : ℝ := (j.choose 2 : ℝ) / d with hS
  have hSsum : (∑ i ∈ Finset.range j, (i : ℝ) / d) = S := by
    rw [← Finset.sum_div, sum_range_id_cast]
  have hS0 : 0 ≤ S := by positivity
  by_cases hjd : j ≤ d
  · have h0 : ∀ i ∈ Finset.range j, 0 ≤ (i : ℝ) / d := fun i _ => by positivity
    have h1 : ∀ i ∈ Finset.range j, (i : ℝ) / d ≤ 1 := by
      intro i hi
      rw [div_le_one hd0]
      have : i < j := Finset.mem_range.mp hi
      exact_mod_cast by omega
    have hlow := one_sub_sum_le_prod_one_sub (Finset.range j) (fun i => (i : ℝ) / d) h0 h1
    have hup := prod_one_sub_le_exp_neg_sum (Finset.range j) (fun i => (i : ℝ) / d) h1
    rw [hSsum] at hlow hup
    have hq := exp_neg_le_quadratic hS0
    rw [abs_le]
    constructor
    · nlinarith [hlow]
    · nlinarith [hup, hq]
  · have hmem : d ∈ Finset.range j := Finset.mem_range.mpr (by omega)
    have hzero : ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) = 0 :=
      Finset.prod_eq_zero hmem (by rw [div_self hd0.ne']; norm_num)
    have hS1 : 1 ≤ S := by
      have hch : (d + 1).choose 2 ≤ j.choose 2 :=
        Nat.choose_le_choose 2 (by omega)
      have hcast : ((d + 1).choose 2 : ℝ) ≤ (j.choose 2 : ℝ) := by exact_mod_cast hch
      have hval : (((d + 1).choose 2 : ℕ) : ℝ) = (d + 1) * d / 2 := by
        rw [Nat.cast_choose_two]
        push_cast
        ring
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hdd : (d : ℝ) ≤ d * d := by nlinarith [hd1, hd0]
      rw [hS, le_div_iff₀ hd0]
      nlinarith [hcast, hval, hdd]
    rw [hzero]
    have : |0 - (1 - S)| = S - 1 := by
      rw [abs_sub_comm, sub_zero, abs_of_nonpos (by linarith)]
      ring
    rw [this]
    nlinarith [hS1]

/-- Lower one-sided form of `(E5)`. -/
theorem phi_first_order_lower_bound (j : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    1 - (j.choose 2 : ℝ) / d - ((j.choose 2 : ℝ) / d) ^ 2 / 2
      ≤ ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) := by
  have h := phi_first_order j hd
  rw [abs_le] at h
  linarith [h.1]

/-- Upper one-sided form of `(E5)`. -/
theorem phi_first_order_upper_bound (j : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)
      ≤ 1 - (j.choose 2 : ℝ) / d + ((j.choose 2 : ℝ) / d) ^ 2 / 2 := by
  have h := phi_first_order j hd
  rw [abs_le] at h
  linarith [h.2]

end RHTower
