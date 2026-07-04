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

/-- The rescaling product is strictly positive in the live range `j ≤ d`. -/
theorem phi_product_pos_of_le {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    0 < ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) := by
  refine Finset.prod_pos ?_
  intro i hi
  have hi_lt : i < j := Finset.mem_range.mp hi
  have hid : (i : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le hi_lt hjd
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv : (i : ℝ) / d < 1 := by
    rwa [div_lt_one hdp]
  linarith

/-- Log of the positive rescaling product is the sum of the logs. -/
theorem log_phi_product_eq_sum_log {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) =
      ∑ i ∈ Finset.range j, Real.log (1 - (i : ℝ) / d) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjd' : j ≤ d := Nat.le_of_succ_le hjd
      have hj_lt_d : (j : ℝ) < d := by
        exact_mod_cast Nat.lt_of_succ_le hjd
      have hdp : (0 : ℝ) < d := by exact_mod_cast hd
      have hfactor_pos : 0 < 1 - (j : ℝ) / d := by
        have hdiv : (j : ℝ) / d < 1 := by rwa [div_lt_one hdp]
        linarith
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      rw [Real.log_mul]
      · rw [ih hjd']
      · exact ne_of_gt (phi_product_pos_of_le hd hjd')
      · exact ne_of_gt hfactor_pos

/-- One-step logarithmic cumulant remainder. -/
theorem abs_log_one_sub_add_le {u : ℝ} (hu : u < 1) :
    |Real.log (1 - u) + u| ≤ u ^ 2 / (1 - u) := by
  have hpos : 0 < 1 - u := by linarith
  have hnonneg : 0 ≤ u ^ 2 / (1 - u) := by positivity
  rw [abs_le]
  constructor
  · have hinvpos : 0 < (1 - u)⁻¹ := inv_pos.mpr hpos
    have hlog := Real.log_le_sub_one_of_pos hinvpos
    rw [Real.log_inv] at hlog
    have hinv_sub : (1 - u)⁻¹ - 1 = u / (1 - u) := by
      field_simp [hpos.ne']
      ring
    have hbound : -Real.log (1 - u) ≤ u / (1 - u) := by
      simpa [hinv_sub] using hlog
    have hdiff : u / (1 - u) - u = u ^ 2 / (1 - u) := by
      field_simp [hpos.ne']
      ring
    linarith
  · have hlog := Real.log_le_sub_one_of_pos hpos
    have hle0 : Real.log (1 - u) + u ≤ 0 := by linarith
    exact le_trans hle0 hnonneg

/-- First cumulant form of R1: after removing `S₁/d`, the log-product remainder is
bounded by the sum of one-step logarithmic tails. -/
theorem log_phi_first_cumulant_abs_bound {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d| ≤
      ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ 2 / (1 - (i : ℝ) / d)) := by
  have hlog := log_phi_product_eq_sum_log hd hjd
  have hsum : (∑ i ∈ Finset.range j, (i : ℝ) / d) = (j.choose 2 : ℝ) / d := by
    rw [← Finset.sum_div, sum_range_id_cast]
  calc
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d|
        = |∑ i ∈ Finset.range j, (Real.log (1 - (i : ℝ) / d) + (i : ℝ) / d)| := by
          rw [hlog, ← hsum, Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ Finset.range j, |Real.log (1 - (i : ℝ) / d) + (i : ℝ) / d| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ 2 / (1 - (i : ℝ) / d)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < j := Finset.mem_range.mp hi
      have hdp : (0 : ℝ) < d := by exact_mod_cast hd
      have hu : (i : ℝ) / d < 1 := by
        rw [div_lt_one hdp]
        exact_mod_cast lt_of_lt_of_le hi_lt hjd
      exact abs_log_one_sub_add_le hu

/-- Mathlib-backed second-order logarithmic cumulant tail.  The constant is the coarse
bound supplied by `Real.abs_log_sub_add_sum_range_le`. -/
theorem abs_log_one_sub_add_add_sq_div_two_le_crude {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    |Real.log (1 - u) + u + u ^ 2 / 2| ≤ u ^ 3 / (1 - u) := by
  have habs : |u| < 1 := by rwa [abs_of_nonneg hu0]
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  rw [abs_of_nonneg hu0] at h
  have hsum : (∑ i ∈ Finset.range 2, u ^ (i + 1) / (i + 1 : ℝ)) = u + u ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  convert h using 1
  · ring_nf

/-- Second cumulant form of R1 with a crude mathlib Taylor tail. -/
theorem log_phi_second_cumulant_abs_bound {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d +
        ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ 2 / 2)| ≤
      ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ 3 / (1 - (i : ℝ) / d)) := by
  have hlog := log_phi_product_eq_sum_log hd hjd
  have hsum : (∑ i ∈ Finset.range j, (i : ℝ) / d) = (j.choose 2 : ℝ) / d := by
    rw [← Finset.sum_div, sum_range_id_cast]
  calc
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d +
        ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ 2 / 2)|
        = |∑ i ∈ Finset.range j,
              (Real.log (1 - (i : ℝ) / d) + (i : ℝ) / d + ((i : ℝ) / d) ^ 2 / 2)| := by
          rw [hlog, ← hsum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ Finset.range j,
        |Real.log (1 - (i : ℝ) / d) + (i : ℝ) / d + ((i : ℝ) / d) ^ 2 / 2| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ 3 / (1 - (i : ℝ) / d)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < j := Finset.mem_range.mp hi
      have hdp : (0 : ℝ) < d := by exact_mod_cast hd
      have hu0 : 0 ≤ (i : ℝ) / d := by positivity
      have hu1 : (i : ℝ) / d < 1 := by
        rw [div_lt_one hdp]
        exact_mod_cast lt_of_lt_of_le hi_lt hjd
      exact abs_log_one_sub_add_add_sq_div_two_le_crude hu0 hu1

/-- General finite-order logarithmic cumulant truncation for the rescaling product.  This
is the all-orders R1 log-product estimate supplied by mathlib's real log Taylor bound. -/
theorem log_phi_cumulant_abs_bound (n : ℕ) {j d : ℕ} (hd : 0 < d) (hjd : j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) +
        ∑ i ∈ Finset.range j,
          (∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ))| ≤
      ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)) := by
  have hlog := log_phi_product_eq_sum_log hd hjd
  calc
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) +
        ∑ i ∈ Finset.range j,
          (∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ))|
        = |∑ i ∈ Finset.range j,
            (Real.log (1 - (i : ℝ) / d) +
              ∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ))| := by
          rw [hlog, Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ Finset.range j,
        |Real.log (1 - (i : ℝ) / d) +
          ∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < j := Finset.mem_range.mp hi
      have hdp : (0 : ℝ) < d := by exact_mod_cast hd
      have hu0 : 0 ≤ (i : ℝ) / d := by positivity
      have hu1 : (i : ℝ) / d < 1 := by
        rw [div_lt_one hdp]
        exact_mod_cast lt_of_lt_of_le hi_lt hjd
      have habs : |(i : ℝ) / d| < 1 := by rwa [abs_of_nonneg hu0]
      have h := Real.abs_log_sub_add_sum_range_le habs n
      rw [abs_of_nonneg hu0] at h
      simpa [add_comm] using h

/-- Power sum notation for the R1 cumulants. -/
def rescalePowerSum (ell j : ℕ) : ℝ := ∑ i ∈ Finset.range j, (i : ℝ) ^ ell

/-- Swap the finite cumulant sums into doc 34's power-sum form. -/
theorem cumulant_sum_eq_powerSum (n j d : ℕ) :
    (∑ i ∈ Finset.range j,
      (∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ))) =
      ∑ l ∈ Finset.range n,
        rescalePowerSum (l + 1) j / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1)) := by
  calc
    (∑ i ∈ Finset.range j,
      (∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ)))
        = ∑ l ∈ Finset.range n,
            (∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ)) := by
          rw [Finset.sum_comm]
    _ = ∑ l ∈ Finset.range n,
        rescalePowerSum (l + 1) j / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1)) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [rescalePowerSum]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [div_pow, div_div]
      ring

/-- R1 log-product truncation in power-sum cumulant form. -/
theorem log_phi_cumulant_powerSum_abs_bound (n : ℕ) {j d : ℕ} (hd : 0 < d)
    (hjd : j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) +
        ∑ l ∈ Finset.range n,
          rescalePowerSum (l + 1) j / ((l + 1 : ℝ) * (d : ℝ) ^ (l + 1))| ≤
      ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)) := by
  have h := log_phi_cumulant_abs_bound n hd hjd
  rw [cumulant_sum_eq_powerSum] at h
  exact h

/-- If the normalized index is at most `1/2`, the logarithmic one-step tail loses its
denominator at cost `2`. -/
theorem log_tail_div_one_sub_le_two_sq {u : ℝ} (hu : u ≤ (1 : ℝ) / 2) :
    u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
  have hpos : 0 < 1 - u := by linarith
  rw [div_le_iff₀ hpos]
  have hnonneg : 0 ≤ u ^ 2 * (1 - 2 * u) := by
    exact mul_nonneg (sq_nonneg u) (by linarith)
  nlinarith

/-- If the normalized index is at most `1/2`, any nonnegative-power logarithmic tail loses
its denominator at cost `2`. -/
theorem log_tail_pow_div_one_sub_le_two_pow {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ (1 : ℝ) / 2) (p : ℕ) :
    u ^ p / (1 - u) ≤ 2 * u ^ p := by
  have hpos : 0 < 1 - u := by linarith
  rw [div_le_iff₀ hpos]
  have hnonneg : 0 ≤ u ^ p * (1 - 2 * u) := by
    exact mul_nonneg (pow_nonneg hu0 p) (by linarith)
  nlinarith

/-- Coarse square-sum envelope used to turn the first cumulant bound into a polynomial
remainder. -/
theorem sum_range_sq_cast_le_cube (j : ℕ) :
    (∑ i ∈ Finset.range j, (i : ℝ) ^ 2) ≤ (j : ℝ) ^ 3 := by
  calc
    (∑ i ∈ Finset.range j, (i : ℝ) ^ 2) ≤ ∑ _i ∈ Finset.range j, (j : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : (i : ℝ) ≤ j := by
        exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hi)
      exact sq_le_sq' (by
        have hi_nonneg : 0 ≤ (i : ℝ) := by positivity
        have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
        linarith) hij
    _ = (j : ℝ) * (j : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (j : ℝ) ^ 3 := by ring

/-- Coarse power-sum envelope: `Σ_{i<j} i^p ≤ j^(p+1)`. -/
theorem sum_range_pow_cast_le_pow_succ (p j : ℕ) :
    (∑ i ∈ Finset.range j, (i : ℝ) ^ p) ≤ (j : ℝ) ^ (p + 1) := by
  calc
    (∑ i ∈ Finset.range j, (i : ℝ) ^ p) ≤ ∑ _i ∈ Finset.range j, (j : ℝ) ^ p := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : (i : ℝ) ≤ j := by
        exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hi)
      exact pow_le_pow_left₀ (by positivity) hij p
    _ = (j : ℝ) * (j : ℝ) ^ p := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (j : ℝ) ^ (p + 1) := by
      rw [pow_succ]
      ring

/-- First-cumulant log-product remainder in the half-range `2j ≤ d`, with the denominator
removed. -/
theorem log_phi_first_cumulant_abs_bound_half {j d : ℕ} (hd : 0 < d)
    (hhalf : 2 * j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d| ≤
      2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ 2 := by
  have hjd : j ≤ d := by omega
  have hbase := log_phi_first_cumulant_abs_bound hd hjd
  calc
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d|
        ≤ ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ 2 / (1 - (i : ℝ) / d)) := hbase
    _ ≤ ∑ i ∈ Finset.range j, (2 * ((i : ℝ) / d) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < j := Finset.mem_range.mp hi
      have hdp : (0 : ℝ) < d := by exact_mod_cast hd
      have hnorm : (i : ℝ) / d ≤ (1 : ℝ) / 2 := by
        rw [div_le_iff₀ hdp]
        have hi2 : 2 * i ≤ d := by omega
        have hi2r : (2 : ℝ) * i ≤ d := by exact_mod_cast hi2
        nlinarith
      exact log_tail_div_one_sub_le_two_sq hnorm
    _ = 2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ 2 := by
      rw [Finset.mul_sum]

/-- Coarse polynomial version of the half-range first-cumulant log-product bound. -/
theorem log_phi_first_cumulant_abs_bound_half_cube {j d : ℕ} (hd : 0 < d)
    (hhalf : 2 * j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d| ≤
      2 * (j : ℝ) ^ 3 / (d : ℝ) ^ 2 := by
  have hhalf_bound := log_phi_first_cumulant_abs_bound_half hd hhalf
  have hsum_div : (∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ 2) =
      (∑ i ∈ Finset.range j, (i : ℝ) ^ 2) / (d : ℝ) ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow]
  have hsum_sq := sum_range_sq_cast_le_cube j
  calc
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) + (j.choose 2 : ℝ) / d|
        ≤ 2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ 2 := hhalf_bound
    _ = 2 * ((∑ i ∈ Finset.range j, (i : ℝ) ^ 2) / (d : ℝ) ^ 2) := by rw [hsum_div]
    _ ≤ 2 * ((j : ℝ) ^ 3 / (d : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hsum_sq (by positivity)) (by norm_num)
    _ = 2 * (j : ℝ) ^ 3 / (d : ℝ) ^ 2 := by ring

/-- All-orders half-range polynomial consequence of the R1 log-product truncation. -/
theorem log_phi_cumulant_abs_bound_half_power (n : ℕ) {j d : ℕ} (hd : 0 < d)
    (hhalf : 2 * j ≤ d) :
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) +
        ∑ i ∈ Finset.range j,
          (∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ))| ≤
      2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) := by
  have hjd : j ≤ d := by omega
  have hbase := log_phi_cumulant_abs_bound n hd hjd
  have htail :
      (∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d))) ≤
        2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1) := by
    calc
      (∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)))
          ≤ ∑ i ∈ Finset.range j, (2 * ((i : ℝ) / d) ^ (n + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_lt : i < j := Finset.mem_range.mp hi
        have hdp : (0 : ℝ) < d := by exact_mod_cast hd
        have hu0 : 0 ≤ (i : ℝ) / d := by positivity
        have hnorm : (i : ℝ) / d ≤ (1 : ℝ) / 2 := by
          rw [div_le_iff₀ hdp]
          have hi2 : 2 * i ≤ d := by omega
          have hi2r : (2 : ℝ) * i ≤ d := by exact_mod_cast hi2
          nlinarith
        exact log_tail_pow_div_one_sub_le_two_pow hu0 hnorm (n + 1)
      _ = 2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1) := by
        rw [Finset.mul_sum]
  have hsum_div : (∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1)) =
      (∑ i ∈ Finset.range j, (i : ℝ) ^ (n + 1)) / (d : ℝ) ^ (n + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow]
  have hpow_sum := sum_range_pow_cast_le_pow_succ (n + 1) j
  calc
    |Real.log (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) +
        ∑ i ∈ Finset.range j,
          (∑ l ∈ Finset.range n, ((i : ℝ) / d) ^ (l + 1) / (l + 1 : ℝ))|
        ≤ ∑ i ∈ Finset.range j, (((i : ℝ) / d) ^ (n + 1) / (1 - (i : ℝ) / d)) := hbase
    _ ≤ 2 * ∑ i ∈ Finset.range j, ((i : ℝ) / d) ^ (n + 1) := htail
    _ = 2 * ((∑ i ∈ Finset.range j, (i : ℝ) ^ (n + 1)) / (d : ℝ) ^ (n + 1)) := by
      rw [hsum_div]
    _ ≤ 2 * ((j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hpow_sum (by positivity)) (by norm_num)
    _ = 2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) := by ring

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
