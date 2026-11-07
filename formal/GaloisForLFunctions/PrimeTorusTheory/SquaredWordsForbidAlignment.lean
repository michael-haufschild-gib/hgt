import GaloisForLFunctions.PrimeTorusTheory.TheLogarithmicHankelForm
import GaloisForLFunctions.PrimeTorusTheory.NonAlignmentAtEveryLargeHeight

/-!
# Squared words forbid alignment

The word `W = Σ c_a z^a`, with integers `|c_a| ≤ H`, `c_0 ≠ 0` and a zero of order `k + 1` at `z = 1`, has the squared phase

`F(u) = (|t|/2π) Σ_{a,b} (−c_a c_b) log(u + a + b)`.

By the logarithmic Hankel form `F` is positive, decreasing and log-convex in `u`, with no cancellation to control. Three facts place
a whole interval of values of `F` away from the integers:

* `c_0 ≠ 0` makes `W` large near `z = 0`, so `F ≥ ½` up to `u ≍ log |t| / log 3H` (`three_pow_le_neg_wordForm`);
* the zero at `z = 1` makes `F` small once `u ≥ 4(M + 1)` (`abs_wordForm_le`);
* log-convexity makes the crossing of `½` slow, because it occurs past that point (`logConvex_step`).

The crossing and its consequences are in `TheMisalignmentBand`.
-/

open Finset Filter Topology Real
open scoped fwdDiff

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The squared phase of the word `c`. -/
def wordForm (M : ℕ) (c : ℕ → ℤ) (x : ℝ) : ℝ :=
  logForm (range (M + 1)) (fun a => (c a : ℝ)) (fun a => (a : ℝ)) x

theorem wordMass_eq_zero {M : ℕ} {c : ℕ → ℤ} (h0 : binomMoment M c 0 = 0) :
    ∑ a ∈ range (M + 1), (c a : ℝ) = 0 := by
  have h : ((binomMoment M c 0 : ℤ) : ℝ) = 0 := by rw [h0]; simp
  simpa [binomMoment] using h

theorem wordForm_nonpos {M : ℕ} {c : ℕ → ℤ} (h0 : binomMoment M c 0 = 0) {x : ℝ} (hx : 0 < x) :
    wordForm M c x ≤ 0 :=
  logForm_nonpos _ (fun a _ => Nat.cast_nonneg a) (wordMass_eq_zero h0) hx

/-- A word is small on `[0, 1/(3H)]` only if its constant coefficient vanishes. -/
theorem quarter_le_word_sq {M : ℕ} {c : ℕ → ℤ} {H : ℝ} (hH : 1 ≤ H) (hc : ∀ a, |(c a : ℝ)| ≤ H)
    (h0 : c 0 ≠ 0) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / (3 * H)) :
    1 / 4 ≤ (∑ a ∈ range (M + 1), (c a : ℝ) * z ^ (a : ℝ)) ^ 2 := by
  have hH0 : 0 < H := by linarith
  have hc0 : (1 : ℝ) ≤ |(c 0 : ℝ)| := by
    have : (1 : ℤ) ≤ |c 0| := Int.one_le_abs h0
    exact_mod_cast this
  have hgeom : ∀ n : ℕ, ∑ a ∈ range n, (1 / 3 : ℝ) ^ a = 3 / 2 * (1 - (1 / 3 : ℝ) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  have hz3 : z ≤ 1 / 3 := by
    refine hz.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have htail : |∑ a ∈ range M, (c (a + 1) : ℝ) * z ^ (a + 1)| ≤ 1 / 2 := by
    calc |∑ a ∈ range M, (c (a + 1) : ℝ) * z ^ (a + 1)|
        ≤ ∑ a ∈ range M, |(c (a + 1) : ℝ) * z ^ (a + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ range M, 1 / 3 * (1 / 3 : ℝ) ^ a := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 _), pow_succ']
          have h2 : z ^ a ≤ (1 / 3 : ℝ) ^ a := pow_le_pow_left₀ hz0 hz3 _
          have h3 : H * z ≤ 1 / 3 := by
            calc H * z ≤ H * (1 / (3 * H)) := mul_le_mul_of_nonneg_left hz hH0.le
              _ = 1 / 3 := by field_simp
          calc |(c (a + 1) : ℝ)| * (z * z ^ a) ≤ H * (z * z ^ a) :=
                mul_le_mul_of_nonneg_right (hc (a + 1)) (by positivity)
            _ = (H * z) * z ^ a := by ring
            _ ≤ 1 / 3 * (1 / 3 : ℝ) ^ a := mul_le_mul h3 h2 (by positivity) (by norm_num)
      _ ≤ 1 / 2 := by
          rw [← Finset.mul_sum, hgeom]
          have : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ M := by positivity
          linarith
  have hsum : ∑ a ∈ range (M + 1), (c a : ℝ) * z ^ (a : ℝ) =
      ∑ a ∈ range M, (c (a + 1) : ℝ) * z ^ (a + 1) + (c 0 : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Real.rpow_natCast, pow_zero, mul_one]
  rw [hsum]
  have hlow : (1 / 2 : ℝ) ≤ |∑ a ∈ range M, (c (a + 1) : ℝ) * z ^ (a + 1) + (c 0 : ℝ)| := by
    have h3 := abs_sub_abs_le_abs_sub (c 0 : ℝ) (-∑ a ∈ range M, (c (a + 1) : ℝ) * z ^ (a + 1))
    rw [abs_neg, sub_neg_eq_add, add_comm] at h3
    linarith
  rw [← sq_abs]
  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hlow 2
  linarith

/-- The Hilbert form of a word with `c_0 ≠ 0`. -/
theorem le_hilbertForm_word {M : ℕ} {c : ℕ → ℤ} {H : ℝ} (hH : 1 ≤ H) (hc : ∀ a, |(c a : ℝ)| ≤ H)
    (h0 : c 0 ≠ 0) {u : ℝ} (hu : 1 ≤ u) :
    (1 / (3 * H)) ^ u / (4 * u) ≤
      hilbertForm (range (M + 1)) (fun a => (c a : ℝ)) (fun a => (a : ℝ)) u := by
  have hu0 : 0 < u := by linarith
  have hH0 : 0 < H := by linarith
  set b : ℝ := 1 / (3 * H) with hb
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one (by positivity)]
    linarith
  rw [hilbertForm_eq_integral _ _ (fun a _ => Nat.cast_nonneg a) hu0]
  set f : ℝ → ℝ := fun z => z ^ (u - 1) * (∑ a ∈ range (M + 1), (c a : ℝ) * z ^ (a : ℝ)) ^ 2 with hf
  have hcont : Continuous f := by
    refine (continuous_id.rpow_const fun _ => Or.inr (by linarith)).mul (Continuous.pow ?_ 2)
    refine continuous_finsetSum _ fun a _ => continuous_const.mul ?_
    exact continuous_id.rpow_const fun _ => Or.inr (Nat.cast_nonneg a)
  have hsplit : ∫ z in (0 : ℝ)..1, f z = (∫ z in (0 : ℝ)..b, f z) + ∫ z in b..1, f z :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hnn : 0 ≤ ∫ z in b..1, f z := by
    refine intervalIntegral.integral_nonneg hb1 fun z hz => ?_
    have : 0 ≤ z := by linarith [hz.1]
    exact mul_nonneg (Real.rpow_nonneg this _) (sq_nonneg _)
  have hgcont : Continuous fun z : ℝ => z ^ (u - 1) * (1 / 4 : ℝ) :=
    (continuous_id.rpow_const fun _ => Or.inr (by linarith)).mul continuous_const
  have hlow : ∫ z in (0 : ℝ)..b, z ^ (u - 1) * (1 / 4 : ℝ) ≤ ∫ z in (0 : ℝ)..b, f z := by
    refine intervalIntegral.integral_mono_on hb0.le (hgcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun z hz => ?_
    exact mul_le_mul_of_nonneg_left (quarter_le_word_sq hH hc h0 hz.1 hz.2) (Real.rpow_nonneg hz.1 _)
  have hval : ∫ z in (0 : ℝ)..b, z ^ (u - 1) * (1 / 4 : ℝ) = b ^ u / (4 * u) := by
    rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by linarith))]
    have e : u - 1 + 1 = u := by ring
    rw [e, Real.zero_rpow hu0.ne', sub_zero]
    field_simp
  rw [hsplit, ← hval]
  linarith

/-- A word with `c_0 ≠ 0` has phase at least `(3H)^{-(x+1)}/(4(x+1))`. -/
theorem three_pow_le_neg_wordForm {M : ℕ} {c : ℕ → ℤ} {H : ℝ} (hH : 1 ≤ H)
    (hc : ∀ a, |(c a : ℝ)| ≤ H) (h0 : c 0 ≠ 0)
    (hm : binomMoment M c 0 = 0) {x : ℝ} (hx : 1 ≤ x) :
    (1 / (3 * H)) ^ (x + 1) / (4 * (x + 1)) ≤ -wordForm M c x := by
  have hx0 : 0 < x := by linarith
  have hH0 : 0 < H := by linarith
  set b : ℝ := 1 / (3 * H) with hb
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one (by positivity)]
    linarith
  set C : ℝ := b ^ (x + 1) / (4 * (x + 1)) with hC
  have hderiv : ∀ y : ℝ, 0 < y → HasDerivAt (wordForm M c)
      (hilbertForm (range (M + 1)) (fun a => (c a : ℝ)) (fun a => (a : ℝ)) y) y := fun y hy =>
    hasDerivAt_logForm _ _ (fun a _ => Nat.cast_nonneg a) hy
  have hstep := Convex.mul_sub_le_image_sub_of_le_deriv (D := Set.Icc x (x + 1)) (convex_Icc _ _)
    (f := wordForm M c)
    (fun y hy => (hderiv y (lt_of_lt_of_le hx0 hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => by
      rw [interior_Icc] at hy
      exact (hderiv y (lt_trans hx0 hy.1)).differentiableAt.differentiableWithinAt)
    (C := C) (fun y hy => by
      rw [interior_Icc] at hy
      rw [(hderiv y (lt_trans hx0 hy.1)).deriv]
      have hy1 : 1 ≤ y := by linarith [hy.1]
      refine le_trans ?_ (le_hilbertForm_word hH hc h0 hy1)
      rw [hC]
      have h1 : b ^ (x + 1) ≤ b ^ y :=
        Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hy.2.le
      have h2 : 4 * y ≤ 4 * (x + 1) := by linarith [hy.2]
      exact div_le_div₀ (by positivity) h1 (by positivity) h2)
    x (Set.left_mem_Icc.mpr (by linarith)) (x + 1) (Set.right_mem_Icc.mpr (by linarith))
    (by linarith)
  have hnp := wordForm_nonpos hm (by linarith : 0 < x + 1)
  have e : x + 1 - x = 1 := by ring
  rw [e, mul_one] at hstep
  linarith

/-- The word form as a double Newton series in the binomial moments. -/
theorem wordForm_eq_newton (M : ℕ) (c : ℕ → ℤ) (x : ℝ) :
    wordForm M c x = ∑ j ∈ range (M + 1), ∑ i ∈ range (M + 1),
      (binomMoment M c j : ℝ) * (binomMoment M c i : ℝ) * (fwdDiff (1 : ℝ))^[i + j] Real.log x := by
  have h1 : ∀ a : ℕ, ∑ b ∈ range (M + 1), (c b : ℝ) * Real.log (x + a + b) =
      ∑ j ∈ range (M + 1), (binomMoment M c j : ℝ) * (fwdDiff (1 : ℝ))^[j] Real.log (x + a) :=
    fun a => sum_word_shift_eq M c Real.log (x + a)
  have h2 : ∀ j : ℕ, ∑ a ∈ range (M + 1), (c a : ℝ) * (fwdDiff (1 : ℝ))^[j] Real.log (x + a) =
      ∑ i ∈ range (M + 1), (binomMoment M c i : ℝ) * (fwdDiff (1 : ℝ))^[i + j] Real.log x := by
    intro j
    rw [sum_word_shift_eq M c ((fwdDiff (1 : ℝ))^[j] Real.log) x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.iterate_add_apply]
  unfold wordForm logForm
  calc ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) * Real.log (x + a + b)
      = ∑ a ∈ range (M + 1), (c a : ℝ) *
          ∑ j ∈ range (M + 1), (binomMoment M c j : ℝ) * (fwdDiff (1 : ℝ))^[j] Real.log (x + a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← h1 a, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = ∑ j ∈ range (M + 1), (binomMoment M c j : ℝ) *
          ∑ a ∈ range (M + 1), (c a : ℝ) * (fwdDiff (1 : ℝ))^[j] Real.log (x + a) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h2 j, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/-- The size of one term of the double Newton series. -/
theorem newton_term_le {M i j : ℕ} {x : ℝ} (hx : 4 * ((M : ℝ) + 1) ≤ x) (hi : 1 ≤ i) :
    ((M + 1).choose (j + 1) : ℝ) * ((M + 1).choose (i + 1) : ℝ) *
        |(fwdDiff (1 : ℝ))^[i + j] Real.log x| ≤ ((M : ℝ) + 1) ^ 2 * ((1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ i) := by
  have hm : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hx0 : 0 < x := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have e1 : m + 1 + j = (m + j) + 1 := by ring
  have hd : |(fwdDiff (1 : ℝ))^[m + 1 + j] Real.log x| ≤ ((m + j).factorial : ℝ) / x ^ (m + j + 1) := by
    rw [e1]
    exact abs_fwdDiff_iter_log_le hx0
  have hA := choose_mul_factorial_le (M + 1) j
  have hB := choose_mul_factorial_le (M + 1) (m + 1)
  have hcast : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hA hB
  -- `(m+j)! ≤ (m+2)! (j+1)! 2^{m+1+j}`
  have hfac : ((m + j).factorial : ℝ) ≤
      ((j + 1).factorial : ℝ) * ((m + 1 + 1).factorial : ℝ) * 2 ^ (m + 1 + j) := by
    have h1 : (m + 1 + j).factorial ≤ 2 ^ (m + 1 + j) * ((m + 1).factorial * j.factorial) := by
      have h2 := Nat.add_choose_mul_factorial_mul_factorial (m + 1) j
      have h3 : (m + 1 + j).choose j ≤ 2 ^ (m + 1 + j) := Nat.choose_le_two_pow _ _
      calc (m + 1 + j).factorial = (m + 1 + j).choose j * (m + 1).factorial * j.factorial :=
            h2.symm
        _ = (m + 1 + j).choose j * ((m + 1).factorial * j.factorial) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ h3
    have h4 : (m + j).factorial ≤ (m + 1 + j).factorial := Nat.factorial_le (by omega)
    have h5 : (m + 1).factorial ≤ (m + 1 + 1).factorial := Nat.factorial_le (by omega)
    have h6 : j.factorial ≤ (j + 1).factorial := Nat.factorial_le (by omega)
    have h7 : (m + j).factorial ≤ (j + 1).factorial * (m + 1 + 1).factorial * 2 ^ (m + 1 + j) := by
      calc (m + j).factorial ≤ 2 ^ (m + 1 + j) * ((m + 1).factorial * j.factorial) := h4.trans h1
        _ ≤ 2 ^ (m + 1 + j) * ((m + 1 + 1).factorial * (j + 1).factorial) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul h5 h6)
        _ = _ := by ring
    exact_mod_cast h7
  have hAnn : (0 : ℝ) ≤ ((M + 1).choose (j + 1) : ℝ) := by positivity
  have hBnn : (0 : ℝ) ≤ ((M + 1).choose (m + 1 + 1) : ℝ) := by positivity
  have hxp : (0 : ℝ) < x ^ (m + j + 1) := by positivity
  have hquot : ((M : ℝ) + 1) ^ (m + j + 1) * 2 ^ (m + 1 + j) / x ^ (m + j + 1) ≤
      (1 / 2 : ℝ) ^ (m + 1 + j) := by
    have e : ((M : ℝ) + 1) ^ (m + j + 1) * 2 ^ (m + 1 + j) / x ^ (m + j + 1) =
        (2 * ((M : ℝ) + 1) / x) ^ (m + 1 + j) := by
      rw [e1, div_pow, mul_pow]
      ring
    rw [e]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [div_le_iff₀ hx0]
    linarith
  calc ((M + 1).choose (j + 1) : ℝ) * ((M + 1).choose (m + 1 + 1) : ℝ) *
        |(fwdDiff (1 : ℝ))^[m + 1 + j] Real.log x|
      ≤ ((M + 1).choose (j + 1) : ℝ) * ((M + 1).choose (m + 1 + 1) : ℝ) *
          (((j + 1).factorial : ℝ) * ((m + 1 + 1).factorial : ℝ) * 2 ^ (m + 1 + j) / x ^ (m + j + 1)) := by
        refine mul_le_mul_of_nonneg_left (hd.trans ?_) (by positivity)
        exact div_le_div_of_nonneg_right hfac hxp.le
    _ = (((M + 1).choose (j + 1) : ℝ) * ((j + 1).factorial : ℝ)) *
          (((M + 1).choose (m + 1 + 1) : ℝ) * ((m + 1 + 1).factorial : ℝ)) *
          (2 ^ (m + 1 + j) / x ^ (m + j + 1)) := by ring
    _ ≤ ((M : ℝ) + 1) ^ (j + 1) * ((M : ℝ) + 1) ^ (m + 1 + 1) * (2 ^ (m + 1 + j) / x ^ (m + j + 1)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul hA hB (by positivity) (by positivity))
          (by positivity)
    _ = ((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) ^ (m + j + 1) * 2 ^ (m + 1 + j) / x ^ (m + j + 1)) := by
        ring
    _ ≤ ((M : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (m + 1 + j) :=
        mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = _ := by
        rw [show m + 1 + j = j + (m + 1) by ring, pow_add]

/-- **A zero of order `k + 1` at `z = 1` makes the phase small** from `x = 4(M + 1)` on. -/
theorem abs_wordForm_le {M k : ℕ} {c : ℕ → ℤ} {H : ℝ} (hH : 0 ≤ H) (hc : ∀ a, |(c a : ℝ)| ≤ H)
    (hm : ∀ j ≤ k, binomMoment M c j = 0) {x : ℝ} (hx : 4 * ((M : ℝ) + 1) ≤ x) :
    |wordForm M c x| ≤ H ^ 2 * ((M : ℝ) + 1) ^ 2 * ((1 / 4 : ℝ) ^ k) := by
  classical
  rw [wordForm_eq_newton]
  set T : Finset ℕ := (range (M + 1)).filter (fun j => k < j) with hT
  have hzero : ∀ j : ℕ, j ≤ k → (binomMoment M c j : ℝ) = 0 := fun j hj => by rw [hm j hj]; simp
  have hbound : ∀ j : ℕ, |(binomMoment M c j : ℝ)| ≤ H * ((M + 1).choose (j + 1) : ℝ) := fun j => by
    unfold binomMoment
    push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : (((M + 1).choose (j + 1) : ℕ) : ℝ) = ∑ a ∈ range (M + 1), (a.choose j : ℝ) := by
      rw [← sum_range_choose_eq]
      push_cast
      rfl
    rw [h1, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (a.choose j) : (0 : ℝ) ≤ (a.choose j : ℝ))]
    exact mul_le_mul_of_nonneg_right (hc a) (Nat.cast_nonneg _)
  have hterm : ∀ j ∈ range (M + 1), ∀ i ∈ range (M + 1),
      |(binomMoment M c j : ℝ) * (binomMoment M c i : ℝ) * (fwdDiff (1 : ℝ))^[i + j] Real.log x| ≤
        (if k < j then H ^ 2 * ((M : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ j else 0) *
          (if k < i then (1 / 2 : ℝ) ^ i else 0) := by
    intro j _ i _
    by_cases hj : k < j
    · by_cases hi : k < i
      · rw [if_pos hj, if_pos hi, abs_mul, abs_mul]
        have h1 := newton_term_le (M := M) (i := i) (j := j) hx (by omega)
        have h2 : |(binomMoment M c j : ℝ)| * |(binomMoment M c i : ℝ)| *
            |(fwdDiff (1 : ℝ))^[i + j] Real.log x| ≤ (H * ((M + 1).choose (j + 1) : ℝ)) *
            (H * ((M + 1).choose (i + 1) : ℝ)) * |(fwdDiff (1 : ℝ))^[i + j] Real.log x| :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hbound j) (hbound i) (abs_nonneg _) (by positivity))
            (abs_nonneg _)
        have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ H ^ 2)
        calc _ ≤ _ := h2
          _ = H ^ 2 * (((M + 1).choose (j + 1) : ℝ) * ((M + 1).choose (i + 1) : ℝ) *
                |(fwdDiff (1 : ℝ))^[i + j] Real.log x|) := by ring
          _ ≤ _ := h3
          _ = _ := by ring
      · have : (binomMoment M c i : ℝ) = 0 := hzero i (by omega)
        simp [this, hi]
    · have : (binomMoment M c j : ℝ) = 0 := hzero j (by omega)
      simp [this, hj]
  have hgeom : ∑ i ∈ range (M + 1), (if k < i then (1 / 2 : ℝ) ^ i else 0) ≤ (1 / 2 : ℝ) ^ k := by
    rw [← Finset.sum_filter]
    have h := sum_filter_gt_pow_le (q := (1 / 2 : ℝ)) (by norm_num) le_rfl k M
    calc _ ≤ _ := h
      _ = _ := by
        rw [pow_succ]
        ring
  have hnn : 0 ≤ ∑ i ∈ range (M + 1), (if k < i then (1 / 2 : ℝ) ^ i else 0) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  calc |∑ j ∈ range (M + 1), ∑ i ∈ range (M + 1), (binomMoment M c j : ℝ) *
        (binomMoment M c i : ℝ) * (fwdDiff (1 : ℝ))^[i + j] Real.log x|
      ≤ ∑ j ∈ range (M + 1), ∑ i ∈ range (M + 1),
          (if k < j then H ^ 2 * ((M : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ j else 0) *
            (if k < i then (1 / 2 : ℝ) ^ i else 0) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => hterm j hj i hi)
    _ = H ^ 2 * ((M : ℝ) + 1) ^ 2 * ((∑ j ∈ range (M + 1), (if k < j then (1 / 2 : ℝ) ^ j else 0)) *
          (∑ i ∈ range (M + 1), (if k < i then (1 / 2 : ℝ) ^ i else 0))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hj : k < j
        · simp only [if_pos hj]
          ring
        · simp [hj]
    _ ≤ H ^ 2 * ((M : ℝ) + 1) ^ 2 * ((1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hgeom hgeom hnn (by positivity)) (by positivity)
    _ = _ := by
        have e : (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = (1 / 4 : ℝ) ^ k := by
          rw [← mul_pow]
          norm_num
        rw [e]

/-- Stripping leading zeros keeps the vanishing moments and makes the constant coefficient nonzero. -/
theorem exists_shift_zero_ne {M k : ℕ} {c : ℕ → ℤ} (hsup : ∀ a, M < a → c a = 0)
    (hne : ∃ a, c a ≠ 0) (hm : ∀ j ≤ k, binomMoment M c j = 0) :
    ∃ ν : ℕ, c (0 + ν) ≠ 0 ∧ ∀ j ≤ k, binomMoment M (fun a => c (a + ν)) j = 0 := by
  classical
  set ν := Nat.find hne with hνdef
  have hν : c ν ≠ 0 := Nat.find_spec hne
  have hmin : ∀ a < ν, c a = 0 := fun a ha => by
    have := Nat.find_min hne ha
    simpa using this
  set c' : ℕ → ℤ := fun a => c (a + ν) with hc'
  have hshift : ∀ j, binomMoment M c j =
      ∑ a ∈ range (M + 1), c' a * ((a + ν).choose j : ℤ) := by
    intro j
    unfold binomMoment
    have hsub : ∑ a ∈ range (M + 1), c a * (a.choose j : ℤ) =
        ∑ a ∈ range (ν + (M + 1)), c a * (a.choose j : ℤ) := by
      refine Finset.sum_subset (fun a ha => ?_) fun a _ ha => ?_
      · simp only [Finset.mem_range] at ha ⊢
        omega
      · have : M < a := by
          simp only [Finset.mem_range] at ha
          omega
        rw [hsup a this, zero_mul]
    rw [hsub, Finset.sum_range_add, Finset.sum_eq_zero fun a ha => by
      rw [hmin a (Finset.mem_range.mp ha), zero_mul], zero_add]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hc', add_comm a ν]
  have hexp : ∀ j, binomMoment M c j =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal j, (ν.choose q.2 : ℤ) * binomMoment M c' q.1 := by
    intro j
    rw [hshift j]
    unfold binomMoment
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.add_choose_eq]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  refine ⟨ν, by simpa using hν, ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have h1 := hexp j
    rw [hm j hj, Finset.sum_eq_single (j, 0)] at h1
    · simpa using h1.symm
    · intro q hq hne
      have hsum : q.1 + q.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      have hlt : q.1 < j := by
        by_contra hge
        apply hne
        ext <;> simp <;> omega
      rw [ih q.1 hlt (by omega), mul_zero]
    · intro hnot
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hnot

/-- A word with vanishing low moments and nonzero constant coefficient. -/
theorem exists_normalized_word {M k : ℕ}
    (h : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ (M + 1)) :
    ∃ c, IsWord M c ∧ (∀ j ≤ k, binomMoment M c j = 0) ∧ c 0 ≠ 0 := by
  obtain ⟨c, hc, hm⟩ := exists_word h
  obtain ⟨ν, hν, hm'⟩ := exists_shift_zero_ne hc.support hc.ne_zero hm
  exact ⟨fun a => c (a + ν), ⟨fun a => hc.bound _, fun a ha => hc.support _ (by omega), ⟨0, hν⟩⟩,
    hm', hν⟩

/-- A positive log-convex sequence: past index `0` a step ratio below `ρ` would make `g n` smaller than `g 0 ρ^n`. -/
theorem logConvex_step {g : ℕ → ℝ} (hpos : ∀ n, 0 < g n)
    (hc : ∀ n, g (n + 1) ^ 2 ≤ g n * g (n + 2)) {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 1 ≤ n)
    (h : g 0 * ρ ^ n ≤ g n) : ρ * g n ≤ g (n + 1) := by
  by_contra hcon
  push Not at hcon
  have hdown : ∀ d, d ≤ n → g (n - d + 1) < ρ * g (n - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using hcon
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      obtain ⟨i, hi⟩ : ∃ i, n - (d + 1) = i := ⟨_, rfl⟩
      have hi2 : n - d = i + 1 := by omega
      rw [hi2] at h1
      rw [hi]
      have h2 := hc i
      have h3 : g i * g (i + 2) < g i * (ρ * g (i + 1)) :=
        mul_lt_mul_of_pos_left h1 (hpos i)
      have h4 : g (i + 1) ^ 2 < (ρ * g i) * g (i + 1) := by
        calc g (i + 1) ^ 2 ≤ g i * g (i + 2) := h2
          _ < g i * (ρ * g (i + 1)) := h3
          _ = _ := by ring
      rw [sq] at h4
      exact lt_of_mul_lt_mul_right h4 (hpos (i + 1)).le
  have hup : ∀ i, 1 ≤ i → i ≤ n → g i < g 0 * ρ ^ i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      intro h1
      have := hdown n le_rfl
      simp only [Nat.sub_self, zero_add] at this
      calc g 1 < ρ * g 0 := this
        _ = _ := by ring
    | succ i hi ih =>
      intro h1
      have h2 := ih (by omega)
      have h3 := hdown (n - i) (by omega)
      have e : n - (n - i) = i := by omega
      rw [e] at h3
      calc g (i + 1) < ρ * g i := h3
        _ ≤ ρ * (g 0 * ρ ^ i) := mul_le_mul_of_nonneg_left h2.le hρ.le
        _ = _ := by ring
  exact absurd h (not_le.mpr (hup n hn le_rfl))

/-- The phase at `x = 1` is at most `2H²(M + 1)³`. -/
theorem neg_wordForm_one_le {M : ℕ} {c : ℕ → ℤ} {H : ℝ} (hc : ∀ a, |(c a : ℝ)| ≤ H) :
    -wordForm M c 1 ≤ 2 * H ^ 2 * ((M : ℝ) + 1) ^ 3 := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hc 0)
  unfold wordForm logForm
  have hterm : ∀ a ∈ range (M + 1), ∀ b ∈ range (M + 1),
      |(c a : ℝ) * (c b : ℝ) * Real.log (1 + a + b)| ≤ H ^ 2 * (2 * ((M : ℝ) + 1)) := by
    intro a ha b hb
    have ha' : (a : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hb' : (b : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hlog0 : 0 ≤ Real.log (1 + a + b) := Real.log_nonneg (by linarith)
    have hlog1 : Real.log (1 + a + b) ≤ a + b := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + a + b)
      linarith
    rw [abs_mul, abs_mul, abs_of_nonneg hlog0]
    have h3 : |(c a : ℝ)| * |(c b : ℝ)| ≤ H ^ 2 := by
      rw [sq]
      exact mul_le_mul (hc a) (hc b) (abs_nonneg _) hH0
    exact mul_le_mul h3 (by linarith) hlog0 (by positivity)
  have hsum : |∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
      (c a : ℝ) * (c b : ℝ) * Real.log (1 + a + b)| ≤
      ((M : ℝ) + 1) * (((M : ℝ) + 1) * (H ^ 2 * (2 * ((M : ℝ) + 1)))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _a ∈ range (M + 1), ((M : ℝ) + 1) * (H ^ 2 * (2 * ((M : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun a ha => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc _ ≤ ∑ _b ∈ range (M + 1), H ^ 2 * (2 * ((M : ℝ) + 1)) :=
                Finset.sum_le_sum fun b hb => hterm a ha b hb
            _ = _ := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                push_cast
                ring
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have := neg_le_abs (∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
      (c a : ℝ) * (c b : ℝ) * Real.log (1 + a + b))
  calc _ ≤ _ := this.trans hsum
    _ = _ := by ring

end

end GaloisForLFunctions.PrimeTorusTheory
