import Mathlib.Analysis.Complex.ExponentialBounds
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheAnchorFlow

/-!
# The medium with reflectors on `½ log n`

Let reflectors sit at `x_n = ½ log n` (`logClock`), with kicks of size `|k_n| ≤ A log n/√n`: the size of the von Mangoldt weights. Between reflectors the
state cools. This is the Born model of the arithmetic medium, with any phases, signs and initial state.

**Theorem** (`abs_kickFlow_logClock`). For `n ≥ 8`,

`|κ_n| ≤ ¼ log n + ½ log(2 log n) + 5A`.

The bound has no term in the past of the flow and no inverse of a lower eigenvalue: the flow reaches `κ_n` from infinity, over a window of `≈ √n/log n` reflectors,
which is the length at which the cooling loss and the sum of kicks balance (`coolingBound_logClock`).

**The margin** (`one_sub_tanh_sq_kickFlow_ge`). `1 − r_n² ≥ e^{−10A}/(2√n log n)`. So the reflection stays inside the unit interval at a polynomial rate:
kicks of arithmetic size cannot cause contact by size. A collapse of the margin has to come from coherence of the kicks over `≳ √n` reflectors.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-- The arithmetic clock `x_n = ½ log n`. -/
def logClock (n : ℕ) : ℝ := Real.log n / 2

theorem monotone_logClock : Monotone logClock := by
  intro a b hab
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h0 : 0 ≤ Real.log (b : ℝ) := Real.log_natCast_nonneg b
    have h1 : Real.log ((0 : ℕ) : ℝ) = 0 := by simp
    simp only [logClock, h1]
    linarith
  · have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (a : ℝ) ≤ b := by exact_mod_cast hab
    have := Real.log_le_log h1 h2
    simp only [logClock]
    linarith

/-- The cooling over `x_m → x_n` is the cross-ratio of the sites. -/
theorem coolingBound_logClock {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    coolingBound (logClock n - logClock m) = Real.log (((n : ℝ) + m) / ((n : ℝ) - m)) / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt : (m : ℝ) < n := by exact_mod_cast hmn
  have he : Real.exp (-2 * (logClock n - logClock m)) = (m : ℝ) / n := by
    have e : -2 * (logClock n - logClock m) = Real.log ((m : ℝ) / n) := by
      rw [Real.log_div hm0.ne' hn0.ne']
      simp only [logClock]
      ring
    rw [e, Real.exp_log (div_pos hm0 hn0)]
  have hsub : 0 < (n : ℝ) - m := by linarith
  have hmem : (m : ℝ) / n ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [div_pos hm0 hn0], (div_le_one hn0).mpr hlt.le⟩
  rw [coolingBound, he, Real.artanh_eq_half_log hmem]
  have e2 : (1 + (m : ℝ) / n) / (1 - (m : ℝ) / n) = ((n : ℝ) + m) / ((n : ℝ) - m) := by
    field_simp
  rw [e2]
  ring

/-- `log n ≤ 2√n`. -/
theorem log_nat_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) : Real.log n ≤ 2 * Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log n = 2 * Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt hn0.le]
    ring
  rw [h2]
  linarith

/-- **The a priori estimate.** Kicks of arithmetic size at the reflectors `½ log n` keep the flow below
`¼ log n + ½ log(2 log n) + 5A`, with any phases and any initial state. -/
theorem abs_kickFlow_logClock {k : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hk : ∀ l : ℕ, 2 ≤ l → |k l| ≤ A * Real.log l / Real.sqrt l) (κ₀ : ℝ) {n : ℕ} (hn : 8 ≤ n) :
    |kickFlow logClock k κ₀ n| ≤
      Real.log n / 4 + Real.log (2 * Real.log n) / 2 + 5 * A := by
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set s : ℝ := Real.sqrt n with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hn0
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hs2 : 2 ≤ s := by nlinarith
  set L : ℝ := Real.log n with hL
  have hL2 : 2 ≤ L := by
    have h8 : Real.log 8 ≤ L := Real.log_le_log (by norm_num) hn8
    have h3 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_gt_d9
    rw [h3] at h8
    linarith
  have hLs : L ≤ 2 * s := log_nat_le_two_sqrt (by omega)
  -- the window of `j ≈ √n/log n` reflectors
  set y : ℝ := s / L with hy
  have hypos : 0 < y := div_pos hspos (by linarith)
  set j : ℕ := ⌈y⌉₊ with hj
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hypos).ne'
  have hjy : y ≤ j := Nat.le_ceil y
  have hjup : (j : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hypos.le).le
  have hyle : y ≤ s / 2 := div_le_div_of_nonneg_left hspos.le (by norm_num) hL2
  have hjn : 2 * (j : ℝ) ≤ n := by nlinarith
  have hjn' : j < n := by
    have : (j : ℝ) < n := by linarith [(by exact_mod_cast hj1 : (1 : ℝ) ≤ j)]
    exact_mod_cast this
  set m : ℕ := n - j with hm
  have hmj : m + j = n := Nat.sub_add_cancel hjn'.le
  have hmcast : (m : ℝ) = (n : ℝ) - j := by
    rw [hm, Nat.cast_sub hjn'.le]
  have hmge : (n : ℝ) / 2 ≤ m := by rw [hmcast]; linarith
  have hm4 : 4 ≤ m := by
    have : (4 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hmn : m < n := by omega
  have hxlt : logClock m < logClock (m + j) := by
    rw [hmj]
    have h1 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have h2 : (m : ℝ) < n := by exact_mod_cast hmn
    have := Real.log_lt_log h1 h2
    simp only [logClock]
    linarith
  have hmain := abs_kickFlow_le (k := k) monotone_logClock κ₀ m j hxlt
  rw [hmj] at hmain
  refine hmain.trans ?_
  -- the cooling part
  have hcool : coolingBound (logClock n - logClock m) ≤ L / 4 + Real.log (2 * L) / 2 := by
    rw [coolingBound_logClock (by omega) hmn]
    have hsub : (n : ℝ) - m = j := by rw [hmcast]; ring
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    have hLpos : 0 < L := by linarith
    have hratio : ((n : ℝ) + m) / ((n : ℝ) - m) ≤ s * (2 * L) := by
      rw [hsub, div_le_iff₀ hjpos]
      have h1 : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
      have h2 : s * (2 * L) * y = 2 * (s * s) := by
        rw [hy]
        field_simp
      have h3 : s * (2 * L) * y ≤ s * (2 * L) * j :=
        mul_le_mul_of_nonneg_left hjy (by positivity)
      rw [hss] at h2
      linarith
    have hpos : 0 < ((n : ℝ) + m) / ((n : ℝ) - m) := by
      rw [hsub]
      positivity
    have h4 := Real.log_le_log hpos hratio
    rw [Real.log_mul hspos.ne' (by positivity), hs, Real.log_sqrt hn0.le] at h4
    linarith
  -- the kicks
  have hkick : ∑ i ∈ range j, |k (m + i + 1)| ≤ 5 * A := by
    have hbound : ∀ i ∈ range j, |k (m + i + 1)| ≤ A * L * (Real.sqrt 2 / s) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      set l := m + i + 1 with hl
      have hl2 : 2 ≤ l := by omega
      have hln : l ≤ n := by omega
      have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have hlle : (l : ℝ) ≤ n := by exact_mod_cast hln
      have hlge : (n : ℝ) / 2 ≤ l := by
        have : (m : ℝ) ≤ l := by exact_mod_cast (by omega : m ≤ l)
        linarith
      have hlog : Real.log l ≤ L := Real.log_le_log hlpos hlle
      have hlog0 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
      have hsqrt : s / Real.sqrt 2 ≤ Real.sqrt l := by
        rw [hs, ← Real.sqrt_div hn0.le]
        exact Real.sqrt_le_sqrt hlge
      have hs2pos : 0 < Real.sqrt 2 := by positivity
      have hinv : 1 / Real.sqrt l ≤ Real.sqrt 2 / s := by
        have hq : 0 < s / Real.sqrt 2 := by positivity
        calc 1 / Real.sqrt l ≤ 1 / (s / Real.sqrt 2) := one_div_le_one_div_of_le hq hsqrt
          _ = Real.sqrt 2 / s := by field_simp
      calc |k l| ≤ A * Real.log l / Real.sqrt l := hk l hl2
        _ = A * Real.log l * (1 / Real.sqrt l) := by ring
        _ ≤ A * L * (Real.sqrt 2 / s) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlog hA) hinv (by positivity) (by positivity)
    refine (Finset.sum_le_sum hbound).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hLpos : 0 < L := by linarith
    have hs2le : Real.sqrt 2 ≤ 5 / 3 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have e1 : (j : ℝ) * (A * L * (Real.sqrt 2 / s)) ≤ (y + 1) * (A * L * (Real.sqrt 2 / s)) :=
      mul_le_mul_of_nonneg_right hjup (by positivity)
    have e2 : (y + 1) * (A * L * (Real.sqrt 2 / s)) = A * Real.sqrt 2 * (1 + L / s) := by
      rw [hy]
      field_simp
    have e3 : L / s ≤ 2 := by
      rw [div_le_iff₀ hspos]
      linarith
    have e4 : A * Real.sqrt 2 * (1 + L / s) ≤ A * (5 / 3) * (1 + 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs2le hA) (by linarith) (by positivity) (by positivity)
    linarith
  linarith

/-- `1 − tanh² κ ≥ e^{−2|κ|}`. -/
theorem exp_neg_two_abs_le (κ : ℝ) : Real.exp (-2 * |κ|) ≤ 1 - Real.tanh κ ^ 2 := by
  rw [one_sub_tanh_sq]
  have hc : Real.cosh κ ≤ Real.exp |κ| := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have := Real.exp_pos (-|κ|)
    have h2 : Real.exp (-|κ|) ≤ Real.exp |κ| := Real.exp_le_exp.mpr (by linarith [abs_nonneg κ])
    linarith
  have hc0 := Real.cosh_pos κ
  have e : Real.exp (-2 * |κ|) = 1 / Real.exp |κ| ^ 2 := by
    rw [one_div, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [e]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hc0.le hc 2)

/-- **The margin of the reflection.** Arithmetic kicks keep `1 − r_n² ≥ e^{−10A}/(2√n log n)`. -/
theorem one_sub_tanh_sq_kickFlow_ge {k : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hk : ∀ l : ℕ, 2 ≤ l → |k l| ≤ A * Real.log l / Real.sqrt l) (κ₀ : ℝ) {n : ℕ} (hn : 8 ≤ n) :
    Real.exp (-(10 * A)) / (2 * Real.sqrt n * Real.log n) ≤
      1 - Real.tanh (kickFlow logClock k κ₀ n) ^ 2 := by
  refine le_trans ?_ (exp_neg_two_abs_le _)
  have hb := abs_kickFlow_logClock hA hk κ₀ hn
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have e : Real.exp (-(10 * A)) / (2 * Real.sqrt n * Real.log n) =
      Real.exp (-(2 * (Real.log n / 4 + Real.log (2 * Real.log n) / 2 + 5 * A))) := by
    have hp : 0 < 2 * Real.sqrt n * Real.log n := by positivity
    have e1 : Real.log (2 * Real.sqrt n * Real.log n) = Real.log n / 2 + Real.log (2 * Real.log n) := by
      rw [show 2 * Real.sqrt n * Real.log n = Real.sqrt n * (2 * Real.log n) by ring,
        Real.log_mul hs.ne' (by positivity), Real.log_sqrt hn0.le]
    rw [div_eq_iff hp.ne']
    have e2 : 2 * Real.sqrt n * Real.log n = Real.exp (Real.log n / 2 + Real.log (2 * Real.log n)) := by
      rw [← e1, Real.exp_log hp]
    rw [e2, ← Real.exp_add]
    congr 1
    ring
  rw [e]
  apply Real.exp_le_exp.mpr
  linarith

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
