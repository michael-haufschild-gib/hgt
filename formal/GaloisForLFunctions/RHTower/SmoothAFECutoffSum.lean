import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# Weighted sums of the Gaussian smooth cutoff

The direct edge of the Gaussian smooth approximate functional equation carries the weights
`n^{-1/2} V(n/x)`, where `V` is the canonical Gaussian cutoff.  Two contour bounds — `V` is
bounded, and `V(v) = O(1/v)` — combine with the two elementary comparison sums
`\sum_{n<K} n^{-1/2} \le 2\sqrt K` and `\sum_{n>K} n^{-3/2} \le 2/\sqrt K` to give
`\sum_n n^{-1/2}\,\|V(n/x)\| = O(\sqrt x)`, with the split taken at `n \approx x`.
-/

open Finset

namespace RHTower

theorem sum_range_inv_sqrt_le (K : ℕ) :
    ∑ n ∈ range K, (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt (K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hs : Real.sqrt (K : ℝ) ≤ Real.sqrt ((K : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hpos : (0 : ℝ) < Real.sqrt ((K : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      have hstep : (Real.sqrt ((K : ℝ) + 1))⁻¹
          ≤ 2 * Real.sqrt ((K : ℝ) + 1) - 2 * Real.sqrt (K : ℝ) := by
        rw [inv_eq_one_div, div_le_iff₀ hpos]
        have hsq : Real.sqrt ((K : ℝ) + 1) * Real.sqrt ((K : ℝ) + 1) = (K : ℝ) + 1 :=
          Real.mul_self_sqrt (by linarith)
        have hsq2 : Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) :=
          Real.mul_self_sqrt hK
        nlinarith [Real.sqrt_nonneg ((K : ℝ) + 1), Real.sqrt_nonneg (K : ℝ)]
      push_cast
      linarith

theorem inv_sqrt_step {m : ℝ} (hm : 1 ≤ m) :
    ((m + 1) * Real.sqrt (m + 1))⁻¹ ≤ 2 / Real.sqrt m - 2 / Real.sqrt (m + 1) := by
  set a := Real.sqrt m with ha
  set b := Real.sqrt (m + 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a * a = m := Real.mul_self_sqrt (by linarith)
  have hb2 : b * b = m + 1 := Real.mul_self_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hprod : a * b ≤ m + 1 / 2 := by nlinarith [sq_nonneg (a - b)]
  have hd : (b - a) * (a + b) = 1 := by nlinarith
  have hpos : 0 < a + b := by linarith
  have h2 : a ≤ 2 * b * b * (b - a) := by
    have hkey : a * (a + b) ≤ (2 * b * b * (b - a)) * (a + b) := by
      rw [show (2 * b * b * (b - a)) * (a + b) = 2 * b * b * ((b - a) * (a + b)) by ring,
        hd, mul_one]
      nlinarith
    exact le_of_mul_le_mul_right hkey hpos
  rw [← hb2, inv_eq_one_div, div_le_iff₀ (by positivity)]
  have hrw : (2 / a - 2 / b) * (b * b * b) = (2 * b * b * (b - a)) / a := by
    field_simp
  rw [hrw, le_div_iff₀ ha0]
  linarith

theorem sum_range_tail_inv_sqrt_cube {K : ℝ} (hK : 1 ≤ K) (L : ℕ) :
    ∑ n ∈ range L, ((K + n + 1) * Real.sqrt (K + n + 1))⁻¹
      ≤ 2 / Real.sqrt K - 2 / Real.sqrt (K + L) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ]
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have hm : (1 : ℝ) ≤ K + L := by linarith
      have hstep := inv_sqrt_step hm
      have hc : K + (L : ℝ) + 1 = (K + (L : ℝ)) + 1 := by ring
      have hc2 : K + (((L : ℕ) + 1 : ℕ) : ℝ) = (K + (L : ℝ)) + 1 := by push_cast; ring
      rw [hc, hc2]
      linarith

theorem summable_tail_inv_sqrt_cube {K : ℝ} (hK : 1 ≤ K) :
    Summable (fun n : ℕ => ((K + n + 1) * Real.sqrt (K + n + 1))⁻¹) := by
  have hK0 : (0 : ℝ) < K := by linarith
  refine summable_of_sum_range_le (c := 2 / Real.sqrt K) (fun n => ?_) (fun L => ?_)
  · have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    positivity
  · refine le_trans (sum_range_tail_inv_sqrt_cube hK L) ?_
    have : (0 : ℝ) ≤ 2 / Real.sqrt (K + L) := by positivity
    linarith

theorem tsum_tail_inv_sqrt_cube_le {K : ℝ} (hK : 1 ≤ K) :
    ∑' n : ℕ, ((K + n + 1) * Real.sqrt (K + n + 1))⁻¹ ≤ 2 / Real.sqrt K := by
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) (fun L => ?_)
  · have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hK0 : (0 : ℝ) < K := by linarith
    positivity
  · refine le_trans (sum_range_tail_inv_sqrt_cube hK L) ?_
    have : (0 : ℝ) ≤ 2 / Real.sqrt (K + L) := by positivity
    linarith

theorem exists_norm_smoothAFECutoff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : ℝ}, 0 < v → ‖smoothAFECutoff v‖ ≤ C := by
  obtain ⟨K, hK, hfar⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  obtain ⟨J, hJ, hnear⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1) one_pos
  refine ⟨max K (J + 1), le_trans hK (le_max_left _ _), fun {v} hv => ?_⟩
  rcases le_total 1 v with h1 | h1
  · refine le_trans (hfar hv) (le_trans ?_ (le_max_left _ _))
    have : v ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ h1
    nlinarith
  · have hd := hnear hv
    have hv1 : v ^ (1 : ℝ) = v := Real.rpow_one v
    rw [hv1] at hd
    have hb : ‖smoothAFECutoff v‖ ≤ J * v + 1 := by
      have := norm_sub_norm_le (smoothAFECutoff v) (1 : ℂ)
      simp at this
      linarith
    refine le_trans hb (le_trans ?_ (le_max_right _ _))
    nlinarith

/-- The `n`-th weight of the direct Gaussian edge. -/
noncomputable def cutoffWeight (x : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt ((n : ℝ) + 1))⁻¹ * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖

theorem cutoffWeight_nonneg (x : ℝ) (n : ℕ) : 0 ≤ cutoffWeight x n := by
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold cutoffWeight
  positivity

theorem exists_summable_tsum_cutoffWeight_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x : ℝ}, 1 ≤ x →
      Summable (cutoffWeight x) ∧ ∑' n : ℕ, cutoffWeight x n ≤ C * Real.sqrt x := by
  obtain ⟨C₁, hC₁, huniform⟩ := exists_norm_smoothAFECutoff_le
  obtain ⟨K, hK, hfar⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  refine ⟨3 * C₁ + 2 * K, by positivity, fun {x} hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  set N : ℕ := ⌈x⌉₊ with hNdef
  have hxN : x ≤ (N : ℝ) := Nat.le_ceil x
  have hNx : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans hx hxN
  -- the tail majorant
  have htail : ∀ n : ℕ, cutoffWeight x (n + N)
      ≤ K * x * (((N : ℝ) + n + 1) * Real.sqrt ((N : ℝ) + n + 1))⁻¹ := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcast : ((n + N : ℕ) : ℝ) + 1 = (N : ℝ) + n + 1 := by push_cast; ring
    have hpos : (0 : ℝ) < (N : ℝ) + n + 1 := by linarith
    have hv : (0 : ℝ) < ((N : ℝ) + n + 1) / x := by positivity
    have hb := hfar hv
    rw [Real.rpow_neg_one] at hb
    have hinv : (((N : ℝ) + n + 1) / x)⁻¹ = x / ((N : ℝ) + n + 1) := by
      rw [inv_div]
    rw [hinv] at hb
    unfold cutoffWeight
    rw [hcast]
    have hsq : (0 : ℝ) < Real.sqrt ((N : ℝ) + n + 1) := Real.sqrt_pos.mpr hpos
    calc (Real.sqrt ((N : ℝ) + n + 1))⁻¹ * ‖smoothAFECutoff (((N : ℝ) + n + 1) / x)‖
        ≤ (Real.sqrt ((N : ℝ) + n + 1))⁻¹ * (K * (x / ((N : ℝ) + n + 1))) := by
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K * x * (((N : ℝ) + n + 1) * Real.sqrt ((N : ℝ) + n + 1))⁻¹ := by
          field_simp
  have hsummTail : Summable (fun n : ℕ => cutoffWeight x (n + N)) := by
    refine Summable.of_nonneg_of_le (fun n => cutoffWeight_nonneg x _) htail ?_
    exact ((summable_tail_inv_sqrt_cube hN1).mul_left (K * x))
  have hsumm : Summable (cutoffWeight x) := (summable_nat_add_iff N).mp hsummTail
  refine ⟨hsumm, ?_⟩
  have hsplit := hsumm.sum_add_tsum_nat_add N
  rw [← hsplit]
  -- head
  have hhead : ∑ n ∈ range N, cutoffWeight x n ≤ 2 * C₁ * Real.sqrt (N : ℝ) := by
    have hterm : ∀ n ∈ range N, cutoffWeight x n ≤ C₁ * (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
      intro n _
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hv : (0 : ℝ) < ((n : ℝ) + 1) / x := by positivity
      unfold cutoffWeight
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (huniform hv) (by positivity)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have := sum_range_inv_sqrt_le N
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  -- tail
  have htsumTail : ∑' n : ℕ, cutoffWeight x (n + N) ≤ K * x * (2 / Real.sqrt (N : ℝ)) := by
    refine le_trans (hsummTail.tsum_le_tsum htail ((summable_tail_inv_sqrt_cube hN1).mul_left (K * x))) ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_tail_inv_sqrt_cube_le hN1) (by positivity)
  have hsqrtN : Real.sqrt (N : ℝ) ≤ Real.sqrt 2 * Real.sqrt x := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsqN : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hratio : x / Real.sqrt (N : ℝ) ≤ Real.sqrt x := by
    rw [div_le_iff₀ hsqN]
    have hsqle : Real.sqrt x ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hxN
    nlinarith
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3/2) ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hK2 : K * x * (2 / Real.sqrt (N : ℝ)) ≤ 2 * K * Real.sqrt x := by
    rw [show K * x * (2 / Real.sqrt (N : ℝ)) = 2 * K * (x / Real.sqrt (N : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  have hC2 : 2 * C₁ * Real.sqrt (N : ℝ) ≤ 3 * C₁ * Real.sqrt x := by
    calc 2 * C₁ * Real.sqrt (N : ℝ) ≤ 2 * C₁ * (Real.sqrt 2 * Real.sqrt x) := by
          exact mul_le_mul_of_nonneg_left hsqrtN (by positivity)
      _ ≤ 2 * C₁ * ((3/2) * Real.sqrt x) := by
          have : Real.sqrt 2 * Real.sqrt x ≤ (3/2) * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hs2 hsqx.le
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 3 * C₁ * Real.sqrt x := by ring
  calc ∑ n ∈ range N, cutoffWeight x n + ∑' n : ℕ, cutoffWeight x (n + N)
      ≤ 3 * C₁ * Real.sqrt x + 2 * K * Real.sqrt x := by linarith
    _ = (3 * C₁ + 2 * K) * Real.sqrt x := by ring

theorem sum_range_succ_inv_sqrt_cube_le (L : ℕ) :
    ∑ n ∈ range (L + 1), (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹
      ≤ 3 - 2 / Real.sqrt ((L : ℝ) + 1) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
      rw [Finset.sum_range_succ]
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have hm : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith
      have hstep := inv_sqrt_step hm
      have hc : (((L : ℕ) + 1 : ℕ) : ℝ) + 1 = ((L : ℝ) + 1) + 1 := by push_cast; ring
      rw [hc]
      linarith

theorem sum_range_inv_sqrt_cube_le (L : ℕ) :
    ∑ n ∈ range L, (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 3 := by
  cases L with
  | zero => norm_num
  | succ L =>
      have h := sum_range_succ_inv_sqrt_cube_le L
      have hpos : (0 : ℝ) < 2 / Real.sqrt ((L : ℝ) + 1) := by
        have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
        positivity
      linarith

theorem summable_inv_sqrt_cube :
    Summable (fun n : ℕ => (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹) := by
  refine summable_of_sum_range_le (c := 3) (fun n => ?_) sum_range_inv_sqrt_cube_le
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  positivity

theorem tsum_inv_sqrt_cube_le :
    ∑' n : ℕ, (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 3 := by
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) sum_range_inv_sqrt_cube_le
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  positivity

/-- Head sums of the direct weights grow at most like the square root of their length. -/
theorem exists_sum_range_cutoffWeight_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x : ℝ}, 0 < x → ∀ M : ℕ,
      ∑ n ∈ range M, cutoffWeight x n ≤ C * Real.sqrt (M : ℝ) := by
  obtain ⟨C₁, hC₁, huniform⟩ := exists_norm_smoothAFECutoff_le
  refine ⟨2 * C₁, by positivity, fun {x} hx M => ?_⟩
  have hterm : ∀ n ∈ range M, cutoffWeight x n ≤ C₁ * (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
    intro n _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hv : (0 : ℝ) < ((n : ℝ) + 1) / x := by positivity
    unfold cutoffWeight
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (huniform hv) (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hs := sum_range_inv_sqrt_le M
  nlinarith [Real.sqrt_nonneg (M : ℝ)]

/-- Discarding a head of the direct weights only decreases their sum. -/
theorem tsum_cutoffWeight_shift_le {x : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    ∑' n : ℕ, cutoffWeight x (n + M) ≤ ∑' n : ℕ, cutoffWeight x n := by
  obtain ⟨C, hC, hmain⟩ := exists_summable_tsum_cutoffWeight_le
  obtain ⟨hsumm, _⟩ := hmain hx
  have hsplit := hsumm.sum_add_tsum_nat_add M
  have hhead : 0 ≤ ∑ n ∈ range M, cutoffWeight x n :=
    Finset.sum_nonneg fun n _ => cutoffWeight_nonneg x n
  linarith [hsplit]

end RHTower
