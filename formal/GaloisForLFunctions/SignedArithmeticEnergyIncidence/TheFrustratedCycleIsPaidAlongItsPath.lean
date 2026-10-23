import GaloisForLFunctions.SignedArithmeticEnergyIncidence.FrustratedCyclesSpoilLocalPayment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The frustrated cycle is paid along its path

On a frustrated cycle local payment stops at charge `½` (`FrustratedCyclesSpoilLocalPayment`).
Positivity goes further, and its certificate is **nonlocal**: the frustrated edge is paid by the
whole path around the cycle.

* **Path certificate** (`antiperiodic_le_of_certificate`): in the gauge `H = v g` every edge splits
  as `2 H_i H_{i+1} = (v_{i+1}/v_i) H_i² + (v_i/v_{i+1}) H_{i+1}² − v_i v_{i+1} (g_i − g_{i+1})²`.  On
  an antiperiodic profile (`H_{n+1} = −H_0`) the gauge `v > 0` turns negative across the
  frustrated edge, whose term becomes `−v_0 v_n (g_0 − g_n)²`.  Cauchy–Schwarz along the path
  absorbs it as soon as `v_0 v_n Σ_{i<n} 1/(v_i v_{i+1}) ≤ 1`.
* **The half-sine** `v_i = sin((2i+1)π/(2k))` solves the signed train equation with the corner
  `v_{−1} = −v_n` (`halfSine_three_term`, `halfSine_corner`), and its path budget is exactly `1`
  (`halfSine_telescope`): `1/(v_i v_{i+1})` telescopes as a difference of cotangents.
* **Exact capacity of a frustrated cycle** (`frustratedCycle_capacity`, `..._attained`): for edge
  signs `e_i = ±1` with `Π e_i = −1` on a cycle of length `k`,
  `2 Σ e_i h_i h_{i+1} ≤ 2 cos(π/k) Σ h_i²`, with equality at the gauged half-sine.  So the frustrated
  cycle form `Σ h² − 2t Σ e h h'` is nonnegative iff `2t cos(π/k) ≤ 1`
  (`frustratedCycle_nonneg_iff`).
* **The local–global window of every frustrated cycle** (`cycleWitness_nonneg_iff`,
  `cycleWitness_locallyPayable_iff`): the cycle witness is locally payable iff `t ≤ ½` and
  nonnegative iff `2t cos(π/k) ≤ 1`.  Frustration costs local payment exactly the factor
  `cos(π/k)`; for the triangle this is the window `½ < κ ≤ 1`.
-/

open Finset Real

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The path pays the frustrated edge -/

/-- One edge in the gauge `H = v g`. -/
theorem two_mul_edge_eq {a b x y : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    2 * x * y = b / a * x ^ 2 + a / b * y ^ 2 - a * b * (x / a - y / b) ^ 2 := by
  field_simp
  ring

section Certificate

variable {n : ℕ} {v H : ℕ → ℝ}

/-- Splitting every edge of the cycle in the gauge `H = v g`. -/
theorem edgeSplit_eq (hne : ∀ i ≤ n, v i ≠ 0 ∧ v (i + 1) ≠ 0) :
    2 * ∑ i ∈ range (n + 1), H i * H (i + 1) =
      (∑ i ∈ range (n + 1), v (i + 1) / v i * H i ^ 2 +
        ∑ i ∈ range (n + 1), v i / v (i + 1) * H (i + 1) ^ 2) -
      ∑ i ∈ range (n + 1), v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2 := by
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  obtain ⟨h1, h2⟩ := hne i (Nat.lt_succ_iff.1 (mem_range.1 hi))
  rw [← mul_assoc]
  exact two_mul_edge_eq h1 h2

/-- The coefficient of `H_j²` is `(v_{j+1} + v_{j−1})/v_j`, with `v_{−1} = −v_n` at the corner. -/
theorem coeffSum_eq (hvn : v (n + 1) = -v 0) (hH : H (n + 1) = -H 0) :
    ∑ i ∈ range (n + 1), v (i + 1) / v i * H i ^ 2 +
        ∑ i ∈ range (n + 1), v i / v (i + 1) * H (i + 1) ^ 2 =
      ∑ i ∈ range n, (v (i + 1 + 1) + v i) / v (i + 1) * H (i + 1) ^ 2 +
        (v 1 - v n) / v 0 * H 0 ^ 2 := by
  rw [sum_range_succ' (fun i => v (i + 1) / v i * H i ^ 2),
    sum_range_succ (fun i => v i / v (i + 1) * H (i + 1) ^ 2), hvn, hH, neg_sq, div_neg]
  have e : ∀ i ∈ range n, (v (i + 1 + 1) + v i) / v (i + 1) * H (i + 1) ^ 2 =
      v (i + 1 + 1) / v (i + 1) * H (i + 1) ^ 2 + v i / v (i + 1) * H (i + 1) ^ 2 :=
    fun i _ => by rw [add_div, add_mul]
  rw [sum_congr rfl e, sum_add_distrib, sub_div]
  ring

/-- The frustrated edge is absorbed by the path when the path budget is at most `1`. -/
theorem remainder_nonneg (hv : ∀ i ≤ n, 0 < v i) (hvn : v (n + 1) = -v 0)
    (hH : H (n + 1) = -H 0) (htel : v 0 * v n * ∑ i ∈ range n, 1 / (v i * v (i + 1)) ≤ 1) :
    0 ≤ ∑ i ∈ range (n + 1), v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2 := by
  have hv0 : 0 < v 0 := hv 0 (Nat.zero_le _)
  rw [sum_range_succ, hvn, hH, neg_div_neg_eq]
  have hw : ∀ i ∈ range n, 0 < v i * v (i + 1) := fun i hi => by
    have := mem_range.1 hi
    exact mul_pos (hv i this.le) (hv (i + 1) this)
  have hW : 0 ≤ ∑ i ∈ range n, v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2 :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi).le (sq_nonneg _)
  have htelsum : ∑ i ∈ range n, (H i / v i - H (i + 1) / v (i + 1)) = H 0 / v 0 - H n / v n :=
    sum_range_sub' (fun i => H i / v i) n
  -- Cauchy–Schwarz along the path
  have hcs : (H 0 / v 0 - H n / v n) ^ 2 ≤ (∑ i ∈ range n, 1 / (v i * v (i + 1))) *
      ∑ i ∈ range n, v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2 := by
    rw [← htelsum]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hu : ∀ i ∈ range n, 0 < 1 / (v i * v (i + 1)) := fun i hi => one_div_pos.2 (hw i hi)
    have hpos : 0 < ∑ i ∈ range n, 1 / (v i * v (i + 1)) :=
      sum_pos hu (nonempty_range_iff.2 hn.ne')
    have h := sq_sum_div_le_sum_sq_div (range n) (fun i => H i / v i - H (i + 1) / v (i + 1)) hu
    rw [div_le_iff₀ hpos] at h
    calc _ ≤ (∑ i ∈ range n, (H i / v i - H (i + 1) / v (i + 1)) ^ 2 /
          (1 / (v i * v (i + 1)))) * ∑ i ∈ range n, 1 / (v i * v (i + 1)) := h
      _ = _ := by
        rw [mul_comm]
        congr 1
        exact sum_congr rfl fun i _ => by rw [div_div_eq_mul_div, div_one, mul_comm]
  have hvv : 0 ≤ v 0 * v n := (mul_pos hv0 (hv n le_rfl)).le
  have key : v 0 * v n * (H 0 / v 0 - H n / v n) ^ 2 ≤
      ∑ i ∈ range n, v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2 :=
    calc v 0 * v n * (H 0 / v 0 - H n / v n) ^ 2
        ≤ v 0 * v n * ((∑ i ∈ range n, 1 / (v i * v (i + 1))) *
          ∑ i ∈ range n, v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hvv
      _ = (v 0 * v n * ∑ i ∈ range n, 1 / (v i * v (i + 1))) *
          ∑ i ∈ range n, v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2 := by ring
      _ ≤ 1 * ∑ i ∈ range n, v i * v (i + 1) * (H i / v i - H (i + 1) / v (i + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_right htel hW
      _ = _ := one_mul _
  have e : v n * -v 0 * (H n / v n - H 0 / v 0) ^ 2 =
      -(v 0 * v n * (H 0 / v 0 - H n / v n) ^ 2) := by ring
  rw [e]
  linarith

/-- **The frustrated edge is paid along the path.**  If `v > 0` on `0, …, n`, `v_{n+1} = −v_0`,
`v` is a signed supersolution `v_{j+1} + v_{j−1} ≤ 2c v_j` (with `v_{−1} = −v_n`) and the path
budget `v_0 v_n Σ_{i<n} 1/(v_i v_{i+1})` is at most `1`, then every antiperiodic profile has
`2 Σ_{i≤n} H_i H_{i+1} ≤ 2c Σ_{i≤n} H_i²`. -/
theorem antiperiodic_le_of_certificate {c : ℝ} (hv : ∀ i ≤ n, 0 < v i)
    (hvn : v (n + 1) = -v 0) (hH : H (n + 1) = -H 0) (hsup0 : v 1 - v n ≤ 2 * c * v 0)
    (hsup : ∀ i < n, v (i + 2) + v i ≤ 2 * c * v (i + 1))
    (htel : v 0 * v n * ∑ i ∈ range n, 1 / (v i * v (i + 1)) ≤ 1) :
    2 * ∑ i ∈ range (n + 1), H i * H (i + 1) ≤ 2 * c * ∑ i ∈ range (n + 1), H i ^ 2 := by
  have hv0 : 0 < v 0 := hv 0 (Nat.zero_le _)
  have hne : ∀ i ≤ n, v i ≠ 0 ∧ v (i + 1) ≠ 0 := by
    intro i hi
    refine ⟨(hv i hi).ne', ?_⟩
    rcases Nat.lt_or_ge i n with h | h
    · exact (hv (i + 1) h).ne'
    · rw [le_antisymm hi h, hvn]; exact neg_ne_zero.2 hv0.ne'
  rw [edgeSplit_eq hne, coeffSum_eq hvn hH]
  have hrem := remainder_nonneg hv hvn hH htel
  have hint : ∀ i ∈ range n, (v (i + 1 + 1) + v i) / v (i + 1) * H (i + 1) ^ 2 ≤
      2 * c * H (i + 1) ^ 2 := by
    intro i hi
    have hi' := mem_range.1 hi
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [div_le_iff₀ (hv (i + 1) hi')]
    exact hsup i hi'
  have h0 : (v 1 - v n) / v 0 * H 0 ^ 2 ≤ 2 * c * H 0 ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [div_le_iff₀ hv0]; exact hsup0
  have hs := sum_le_sum hint
  rw [mul_sum, sum_range_succ' (fun i => 2 * c * H i ^ 2)]
  linarith

end Certificate

/-! ### The half-sine -/

/-- The half angle `π/(2(n+1))`. -/
def halfAngle (n : ℕ) : ℝ := π / (2 * (n + 1))

/-- The phase `(2i+1) π/(2(n+1))`. -/
def halfPhase (n i : ℕ) : ℝ := (2 * (i : ℝ) + 1) * halfAngle n

/-- The half-sine `sin((2i+1)π/(2(n+1)))`. -/
def halfSine (n i : ℕ) : ℝ := sin (halfPhase n i)

theorem two_mul_succ_halfAngle (n : ℕ) : 2 * ((n : ℝ) + 1) * halfAngle n = π := by
  unfold halfAngle; field_simp

theorem halfAngle_pos (n : ℕ) : 0 < halfAngle n := by unfold halfAngle; positivity

theorem halfPhase_succ (n i : ℕ) : halfPhase n (i + 1) = halfPhase n i + 2 * halfAngle n := by
  unfold halfPhase; push_cast; ring

theorem halfPhase_zero (n : ℕ) : halfPhase n 0 = halfAngle n := by
  unfold halfPhase; push_cast; ring

theorem halfPhase_last (n : ℕ) : halfPhase n n = π - halfAngle n := by
  rw [← two_mul_succ_halfAngle n]; unfold halfPhase; ring

theorem halfPhase_after (n : ℕ) : halfPhase n (n + 1) = halfAngle n + π := by
  rw [← two_mul_succ_halfAngle n]; unfold halfPhase; push_cast; ring

theorem halfSine_pos (n : ℕ) {i : ℕ} (hi : i ≤ n) : 0 < halfSine n i := by
  unfold halfSine halfPhase
  apply sin_pos_of_pos_of_lt_pi
  · have := halfAngle_pos n; positivity
  · have hi' : (2 * (i : ℝ) + 1) < 2 * ((n : ℝ) + 1) := by
      have : (i : ℝ) ≤ n := by exact_mod_cast hi
      linarith
    calc (2 * (i : ℝ) + 1) * halfAngle n < 2 * ((n : ℝ) + 1) * halfAngle n :=
          mul_lt_mul_of_pos_right hi' (halfAngle_pos n)
      _ = π := two_mul_succ_halfAngle n

theorem halfSine_succ (n : ℕ) : halfSine n (n + 1) = -halfSine n 0 := by
  unfold halfSine; rw [halfPhase_after, sin_add_pi, halfPhase_zero]

theorem halfSine_last (n : ℕ) : halfSine n n = halfSine n 0 := by
  unfold halfSine; rw [halfPhase_last, sin_pi_sub, halfPhase_zero]

/-- The signed train equation `v_i + v_{i+2} = 2 cos(2θ) v_{i+1}`. -/
theorem halfSine_three_term (n i : ℕ) :
    halfSine n (i + 2) + halfSine n i = 2 * cos (2 * halfAngle n) * halfSine n (i + 1) := by
  unfold halfSine
  rw [show i + 2 = i + 1 + 1 from rfl, halfPhase_succ n (i + 1)]
  have e : halfPhase n i = halfPhase n (i + 1) - 2 * halfAngle n := by rw [halfPhase_succ]; ring
  rw [e, sin_add, sin_sub]
  ring

/-- The corner: `v_1 − v_n = 2 cos(2θ) v_0`, i.e. the equation at `0` with `v_{−1} = −v_n`. -/
theorem halfSine_corner (n : ℕ) :
    halfSine n 1 - halfSine n n = 2 * cos (2 * halfAngle n) * halfSine n 0 := by
  rw [halfSine_last]
  unfold halfSine
  have e1 : halfPhase n 1 = halfPhase n 0 + 2 * halfAngle n := halfPhase_succ n 0
  rw [e1, halfPhase_zero]
  have h1 : -sin (halfAngle n) = sin (halfAngle n - 2 * halfAngle n) := by
    rw [show halfAngle n - 2 * halfAngle n = -halfAngle n by ring, sin_neg]
  rw [sub_eq_add_neg, h1, sin_add, sin_sub]
  ring

/-- **The path budget of the half-sine is exactly `1`**: `1/(v_i v_{i+1})` telescopes as a
difference of cotangents. -/
theorem halfSine_telescope {n : ℕ} (hn : 1 ≤ n) :
    halfSine n 0 * halfSine n n * ∑ i ∈ range n, 1 / (halfSine n i * halfSine n (i + 1)) = 1 := by
  set θ := halfAngle n with hθ
  have hθ0 : 0 < θ := halfAngle_pos n
  have hθ2 : θ < π / 2 := by
    have h2 := two_mul_succ_halfAngle n
    have : (2 : ℝ) ≤ (n : ℝ) + 1 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                       linarith
    nlinarith [pi_pos]
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ0 (by linarith [pi_pos])
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hθ2⟩
  -- each term is a difference of cotangents over `sin 2θ`
  have hterm : ∀ i ∈ range n, 1 / (halfSine n i * halfSine n (i + 1)) =
      (cos (halfPhase n i) / sin (halfPhase n i) -
        cos (halfPhase n (i + 1)) / sin (halfPhase n (i + 1))) / sin (2 * θ) := by
    intro i hi
    have hi' := mem_range.1 hi
    have h1 : sin (halfPhase n i) ≠ 0 := (halfSine_pos n hi'.le).ne'
    have h2 : sin (halfPhase n (i + 1)) ≠ 0 := (halfSine_pos n hi').ne'
    have h3 : sin (2 * θ) ≠ 0 := by rw [sin_two_mul]; positivity
    have hsub : sin (2 * θ) = sin (halfPhase n (i + 1)) * cos (halfPhase n i) -
        cos (halfPhase n (i + 1)) * sin (halfPhase n i) := by
      rw [← sin_sub, halfPhase_succ, ← hθ]; congr 1; ring
    unfold halfSine
    rw [eq_div_iff h3, hsub]
    field_simp
  rw [sum_congr rfl hterm, ← sum_div,
    sum_range_sub' (fun i => cos (halfPhase n i) / sin (halfPhase n i)) n]
  unfold halfSine
  rw [halfPhase_last, halfPhase_zero, sin_pi_sub, cos_pi_sub, sin_two_mul]
  field_simp
  ring

/-! ### The exact capacity of a frustrated cycle -/

/-- **Capacity of an antiperiodic path**: if `H_{n+1} = −H_0` then
`2 Σ_{i≤n} H_i H_{i+1} ≤ 2 cos(π/(n+1)) Σ_{i≤n} H_i²`. -/
theorem antiperiodic_capacity (n : ℕ) (H : ℕ → ℝ) (hH : H (n + 1) = -H 0) :
    2 * ∑ i ∈ range (n + 1), H i * H (i + 1) ≤
      2 * cos (π / (n + 1)) * ∑ i ∈ range (n + 1), H i ^ 2 := by
  have hc : π / ((n : ℝ) + 1) = 2 * halfAngle n := by unfold halfAngle; field_simp
  rw [hc]
  refine antiperiodic_le_of_certificate (v := halfSine n) (fun i hi => halfSine_pos n hi)
    (halfSine_succ n) hH (halfSine_corner n).le (fun i _ => ?_) ?_
  · rw [halfSine_three_term]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (halfSine_telescope hn).le

/-- The half-sine attains the antiperiodic capacity. -/
theorem antiperiodic_capacity_attained (n : ℕ) :
    2 * ∑ i ∈ range (n + 1), halfSine n i * halfSine n (i + 1) =
      2 * cos (π / (n + 1)) * ∑ i ∈ range (n + 1), halfSine n i ^ 2 := by
  have hc : π / ((n : ℝ) + 1) = 2 * halfAngle n := by unfold halfAngle; field_simp
  rw [hc]
  have hv0 := halfSine_pos n (Nat.zero_le n)
  have hne : ∀ i ≤ n, halfSine n i ≠ 0 ∧ halfSine n (i + 1) ≠ 0 := by
    intro i hi
    refine ⟨(halfSine_pos n hi).ne', ?_⟩
    rcases Nat.lt_or_ge i n with h | h
    · exact (halfSine_pos n h).ne'
    · rw [le_antisymm hi h, halfSine_succ]; exact neg_ne_zero.2 hv0.ne'
  rw [edgeSplit_eq hne, coeffSum_eq (halfSine_succ n) (halfSine_succ n)]
  -- the gauge is the profile itself: no remainder, and every coefficient is `2 cos 2θ`
  have hR : ∑ i ∈ range (n + 1), halfSine n i * halfSine n (i + 1) *
      (halfSine n i / halfSine n i - halfSine n (i + 1) / halfSine n (i + 1)) ^ 2 = 0 :=
    sum_eq_zero fun i hi => by
      obtain ⟨h1, h2⟩ := hne i (Nat.lt_succ_iff.1 (mem_range.1 hi))
      rw [div_self h1, div_self h2, sub_self, zero_pow two_ne_zero, mul_zero]
  have hint : ∀ i ∈ range n, (halfSine n (i + 1 + 1) + halfSine n i) / halfSine n (i + 1) *
      halfSine n (i + 1) ^ 2 = 2 * cos (2 * halfAngle n) * halfSine n (i + 1) ^ 2 := by
    intro i hi
    have hp := (halfSine_pos n (mem_range.1 hi)).ne'
    rw [show i + 1 + 1 = i + 2 from rfl, halfSine_three_term]
    field_simp
  have h0 : (halfSine n 1 - halfSine n n) / halfSine n 0 * halfSine n 0 ^ 2 =
      2 * cos (2 * halfAngle n) * halfSine n 0 ^ 2 := by
    rw [halfSine_corner]; field_simp
  rw [hR, sub_zero, sum_congr rfl hint, h0, mul_sum, sum_range_succ' (fun i => 2 * cos (2 * halfAngle n) * halfSine n i ^ 2)]

/-- **Exact capacity of a frustrated cycle**: for signs `e_i = ±1` with `Π_{i≤n} e_i = −1` and a
profile on the cycle (`h_{n+1} = h_0`), `2 Σ e_i h_i h_{i+1} ≤ 2 cos(π/(n+1)) Σ h_i²`. -/
theorem frustratedCycle_capacity {e : ℕ → ℝ} (he : ∀ i, e i ^ 2 = 1) {n : ℕ}
    (hhol : ∏ i ∈ range (n + 1), e i = -1) (h : ℕ → ℝ) (hk : h (n + 1) = h 0) :
    2 * ∑ i ∈ range (n + 1), e i * h i * h (i + 1) ≤
      2 * cos (π / (n + 1)) * ∑ i ∈ range (n + 1), h i ^ 2 := by
  have key := antiperiodic_capacity n (fun i => prefixSign e i * h i) (by
    simp only [prefixSign, hhol, hk, prod_range_zero]; ring)
  have e1 : ∀ i, prefixSign e i * h i * (prefixSign e (i + 1) * h (i + 1)) =
      e i * h i * h (i + 1) := by
    intro i
    rw [prefixSign_succ]
    linear_combination (e i * h i * h (i + 1)) * prefixSign_sq he i
  have e2 : ∀ i, (prefixSign e i * h i) ^ 2 = h i ^ 2 := by
    intro i; rw [mul_pow, prefixSign_sq he, one_mul]
  simp only [e1, e2] at key
  exact key

/-- The gauged half-sine attains the capacity of the frustrated cycle. -/
theorem frustratedCycle_capacity_attained {e : ℕ → ℝ} (he : ∀ i, e i ^ 2 = 1) {n : ℕ}
    (hhol : ∏ i ∈ range (n + 1), e i = -1) :
    ∃ h : ℕ → ℝ, h (n + 1) = h 0 ∧ 0 < ∑ i ∈ range (n + 1), h i ^ 2 ∧
      2 * ∑ i ∈ range (n + 1), e i * h i * h (i + 1) =
        2 * cos (π / (n + 1)) * ∑ i ∈ range (n + 1), h i ^ 2 := by
  refine ⟨fun i => prefixSign e i * halfSine n i, ?_, ?_, ?_⟩
  · simp only [prefixSign, hhol, halfSine_succ, prod_range_zero]; ring
  · have e2 : ∀ i, (prefixSign e i * halfSine n i) ^ 2 = halfSine n i ^ 2 := by
      intro i; rw [mul_pow, prefixSign_sq he, one_mul]
    simp only [e2]
    exact sum_pos (fun i hi => pow_pos (halfSine_pos n (Nat.lt_succ_iff.1 (mem_range.1 hi))) 2)
      (nonempty_range_iff.2 (Nat.succ_ne_zero n))
  · have e1 : ∀ i, e i * (prefixSign e i * halfSine n i) * (prefixSign e (i + 1) * halfSine n (i + 1)) =
        halfSine n i * halfSine n (i + 1) := by
      intro i
      rw [prefixSign_succ]
      have h2 := prefixSign_sq he i
      have h3 := he i
      linear_combination (halfSine n i * halfSine n (i + 1)) * (e i ^ 2 * h2 + h3)
    have e2 : ∀ i, (prefixSign e i * halfSine n i) ^ 2 = halfSine n i ^ 2 := by
      intro i; rw [mul_pow, prefixSign_sq he, one_mul]
    simp only [e1, e2]
    exact antiperiodic_capacity_attained n

/-- **The frustrated cycle form is nonnegative iff `2t cos(π/k) ≤ 1`**, for `t ≥ 0`. -/
theorem frustratedCycle_nonneg_iff {e : ℕ → ℝ} (he : ∀ i, e i ^ 2 = 1) {n : ℕ}
    (hhol : ∏ i ∈ range (n + 1), e i = -1) {t : ℝ} (ht : 0 ≤ t) :
    (∀ h : ℕ → ℝ, h (n + 1) = h 0 →
      0 ≤ ∑ i ∈ range (n + 1), h i ^ 2 - 2 * t * ∑ i ∈ range (n + 1), e i * h i * h (i + 1)) ↔
      2 * t * cos (π / (n + 1)) ≤ 1 := by
  constructor
  · intro H
    obtain ⟨h, hk, hpos, heq⟩ := frustratedCycle_capacity_attained he hhol
    have := H h hk
    nlinarith
  · intro htc h hk
    have hcap := frustratedCycle_capacity he hhol h hk
    have hA : 0 ≤ ∑ i ∈ range (n + 1), h i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hcap ht]

/-! ### The local–global window of every frustrated cycle -/

section Window

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_pairCoupling_right (a b x : ι) :
    ∑ y, pairCoupling a b x y = if x = a then 1 else 0 := by
  unfold pairCoupling
  by_cases hx : x = a
  · simp only [hx, true_and, if_true, sum_ite_eq', mem_univ]
  · simp only [hx, false_and, if_false, sum_const_zero]

omit [Fintype ι] in
/-- An injective index map meets each point at most once. -/
theorem sum_ite_eq_le_one {s : Finset ℕ} {w : ℕ → ι} (hw : Set.InjOn w s) (x : ι) :
    ∑ i ∈ s, (if x = w i then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ i ∈ s, x = w i
  · obtain ⟨i, hi, hxi⟩ := h
    rw [sum_eq_single_of_mem i hi fun j hj hji => if_neg fun hxj =>
      hji (hw hj hi (hxj.symm.trans hxi))]
    simp only [hxi, if_true, le_refl]
  · push Not at h
    rw [sum_eq_zero fun i hi => if_neg (h i hi)]
    norm_num

/-- The cycle witness is locally payable at charge `t ≤ ½`: each point lends `t` to each of its
two cycle edges. -/
theorem cycleWitness_locallyPayable {σ : ι → ι → ℝ} (hσ : IsSymmetricCoupling σ) {v : ℕ → ι}
    {k : ℕ} (hk : 2 ≤ k) (hinj : ∀ i j, i < k → j < k → v i = v j → i = j) (hvk : v k = v 0)
    (hedge : ∀ i < k, σ (v i) (v (i + 1)) ≠ 0) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    LocallyPayable (cycleWitness σ v k t) := by
  -- consecutive points are distinct
  have hne : ∀ i < k, v i ≠ v (i + 1) := by
    intro i hi h
    rcases Nat.lt_or_ge (i + 1) k with h1 | h1
    · exact absurd (hinj i (i + 1) hi h1 h) (by omega)
    · have hik : i + 1 = k := by omega
      rw [hik, hvk] at h
      exact absurd (hinj i 0 hi (by omega) h) (by omega)
  have hinj0 : Set.InjOn v (range k : Finset ℕ) := fun i hi j hj h =>
    hinj i j (mem_range.1 hi) (mem_range.1 hj) h
  have hinj1 : Set.InjOn (fun i => v (i + 1)) (range k : Finset ℕ) := by
    intro i hi j hj h
    have hi' := mem_range.1 hi
    have hj' := mem_range.1 hj
    simp only at h
    -- reading the index `k` as `0`
    have key : ∀ m, m ≤ k → v m = v (if m = k then 0 else m) := fun m _ => by
      split_ifs with hm
      · rw [hm, hvk]
      · rfl
    rw [key (i + 1) hi', key (j + 1) hj'] at h
    have := hinj _ _ (by split_ifs <;> omega) (by split_ifs <;> omega) h
    split_ifs at this <;> omega
  refine ⟨⟨fun x y => |cycleWitness σ v k t x y|, fun x y => abs_nonneg _,
    fun x y _ => by rw [cycleWitness_isSymmetric σ v k t y x, abs_mul_abs_self, sq],
    fun x => ?_⟩⟩
  rw [cycleWitness_diag σ hne]
  -- off the diagonal `|c| ≤ t · (edge multiplicity)`
  have hle : ∀ y ∈ univ.erase x, |cycleWitness σ v k t x y| ≤ t * edgeCount v k x y := by
    intro y hy
    rw [cycleWitness_offDiag hσ hedge t (Ne.symm (mem_erase.1 hy).1), abs_mul,
      abs_of_nonneg (mul_nonneg ht0 (edgeCount_nonneg v k x y))]
    have hu : abs (σ x y / abs (σ x y)) ≤ 1 := by
      rw [abs_div, abs_abs]
      exact div_self_le_one _
    calc t * edgeCount v k x y * abs (σ x y / abs (σ x y)) ≤ t * edgeCount v k x y * 1 :=
          mul_le_mul_of_nonneg_left hu (mul_nonneg ht0 (edgeCount_nonneg v k x y))
      _ = _ := mul_one _
  have hrow : ∑ y, edgeCount v k x y =
      ∑ i ∈ range k, ((if x = v i then (1 : ℝ) else 0) + if x = v (i + 1) then 1 else 0) := by
    unfold edgeCount
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_add_distrib, sum_pairCoupling_right, sum_pairCoupling_right]
  have hcount : ∑ y, edgeCount v k x y ≤ 2 := by
    rw [hrow, sum_add_distrib]
    have h1 := sum_ite_eq_le_one hinj0 x
    have h2 := sum_ite_eq_le_one hinj1 x
    linarith
  calc ∑ y ∈ univ.erase x, |cycleWitness σ v k t x y| ≤ ∑ y ∈ univ.erase x, t * edgeCount v k x y :=
        sum_le_sum hle
    _ ≤ ∑ y, t * edgeCount v k x y :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun y _ _ =>
          mul_nonneg ht0 (edgeCount_nonneg v k x y)
    _ = t * ∑ y, edgeCount v k x y := by rw [mul_sum]
    _ ≤ t * 2 := mul_le_mul_of_nonneg_left hcount ht0
    _ ≤ 1 := by linarith

/-- **Local payment on a frustrated cycle stops at `½`.** -/
theorem cycleWitness_locallyPayable_iff {σ : ι → ι → ℝ} (hσ : IsSymmetricCoupling σ)
    {v : ℕ → ι} {k : ℕ} (hk3 : 3 ≤ k) (hinj : ∀ i j, i < k → j < k → v i = v j → i = j)
    (hvk : v k = v 0) (hedge : ∀ i < k, σ (v i) (v (i + 1)) ≠ 0) {t : ℝ} (ht0 : 0 ≤ t) :
    LocallyPayable (cycleWitness σ v k t) ↔ t ≤ 1 / 2 := by
  constructor
  · intro h
    by_contra hlt
    exact cycleWitness_not_locallyPayable hσ hk3 hinj hvk hedge (not_le.1 hlt) h
  · exact cycleWitness_locallyPayable hσ (by omega) hinj hvk hedge ht0

/-- **Positivity on a frustrated cycle stops at `1/(2 cos(π/k))`.** -/
theorem cycleWitness_nonneg_iff (σ : ι → ι → ℝ) {v : ℕ → ι} {n : ℕ}
    (hinj : ∀ i j, i < n + 1 → j < n + 1 → v i = v j → i = j) (hvk : v (n + 1) = v 0)
    (hhol : ∏ i ∈ range (n + 1), edgeSign σ (v i) (v (i + 1)) = -1) {t : ℝ} (ht0 : 0 ≤ t) :
    (∀ f, 0 ≤ incidenceEnergy (cycleWitness σ v (n + 1) t) f) ↔
      2 * t * cos (π / (n + 1)) ≤ 1 := by
  have hinj' : Set.InjOn v (range (n + 1) : Finset ℕ) := fun i hi j hj h =>
    hinj i j (mem_range.1 hi) (mem_range.1 hj) h
  have hcyc := frustratedCycle_nonneg_iff (e := fun i => edgeSign σ (v i) (v (i + 1)))
    (fun i => edgeSign_sq σ _ _) hhol ht0
  rw [← hcyc]
  constructor
  · -- a profile on the cycle is a profile of the witness supported on the cycle points
    intro H h hk
    let f : ι → ℝ := fun x => ∑ i ∈ range (n + 1), if x = v i then h i else 0
    have hf : ∀ j < n + 1, f (v j) = h j := by
      intro j hj
      show ∑ i ∈ range (n + 1), (if v j = v i then h i else 0) = h j
      rw [sum_eq_single_of_mem j (mem_range.2 hj) fun i hi hij => if_neg fun h' =>
        hij (hinj' hi (mem_range.2 hj) h'.symm)]
      simp only [if_true]
    have hf1 : f (v (n + 1)) = h (n + 1) := by rw [hvk, hf 0 (Nat.succ_pos n), hk]
    have hsupp : ∀ x ∉ (range (n + 1)).image v, f x = 0 := by
      intro x hx
      refine sum_eq_zero fun i hi => if_neg fun h' => hx (mem_image.2 ⟨i, hi, h'.symm⟩)
    have hmass : ∑ x, f x ^ 2 = ∑ i ∈ range (n + 1), h i ^ 2 := by
      rw [← sum_subset (subset_univ ((range (n + 1)).image v)) fun x _ hx => by
        rw [hsupp x hx]; ring, sum_image fun i hi j hj h' => hinj' hi hj h']
      exact sum_congr rfl fun i hi => by rw [hf i (mem_range.1 hi)]
    have hcharge : ∑ i ∈ range (n + 1), edgeSign σ (v i) (v (i + 1)) * f (v i) * f (v (i + 1)) =
        ∑ i ∈ range (n + 1), edgeSign σ (v i) (v (i + 1)) * h i * h (i + 1) := by
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.1 hi
      rw [hf i hi']
      rcases Nat.lt_or_ge (i + 1) (n + 1) with h1 | h1
      · rw [hf (i + 1) h1]
      · rw [show i + 1 = n + 1 by omega, hf1]
    have := H f
    rw [incidenceEnergy_cycleWitness, hmass, hcharge] at this
    exact this
  · intro H f
    rw [incidenceEnergy_cycleWitness]
    have hsub : ∑ i ∈ range (n + 1), f (v i) ^ 2 ≤ ∑ x, f x ^ 2 := by
      rw [← sum_image (f := fun x => f x ^ 2) fun i hi j hj h => hinj' hi hj h]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => sq_nonneg _
    have := H (fun i => f (v i)) (congrArg f hvk)
    linarith

/-- **The local–global window of a frustrated cycle**: for `½ < t ≤ 1/(2 cos(π/k))` the cycle
witness is nonnegative and not locally payable. -/
theorem cycleWitness_window {σ : ι → ι → ℝ} (hσ : IsSymmetricCoupling σ) {v : ℕ → ι} {n : ℕ}
    (hn : 2 ≤ n) (hinj : ∀ i j, i < n + 1 → j < n + 1 → v i = v j → i = j)
    (hvk : v (n + 1) = v 0) (hedge : ∀ i < n + 1, σ (v i) (v (i + 1)) ≠ 0)
    (hhol : ∏ i ∈ range (n + 1), edgeSign σ (v i) (v (i + 1)) = -1) {t : ℝ} (ht : 1 / 2 < t)
    (htc : 2 * t * cos (π / (n + 1)) ≤ 1) :
    (∀ f, 0 ≤ incidenceEnergy (cycleWitness σ v (n + 1) t) f) ∧
      ¬ LocallyPayable (cycleWitness σ v (n + 1) t) :=
  ⟨(cycleWitness_nonneg_iff σ hinj hvk hhol (by linarith)).2 htc,
    cycleWitness_not_locallyPayable hσ (by omega) hinj hvk hedge ht⟩

end Window

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
