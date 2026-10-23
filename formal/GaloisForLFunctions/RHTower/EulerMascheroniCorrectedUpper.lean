import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# A corrected upper sequence for the Euler--Mascheroni constant

Subtracting `1 / (2 * (n + 1))` from the standard upper sequence
`H_n - log n` preserves strict decrease to Euler's constant while removing
its first-order error.  The proof uses the rational Padé lower bound
`2x / (x + 2) < log (1 + x)`.

At the factorable index `1250 = 2 * 5^(4 : ℕ)`, this gives the exact certified
bound `gamma < 0.577216` without a large harmonic evaluation.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- First-order-corrected upper approximation to Euler's constant. -/
def eulerMascheroniCorrectedUpper (n : ℕ) : ℝ :=
  if n = 0 then 2 else
    Real.eulerMascheroniSeq' n - 1 / (2 * ((n : ℝ) + 1))

/-- The corrected upper approximants are strictly decreasing. -/
theorem strictAnti_eulerMascheroniCorrectedUpper :
    StrictAnti eulerMascheroniCorrectedUpper := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  rcases n with _ | n
  · norm_num [eulerMascheroniCorrectedUpper, Real.eulerMascheroniSeq']
  · let m : ℕ := n + 1
    have hm0 : 0 < (m : ℝ) := by
      dsimp only [m]
      positivity
    have hm1 : 0 < (m : ℝ) + 1 := by positivity
    have hm2 : 0 < (m : ℝ) + 2 := by positivity
    have hlogPadé := Real.lt_log_one_add_of_pos (x := 1 / (m : ℝ)) (by positivity)
    have hlogEq :
        Real.log (1 + 1 / (m : ℝ)) =
          Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
      rw [show 1 + 1 / (m : ℝ) = ((m : ℝ) + 1) / (m : ℝ) by
        field_simp]
      rw [Real.log_div hm1.ne' hm0.ne']
    have hrat :
        (2 * (m : ℝ) + 5) / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) <
          2 / (2 * (m : ℝ) + 1) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hlog :
        (2 * (m : ℝ) + 5) / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) <
          Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
      rw [← hlogEq]
      apply hrat.trans
      calc
        2 / (2 * (m : ℝ) + 1) =
            2 * (1 / (m : ℝ)) / (1 / (m : ℝ) + 2) := by
              field_simp [hm0.ne']; ring_nf
        _ < Real.log (1 + 1 / (m : ℝ)) := hlogPadé
    simp only [eulerMascheroniCorrectedUpper, Nat.succ_ne_zero, if_false]
    rw [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq']
    simp only [Nat.succ_ne_zero, if_false]
    have htarget :
        ((harmonic (m + 1) : ℚ) : ℝ) - Real.log (m + 1) -
            1 / (2 * (((m + 1 : ℕ) : ℝ) + 1)) <
          ((harmonic m : ℚ) : ℝ) - Real.log m -
            1 / (2 * ((m : ℝ) + 1)) := by
      rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      push_cast
      field_simp at hlog ⊢
      nlinarith
    simpa only [m, Nat.cast_add, Nat.cast_one] using htarget

/-- The corrected sequence has the same limit as the standard upper sequence. -/
theorem tendsto_eulerMascheroniCorrectedUpper :
    Tendsto eulerMascheroniCorrectedUpper atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hden : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
      (by norm_num)
  have hcorr :
      Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hmain := Real.tendsto_eulerMascheroniSeq'.sub hcorr
  have hmain' :
      Tendsto (fun n : ℕ => Real.eulerMascheroniSeq' n -
        1 / (2 * ((n : ℝ) + 1))) atTop
        (nhds Real.eulerMascheroniConstant) := by
    simpa only [sub_zero] using hmain
  apply hmain'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [eulerMascheroniCorrectedUpper, hn]

/-- Every corrected approximant is a strict upper bound for Euler's constant. -/
theorem eulerMascheroniConstant_lt_correctedUpper (n : ℕ) :
    Real.eulerMascheroniConstant < eulerMascheroniCorrectedUpper n := by
  refine lt_of_le_of_lt ?_
    (strictAnti_eulerMascheroniCorrectedUpper (Nat.lt_succ_self n))
  exact strictAnti_eulerMascheroniCorrectedUpper.antitone.le_of_tendsto
    tendsto_eulerMascheroniCorrectedUpper (n + 1)

/-! ## A second-order corrected upper sequence -/

/-- Second-order-corrected upper approximation `H_n - log n - 1/(2n) + 1/(12n²)` to Euler's
constant; its error is `O(n⁻⁴)`. -/
def eulerMascheroniSecondUpper (n : ℕ) : ℝ :=
  if n = 0 then 2 else
    Real.eulerMascheroniSeq' n - 1 / (2 * (n : ℝ)) + 1 / (12 * (n : ℝ) ^ 2)

/-- `H_{n+k}` splits after its first `n` terms. -/
theorem harmonic_add_eq_add_sum (n k : ℕ) :
    harmonic (n + k) = harmonic n + ∑ i ∈ Finset.range k, ((n + i + 1 : ℕ) : ℚ)⁻¹ := by
  show ∑ i ∈ Finset.range (n + k), ((i + 1 : ℕ) : ℚ)⁻¹ =
    ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℚ)⁻¹ + ∑ i ∈ Finset.range k, ((n + i + 1 : ℕ) : ℚ)⁻¹
  exact Finset.sum_range_add _ n k

/-- The first two terms of `log(1 + 1/m) = 2 Σ t^{2k+1}/(2k+1)`, `t = 1/(2m+1)`. -/
private theorem two_div_add_le_log_one_add_inv {m : ℝ} (hm : 0 < m) :
    2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3) ≤ Real.log (1 + m⁻¹) := by
  have key : 2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3) =
      ∑ k ∈ Finset.range 2, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * m + 1)) ^ (2 * k + 1) := by
    have h1 : 2 * m + 1 ≠ 0 := by positivity
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one]
    rw [show (2 * 0 + 1 : ℕ) = 1 from rfl, show (2 * 1 + 1 : ℕ) = 3 from rfl]
    field_simp
    ring
  rw [key]
  exact sum_le_hasSum (Finset.range 2) (fun i _ => by positivity)
    (Real.hasSum_log_one_add_inv hm)

/-- The monotonicity gap of the second-order sequence: after clearing denominators the difference
is `(6m² + 6m + 3) / (36 m² (m+1)² (2m+1)³) > 0`. -/
private theorem second_upper_gap_lt {m : ℝ} (hm : 0 < m) :
    1 / (2 * m) + 1 / (2 * (m + 1)) - 1 / (12 * m ^ 2) + 1 / (12 * (m + 1) ^ 2) <
      2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3) := by
  rw [← sub_pos]
  have key : 2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3) -
      (1 / (2 * m) + 1 / (2 * (m + 1)) - 1 / (12 * m ^ 2) + 1 / (12 * (m + 1) ^ 2)) =
      (6 * m ^ 2 + 6 * m + 3) / (36 * m ^ 2 * (m + 1) ^ 2 * (2 * m + 1) ^ 3) := by
    field_simp
    ring
  rw [key]
  positivity

/-- The second-order corrected approximants decrease from index `1` on. -/
theorem eulerMascheroniSecondUpper_succ_lt {n : ℕ} (hn : 1 ≤ n) :
    eulerMascheroniSecondUpper (n + 1) < eulerMascheroniSecondUpper n := by
  have hn0 : n ≠ 0 := by omega
  have hx0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n = Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_div (by positivity) hx0.ne']
    congr 1
    field_simp
  have hL := two_div_add_le_log_one_add_inv hx0
  have hS := second_upper_gap_lt hx0
  simp only [eulerMascheroniSecondUpper, Real.eulerMascheroniSeq', hn0, Nat.succ_ne_zero,
    if_false, harmonic_succ]
  push_cast
  -- the difference is `log(1 + 1/n)` minus the gap bounded in `hS`
  have hdiff : ((harmonic n : ℝ) - Real.log n - 1 / (2 * (n : ℝ)) + 1 / (12 * (n : ℝ) ^ 2)) -
      ((harmonic n : ℝ) + ((n : ℝ) + 1)⁻¹ - Real.log ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) +
        1 / (12 * ((n : ℝ) + 1) ^ 2)) =
      Real.log (1 + (n : ℝ)⁻¹) - (1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1)) -
        1 / (12 * (n : ℝ) ^ 2) + 1 / (12 * ((n : ℝ) + 1) ^ 2)) := by
    rw [← hlog]
    field_simp
    ring
  linarith

/-- The second-order sequence has Euler's constant as limit. -/
theorem tendsto_eulerMascheroniSecondUpper :
    Tendsto eulerMascheroniSecondUpper atTop (nhds Real.eulerMascheroniConstant) := by
  have h2 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have h12 : Tendsto (fun n : ℕ => 1 / (12 * (n : ℝ) ^ 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop |>.const_mul_atTop
        (by norm_num))
  have hmain := (Real.tendsto_eulerMascheroniSeq'.sub h2).add h12
  rw [sub_zero, add_zero] at hmain
  apply hmain.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [eulerMascheroniSecondUpper, hn]

/-- Every second-order approximant from index `1` on is a strict upper bound for Euler's
constant. -/
theorem eulerMascheroniConstant_lt_secondUpper {n : ℕ} (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant < eulerMascheroniSecondUpper n := by
  have hanti : StrictAnti fun k : ℕ => eulerMascheroniSecondUpper (k + 1) :=
    strictAnti_nat_of_succ_lt fun k => eulerMascheroniSecondUpper_succ_lt (by omega)
  have hlim : Tendsto (fun k : ℕ => eulerMascheroniSecondUpper (k + 1)) atTop
      (nhds Real.eulerMascheroniConstant) :=
    tendsto_eulerMascheroniSecondUpper.comp (tendsto_add_atTop_nat 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact lt_of_le_of_lt (hanti.antitone.le_of_tendsto hlim (k + 1)) (hanti (Nat.lt_succ_self k))

/-- Exact six-decimal upper bound from the second-order approximant at `16 = 2^4`, with
`log 2 > 0.6931471803`; `H_16` is evaluated as two blocks of eight terms. -/
theorem eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion :
    Real.eulerMascheroniConstant < 577216 / 1000000 := by
  refine (eulerMascheroniConstant_lt_secondUpper (n := 16) (by norm_num)).trans ?_
  have hH : harmonic 16 = 2436559 / 720720 := by
    rw [show (16 : ℕ) = 8 + 8 from rfl, harmonic_add_eq_add_sum]
    norm_num [harmonic, Finset.sum_range_succ]
  have hlog : Real.log ((16 : ℕ) : ℝ) = 4 * Real.log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_two_gt_d9
  rw [eulerMascheroniSecondUpper, if_neg (by norm_num), Real.eulerMascheroniSeq',
    if_neg (by norm_num), hH, hlog]
  norm_num
  linarith

end

end RHTower
