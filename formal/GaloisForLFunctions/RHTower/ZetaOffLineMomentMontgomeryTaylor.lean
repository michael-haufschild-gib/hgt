import GaloisForLFunctions.RHTower.ZetaOffLineMomentProportionTransfer
import GaloisForLFunctions.RHTower.LamzouriMontgomeryTaylorXiDensity
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper
import GaloisForLFunctions.RHTower.HorizontalSimplicityTradeoffDensity
import GaloisForLFunctions.HTGeometry.MidpointRadiusTrigEnclosures

/-!
# The off-line moment `66/1000` from the Montgomery–Taylor proportion

The count credit of the upper-range gate uses a lower density of simple critical zeros
(`eventually_offLineMoment_le_of_zetaGateFrom_proportion`).  Zeta23's Theorem D gives the
Montgomery–Taylor density `HD(1) = 3/2 − 2^{−1/2} cot 2^{−1/2} = 0.6725…`
(`lamzouri_montgomeryTaylor_simpleCritical_epsilon`).  With `HD(1) ≥ 1681/2500`
(`HD_one_ge`, from degree-20 Taylor enclosures of `sin` and `cos` at `s = 2^{−1/2}`, where
`s² = 1/2` makes the Taylor sums rational) and Selberg's mollifier of length `U^{21/50}` at
`R = 3/2`:

  `Σ_{0 < Im ρ ≤ V} m(ρ)(Re ρ − ½) ≤ (66/1000) V`   for all large `V`

(`eventually_offLineMoment_le_montgomeryTaylor`), and horizontal singleton fibres have lower
density at least `HD(1) − 11π/2000` (`horizontalSingleton_density_montgomeryTaylor`).
-/

open Filter

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## The Montgomery–Taylor constant -/

/-- The cosine Taylor sum at a point with square `1/2`. -/
theorem cosTaylor_ten_of_sq {s : ℝ} (hs2 : s ^ 2 = 1 / 2) :
    cosTaylor 10 s = ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j / ((2 * j).factorial : ℝ) := by
  unfold cosTaylor
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_mul, hs2]

/-- The sine Taylor sum at a point with square `1/2`. -/
theorem sinTaylor_ten_of_sq {s : ℝ} (hs2 : s ^ 2 = 1 / 2) :
    sinTaylor 10 s
      = s * ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j / ((2 * j + 1).factorial : ℝ) := by
  unfold sinTaylor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ, pow_mul, hs2]
  ring

/-- `C − (2069/2500)·S ≤ −1/20000` for the two rational Taylor sums. -/
theorem taylor_sums_gap :
    ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j / ((2 * j).factorial : ℝ)
      - 2069 / 2500 * ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j
          / ((2 * j + 1).factorial : ℝ) ≤ -(1 / 20000) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `HD(1) ≥ 1681/2500 = 0.6724`. -/
theorem HD_one_ge : (1681 / 2500 : ℝ) ≤ Zeta23.ThmD.HD 1 := by
  rw [Zeta23.ThmD.HD_one]
  set s : ℝ := (Real.sqrt 2)⁻¹ with hs
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := inv_pos.mpr hsqrt0
  have hs2 : s ^ 2 = 1 / 2 := by rw [hs, inv_pow, hsq, one_div]
  have hsqrt_le : Real.sqrt 2 ≤ 71 / 50 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs7 : 7 / 10 ≤ s := by
    rw [hs, le_inv_comm₀ (by norm_num) hsqrt0]
    linarith
  have hs1 : s < 1 := by nlinarith
  have hsabs : |s| ≤ 10 := by rw [abs_of_pos hs0]; linarith
  set C : ℝ := ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j / ((2 * j).factorial : ℝ) with hC
  set S : ℝ := ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j
    / ((2 * j + 1).factorial : ℝ) with hS
  set r : ℝ := |s| ^ 20 / (Nat.factorial 20 : ℝ) * 2 with hr
  have hr_eq : r = (1 / 2) ^ 10 / (Nat.factorial 20 : ℝ) * 2 := by
    rw [hr, abs_of_pos hs0, show (20 : ℕ) = 2 * 10 by norm_num, pow_mul, hs2]
  have hr_small : r ≤ 1 / 10 ^ 20 := by
    rw [hr_eq]
    norm_num [Nat.factorial]
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hcos := Encl.le_of_holds (encl_cos s hsabs)
  have hsin := Encl.ge_of_holds (encl_sin s hsabs)
  simp only at hcos hsin
  rw [cosTaylor_ten_of_sq hs2, ← hC, ← hr] at hcos
  rw [sinTaylor_ten_of_sq hs2, ← hS, ← hr] at hsin
  have hgap := taylor_sums_gap
  rw [← hC, ← hS] at hgap
  have hsinpos : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith [Real.pi_gt_three])
  -- `s cos s ≤ (2069/2500) sin s`
  clear_value r S C s
  have hD : C - 2069 / 2500 * S + r < 0 := by linarith
  have hkey : s * Real.cos s ≤ 2069 / 2500 * Real.sin s := by
    have h1 : s * Real.cos s ≤ s * (C + r) := mul_le_mul_of_nonneg_left hcos hs0.le
    have h2 : s * (C - 2069 / 2500 * S + r) ≤ 7 / 10 * (C - 2069 / 2500 * S + r) :=
      mul_le_mul_of_nonpos_right hs7 hD.le
    have e1 : s * (C + r) = s * C + s * r := by ring
    have e2 : s * (C - 2069 / 2500 * S + r) = s * C - 2069 / 2500 * (s * S) + s * r := by ring
    have hr' : r ≤ 1 / 100000 := le_trans hr_small (by norm_num)
    have h3 : 2069 / 2500 * (s * S - r) ≤ 2069 / 2500 * Real.sin s :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    linarith
  have hdiv : s * (Real.cos s / Real.sin s) ≤ 2069 / 2500 := by
    rw [← mul_div_assoc, div_le_iff₀ hsinpos]
    linarith
  linarith

/-! ## The off-line moment -/

/-- `e^{−335/1000} ≤ 1 − e^{−63/50}`. -/
theorem exp_neg_threeHundredThirtyFive_le_one_sub_exp_neg_sixtyThree_fiftieths :
    Real.exp (-(335 / 1000 : ℝ)) ≤ 1 - Real.exp (-(63 / 50 : ℝ)) := by
  have h1 : (43983508931 : ℝ) / 12500000000 ≤ Real.exp (63 / 50) := by
    have := Real.sum_le_exp_of_nonneg (x := (63 / 50 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have h2 : (13979 : ℝ) / 10000 ≤ Real.exp (335 / 1000) := by
    have := Real.sum_le_exp_of_nonneg (x := (335 / 1000 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have e1 : Real.exp (-(63 / 50 : ℝ)) ≤ 12500000000 / 43983508931 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith
  have e2 : Real.exp (-(335 / 1000 : ℝ)) ≤ 10000 / 13979 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith
  linarith

/-- `log c_{3/2} − (1 + 1681/2500)(3/2) + 1/1000 ≤ 4π · 66/1000`. -/
theorem log_selbergBlockConstUpper_three_halves_le_montgomeryTaylor :
    Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) - (1 + 1681 / 2500) * (3 / 2)
      + 1 / 1000 ≤ 4 * Real.pi * (66 / 1000) := by
  set y : ℝ := Real.exp (-(63 / 50 : ℝ)) with hy
  have hden := exp_neg_threeHundredThirtyFive_le_one_sub_exp_neg_sixtyThree_fiftieths
  rw [← hy] at hden
  have h1y : 0 < 1 - y := lt_of_lt_of_le (Real.exp_pos _) hden
  have hc : ZetaGateProductAFE.selbergBlockConstUpper (3 / 2) = Real.exp 3 / (1 - y) := by
    unfold ZetaGateProductAFE.selbergBlockConstUpper
    rw [hy]
    norm_num
  rw [hc, Real.log_div (Real.exp_pos _).ne' h1y.ne', Real.log_exp]
  have hlog : -(335 / 1000) ≤ Real.log (1 - y) := by
    have := Real.log_le_log (Real.exp_pos _) hden
    rwa [Real.log_exp] at this
  have hπ := Real.pi_gt_d4
  norm_num at hπ ⊢
  linarith

/-- **The off-line first moment is at most `66/1000` of the height, unconditionally.** -/
theorem eventually_offLineMoment_le_montgomeryTaylor :
    ∀ᶠ V in atTop, offLineMoment V ≤ 66 / 1000 * V := by
  have hp : (1681 / 2500 : ℝ) ≤ Zeta23.ThmD.HD 1 := HD_one_ge
  have hprop : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1681 / 2500 - ε) * (xiPosZeroCount T : ℝ) ≤ (xiSimpleCriticalZeroCount T : ℝ) := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon ε hε
    refine ⟨T₀, fun T hT => le_trans ?_ (hT₀ T hT)⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have h := eventually_offLineMoment_le_of_zetaGateFrom_proportion (α := (49 : ℝ) / 50)
    (R := 3 / 2) (η := 1 / 1000) (p := 1681 / 2500) (by norm_num) (by norm_num) (by norm_num)
    (ZetaGateProductAFE.one_le_selbergBlockConstUpper (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) hprop (ZetaGateProductAFE.zetaMollifiedMeanSquareGateFrom_selberg_upper
      (by norm_num))
  filter_upwards [h, eventually_ge_atTop 0] with V hV hV0
  have hc := log_selbergBlockConstUpper_three_halves_le_montgomeryTaylor
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * offLineMoment V ≤ 4 * Real.pi * (66 / 1000) * V :=
    hV.trans (mul_le_mul_of_nonneg_right hc hV0)
  have h2 : 4 * Real.pi * (66 / 1000) * V = 4 * Real.pi * (66 / 1000 * V) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

/-- **Horizontal singleton fibres of lower density `HD(1) − 11π/2000`.** -/
theorem horizontalSingleton_density_montgomeryTaylor :
    Zeta23.ThmD.HD 1 - 11 * Real.pi / 2000 ≤ liminf xiSingletonFiberRatio atTop := by
  have h := horizontalSingleton_density_of_moment (μ := 66 / 1000) (by norm_num) (by norm_num)
    eventually_offLineMoment_le_montgomeryTaylor
  have hid : Real.pi * (66 / 1000) / 12 = 11 * Real.pi / 2000 := by ring
  rw [hid] at h
  exact h

end

end RHTower
