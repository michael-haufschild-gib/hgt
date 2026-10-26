import GaloisForLFunctions.BiScaleUncertainty.DyadicMantissaTent
import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonCoercivityClassification
import GaloisForLFunctions.BiScaleUncertainty.FiniteWindowVariance

/-!
# Exact variance and optimal constants on the dyadic windows

Disjoint pairs in the last dyadic level differ by at least one quarter.
Their squared errors give the lower bound about every center. The existing
binary-parent estimate supplies the upper bound on the same native energies.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

private theorem paired_block_sum_le (r : ℕ) (hr : 0 < r) (f : ℕ → ℝ) (c : ℝ) :
    (∑ j ∈ range r, ((f (8 * r + j) - c) ^ 2 + (f (12 * r + j) - c) ^ 2)) ≤
      ∑ n ∈ Icc 1 (16 * r - 1), (f n - c) ^ 2 := by
  let U := (range r).image (fun j => 8 * r + j)
  let V := (range r).image (fun j => 12 * r + j)
  have hd : Disjoint U V := by
    apply disjoint_left.mpr
    intro n hn hm
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    obtain ⟨j, hj, he⟩ := mem_image.mp hm
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    omega
  have hsub : U ∪ V ⊆ Icc 1 (16 * r - 1) := by
    intro n hn
    rcases mem_union.mp hn with hn | hn
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
      have hj' := mem_range.mp hj
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
      have hj' := mem_range.mp hj
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hU : (∑ n ∈ U, (f n - c) ^ 2) = ∑ j ∈ range r, (f (8 * r + j) - c) ^ 2 := by
    apply sum_image
    intro i hi j hj he
    change 8 * r + i = 8 * r + j at he
    exact Nat.add_left_cancel he
  have hV : (∑ n ∈ V, (f n - c) ^ 2) = ∑ j ∈ range r, (f (12 * r + j) - c) ^ 2 := by
    apply sum_image
    intro i hi j hj he
    change 12 * r + i = 12 * r + j at he
    exact Nat.add_left_cancel he
  calc
    _ = ∑ n ∈ U ∪ V, (f n - c) ^ 2 := by rw [sum_add_distrib, sum_union hd, hU, hV]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg (f n - c))

/-- The two final-level blocks have the exact stated tent values. -/
theorem dyadicMantissaTent_paired_values (h j : ℕ) (hj : j < 2 ^ h) :
    dyadicMantissaTent (8 * 2 ^ h + j) = (j : ℝ) / (8 * (2 : ℝ) ^ h) ∧
      dyadicMantissaTent (12 * 2 ^ h + j) =
        (4 * (2 : ℝ) ^ h - (j : ℝ)) / (8 * (2 : ℝ) ^ h) := by
  have hpow : (2 : ℕ) ^ (h + 3) = 8 * 2 ^ h := by rw [pow_add]; norm_num; ring
  have hpowR : (2 : ℝ) ^ (h + 3) = 8 * (2 : ℝ) ^ h := by rw [pow_add]; norm_num; ring
  have hjR : (j : ℝ) < (2 : ℝ) ^ h := by exact_mod_cast hj
  have hq : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  constructor
  · have hjq : j ≤ 2 ^ (h + 3) := by rw [hpow]; omega
    rw [← hpow, dyadicMantissaTent_pow_add (h + 3) j hjq, hpowR,
      min_eq_left (by linarith only [hjR, hq])]
  · have hindex : 12 * 2 ^ h + j = 2 ^ (h + 3) + (4 * 2 ^ h + j) := by
      rw [hpow]
      omega
    have hjq : 4 * 2 ^ h + j ≤ 2 ^ (h + 3) := by rw [hpow]; omega
    rw [hindex, dyadicMantissaTent_pow_add (h + 3) (4 * 2 ^ h + j) hjq, hpowR]
    push_cast
    rw [min_eq_right (by have hj0 := Nat.cast_nonneg (α := ℝ) j; linarith only [hj0])]
    congr 1
    ring

/-- Each explicit pair has a uniform gap independent of the dyadic depth. -/
theorem dyadicMantissaTent_paired_gap (h j : ℕ) (hj : j < 2 ^ h) :
    (1 : ℝ) / 4 ≤ dyadicMantissaTent (12 * 2 ^ h + j) -
      dyadicMantissaTent (8 * 2 ^ h + j) := by
  rw [(dyadicMantissaTent_paired_values h j hj).1,
    (dyadicMantissaTent_paired_values h j hj).2, ← sub_div]
  have hjR : (j : ℝ) < (2 : ℝ) ^ h := by exact_mod_cast hj
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (2 : ℝ) ^ h)).mpr
  linarith only [hjR]

/-- The original tent has the required variance lower bound about every center, at every depth. -/
theorem dyadicMantissaTent_variance_lower (h : ℕ) (c : ℝ) :
    ((2 ^ (h + 4) - 1 : ℕ) : ℝ) / 2048 ≤
      ∑ n ∈ Icc 1 (2 ^ (h + 4) - 1), (dyadicMantissaTent n - c) ^ 2 := by
  have hr : 0 < (2 : ℕ) ^ h := by positivity
  have hN : (2 : ℕ) ^ (h + 4) = 16 * 2 ^ h := by rw [pow_add]; norm_num; ring
  have hp (j : ℕ) (hj : j ∈ range (2 ^ h)) : (1 : ℝ) / 32 ≤
      (dyadicMantissaTent (8 * 2 ^ h + j) - c) ^ 2 +
        (dyadicMantissaTent (12 * 2 ^ h + j) - c) ^ 2 := by
    have hg := dyadicMantissaTent_paired_gap h j (mem_range.mp hj)
    have hsq := sq_nonneg (dyadicMantissaTent (8 * 2 ^ h + j) +
      dyadicMantissaTent (12 * 2 ^ h + j) - 2 * c)
    nlinarith only [hg, hsq,
      sq_nonneg (dyadicMantissaTent (12 * 2 ^ h + j) -
        dyadicMantissaTent (8 * 2 ^ h + j) - 1 / 4)]
  have hs := sum_le_sum hp
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hs
  have htotal := hs.trans (paired_block_sum_le (2 ^ h) hr dyadicMantissaTent c)
  rw [hN]
  have hNcast : ((16 * 2 ^ h - 1 : ℕ) : ℝ) = 16 * (2 : ℝ) ^ h - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 16 * 2 ^ h)]
    push_cast
    rfl
  rw [hNcast]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  linarith only [htotal, hpos]

/-- Every valid native joint coercivity constant satisfies the exact linear lower bound. -/
theorem dyadic_window_coercivity_lower (h : ℕ) (C : ℝ)
    (hC : WindowCoercivityBound 2 (2 ^ (h + 4) - 1) C) :
    ((2 ^ (h + 4) - 1 : ℕ) : ℝ) / 4096 ≤ C := by
  let N := 2 ^ (h + 4) - 1
  have hN : 2 ≤ N := by
    have hp : (2 : ℕ) ^ (h + 4) = 16 * 2 ^ h := by rw [pow_add]; norm_num; ring
    have hh : 0 < (2 : ℕ) ^ h := by positivity
    dsimp [N]
    omega
  obtain ⟨c, hc⟩ := hC dyadicMantissaTent
  have hv := dyadicMantissaTent_variance_lower h c
  have he : biScaleJointEnergy 2 N dyadicMantissaTent ≤ 2 := by
    rw [biScaleJointEnergy, multiplicativeScaleEnergy_dyadicMantissaTent, add_zero]
    exact (additiveStepEnergy_dyadicMantissaTent_lt_two hN).le
  have hnR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hC0 : 0 ≤ C := by
    by_contra h
    have hb := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge h))
      (biScaleJointEnergy_nonneg 2 N dyadicMantissaTent)
    change (N : ℝ) / 2048 ≤ _ at hv
    linarith only [hv, hc, hb, hnR]
  have hb := mul_le_mul_of_nonneg_left he hC0
  change (N : ℝ) / 2048 ≤ _ at hv
  change (N : ℝ) / 4096 ≤ C
  linarith only [hv, hc, hb]

/-- The best constant is the infimum of the constants valid on the exact integer window. -/
def dyadicWindowBestConstant (h : ℕ) : ℝ :=
  sInf {C : ℝ | WindowCoercivityBound 2 (2 ^ (h + 4) - 1) C}

/-- The exact dyadic family has the stated two-sided linear bounds, including its smallest window. -/
theorem dyadicWindowBestConstant_bounds (h : ℕ) :
    ((2 ^ (h + 4) - 1 : ℕ) : ℝ) / 4096 ≤ dyadicWindowBestConstant h ∧
      dyadicWindowBestConstant h ≤ 24 * ((2 ^ (h + 4) - 1 : ℕ) : ℝ) := by
  let N := 2 ^ (h + 4) - 1
  have hne : {C : ℝ | WindowCoercivityBound 2 N C}.Nonempty :=
    ⟨6 * (N : ℝ), windowCoercivityBound_six_mul 2 N (by norm_num)⟩
  have hlo : BddBelow {C : ℝ | WindowCoercivityBound 2 N C} :=
    ⟨(N : ℝ) / 4096, fun C hC => dyadic_window_coercivity_lower h C hC⟩
  constructor
  · exact le_csInf hne (fun C hC => dyadic_window_coercivity_lower h C hC)
  · have hu : dyadicWindowBestConstant h ≤ 6 * (N : ℝ) :=
      csInf_le hlo (windowCoercivityBound_six_mul 2 N (by norm_num))
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    change dyadicWindowBestConstant h ≤ 24 * (N : ℝ)
    linarith only [hu, hn]

/-- The best constant is attained and controls the literal minimum squared error. -/
theorem dyadicWindowBestConstant_valid (h : ℕ) :
    WindowCoercivityBound 2 (2 ^ (h + 4) - 1) (dyadicWindowBestConstant h) := by
  apply windowCoercivityBound_sInf
  exact ⟨6 * ((2 ^ (h + 4) - 1 : ℕ) : ℝ),
    windowCoercivityBound_six_mul 2 (2 ^ (h + 4) - 1) (by norm_num)⟩

/-- The literal minimum variance obeys the exact best-constant inequality. -/
theorem integerWindowVariance_le_dyadicWindowBestConstant (h : ℕ) (f : ℕ → ℝ) :
    integerWindowVariance (2 ^ (h + 4) - 1) f ≤
      dyadicWindowBestConstant h * biScaleJointEnergy 2 (2 ^ (h + 4) - 1) f :=
  (windowCoercivityBound_iff_variance 2 (2 ^ (h + 4) - 1) _).mp
    (dyadicWindowBestConstant_valid h) f

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
