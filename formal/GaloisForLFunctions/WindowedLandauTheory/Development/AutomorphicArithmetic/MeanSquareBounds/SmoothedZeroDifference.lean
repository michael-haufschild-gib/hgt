import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedTruncation
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.SiegelWalfisz
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import Mathlib.Analysis.Calculus.MeanValue

/-! Bounds for differences of the primitive explicit formula in a zero-free box. -/

open Complex Finset Set UpperTheory.Top WindowedLandauTheory.HC
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

namespace QH

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private theorem norm_cpow_increment_le {ρ : ℂ} (hρ : ρ ≠ 0) {z h σ : ℝ}
    (hz : 1 ≤ z) (hh : 0 ≤ h) (hσ : σ ≤ 1) (hre : ρ.re ≤ σ) :
    ‖((z + h : ℝ) : ℂ) ^ ρ - (z : ℂ) ^ ρ‖ ≤ ‖ρ‖ * z ^ (σ - 1) * h := by
  have hz₀ : 0 < z := zero_lt_one.trans_le hz
  have hz₁ : z ≤ z + h := le_add_of_nonneg_right hh
  have hder (u : ℝ) (hu : u ∈ Set.Icc z (z + h)) :
      HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ ρ) (ρ * (u : ℂ) ^ (ρ - 1)) (Set.Icc z (z + h)) u :=
    (hasDerivAt_ofReal_cpow_const (hz₀.trans_le hu.1).ne' hρ).hasDerivWithinAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc z (z + h)) :
      ‖ρ * (u : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ * z ^ (σ - 1) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hz₀.trans_le hu.1), sub_re, one_re]
    exact mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow_of_exponent_le (hz.trans hu.1) (sub_le_sub_right hre 1)).trans
        (Real.rpow_le_rpow_of_nonpos hz₀ hu.1 (sub_nonpos.mpr hσ))) (norm_nonneg _)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (convex_Icc z (z + h)) (Set.left_mem_Icc.mpr hz₁) (Set.right_mem_Icc.mpr hz₁)
  simpa only [add_sub_cancel_left, Real.norm_of_nonneg hh] using hm

private def zeroTerm (z : ℝ) (ρ : ℂ) : ℂ :=
  (z : ℂ) ^ ρ / (ρ * (ρ - 1))

theorem norm_smoothed_zero_difference_le (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    {Q z h : ℝ} (hbox : ZeroBox Q χ) (hz : 1 ≤ z) (hh : 0 < h) {T : ℕ} (hT : 1 ≤ T)
    (hTQ : (T : ℝ) + 1 ≤ Q) :
    ‖(∑' q : LZero χ, ((z + h : ℝ) : ℂ) ^ q.point / (q.point * (q.point - 1))) -
       ∑' q : LZero χ, (z : ℂ) ^ q.point / (q.point * (q.point - 1))‖ / h ≤
      4 * localCountConst N *
        (400 * z ^ (-1 / 400 : ℝ) * Real.log (T + 3) * (2 + Real.log T) +
          8 * (2 * z + h) / h / Real.sqrt T) := by
  classical
  let E := z ^ (-1 / 400 : ℝ)
  let U := (2 * z + h) / h
  let fl (q : LZero χ) := ⌊|q.point.im|⌋₊
  let bnd (m : ℕ) : ℝ :=
    if m ≤ T then 400 * E / max 1 (m : ℝ) else U * (m : ℝ) ^ (-(2 : ℝ))
  let w (q : LZero χ) := ‖zeroTerm (z + h) q.point - zeroTerm z q.point‖ / h
  have hz₁ : 1 ≤ z + h := hz.trans (le_add_of_nonneg_right hh.le)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC := localCountConst_nonneg (NeZero.pos N)
  have hb₀ (m : ℕ) : 0 ≤ bnd m := by
    dsimp [bnd]
    split_ifs <;> positivity
  have hweight (q : LZero χ) : w q ≤ bnd (fl q) := by
    let ρ := q.point
    let m := fl q
    have hre := zero_re_mem hχ hp q
    have hρ : ρ ≠ 0 := by
      intro h
      have hzre : ρ.re = 0 := by rw [h, zero_re]
      exact hre.1.ne' hzre
    have hρ₁ : 1 - ρ ≠ 0 := by
      intro h
      have hzre : ρ.re = 1 := congrArg Complex.re (sub_eq_zero.mp h).symm
      exact hre.2.ne hzre
    have hm : (m : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
    have hmρ : (m : ℝ) ≤ ‖ρ‖ := hm.trans (abs_im_le_norm _)
    have hmρ₁ : (m : ℝ) ≤ ‖1 - ρ‖ := hm.trans (by simpa using abs_im_le_norm (1 - ρ))
    have hform : w q = ‖((z + h : ℝ) : ℂ) ^ ρ - (z : ℂ) ^ ρ‖ / (‖ρ‖ * ‖1 - ρ‖) / h := by
      dsimp [w, zeroTerm, ρ]
      rw [← sub_div, norm_div, norm_mul, norm_sub_rev q.point 1]
    have hprod : 0 < ‖ρ‖ * ‖1 - ρ‖ := mul_pos (norm_pos_iff.mpr hρ) (norm_pos_iff.mpr hρ₁)
    change w q ≤ bnd m
    rw [hform, bnd]
    by_cases hmT : m ≤ T
    · rw [if_pos hmT]
      have hm' : |ρ.im| ≤ Q := by
        apply le_trans _ hTQ
        exact (Nat.lt_floor_add_one _).le.trans (add_le_add (by exact_mod_cast hmT) le_rfl)
      have hgap : ρ.re ≤ 1 - 1 / 400 :=
        le_of_not_gt fun h => hbox ρ h hm' (LFunction_point_eq_zero hχ hp q)
      have hd : (1 : ℝ) / 400 ≤ ‖1 - ρ‖ := by
        have h := Complex.re_le_norm (1 - ρ)
        simp only [sub_re, one_re] at h
        linarith only [h, hgap]
      have hd' : max 1 (m : ℝ) ≤ 400 * ‖1 - ρ‖ := by
        apply max_le
        · linarith only [hd]
        · linarith only [hmρ₁, norm_nonneg (1 - ρ)]
      have hlow := norm_cpow_increment_le hρ hz hh.le (by norm_num : 1 - (1 : ℝ) / 400 ≤ 1) hgap
      rw [show 1 - (1 : ℝ) / 400 - 1 = -1 / 400 by ring] at hlow
      calc _ ≤ ‖ρ‖ * E * h / (‖ρ‖ * ‖1 - ρ‖) / h :=
            div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hlow hprod.le) hh.le
        _ = E / ‖1 - ρ‖ := by field_simp [hρ, hρ₁, hh.ne']
        _ = (400 * E) / (400 * ‖1 - ρ‖) := by
              rw [mul_div_mul_left _ _ (by norm_num : (400 : ℝ) ≠ 0)]
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (zero_lt_one.trans_le (le_max_left _ _)) hd'
    · rw [if_neg hmT]
      have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hzterm {y : ℝ} (hy : 1 ≤ y) : ‖(y : ℂ) ^ ρ‖ ≤ y := by
        rw [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hy)]
        exact (Real.rpow_le_rpow_of_exponent_le hy hre.2.le).trans_eq (Real.rpow_one y)
      have hhigher := (norm_sub_le (((z + h : ℝ) : ℂ) ^ ρ) ((z : ℂ) ^ ρ)).trans
        (add_le_add (hzterm hz₁) (hzterm hz))
      have hhigher' : ‖((z + h : ℝ) : ℂ) ^ ρ - (z : ℂ) ^ ρ‖ ≤ 2 * z + h := by
        linarith only [hhigher]
      have hmprod : (m : ℝ) ^ 2 ≤ ‖ρ‖ * ‖1 - ρ‖ := by
        rw [sq]
        exact mul_le_mul hmρ hmρ₁ hm₀.le (norm_nonneg _)
      calc _ ≤ (2 * z + h) / ((m : ℝ) ^ 2) / h := by
            apply div_le_div_of_nonneg_right _ hh.le
            exact (div_le_div_of_nonneg_right hhigher' hprod.le).trans
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hmprod)
        _ = _ := by rw [Real.rpow_neg hm₀.le, Real.rpow_two]; dsimp [U]; ring
  have hs₁ := summable_cpow_div hχ hp hz₁
  have hs₂ := summable_cpow_div hχ hp hz
  have hs := (hs₁.sub hs₂).norm.div_const h
  have hfinite (F : Finset (LZero χ)) :
      ∑ q ∈ F, w q ≤
        4 * localCountConst N *
          (400 * E * Real.log (T + 3) * (2 + Real.log T) + 8 * U / Real.sqrt T) := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem fl hq)]
    let K (m : ℕ) := Real.log (m + 3) * bnd m
    have hK (m : ℕ) : 0 ≤ K m :=
      mul_nonneg (Real.log_nonneg (by positivity)) (hb₀ m)
    have hfiber (m : ℕ) : ∑ q ∈ F with fl q = m, w q ≤ 4 * localCountConst N * K m := by
      obtain ⟨hf, hc⟩ := ncard_zeros_floor_le hχ hp m
      have hcard : (((F.filter fun q => fl q = m).card : ℕ) : ℝ) ≤
          4 * localCountConst N * Real.log (m + 3) := by
        have hsub : (↑(F.filter fun q => fl q = m) : Set (LZero χ)) ⊆
            {q : LZero χ | ⌊|q.point.im|⌋₊ = m} :=
          fun q hq => (mem_filter.mp hq).2
        have h := Set.ncard_le_ncard hsub hf
        rw [Set.ncard_coe_finset] at h
        exact (Nat.cast_le.mpr h).trans hc
      calc _ ≤ ∑ _q ∈ F with fl q = m, bnd m := by
            exact sum_le_sum fun q hq => (hweight q).trans_eq
              (congrArg bnd (mem_filter.mp hq).2)
        _ ≤ _ := by
            rw [sum_const, nsmul_eq_mul]
            change _ ≤ 4 * localCountConst N * (Real.log (m + 3) * bnd m)
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hcard (hb₀ m)
    let M := (F.image fl).sup id
    have hsub : F.image fl ⊆ range (M + 1) := fun m hm => mem_range.mpr
      (Nat.lt_succ_iff.mpr (le_sup (f := id) hm))
    have hsmall : ∑ m ∈ range (T + 1), K m ≤
        400 * E * Real.log (T + 3) * (2 + Real.log T) := by
      have he : range (T + 1) = insert 0 (Icc 1 T) := by
        ext m
        simp only [mem_range, mem_insert, mem_Icc]
        omega
      have hharm : ∑ m ∈ Icc 1 T, (1 : ℝ) / m ≤ 1 + Real.log T := by
        rw [show Icc 1 T = insert 1 (Icc 2 T) by
          ext m; simp only [mem_Icc, mem_insert]; omega, sum_insert (by simp)]
        have h := RHTower.Sieve.sum_Icc_one_div_le_log_sub (m := 2) (n := T) le_rfl (by omega)
        norm_num at h ⊢
        linarith only [h]
      have hlog : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by positivity)
      calc ∑ m ∈ range (T + 1), K m
          ≤ ∑ m ∈ range (T + 1), (400 * E * Real.log (T + 3)) * (1 / max 1 (m : ℝ)) := by
            refine sum_le_sum fun m hm => ?_
            have hmT : m ≤ T := by simpa using (mem_range.mp hm)
            have hl := Real.log_le_log (by positivity : 0 < (m : ℝ) + 3)
              (add_le_add (Nat.cast_le.mpr hmT) le_rfl)
            dsimp [K, bnd]
            rw [if_pos hmT]
            calc _ ≤ Real.log (T + 3) * (400 * E / max 1 (m : ℝ)) :=
                  mul_le_mul_of_nonneg_right hl (by positivity)
              _ = _ := by ring
        _ = (400 * E * Real.log (T + 3)) * (1 + ∑ m ∈ Icc 1 T, (1 : ℝ) / m) := by
              rw [← mul_sum, he, sum_insert (by simp)]
              simp only [Nat.cast_zero, max_eq_left zero_le_one, div_one, one_div_one]
              congr 1
              refine congrArg (1 + ·) (sum_congr rfl fun m hm => ?_)
              rw [max_eq_right (by exact_mod_cast (mem_Icc.mp hm).1)]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hharm]) (by positivity)
    have hlarge : ∑ m ∈ Ioc T M, K m ≤ 8 * U / Real.sqrt T := by
      calc ∑ m ∈ Ioc T M, K m
          ≤ ∑ m ∈ Ioc T M, 4 * U * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
            refine sum_le_sum fun m hm => ?_
            have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast (hT.trans (mem_Ioc.mp hm).1.le)
            dsimp [K, bnd]
            rw [if_neg (not_le_of_gt (mem_Ioc.mp hm).1)]
            calc _ ≤ (4 * Real.sqrt m) * (U * (m : ℝ) ^ (-(2 : ℝ))) :=
                  mul_le_mul_of_nonneg_right (log_add_three_le_four_sqrt hm₁) (by positivity)
              _ = _ := by
                rw [Real.sqrt_eq_rpow, mul_mul_mul_comm, ← Real.rpow_add (zero_lt_one.trans_le hm₁)]
                norm_num
        _ = (4 * U) * ∑ m ∈ Ioc T M, (m : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [mul_sum]
        _ ≤ (4 * U) * (2 / Real.sqrt T) :=
            mul_le_mul_of_nonneg_left (sum_Ioc_rpow_neg_three_halves_le hT M) (by positivity)
        _ = _ := by ring
    have hcover : range (M + 1) ⊆ range (T + 1) ∪ Ioc T M := by
      intro m hm
      simp only [mem_range, mem_union, mem_Ioc] at hm ⊢
      omega
    calc _ ≤ ∑ m ∈ F.image fl, 4 * localCountConst N * K m := sum_le_sum fun m _ => hfiber m
      _ ≤ 4 * localCountConst N * ∑ m ∈ range (M + 1), K m := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hK m)) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (sum_le_sum_of_subset_of_nonneg hcover (fun m _ _ => hK m)).trans ?_
        rw [sum_union (disjoint_left.mpr (by
          intro m hm hm'
          exact (mem_Ioc.mp hm').1.not_ge (Nat.lt_succ_iff.mp (mem_range.mp hm))))]
        exact add_le_add hsmall hlarge
  have hb := hs.tsum_le_of_sum_le hfinite
  rw [← hs₁.tsum_sub hs₂]
  exact (div_le_div_of_nonneg_right (norm_tsum_le_tsum_norm (hs₁.sub hs₂).norm) hh.le).trans
    (by rw [← tsum_div_const]; exact hb)

end

end QH
