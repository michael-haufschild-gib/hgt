import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.NoExcRegion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedZeroSum
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedZeta

/-! A conductor-uniform bound for the centered primitive Cesàro sums. -/

open Complex Finset WindowedLandauTheory.HC
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

namespace QH

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private theorem norm_zero_sum_eq (y : ℝ) (hy : 0 < y) :
    ‖∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))‖ =
      ‖∑' q : LZero χ, zeroKernel y q.point‖ * y := by
  rw [zeroKernel_sum_eq_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hy.le, div_mul_cancel₀ _ hy.ne']

private theorem beta_le (hχ : χ ≠ 1) {B : ℝ} (hB : 0 ≤ B) {β : ℂ}
    (hzero : ∀ y : ℝ, 1 ≤ y → ‖∑' q : LZero χ, zeroKernel y q.point‖ ≤ B)
    (hβ : ∀ y : ℝ, 1 < y →
      ‖An.gChi χ y + ∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1)) -
          (β + efGamma χ * Complex.log y)‖ ≤ efD / y) :
    ‖β‖ ≤ 13 * (2 * B + 3) := by
  have hval (y : ℝ) (hy : 1 < y) (hy' : y < 2) :
      ‖(y : ℂ) * An.logDerivativeAtOne χ - β‖ ≤ 2 * B + 3 := by
    have hy₀ : 0 < y := zero_lt_one.trans hy
    have hfl : ⌊y⌋₊ = 1 := (Nat.floor_eq_iff hy₀.le).mpr (by push_cast; exact ⟨hy.le, hy'⟩)
    have hsum : An.sumLamChi χ y = 0 := by
      simp [An.sumLamChi, hfl, An.abelian₂]
    have he := hβ y hy
    rw [An.gChi, if_neg hχ, hsum, zero_add] at he
    let Z : ℂ := ∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))
    let C := efGamma χ * Complex.log y
    have he' : ‖(y : ℂ) * An.logDerivativeAtOne χ + Z - (β + C)‖ ≤ 2 :=
      he.trans ((div_le_self efD_nonneg hy.le).trans efD_le_two)
    have hZ : ‖Z‖ ≤ 2 * B := by
      rw [show ‖Z‖ = ‖∑' q : LZero χ, zeroKernel y q.point‖ * y from norm_zero_sum_eq y hy₀]
      calc ‖∑' q : LZero χ, zeroKernel y q.point‖ * y ≤ B * y :=
            mul_le_mul_of_nonneg_right (hzero y hy.le) hy₀.le
        _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hy'.le hB]
    have hC : ‖C‖ ≤ 1 := by
      have hlog : Real.log y ≤ 1 := (Real.log_le_log hy₀ hy'.le).trans (by linarith only [Real.log_two_lt_d9])
      dsimp [C]
      rw [norm_mul, ← Complex.ofReal_log hy₀.le, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy.le)]
      exact mul_le_one₀ (norm_efGamma_le χ) (Real.log_nonneg hy.le) hlog
    have heq : (y : ℂ) * An.logDerivativeAtOne χ - β =
        ((y : ℂ) * An.logDerivativeAtOne χ + Z - (β + C)) - Z + C := by ring
    rw [heq]
    exact ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans (by linarith only [he', hZ, hC])
  have h₁ := hval (3 / 2) (by norm_num) (by norm_num)
  have h₂ := hval (7 / 4) (by norm_num) (by norm_num)
  have heq : β = 6 * (((7 / 4 : ℝ) : ℂ) * An.logDerivativeAtOne χ - β) -
      7 * (((3 / 2 : ℝ) : ℂ) * An.logDerivativeAtOne χ - β) := by push_cast; ring
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_ofNat]
  linarith only [h₁, h₂]

theorem smoothed_primitive_bound (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (lam : ℝ),
      χ.IsPrimitive → 1 ≤ lam → Real.log N ≤ lam → (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) →
      ∀ y : ℝ, Real.exp 1 ≤ y →
        ‖An.gChi χ y‖ ≤ C * y * (Real.log y + lam) ^ 4 *
          Real.exp (-k * Real.log y / (lam + Real.sqrt (Real.log y))) := by
  obtain ⟨c, hc, hzf⟩ := zero_free_of_noExc c₀ hc₀
  obtain ⟨Kζ, kζ, hKζ, hkζ, hζ⟩ := smoothed_zeta_bound
  let a := min 1 (c / 8) / 2
  let d := min (c / 3) 1
  have hd : 0 < d := lt_min (by positivity) one_pos
  let B := 640 * (2 * Real.log 4 + 8) / d ^ 2
  let C := 10880 / d ^ 2 + 13 * (2 * B + 3) + 3
  have hB : 0 < B := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [B]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have ha : 0 < a := div_pos (lt_min one_pos (by positivity)) (by norm_num)
  refine ⟨max Kζ C, min kζ a, lt_of_lt_of_le hKζ (le_max_left _ _), lt_min hkζ ha,
    fun N _ χ lam hp hlam hN hex y hy => ?_⟩
  have hy₀ : 0 < y := (Real.exp_pos _).trans_le hy
  have hy₁ : 1 < y := (Real.one_lt_exp_iff.mpr one_pos).trans_le hy
  let v := Real.log y
  have hv₁ : 1 ≤ v := (Real.le_log_iff_exp_le hy₀).mpr hy
  let W := v + lam
  have hW : 1 ≤ W := by dsimp [W]; linarith only [hv₁, hlam]
  have hlamW : lam ≤ W := le_add_of_nonneg_left (zero_le_one.trans hv₁)
  have hlam₀ : 0 < lam := zero_lt_one.trans_le hlam
  have hD : 0 < lam + Real.sqrt v := by positivity
  have hvD : v / (lam + Real.sqrt v) ≤ Real.sqrt v := by
    rw [div_le_iff₀ hD, mul_add, Real.mul_self_sqrt (zero_le_one.trans hv₁)]
    exact le_add_of_nonneg_left (by positivity)
  by_cases hχ : χ = 1
  · rw [An.gChi, if_pos hχ]
    have hmono : Real.exp (-kζ * Real.sqrt v) ≤ Real.exp (-(min kζ a) * v / (lam + Real.sqrt v)) := by
      have h := mul_le_mul (min_le_left kζ a) hvD (by positivity) hkζ.le
      rw [mul_div_assoc]
      exact Real.exp_le_exp.mpr (by linarith only [h])
    calc ‖(An.G y : ℂ)‖ ≤ Kζ * y * Real.exp (-kζ * Real.sqrt v) := hζ y hy
      _ ≤ Kζ * y * (W ^ 4 * Real.exp (-(min kζ a) * v / (lam + Real.sqrt v))) := by
        apply mul_le_mul_of_nonneg_left (hmono.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hW))) (by positivity)
      _ ≤ _ := by rw [← mul_assoc]; gcongr <;> exact le_max_left _ _
  have hgap (q : LZero χ) : q.point.re ≤ 1 - c / (lam + Real.log (|q.point.im| + 3)) :=
    hzf N χ lam hlam hN hex q.point (zero_re_mem hχ hp q).2 (LFunction_point_eq_zero hχ hp q)
  have hinv : χ⁻¹.IsPrimitive := by rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  have hex' : χ⁻¹ ^ 2 = 1 → χ⁻¹ ≠ 1 → NoExc c₀ χ⁻¹ := by
    intro h₂ _
    have h₂' : χ ^ 2 = 1 := by rwa [inv_pow, inv_eq_one] at h₂
    have hχ' : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    rw [hχ']
    exact hex h₂' hχ
  let A := (lam / d) ^ 2
  have hdlam : d ≤ lam := (min_le_right _ _).trans hlam
  have hA : 1 ≤ A := one_le_pow₀ ((le_div_iff₀ hd).2 (by simpa using hdlam))
  have hweight (q : LZero χ) : 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ A := by
    have hr := zero_distance_of_gap hc hlam (hgap q)
    let q' := reflectZero hχ hp q
    have hq' := hzf N χ⁻¹ lam hlam hN hex' q'.point (zero_re_mem (inv_ne_one hχ) hinv q').2
      (LFunction_point_eq_zero (inv_ne_one hχ) hinv q')
    have hl := zero_distance_of_gap hc hlam hq'
    rw [show q'.point = 1 - q.point from reflectZero_point hχ hp q, sub_sub_cancel] at hl
    have hprod : (d / lam) ^ 2 ≤ ‖q.point‖ * ‖1 - q.point‖ := by
      rw [sq]
      exact mul_le_mul hl hr (by positivity) (norm_nonneg _)
    calc 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ 1 / (d / lam) ^ 2 :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) hprod
      _ = A := by dsimp [A]; field_simp [hd.ne', hlam₀.ne']
  have hCount : localCountConst N ≤ 160 * lam := (localCountConst_le (NeZero.pos N)).trans
    (by linarith only [hN, hlam])
  have hCountW : localCountConst N ≤ 160 * W :=
    hCount.trans (mul_le_mul_of_nonneg_left hlamW (by norm_num))
  have hCount₀ : 0 ≤ localCountConst N := localCountConst_nonneg (NeZero.pos N)
  have hcoarse (z : ℝ) (hz : 1 ≤ z) : ‖∑' q : LZero χ, zeroKernel z q.point‖ ≤ B * lam ^ 3 := by
    have hh := zeroKernel_sum_le hχ hp hz hA (E := 1) zero_le_one (T := 1) le_rfl hweight
      (fun q _ => Real.rpow_le_one_of_one_le_of_nonpos hz (sub_nonpos.mpr (zero_re_mem hχ hp q).2.le))
    norm_num at hh
    refine hh.trans ?_
    have hpos : 0 ≤ 2 * Real.log 4 + 8 := by
      have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      linarith only [h]
    calc A * (4 * localCountConst N * (2 * Real.log 4 + 8))
        ≤ A * (4 * (160 * lam) * (2 * Real.log 4 + 8)) := by gcongr
      _ = B * lam ^ 3 := by dsimp [A, B]; ring
  obtain ⟨β, hβ⟩ := smoothed_identity hχ hp
  have hb := beta_le hχ (mul_nonneg hB.le (by positivity)) hcoarse hβ
  set E := Real.exp (-a * v / (lam + Real.sqrt v)) with hE
  have hE₁ : 1 ≤ y * E := by
    have hys : y = Real.exp v := (Real.exp_log hy₀).symm
    have ha₁ : a ≤ 1 := by dsimp [a]; linarith only [min_le_left (1 : ℝ) (c / 8)]
    have hv' : a * v / (lam + Real.sqrt v) ≤ v := by
      rw [div_le_iff₀ hD]
      have hD₁ : 1 ≤ lam + Real.sqrt v := hlam.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      exact (mul_le_of_le_one_left (zero_le_one.trans hv₁) ha₁).trans
        (le_mul_of_one_le_right (zero_le_one.trans hv₁) hD₁)
    rw [hys, hE, ← Real.exp_add, neg_mul, neg_div]
    exact Real.one_le_exp (by linarith only [hv'])
  have hz := exp_zeroKernel_sum_le hχ hp hy hc hlam hA hweight hgap
  have hz' : ‖∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))‖ ≤
      (10880 / d ^ 2) * W ^ 4 * (y * E) := by
    rw [norm_zero_sum_eq y hy₀]
    have h1 : 14 + 3 * v ≤ 17 * W := by dsimp [W]; linarith only [hv₁, hlam]
    have h2 : A ≤ (W / d) ^ 2 := pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hlamW hd.le) 2
    calc ‖∑' q : LZero χ, zeroKernel y q.point‖ * y
        ≤ 4 * A * localCountConst N * (14 + 3 * v) * E * y := mul_le_mul_of_nonneg_right hz hy₀.le
      _ ≤ 4 * (W / d) ^ 2 * (160 * W) * (17 * W) * E * y := by gcongr
      _ = _ := by ring
  have hlog : ‖efGamma χ * Complex.log y‖ ≤ v := by
    rw [norm_mul, ← Complex.ofReal_log hy₀.le, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy₁.le)]
    exact mul_le_of_le_one_left (Real.log_nonneg hy₁.le) (norm_efGamma_le χ)
  have hW₄ : 1 ≤ W ^ 4 := one_le_pow₀ hW
  have hb' : ‖β‖ ≤ 13 * (2 * B + 3) * W ^ 4 := by
    have hp₃ := pow_le_pow_left₀ hlam₀.le hlamW 3
    have hp₄ : W ^ 3 ≤ W ^ 4 := pow_le_pow_right₀ hW (by norm_num)
    have h := mul_le_mul_of_nonneg_left (hp₃.trans hp₄) (show 0 ≤ 2 * B by positivity)
    linarith only [hb, h, hW₄]
  have hrem : ‖An.gChi χ y‖ ≤
      ‖∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))‖ + ‖β‖ + v + 2 := by
    let Z : ℂ := ∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))
    let t := efGamma χ * Complex.log y
    have hh := hβ y hy₁
    have hE' : ‖An.gChi χ y + Z - (β + t)‖ ≤ 2 := hh.trans ((div_le_self efD_nonneg hy₁.le).trans efD_le_two)
    have he : An.gChi χ y = (An.gChi χ y + Z - (β + t)) - Z + β + t := by ring
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)).trans
      (by linarith only [hE', hlog])
  have hvW : v ≤ W ^ 4 := (le_add_of_nonneg_right hlam₀.le : v ≤ W).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hW (by norm_num : (1 : ℕ) ≤ 4))
  calc ‖An.gChi χ y‖ ≤ (10880 / d ^ 2) * W ^ 4 * (y * E) + (13 * (2 * B + 3) + 3) * W ^ 4 := by
        linarith only [hrem, hz', hb', hvW, hW₄]
    _ ≤ C * y * W ^ 4 * E := by
      have hnn : 0 ≤ (13 * (2 * B + 3) + 3) * W ^ 4 := by positivity
      have hm := le_mul_of_one_le_right hnn hE₁
      dsimp [C]
      linarith only [hm]
    _ ≤ _ := by
      apply mul_le_mul (by gcongr <;> exact le_max_right _ _) _ (by positivity) (by positivity)
      rw [hE]
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_right
        (min_le_right kζ a) (zero_le_one.trans hv₁)]) hD.le

end

end QH
