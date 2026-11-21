import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedPrimitive

/-! The smoothed cancellation estimate at the thin scales of a host. -/

open Filter WindowedLandauTheory.HC

namespace QH

private theorem thin_decay {C k : ℝ} (hC : 0 < C) (hk : 0 < k) :
    ∀ᶠ v : ℝ in atTop, 1 ≤ v ∧ ∀ lam : ℝ, 1 ≤ lam → lam ≤ v ^ (61 / 100 : ℝ) →
      C * (v + lam) ^ 4 * Real.exp (-k * v / (lam + Real.sqrt v)) ≤
        Real.exp (-(k / 4) * v ^ (39 / 100 : ℝ)) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 100)).bound
    (c := k / 32) (by positivity)
  have hscale := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 100)).eventually_ge_atTop
    (8 * Real.log (16 * C) / k)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog, hscale] with v hv hvlog hvs
  refine ⟨hv, fun lam hlam hl => ?_⟩
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hlamv : lam ≤ v := hl.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hv (show (61 / 100 : ℝ) ≤ 1 by norm_num))
  have hs : Real.sqrt v ≤ v ^ (61 / 100 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
  have hPow : v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ) = v := by
    rw [← Real.rpow_add hv₀]; norm_num
  have hden : 0 < lam + Real.sqrt v := by positivity
  have hrate : k / 2 * v ^ (39 / 100 : ℝ) ≤ k * v / (lam + Real.sqrt v) := by
    rw [le_div_iff₀ hden]
    have hlams : lam + Real.sqrt v ≤ 2 * v ^ (61 / 100 : ℝ) := by linarith only [hl, hs]
    calc k / 2 * v ^ (39 / 100 : ℝ) * (lam + Real.sqrt v)
        ≤ k / 2 * v ^ (39 / 100 : ℝ) * (2 * v ^ (61 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlams (by positivity)
      _ = k * (v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ)) := by ring
      _ = k * v := by rw [hPow]
  have hpoly : C * (v + lam) ^ 4 ≤ Real.exp (k / 4 * v ^ (39 / 100 : ℝ)) := by
    have h₁ : C * (v + lam) ^ 4 ≤ (16 * C) * v ^ 4 := by
      calc C * (v + lam) ^ 4 ≤ C * (2 * v) ^ 4 := by gcongr; linarith only [hlamv]
        _ = _ := by ring
    refine h₁.trans ?_
    rw [← Real.log_le_log_iff (by positivity) (Real.exp_pos _), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_exp]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hv),
      abs_of_nonneg (Real.rpow_nonneg hv₀.le _)] at hvlog
    have h₂ := (div_le_iff₀ hk).mp hvs
    linarith only [h₂, hvlog]
  have he : Real.exp (-k * v / (lam + Real.sqrt v)) ≤ Real.exp (-(k / 2) * v ^ (39 / 100 : ℝ)) := by
    rw [neg_mul, neg_div]
    exact Real.exp_le_exp.mpr (by linarith only [hrate])
  calc C * (v + lam) ^ 4 * Real.exp (-k * v / (lam + Real.sqrt v))
      ≤ Real.exp (k / 4 * v ^ (39 / 100 : ℝ)) * Real.exp (-(k / 2) * v ^ (39 / 100 : ℝ)) :=
        mul_le_mul hpoly he (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem thin :
    ∀ ε A c c₀ : ℝ, 0 < ε → 0 < A → 0 < c → 0 < c₀ → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      Real.log N ≤ A * x ^ (ε / 5) * Real.log x ^ 2 → (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) →
      ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → ‖An.gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (ε / 8))) := by
  intro ε A c c₀ hε hA hc hc₀
  obtain ⟨C, k, hC, hk, hprim⟩ := smoothed_primitive_bound c₀ hc₀
  obtain ⟨V, hV⟩ := eventually_atTop.mp (thin_decay hC hk)
  let B := A + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop 2 (by positivity : 0 < ε / 300)).bound
    (c := 1 / (2 * B)) (by positivity)
  have hv := (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop (max 4 (2 * V))
  have hrate := (tendsto_rpow_atTop (by positivity : 0 < ε / 200)).eventually_ge_atTop (8 * c / k)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (Real.exp 1)).and (hlog.and (hv.and hrate)))
  refine ⟨x₀, fun x hx N _ χ hp hN hex y hy => ?_⟩
  obtain ⟨hxe, hxlog, hxv, hxrate⟩ := hx₀ x hx
  have hx₀' : 0 < x := (Real.exp_pos _).trans_le hxe
  have hx₁ : 1 ≤ x := (Real.one_le_exp one_pos.le).trans hxe
  have hL : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx₀').mpr hxe
  let X := x ^ (ε / 3)
  have hX₄ : 4 ≤ X := (le_max_left _ _).trans hxv
  have hXV : 2 * V ≤ X := (le_max_right _ _).trans hxv
  have hy₀ : 0 < y := (div_pos (Real.exp_pos _) (by norm_num)).trans_le hy
  let v := Real.log y
  have hXv : X / 2 ≤ v := by
    have h₃ : Real.log (3 : ℝ) ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      linarith only [Real.add_one_le_exp (2 : ℝ)]
    have h := Real.log_le_log (show 0 < Real.exp X / 3 by positivity) hy
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h
    linarith only [h, h₃, hX₄]
  have hv₁ : 1 ≤ v := by linarith only [hX₄, hXv]
  have hvV : V ≤ v := by linarith only [hXV, hXv]
  have hye : Real.exp 1 ≤ y := (Real.le_log_iff_exp_le hy₀).mp hv₁
  let lam := max 1 (Real.log N)
  have hlam : 1 ≤ lam := le_max_left _ _
  have hP : 1 ≤ x ^ (ε / 5) * Real.log x ^ 2 :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hx₁ (by positivity)) (one_le_pow₀ hL)
  have hlamB : lam ≤ B * x ^ (ε / 5) * Real.log x ^ 2 := by
    rw [mul_assoc]
    apply max_le
    · exact hP.trans (le_mul_of_one_le_left (by positivity) (by dsimp [B]; linarith only [hA]))
    · rw [mul_assoc] at hN
      exact hN.trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (by positivity))
  have hl : lam ≤ v ^ (61 / 100 : ℝ) := by
    rw [Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg hx₀'.le _)] at hxlog
    have hlog' : 2 * B * Real.log x ^ 2 ≤ x ^ (ε / 300) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)] at hxlog
      linarith only [hxlog]
    have htwo : (2 : ℝ) ^ (61 / 100 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (61 / 100 : ℝ) ≤ 1 by norm_num)
    have hXpow : X ^ (61 / 100 : ℝ) = x ^ (ε / 5) * x ^ (ε / 300) := by
      dsimp [X]
      rw [← Real.rpow_mul hx₀'.le, ← Real.rpow_add hx₀']
      congr 1
      ring
    calc lam ≤ B * x ^ (ε / 5) * Real.log x ^ 2 := hlamB
      _ = x ^ (ε / 5) * (2 * B * Real.log x ^ 2) / 2 := by ring
      _ ≤ x ^ (ε / 5) * x ^ (ε / 300) / 2 := by gcongr
      _ = X ^ (61 / 100 : ℝ) / 2 := by rw [hXpow]
      _ ≤ (X / 2) ^ (61 / 100 : ℝ) := by
        rw [Real.div_rpow (by positivity) (by norm_num)]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) htwo
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hXv (by norm_num)
  have hc' : c * x ^ (ε / 8) ≤ k / 4 * v ^ (39 / 100 : ℝ) := by
    have htwo : (2 : ℝ) ^ (39 / 100 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (39 / 100 : ℝ) ≤ 1 by norm_num)
    have hXpow : X ^ (39 / 100 : ℝ) = x ^ (ε / 8) * x ^ (ε / 200) := by
      dsimp [X]
      rw [← Real.rpow_mul hx₀'.le, ← Real.rpow_add hx₀']
      congr 1
      ring
    have hprod : X ^ (39 / 100 : ℝ) / 2 ≤ v ^ (39 / 100 : ℝ) := by
      calc X ^ (39 / 100 : ℝ) / 2 ≤ (X / 2) ^ (39 / 100 : ℝ) := by
            rw [Real.div_rpow (by positivity) (by norm_num)]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) htwo
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hXv (by norm_num)
    calc c * x ^ (ε / 8) = k / 4 * (x ^ (ε / 8) * (8 * c / k) / 2) := by field_simp [hk.ne']; ring
      _ ≤ k / 4 * (x ^ (ε / 8) * x ^ (ε / 200) / 2) := by gcongr
      _ ≤ _ := by rw [← hXpow]; exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have hh := hprim N χ lam hp hlam (le_max_right _ _) hex y hye
  calc ‖An.gChi χ y‖ ≤ C * y * (v + lam) ^ 4 * Real.exp (-k * v / (lam + Real.sqrt v)) := hh
    _ = y * (C * (v + lam) ^ 4 * Real.exp (-k * v / (lam + Real.sqrt v))) := by ring
    _ ≤ y * Real.exp (-(k / 4) * v ^ (39 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_left ((hV v hvV).2 lam hlam hl) hy₀.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hc'])) hy₀.le

end QH
