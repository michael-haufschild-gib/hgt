import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SubWeylCollisionFreeHorizon
import GaloisForLFunctions.RHTower.Heat.TheLocalDeBruijnNewmanConstant
import GaloisForLFunctions.RHTower.XiSliceTypicalOrderPowerSaving

/-!
# The heat horizon reaches the saddle on almost all heights

The Euler-anchored half-Gauss comparison needs only the size of `ζ` at the height of the zero. The
heights near which `|ζ| > T^e` on `½ ≤ Re s ≤ 2` have measure `O(T^{1−e})`, and on the remaining
heights the strip profile is the constant `e`. So every obstruction above the saddle vanishes:

* `norm_xiLine_le_of_norm_zeta_le`: a bound for `ζ` at one height gives the strip comparison at that
  height;
* `riemannHeat_ne_zero_of_typical`: at a height where `|ζ| ≤ 2 X^e` on the strip and
  `X ≥ 2π e^{(½+ε)/t}`, the flow `H_t` has no non-real zero above `X`;
* `localNewmanConstant_le_of_typical`: `Λ_X ≤ (½+ε)/log((X−1)/2π)` when this holds on the whole unit
  window about `X`;
* `exists_volume_localNewmanConstant_gt_le`: for every `ε > 0` the heights in `[T, 2T]` with
  `Λ_X > (½+ε)/log((X−1)/2π)` have measure `O(T^{1−ε²/32})`.

For `t = (½+ε)/log X` the saddle lies at `Re s = 1 + ε`, right of the Euler boundary, so the exponent
`½` is the limit of this anchor; `log X · Λ_X → 0` on typical heights needs a different source.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The constant of the comparison between a line near `½` and an Euler anchor. -/
def typicalAnchorConstant (η C : ℝ) : ℝ :=
  2 * Real.exp 6 * C / (1 / (1 + 1 / (2 * η)))

/-- **Strip comparison at one height.** A bound for `ζ` at the height `X` on the line `½ + w` gives
`‖ξ(½ + w + iX)‖ ≤ K X^E (X/2π)^{(w−u)/2} ‖ξ(½ + u + iX)‖` for every Euler anchor `u ≥ ½ + 2η`. -/
theorem norm_xiLine_le_of_norm_zeta_le {η C E X w u : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hC : 0 ≤ C) (hX : 16 ≤ X) (hw0 : 0 ≤ w) (hwη : w ≤ 1 / 2 + 2 * η) (hu1 : 1 / 2 + 2 * η ≤ u)
    (huX : u ≤ X) (hZ : ‖riemannZeta (((w + 1 / 2 : ℝ) : ℂ) + X * I)‖ ≤ C * X ^ E) :
    ‖xiLine X w‖ ≤ typicalAnchorConstant η C * X ^ E * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
      ‖xiLine X u‖ := by
  set c := 1 / (1 + 1 / (2 * η)) with hcdef
  have hc : 0 < c := by positivity
  have hX0 : 0 < X := by linarith
  have hu0 : 0 ≤ u := by linarith
  rw [norm_xiLine_eq_factors hX0 hw0, norm_xiLine_eq_factors hX0 hu0]
  set sw : ℂ := ((w + 1 / 2 : ℝ) : ℂ) + X * I with hsw
  set su : ℂ := ((u + 1 / 2 : ℝ) : ℂ) + X * I with hsu
  set Pw := ‖sw * (sw - 1) / 2‖ with hPw
  set Pu := ‖su * (su - 1) / 2‖ with hPu
  set Gw := ‖Complex.Gamma ((((w + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGw
  set Gu := ‖Complex.Gamma ((((u + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGu
  set Zw := ‖riemannZeta sw‖ with hZw
  set Zu := ‖riemannZeta su‖ with hZu
  have hsuim : X ≤ ‖su‖ := by
    have := Complex.abs_im_le_norm su; simpa [hsu, abs_of_pos hX0] using this
  have hsu1im : X ≤ ‖su - 1‖ := by
    have := Complex.abs_im_le_norm (su - 1); simpa [hsu, abs_of_pos hX0] using this
  have hsw_le : ‖sw‖ ≤ X + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0, Complex.norm_I, mul_one]
    linarith
  have hsw1_le : ‖sw - 1‖ ≤ X + 1 := by
    have e : sw - 1 = (((w - 1 / 2 : ℝ)) : ℂ) + X * I := by rw [hsw]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hX0, Complex.norm_I, mul_one]
    have : |w - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hPwu : Pw ≤ 2 * Pu := by
    rw [hPw, hPu, norm_div, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    have h1 : ‖sw‖ * ‖sw - 1‖ ≤ (X + 2) * (X + 1) :=
      mul_le_mul hsw_le hsw1_le (norm_nonneg _) (by linarith)
    have h2 : X * X ≤ ‖su‖ * ‖su - 1‖ := mul_le_mul hsuim hsu1im hX0.le (norm_nonneg _)
    have h3 : (X + 2) * (X + 1) ≤ 2 * (X * X) := by nlinarith
    linarith
  have hGamma : Gw ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by
    have h := norm_Gamma_vertical_le_rpow_mul (a := (w + 1 / 2) / 2) (b := (u + 1 / 2) / 2)
      (y := X / 2) (by linarith) (by linarith) (by linarith)
    have hab : (w + 1 / 2) / 2 - (u + 1 / 2) / 2 = (w - u) / 2 := by ring
    rw [hab] at h
    have hexp : Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) ≤ Real.exp 6 := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc Gw ≤ (X / 2) ^ ((w - u) / 2) *
          Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) * Gu := h
      _ ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by gcongr
  have hZu_ge : c ≤ Zu := by
    have hsad := inv_le_norm_riemannZeta_saddle X hη hu1
    have hsu_eq : (((1 / 2 + u : ℝ) : ℂ) + (X : ℂ) * I) = su := by rw [hsu]; push_cast; ring
    rw [hsu_eq] at hsad
    exact hsad
  have hpi : Real.pi ^ (-((w + 1 / 2) / 2)) =
      Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  have hpow : (X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2) =
      (X / (2 * Real.pi)) ^ ((w - u) / 2) := by
    have e : (u - w) / 2 = -((w - u) / 2) := by ring
    rw [e, Real.rpow_neg Real.pi_pos.le, ← Real.inv_rpow Real.pi_pos.le,
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hPu0 : 0 ≤ Pu := norm_nonneg _
  have hGu0 : 0 ≤ Gu := norm_nonneg _
  have hZw0 : 0 ≤ Zw := norm_nonneg _
  rw [hpi]
  unfold typicalAnchorConstant
  rw [← hcdef]
  calc Pw * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) * Gw * Zw
      ≤ (2 * Pu) * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) *
          ((X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu) * (C * X ^ E) := by
        gcongr
    _ = 2 * Real.exp 6 * C * X ^ E *
          ((X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2)) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by ring
    _ = 2 * Real.exp 6 * C * X ^ E * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by rw [hpow]
    _ ≤ 2 * Real.exp 6 * C * X ^ E * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * (Zu / c)) := by
        have h1 : 1 ≤ Zu / c := by rw [le_div_iff₀ hc]; linarith
        have h0 : 0 ≤ Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu := by positivity
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h0 h1) (by positivity)
    _ = 2 * Real.exp 6 * C / c * X ^ E *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * Zu) := by
        field_simp

/-- The quadratic margin of the constant profile `ε²/32` above the threshold `½ + ε`. -/
theorem typical_margin {ε c w : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hc : 1 / 2 + ε ≤ c)
    (hw : w ≤ 1 / 2 + 2 * (ε / 8)) :
    3 * ε ^ 2 / 8 ≤ (c - w) ^ 2 - 4 * c * (ε ^ 2 / 32) - 2 * (ε ^ 2 / 16) * c := by
  obtain ⟨d, hd⟩ : ∃ d, d = c - w - 3 * ε / 4 := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; linarith only [hc, hw]
  have hcle : c ≤ d + 3 * ε / 4 + (1 / 2 + ε / 4) := by rw [hd]; linarith only [hw]
  have hcw : c - w = d + 3 * ε / 4 := by rw [hd]; ring
  have hmul := mul_le_mul_of_nonneg_left hcle (show 0 ≤ ε ^ 2 / 4 by positivity)
  have h2 : 0 ≤ d * (3 * ε / 2 - ε ^ 2 / 4) := mul_nonneg hd0 (by nlinarith only [hε, hε4])
  have h3 : ε ^ 2 / 4 * (1 / 2 + ε) ≤ ε ^ 2 / 4 * (3 / 4) :=
    mul_le_mul_of_nonneg_left (by linarith only [hε4]) (by positivity)
  rw [hcw]
  nlinarith only [hmul, h2, h3, sq_nonneg d]

/-- **Non-real zeros are absent at a typical height.** Above a uniform `X₀`, at a height `X` with
`X ≥ 2π e^{(½+ε)/t}` where `|ζ| ≤ 2 X^{ε²/32}` on `½ ≤ Re s ≤ 1 + ε/4`, `H_t(X + iy) ≠ 0` for
`0 < |y| ≤ ½`. -/
theorem exists_riemannHeat_ne_zero_of_typical {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ X₀ : ℝ, 16 ≤ X₀ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ X : ℝ, X₀ ≤ X →
      2 * Real.pi * Real.exp ((1 / 2 + ε) / t) ≤ X →
      (∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 + 2 * (ε / 8) →
        ‖riemannZeta (((w + 1 / 2 : ℝ) : ℂ) + X * I)‖ ≤ 2 * X ^ (ε ^ 2 / 32)) →
      ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 → riemannHeat t ((X : ℂ) + I * y) ≠ 0 := by
  set η := ε / 8 with hηdef
  have hη : 0 < η := by positivity
  have hη8 : η ≤ 1 / 8 := by rw [hηdef]; linarith only [hε4]
  set K := typicalAnchorConstant η 2 with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    unfold typicalAnchorConstant
    positivity
  set δ₀ := ε ^ 2 / 16 with hδ₀def
  set γ := ε / 2 with hγdef
  set m := 3 * ε ^ 2 / 8 with hmdef
  have hδ₀ : 0 < δ₀ := by positivity
  have hγ : 0 < γ := by positivity
  have hm : 0 < m := by positivity
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    (eventually_interior_errors_small (η' := 2 * η) (δ₀ := δ₀) (γ := γ) (m := m) (K := K)
      (b := 9 / 2 * (1 / (2 * η) + 3)) (by positivity) hδ₀ hγ hm)
  have h2π : (6 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hexp : (321 : ℝ) ≤ Real.exp (2 * max α₀ 160) := by
    have h1 := Real.add_one_le_exp (2 * max α₀ 160)
    linarith only [h1, le_max_right α₀ 160]
  refine ⟨2 * Real.pi * Real.exp (2 * max α₀ 160), by nlinarith only [h2π, hexp],
    fun t ht ht8 X hX hXc hZ y hy0 hy => ?_⟩
  have hX16 : (16 : ℝ) ≤ X := by nlinarith only [hX, h2π, hexp]
  refine (re_slope_zero_and_ne_zero_of_profile (E := fun _ => ε ^ 2 / 32) (c₀ := 1 / 2 + ε)
    (η := η) (δ₀ := δ₀) (γ := γ) (m := m) (K := K) (α₀ := α₀) hη hη8 hδ₀
    (by rw [hδ₀def]; nlinarith only [hε, hε4]) hγ
    (by rw [hδ₀def, hγdef]; nlinarith only [hε, hε4]) hm (by linarith only [hε])
    (by rw [hδ₀def, hγdef, hηdef]; nlinarith only [hε, hε4])
    (fun _ _ => by positivity)
    (fun w _ => by
      have h1 : ε ^ 2 / 32 ≤ 1 / 4 := by nlinarith only [hε, hε4]
      rw [hηdef]
      linarith only [h1, hε])
    (fun c hc w hw => by
      rw [hδ₀def, hmdef]
      exact typical_margin hε hε4 hc hw.2)
    (fun w u hw0 hwη hu1 huX =>
      norm_xiLine_le_of_norm_zeta_le hη (by linarith only [hη8]) (by norm_num) hX16 hw0 hwη hu1 huX
        (hZ w hw0 hwη))
    hK0 hα₀ ht ht8 hX hXc).2 y hy0 hy

/-- **The local constant at a typical window.** If `|ζ| ≤ 2 x^{ε²/32}` on `½ ≤ Re s ≤ 1 + ε/4` at every
height `x` of the unit window about `X`, then `Λ_X ≤ (½+ε)/log((X−1)/2π)`. -/
theorem exists_localNewmanConstant_le_of_typical {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ X₁ : ℝ, 3 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X →
      (∀ x : ℝ, |x - X| ≤ 1 → ∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 + 2 * (ε / 8) →
        ‖riemannZeta (((w + 1 / 2 : ℝ) : ℂ) + x * I)‖ ≤ 2 * x ^ (ε ^ 2 / 32)) →
      localNewmanConstant X ≤ (1 / 2 + ε) / Real.log ((X - 1) / (2 * Real.pi)) := by
  obtain ⟨X₀, hX₀16, h⟩ := exists_riemannHeat_ne_zero_of_typical hε hε4
  have h2π : 0 < 2 * Real.pi := by positivity
  refine ⟨max (X₀ + 1) (2 * Real.pi * Real.exp 1 + 1 + 1), le_trans (by linarith only [hX₀16])
    (le_max_left _ _), fun X hX hZ => ?_⟩
  have hX1 : X₀ + 1 ≤ X := (le_max_left _ _).trans hX
  have hX2 : 2 * Real.pi * Real.exp 1 + 1 + 1 ≤ X := (le_max_right _ _).trans hX
  have hdiv : Real.exp 1 < (X - 1) / (2 * Real.pi) := by
    rw [lt_div_iff₀ h2π]
    linarith only [hX2]
  set L := Real.log ((X - 1) / (2 * Real.pi)) with hLdef
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos 1) hdiv)]
    exact hdiv
  have hL0 : 0 < L := by linarith only [hL1]
  have hc : (0 : ℝ) < 1 / 2 + ε := by linarith only [hε]
  set s := (1 / 2 + ε) / L with hs
  have hs0 : 0 < s := by positivity
  refine localNewmanConstant_le ⟨hs0.le, fun s' hss' z hz hre => ?_⟩
  rcases le_or_gt (1 / 8) s' with h8 | h8
  · exact ((mem_realRootedTimes_iff (by linarith only [h8])).mpr
      ((newmanConstant_lt_eighth.le).trans h8)).2 z hz
  by_contra him
  have ht : 0 < s' := hs0.trans_le hss'
  have hx := abs_le.mp hre
  have him2 : z.im ^ 2 ≤ 1 / 4 :=
    (riemannHeat_zeros_im_sq_le ht hz).trans (max_le (by linarith only [ht]) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
    linarith only [him2]
  have hxc : 2 * Real.pi * Real.exp ((1 / 2 + ε) / s') ≤ z.re := by
    have hexp : Real.exp ((1 / 2 + ε) / s') ≤ Real.exp ((1 / 2 + ε) / s) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hc.le hs0 hss')
    have hval : Real.exp ((1 / 2 + ε) / s) = (X - 1) / (2 * Real.pi) := by
      rw [hs, div_div_cancel₀ hc.ne', hLdef, Real.exp_log (lt_trans (Real.exp_pos 1) hdiv)]
    calc 2 * Real.pi * Real.exp ((1 / 2 + ε) / s')
        ≤ 2 * Real.pi * ((X - 1) / (2 * Real.pi)) := by
          rw [← hval]
          exact mul_le_mul_of_nonneg_left hexp h2π.le
      _ = X - 1 := by field_simp
      _ ≤ z.re := by linarith only [hx.1]
  refine h s' ht h8.le z.re (by linarith only [hx.1, hX1]) hxc (hZ z.re hre) z.im him him' ?_
  rw [← hz]
  congr 1
  apply Complex.ext <;> simp

/-- **The saddle horizon on almost all heights.** For every `0 < ε ≤ ¼` the heights `X ∈ [T, 2T]` with
`Λ_X > (½+ε)/log((X−1)/2π)` have measure `O(T^{1−ε²/32})`. -/
theorem exists_volume_localNewmanConstant_gt_le {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      volume {X ∈ Icc T (2 * T) |
          (1 / 2 + ε) / Real.log ((X - 1) / (2 * Real.pi)) < localNewmanConstant X} ≤
        ENNReal.ofReal (C * T ^ (1 - ε ^ 2 / 32)) := by
  have he0 : 0 < ε ^ 2 / 32 := by positivity
  have he1 : ε ^ 2 / 32 ≤ 1 := by nlinarith only [hε, hε4]
  obtain ⟨C, hC, hvol⟩ := exists_volume_zetaLargeNear_le_rpow he0 he1
  obtain ⟨X₁, hX₁, hloc⟩ := exists_localNewmanConstant_le_of_typical hε hε4
  refine ⟨C, max 6 X₁, hC, fun T hT => ?_⟩
  have hT6 : 6 ≤ T := (le_max_left _ _).trans hT
  have hTX : X₁ ≤ T := (le_max_right _ _).trans hT
  refine (measure_mono fun X hXmem => ?_).trans (hvol T hT6)
  obtain ⟨hXI, hbad⟩ := hXmem
  refine ⟨hXI, ?_⟩
  by_contra hno
  push Not at hno
  refine absurd (hloc X (hTX.trans hXI.1) fun x hx w hw0 hw => ?_) (not_le.mpr hbad)
  have hx' := abs_le.mp hx
  have hx1 : 1 ≤ x := by linarith only [hx'.1, hXI.1, hT6]
  have hx0 : 0 < x := by linarith only [hx1]
  have hre : ((((w + 1 / 2 : ℝ) : ℂ) + x * I)).re = w + 1 / 2 := by simp
  have him : ((((w + 1 / 2 : ℝ) : ℂ) + x * I)).im = x := by simp
  have hz := hno ((w + 1 / 2 : ℝ) + x * I) (by rw [hre]; linarith only [hw0])
    (by rw [hre]; linarith only [hw, hε4]) (by rw [him]; linarith only [hx'.1, hx'.2, abs_le.mpr hx'])
  refine hz.trans ?_
  have hT2x : T ≤ 2 * x := by linarith only [hx'.1, hXI.1, hT6]
  calc T ^ (ε ^ 2 / 32) ≤ (2 * x) ^ (ε ^ 2 / 32) :=
        Real.rpow_le_rpow (by linarith only [hT6]) hT2x he0.le
    _ = (2 : ℝ) ^ (ε ^ 2 / 32) * x ^ (ε ^ 2 / 32) := Real.mul_rpow (by norm_num) hx0.le
    _ ≤ 2 * x ^ (ε ^ 2 / 32) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx0.le _)
        calc (2 : ℝ) ^ (ε ^ 2 / 32) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
          _ = 2 := Real.rpow_one 2

end

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_volume_localNewmanConstant_gt_le
