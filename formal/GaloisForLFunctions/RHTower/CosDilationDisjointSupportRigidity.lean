import GaloisForLFunctions.RHTower.CosDilationMediumSupportRigidity

/-!
# Disjoint-preimage autocorrelation halving law and medium-support rigidity (`β ≤ 3α`, `β ≤ 9α/4`)

Let `f : ℝ → ℝ` be continuous and supported in `[α, β]` (`0 < α ≤ β`), with dilation
autocorrelation `A_f(r) = ∫_0^∞ f(y) f(ry) dy` (`dilationAutocorr`) and cosine–dilation kernel
`Ψ_f = Cf ⋆ f` (`cosDilationKernel`).

* **Disjoint-preimage halving law** (`sqrt_mul_abs_dilationAutocorr_le_half_of_le_sq_mul`,
  `sqrt_mul_abs_dilationAutocorr_le_half_of_sq_mul_le`): whenever `β ≤ r² α` (or symmetrically
  `r² β ≤ α` via `A_f(r⁻¹) = r A_f(r)`), the pre-image support `[α, β/r]` and the dilated support
  `[rα, β]` of `f(y) f(ry)` lie on opposite sides of the cut point `rα`. Consequently, the global
  scale-invariant Cauchy–Schwarz bound `√r |A_f(r)| ≤ A_f(1)` sharpens by a factor of `½`:
  `√r |A_f(r)| ≤ ½ A_f(1)`.
* **Dyadic and sesqui-dyadic autocorrelation bounds**
  (`abs_dilationAutocorr_two_le`, `abs_dilationAutocorr_three_halves_le`):
  - for all `β ≤ 4α`, `√2 |A_f(2)| ≤ ½ A_f(1)` (and `|A_f(2)| ≤ (3/8) A_f(1)`);
  - for all `β ≤ (9/4)α`, `√(3/2) |A_f(3/2)| ≤ ½ A_f(1)` (and `|A_f(3/2)| ≤ (5/12) A_f(1)`).
* **Energy comparability of `Ψ_f(1)` up to `β ≤ 3α` from the `x = 0` node alone**
  (`cosDilationKernel_one_bounds_of_blind_of_le_three_mul`,
  `eq_zero_of_cosDilationKernel_blind_of_le_three_mul_of_one_le_zero`):
  combining `A_f(1) + A_f(2) = Ψ_f(1)` (`β ≤ 3α`) with `|A_f(2)| ≤ (3/8) A_f(1)` gives
  `(5/8) A_f(1) ≤ Ψ_f(1) ≤ (11/8) A_f(1)` for every continuous blind core with `Ψ_f(0) = 0` and
  `β ≤ 3α` (without requiring smoothness or `ζ`).
* **Strengthened dyadic anti-correlation and `x = ¼` node identity for `β ≤ 9α/4`**
  (`cosDilationKernel_one_bounds_of_blind_of_le_nine_fourths_mul`,
  `dilationAutocorr_two_le_neg_seven_div_thirty_six`,
  `dilationAutocorr_quarter_periodization_eq`):
  for `β ≤ (9/4)α`, `(19/36) A_f(1) ≤ Ψ_f(1) ≤ (29/36) A_f(1)`, `A_f(2) ≤ −(7/36) A_f(1)`, and the
  quarter-period node `x = ¼` satisfies `(4/3) A_f(4/3) + A_f(5/4) + A_f(7/4) = 0`.
-/

open MeasureTheory Set Real Filter

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### Disjoint-preimage halving law for `dilationAutocorr` -/

/-- **Disjoint-preimage autocorrelation halving law (`β ≤ r² α`).**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`), and `r > 0` satisfies
`β ≤ r² α`, then `√r |A_f(r)| ≤ ½ A_f(1)`. -/
theorem sqrt_mul_abs_dilationAutocorr_le_half_of_le_sq_mul (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {r : ℝ} (hr : 0 < r)
    (hβ : β ≤ r ^ 2 * α) :
    Real.sqrt r * |dilationAutocorr f r| ≤ 1 / 2 * dilationAutocorr f 1 := by
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun z hz => ?_
    by_contra h
    exact hz (hsupp z h)
  have hsq : Integrable fun z => f z * f z :=
    (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hsqr : Integrable fun z => f (r * z) * f (r * z) := by
    have hc : HasCompactSupport fun z => f (r * z) := by
      have h := hfc.comp_smul hr.ne'
      simpa only [Function.comp_def, smul_eq_mul] using h
    exact ((hf.comp (continuous_const.mul continuous_id)).mul
      (hf.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hc.mul_right
  have hint : Integrable fun z => f z * f (r * z) :=
    (hf.mul (hf.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hfc.mul_right
  set gL : ℝ → ℝ := (Iio (r * α)).indicator (fun z => f z * f z) with hgL_def
  set gR : ℝ → ℝ := (Ici (r * α)).indicator (fun z => f z * f z) with hgR_def
  have hgL : Integrable gL := hsq.indicator measurableSet_Iio
  have hgR : Integrable gR := hsq.indicator measurableSet_Ici
  have hgRr_eq : (fun z => gR (r * z)) =
      (Ici α).indicator (fun z => f (r * z) * f (r * z)) := by
    funext z
    simp only [hgR_def]
    by_cases hz : α ≤ z
    · rw [indicator_of_mem (show r * z ∈ Ici (r * α) from mul_le_mul_of_nonneg_left hz hr.le),
        indicator_of_mem (show z ∈ Ici α from hz)]
    · rw [indicator_of_notMem (show r * z ∉ Ici (r * α) from
        fun h => hz (le_of_mul_le_mul_left h hr)),
        indicator_of_notMem (show z ∉ Ici α from hz)]
  have hgRr : Integrable (fun z => gR (r * z)) := by
    rw [hgRr_eq]
    exact hsqr.indicator measurableSet_Ici
  have hscale : r * ∫ z, gR (r * z) = ∫ z, gR z := by
    have h := Measure.integral_comp_mul_left gR r
    simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hr)] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have hsum : ∀ z, gL z + gR z = f z * f z := fun z => by
    simp only [hgL_def, hgR_def]
    by_cases hz : z < r * α
    · rw [indicator_of_mem (show z ∈ Iio (r * α) from hz),
        indicator_of_notMem (show z ∉ Ici (r * α) from not_le.mpr hz), add_zero]
    · rw [indicator_of_notMem (show z ∉ Iio (r * α) from hz),
        indicator_of_mem (show z ∈ Ici (r * α) from not_lt.mp hz), zero_add]
  have hAr : dilationAutocorr f r = ∫ z, f z * f (r * z) := by
    unfold dilationAutocorr
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    have : f z = 0 := by
      by_contra h
      exact hz (lt_of_lt_of_le hα (hsupp z h).1)
    simp [this]
  rw [hAr, dilationAutocorr_one_eq_integral_sq hα hsupp]
  have hsqrt0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  calc Real.sqrt r * |∫ z, f z * f (r * z)|
      ≤ Real.sqrt r * ∫ z, |f z * f (r * z)| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hsqrt0
    _ = ∫ z, Real.sqrt r * |f z * f (r * z)| := (integral_const_mul _ _).symm
    _ ≤ ∫ z, (gL z + r * gR (r * z)) / 2 := by
        refine integral_mono_ae (hint.abs.const_mul _) ((hgL.add (hgRr.const_mul r)).div_const 2) ?_
        filter_upwards [Measure.ae_ne volume (r * α)] with z hz
        have hgL0 : 0 ≤ gL z := indicator_nonneg (fun _ _ => mul_self_nonneg _) _
        have hgR0 : 0 ≤ gR (r * z) := indicator_nonneg (fun _ _ => mul_self_nonneg _) _
        by_cases hfz : f z = 0
        · rw [hfz, zero_mul, abs_zero, mul_zero]
          positivity
        · by_cases hfrz : f (r * z) = 0
          · rw [hfrz, mul_zero, abs_zero, mul_zero]
            positivity
          · obtain ⟨hz1, _⟩ := hsupp z hfz
            obtain ⟨_, hrz2⟩ := hsupp (r * z) hfrz
            have hzr : z ≤ r * α := by
              apply le_of_mul_le_mul_left _ hr
              calc r * z ≤ β := hrz2
                _ ≤ r ^ 2 * α := hβ
                _ = r * (r * α) := by ring
            have hzl : z < r * α := lt_of_le_of_ne hzr hz
            have hrz_ge : r * α ≤ r * z := mul_le_mul_of_nonneg_left hz1 hr.le
            have hL : gL z = f z * f z := indicator_of_mem (show z ∈ Iio (r * α) from hzl) _
            have hR : gR (r * z) = f (r * z) * f (r * z) :=
              indicator_of_mem (show r * z ∈ Ici (r * α) from hrz_ge) _
            rw [hL, hR, abs_mul]
            nlinarith [sq_nonneg (|f z| - Real.sqrt r * |f (r * z)|), sq_abs (f z),
              sq_abs (f (r * z)), Real.mul_self_sqrt hr.le]
    _ = 1 / 2 * ∫ z, f z * f z := by
        rw [integral_div, integral_add hgL (hgRr.const_mul r), integral_const_mul, hscale,
          ← integral_add hgL hgR]
        simp_rw [hsum]
        ring

/-- **Symmetric disjoint-preimage halving law (`r² β ≤ α`).**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`), and `r > 0` satisfies
`r² β ≤ α`, then `√r |A_f(r)| ≤ ½ A_f(1)`. -/
theorem sqrt_mul_abs_dilationAutocorr_le_half_of_sq_mul_le (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {r : ℝ} (hr : 0 < r)
    (hβ : r ^ 2 * β ≤ α) :
    Real.sqrt r * |dilationAutocorr f r| ≤ 1 / 2 * dilationAutocorr f 1 := by
  have hinv_pos : 0 < r⁻¹ := inv_pos.mpr hr
  have hβ' : β ≤ (r⁻¹) ^ 2 * α := by
    rw [inv_pow, le_inv_mul_iff₀ (pow_pos hr 2)]
    exact hβ
  have h := sqrt_mul_abs_dilationAutocorr_le_half_of_le_sq_mul hf hα hsupp hinv_pos hβ'
  rw [dilationAutocorr_inv f hr, abs_mul, abs_of_pos hr, Real.sqrt_inv, ← mul_assoc] at h
  have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hr_eq : (Real.sqrt r)⁻¹ * r = Real.sqrt r := by
    rw [inv_mul_eq_iff_eq_mul₀ hsqrt_pos.ne', Real.mul_self_sqrt hr.le]
  rwa [hr_eq] at h

/-- **Dyadic autocorrelation bound for `β ≤ 4α`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β ≤ 4α`),
`√2 |A_f(2)| ≤ ½ A_f(1)` and `|A_f(2)| ≤ (3/8) A_f(1)`. -/
theorem abs_dilationAutocorr_two_le (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hβ : β ≤ 4 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    |dilationAutocorr f 2| ≤ 3 / 8 * dilationAutocorr f 1 := by
  have h := sqrt_mul_abs_dilationAutocorr_le_half_of_le_sq_mul hf hα hsupp
    (by norm_num : (0 : ℝ) < 2) (by linarith)
  have hA1 : 0 ≤ dilationAutocorr f 1 := dilationAutocorr_one_nonneg hα hsupp
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h1 : (4 / 3 : ℝ) * |dilationAutocorr f 2| ≤ 1 / 2 * dilationAutocorr f 1 :=
    (mul_le_mul_of_nonneg_right hsqrt (abs_nonneg _)).trans h
  linarith

/-- **Sesqui-dyadic autocorrelation bound for `β ≤ (9/4)α`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β ≤ (9/4)α`),
`|A_f(3/2)| ≤ (5/12) A_f(1)`. -/
theorem abs_dilationAutocorr_three_halves_le (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hβ : β ≤ 9 / 4 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    |dilationAutocorr f (3 / 2)| ≤ 5 / 12 * dilationAutocorr f 1 := by
  have h := sqrt_mul_abs_dilationAutocorr_le_half_of_le_sq_mul hf hα hsupp
    (by norm_num : (0 : ℝ) < 3 / 2) (by linarith)
  have hA1 : 0 ≤ dilationAutocorr f 1 := dilationAutocorr_one_nonneg hα hsupp
  have hsqrt : (6 / 5 : ℝ) ≤ Real.sqrt (3 / 2) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6 / 5)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h1 : (6 / 5 : ℝ) * |dilationAutocorr f (3 / 2)| ≤ 1 / 2 * dilationAutocorr f 1 :=
    (mul_le_mul_of_nonneg_right hsqrt (abs_nonneg _)).trans h
  linarith

/-! ### Energy comparability of `Ψ_f(1)` up to `β ≤ 3α` and `β ≤ (9/4)α` -/

/-- **Purely archimedean energy comparability of `Ψ_f(1)` for `β ≤ 3α`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β ≤ 3α`) with `Ψ_f(0) = 0`,
`(5/8) A_f(1) ≤ Ψ_f(1) ≤ (11/8) A_f(1)`. -/
theorem cosDilationKernel_one_bounds_of_blind_of_le_three_mul (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 3 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    5 / 8 * dilationAutocorr f 1 ≤ cosDilationKernel f 1 ∧
      cosDilationKernel f 1 ≤ 11 / 8 * dilationAutocorr f 1 := by
  have h1 := dilationAutocorr_one_add_two_eq_cosDilationKernel_one hf hα hαβ hβ hsupp h0 hblind
  have hb := abs_le.mp (abs_dilationAutocorr_two_le hf hα (by linarith) hsupp)
  constructor <;> linarith

/-- If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β ≤ 3α`) with `Ψ_f(0) = 0`
and `Ψ_f(1) ≤ 0`, then `f = 0` (without requiring smoothness of `f`). -/
theorem eq_zero_of_cosDilationKernel_blind_of_le_three_mul_of_one_le_zero (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 3 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (h1 : cosDilationKernel f 1 ≤ 0) (y : ℝ) : f y = 0 := by
  have hb := (cosDilationKernel_one_bounds_of_blind_of_le_three_mul
    hf hα hαβ hβ hsupp h0 hblind).1
  exact eq_zero_of_dilationAutocorr_one_le_zero hf hα hsupp (by linarith) y

/-- **Sharpened energy comparability of `Ψ_f(1)` for `β ≤ (9/4)α`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β ≤ (9/4)α`) with `Ψ_f(0) = 0`,
`(19/36) A_f(1) ≤ Ψ_f(1) ≤ (29/36) A_f(1)`. -/
theorem cosDilationKernel_one_bounds_of_blind_of_le_nine_fourths_mul (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 9 / 4 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    19 / 36 * dilationAutocorr f 1 ≤ cosDilationKernel f 1 ∧
      cosDilationKernel f 1 ≤ 29 / 36 * dilationAutocorr f 1 := by
  have h3 := three_mul_cosDilationKernel_one_eq hf hα hαβ (by linarith) hsupp h0 hblind
  have hb := abs_le.mp (abs_dilationAutocorr_three_halves_le hf hα hβ hsupp)
  constructor <;> linarith

/-- **Sharpened mandatory dyadic anti-correlation for `β ≤ (9/4)α`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β ≤ (9/4)α`) with `Ψ_f(0) = 0`,
`A_f(2) ≤ −(7/36) A_f(1)`. -/
theorem dilationAutocorr_two_le_neg_seven_div_thirty_six (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 9 / 4 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    dilationAutocorr f 2 ≤ -(7 / 36) * dilationAutocorr f 1 := by
  have h1 := dilationAutocorr_one_add_two_eq_cosDilationKernel_one hf hα hαβ (by linarith)
    hsupp h0 hblind
  have h2 := (cosDilationKernel_one_bounds_of_blind_of_le_nine_fourths_mul
    hf hα hαβ hβ hsupp h0 hblind).2
  linarith

/-- **Three-term quarter-period node identity at `x = ¼` for `β ≤ (9/4)α`.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β ≤ (9/4)α`) with `Ψ_f(0) = 0` and
`Ψ_f(n) = 0` for all `n ≥ 2`, then
`(4/3) A_f(4/3) + A_f(5/4) + A_f(7/4) = 0`. -/
theorem dilationAutocorr_quarter_periodization_eq (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 9 / 4 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    4 / 3 * dilationAutocorr f (4 / 3) + dilationAutocorr f (5 / 4) +
      dilationAutocorr f (7 / 4) = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 9 / 4 := by rw [div_le_iff₀ hα]; linarith
  have hlo : 4 / 9 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hZ : ∀ r : ℝ, (r ≤ 4 / 9 ∨ 9 / 4 ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have hP := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ (1 / 4)
  rw [tsum_eq_sum (s := {-2, -1, 0, 1}) fun k hk => ?_] at hP
  rotate_left
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hZ _ ?_, Complex.ofReal_zero]
    right
    rcases le_or_gt 2 k with hk2 | hk2
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      rw [abs_of_pos (by linarith)]; linarith
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      rw [abs_of_neg (by linarith)]; linarith
  have a1 : |(1 / 4 : ℝ) + ((-2 : ℤ) : ℝ)| = 7 / 4 := by
    rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
  have a2 : |(1 / 4 : ℝ) + ((-1 : ℤ) : ℝ)| = 3 / 4 := by
    rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
  have a3 : |(1 / 4 : ℝ) + ((0 : ℤ) : ℝ)| = 1 / 4 := by
    rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
  have a4 : |(1 / 4 : ℝ) + ((1 : ℤ) : ℝ)| = 5 / 4 := by
    rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
  have h14 : dilationAutocorr f (1 / 4) = 0 := hZ _ (Or.inl (by norm_num))
  have h34 : dilationAutocorr f (3 / 4) = 4 / 3 * dilationAutocorr f (4 / 3) := by
    have hinv := dilationAutocorr_inv f (by norm_num : (0 : ℝ) < 4 / 3)
    rw [show (4 / 3 : ℝ)⁻¹ = 3 / 4 by norm_num] at hinv
    exact hinv
  have hcos : Real.cos (2 * π * (1 / 4)) = 0 := by
    rw [show 2 * π * (1 / 4 : ℝ) = π / 2 by ring, Real.cos_pi_div_two]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    a1, a2, a3, a4, h14, h34, hcos, h0] at hP
  have e' : ((4 / 3 * dilationAutocorr f (4 / 3) + dilationAutocorr f (5 / 4) +
      dilationAutocorr f (7 / 4) : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
    push_cast
    rw [show (0 : ℂ) = ((0 + 2 * cosDilationKernel f 1 * 0 : ℝ) : ℂ) by push_cast; ring, ← hP]
    push_cast; ring
  exact Complex.ofReal_injective e'

end

end RHTower
