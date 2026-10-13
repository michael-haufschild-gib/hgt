import GaloisForLFunctions.RHTower.CosDilationShortSupportRigidity

/-!
# Scale-invariant autocorrelation bounds and medium-support rigidity (`β ≤ 5α/2` and `β ≤ 7α/3`)

Let `f : ℝ → ℝ` be continuous and supported in `[α, β]` (`0 < α ≤ β`), with dilation
autocorrelation `A_f(r) = ∫_0^∞ f(y) f(ry) dy` (`dilationAutocorr`) and cosine–dilation kernel
`Ψ_f = Cf ⋆ f` (`cosDilationKernel`).

* **Scale-invariant Cauchy–Schwarz bound** (`sqrt_mul_abs_dilationAutocorr_le`,
  `abs_dilationAutocorr_le_of_pos`): for every `r > 0`,
  `√r |A_f(r)| ≤ A_f(1)` and `|A_f(r)| ≤ (1 + r⁻¹) / 2 · A_f(1)`, with `0 ≤ A_f(1) = ∫ f²`
  (`dilationAutocorr_one_nonneg`, `eq_zero_of_dilationAutocorr_one_le_zero`).
* **Medium-support periodization identities (`β ≤ 3α` and `β ≤ 5α/2`)**
  (`dilationAutocorr_one_add_two_eq_cosDilationKernel_one`,
  `two_mul_dilationAutocorr_two_add_three_halves_eq_neg_cosDilationKernel_one`,
  `three_mul_cosDilationKernel_one_eq`):
  when `Ψ_f(0) = 0` and `Ψ_f(n) = 0` for all `n ≥ 2`:
  - if `β ≤ 3α`, periodization at `x = 0` gives `A_f(1) + A_f(2) = Ψ_f(1)`;
  - if `β ≤ 5α/2`, periodization at `x = ½` combined with the inversion law `A_f(½) = 2 A_f(2)`
    gives `2 A_f(2) + A_f(3/2) = −Ψ_f(1)`;
  - eliminating `A_f(2)` between the two gives the exact identity
    `3 Ψ_f(1) = 2 A_f(1) − A_f(3/2)`.
* **Purely archimedean energy comparability and mandatory dyadic anti-correlation (`β ≤ 5α/2`)**
  (`cosDilationKernel_one_bounds_of_blind_of_le_five_halves_mul`,
  `dilationAutocorr_two_le_neg_one_div_eighteen`,
  `eq_zero_of_cosDilationKernel_blind_of_le_five_halves_mul_of_dilationAutocorr_two_gt`):
  combining `3 Ψ_f(1) = 2 A_f(1) − A_f(3/2)` with `|A_f(3/2)| ≤ (5/6) A_f(1)` yields, for every
  continuous blind core with `Ψ_f(0) = 0` and `β ≤ 5α/2` (without requiring smoothness or `ζ`),
  `(7/18) A_f(1) ≤ Ψ_f(1) ≤ (17/18) A_f(1)` and `A_f(2) ≤ −(1/18) A_f(1)`.
  In particular, if `−(1/18) A_f(1) < A_f(2)` (or `0 ≤ A_f(2)`), then `f = 0`.
* **Three-term periodization at `x = 1/3` (`β ≤ 7α/3`)**
  (`dilationAutocorr_third_periodization_eq`,
  `eq_zero_of_cosDilationKernel_blind_of_le_seven_thirds_mul_of_third_nonneg`):
  if `β ≤ 7α/3`, periodization at `x = 1/3` and `A_f(2/3) = (2/3) A_f(3/2)` give
  `(2/3) A_f(3/2) + A_f(4/3) + A_f(5/3) = −Ψ_f(1) ≤ −(7/18) A_f(1)`, so
  `0 ≤ (2/3) A_f(3/2) + A_f(4/3) + A_f(5/3)` forces `f = 0` (killing two-bump cores concentrated
  near `r ∈ {½, 1, 2}`).
-/

open MeasureTheory Set Real

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### Scale-invariant Cauchy–Schwarz and AM–GM bounds for `dilationAutocorr` -/

/-- `A_f(1) = ∫_ℝ f(z)² dz` for a core supported in `[α, β] ⊂ (0, ∞)`. -/
theorem dilationAutocorr_one_eq_integral_sq {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    dilationAutocorr f 1 = ∫ z, f z * f z := by
  unfold dilationAutocorr
  simp only [one_mul]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
  have : f z = 0 := by
    by_contra h
    exact hz (lt_of_lt_of_le hα (hsupp z h).1)
  simp [this]

/-- `0 ≤ A_f(1)` for any core supported in `[α, β] ⊂ (0, ∞)`. -/
theorem dilationAutocorr_one_nonneg {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    0 ≤ dilationAutocorr f 1 := by
  rw [dilationAutocorr_one_eq_integral_sq hα hsupp]
  exact integral_nonneg fun _ => mul_self_nonneg _

/-- If `f` is continuous and supported in `[α, β] ⊂ (0, ∞)` with `A_f(1) ≤ 0`, then `f = 0`. -/
theorem eq_zero_of_dilationAutocorr_one_le_zero (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hA1 : dilationAutocorr f 1 ≤ 0) (y : ℝ) :
    f y = 0 := by
  have hEz : ∫ z, f z * f z = 0 := by
    have h0 := dilationAutocorr_one_nonneg hα hsupp
    have h1 := le_antisymm hA1 h0
    rwa [← dilationAutocorr_one_eq_integral_sq hα hsupp]
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun z hz => ?_
    by_contra h
    exact hz (hsupp z h)
  have hsq : Integrable fun z => f z * f z :=
    (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hae : (fun z => f z * f z) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg (f z)) hsq).mp hEz
  have heq := (Continuous.ae_eq_iff_eq volume (hf.mul hf) continuous_const).mp hae
  exact mul_self_eq_zero.mp (congrFun heq y)

/-- **Scale-invariant Cauchy–Schwarz bound for the dilation autocorrelation.**
For any continuous `f` supported in `[α, β]` (`0 < α ≤ β`) and any `r > 0`,
`√r |A_f(r)| ≤ A_f(1)`. -/
theorem sqrt_mul_abs_dilationAutocorr_le (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {r : ℝ} (hr : 0 < r) :
    Real.sqrt r * |dilationAutocorr f r| ≤ dilationAutocorr f 1 := by
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
  have hAr : dilationAutocorr f r = ∫ z, f z * f (r * z) := by
    unfold dilationAutocorr
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    have : f z = 0 := by
      by_contra h
      exact hz (lt_of_lt_of_le hα (hsupp z h).1)
    simp [this]
  have hscale : r * ∫ z, f (r * z) * f (r * z) = ∫ z, f z * f z := by
    have h := Measure.integral_comp_mul_left (fun z => f z * f z) r
    simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hr)] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hAr, dilationAutocorr_one_eq_integral_sq hα hsupp]
  have hsqrt0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  calc Real.sqrt r * |∫ z, f z * f (r * z)|
      ≤ Real.sqrt r * ∫ z, |f z * f (r * z)| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hsqrt0
    _ = ∫ z, Real.sqrt r * |f z * f (r * z)| := (integral_const_mul _ _).symm
    _ ≤ ∫ z, (f z * f z + r * (f (r * z) * f (r * z))) / 2 := by
        refine integral_mono (hint.abs.const_mul _) ((hsq.add (hsqr.const_mul r)).div_const 2)
          fun z => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|f z| - Real.sqrt r * |f (r * z)|), sq_abs (f z),
          sq_abs (f (r * z)), Real.mul_self_sqrt hr.le]
    _ = ∫ z, f z * f z := by
        rw [integral_div, integral_add hsq (hsqr.const_mul r), integral_const_mul, hscale]
        ring

/-- Unweighted AM–GM bound `|A_f(r)| ≤ (1 + r⁻¹) / 2 · A_f(1)` for `r > 0`. -/
theorem abs_dilationAutocorr_le_of_pos (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {r : ℝ} (hr : 0 < r) :
    |dilationAutocorr f r| ≤ (1 + r⁻¹) / 2 * dilationAutocorr f 1 := by
  have h := sqrt_mul_abs_dilationAutocorr_le hf hα hsupp hr
  have hA1 : 0 ≤ dilationAutocorr f 1 := dilationAutocorr_one_nonneg hα hsupp
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h1 : |dilationAutocorr f r| ≤ (Real.sqrt r)⁻¹ * dilationAutocorr f 1 := by
    rw [inv_mul_eq_div, le_div_iff₀' hsqrt]
    exact h
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hA1)
  have hsq : 0 ≤ (1 - (Real.sqrt r)⁻¹) ^ 2 := sq_nonneg _
  have hinv_sq : ((Real.sqrt r)⁻¹) ^ 2 = r⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hr.le]
  linarith

/-! ### Medium-support periodization identities (`β ≤ 3α` and `β ≤ 5α/2`) -/

/-- **Two-term periodization at `x = 0` for `β ≤ 3α`.**
If `f` is continuous and supported in `[α, β]` with `0 < α ≤ β ≤ 3α`, `Ψ_f(0) = 0`, and
`Ψ_f(n) = 0` for all `n ≥ 2`, then `A_f(1) + A_f(2) = Ψ_f(1)`. -/
theorem dilationAutocorr_one_add_two_eq_cosDilationKernel_one (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 3 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    dilationAutocorr f 1 + dilationAutocorr f 2 = cosDilationKernel f 1 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 3 := by rw [div_le_iff₀ hα]; linarith
  have hlo : 1 / 3 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hZ : ∀ r : ℝ, (r ≤ 1 / 3 ∨ 3 ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have hP0 := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ 0
  rw [tsum_eq_sum (s := {-2, -1, 1, 2}) fun k hk => ?_] at hP0
  rotate_left
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hZ _ ?_, Complex.ofReal_zero]
    by_cases hk0 : k = 0
    · subst hk0; left; norm_num
    · right
      have hk3 : 3 ≤ |k| := by rw [le_abs']; omega
      rw [zero_add, ← Int.cast_abs]
      exact_mod_cast hk3
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hP0
  simp only [Int.cast_neg, Int.cast_ofNat, Int.cast_one, zero_add, abs_neg,
    Nat.abs_ofNat, abs_one, mul_zero, Real.cos_zero, mul_one, h0] at hP0
  have e' : ((2 * (dilationAutocorr f 1 + dilationAutocorr f 2) : ℝ) : ℂ) =
      ((2 * cosDilationKernel f 1 : ℝ) : ℂ) := by
    rw [← hP0]; push_cast; ring
  have := Complex.ofReal_injective e'
  linarith

/-- **Two-term periodization at `x = ½` for `β ≤ 5α/2`.**
If `f` is continuous and supported in `[α, β]` with `0 < α ≤ β ≤ (5/2)α`, `Ψ_f(0) = 0`, and
`Ψ_f(n) = 0` for all `n ≥ 2`, then `2 A_f(2) + A_f(3/2) = −Ψ_f(1)`. -/
theorem two_mul_dilationAutocorr_two_add_three_halves_eq_neg_cosDilationKernel_one
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 5 / 2 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    2 * dilationAutocorr f 2 + dilationAutocorr f (3 / 2) = -cosDilationKernel f 1 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 5 / 2 := by rw [div_le_iff₀ hα]; linarith
  have hlo : 2 / 5 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hZ : ∀ r : ℝ, (r ≤ 2 / 5 ∨ 5 / 2 ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have hP1 := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ (1 / 2)
  rw [tsum_eq_sum (s := {-2, -1, 0, 1}) fun k hk => ?_] at hP1
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
  have a1 : |(1 / 2 : ℝ) + ((-2 : ℤ) : ℝ)| = 3 / 2 := by
    rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
  have a2 : |(1 / 2 : ℝ) + ((-1 : ℤ) : ℝ)| = 1 / 2 := by
    rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
  have a3 : |(1 / 2 : ℝ) + ((0 : ℤ) : ℝ)| = 1 / 2 := by
    rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
  have a4 : |(1 / 2 : ℝ) + ((1 : ℤ) : ℝ)| = 3 / 2 := by
    rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
  have hcos : Real.cos (2 * π * (1 / 2)) = -1 := by
    rw [show 2 * π * (1 / 2) = π by ring, Real.cos_pi]
  have hinv2 : dilationAutocorr f (1 / 2) = 2 * dilationAutocorr f 2 := by
    simpa [one_div] using dilationAutocorr_inv f (by norm_num : (0 : ℝ) < 2)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    a1, a2, a3, a4, hinv2, hcos, h0] at hP1
  have e' : ((2 * (2 * dilationAutocorr f 2 + dilationAutocorr f (3 / 2)) : ℝ) : ℂ) =
      ((-(2 * cosDilationKernel f 1) : ℝ) : ℂ) := by
    push_cast
    rw [show (-(2 * (cosDilationKernel f 1 : ℂ))) =
      ((0 + 2 * cosDilationKernel f 1 * -1 : ℝ) : ℂ) by push_cast; ring, ← hP1]
    push_cast; ring
  have := Complex.ofReal_injective e'
  linarith

/-- **Elimination of `A_f(2)` for `β ≤ 5α/2`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β ≤ (5/2)α`) with `Ψ_f(0) = 0`,
`3 Ψ_f(1) = 2 A_f(1) − A_f(3/2)`. -/
theorem three_mul_cosDilationKernel_one_eq (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 5 / 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    3 * cosDilationKernel f 1 = 2 * dilationAutocorr f 1 - dilationAutocorr f (3 / 2) := by
  have h1 := dilationAutocorr_one_add_two_eq_cosDilationKernel_one hf hα hαβ (by linarith)
    hsupp h0 hblind
  have h2 := two_mul_dilationAutocorr_two_add_three_halves_eq_neg_cosDilationKernel_one
    hf hα hαβ hβ hsupp h0 hblind
  linarith

/-! ### Purely archimedean energy comparability and mandatory dyadic anti-correlation -/

/-- **Purely archimedean energy comparability of `Ψ_f(1)` for `β ≤ 5α/2`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β ≤ (5/2)α`) with `Ψ_f(0) = 0`,
`(7/18) A_f(1) ≤ Ψ_f(1) ≤ (17/18) A_f(1)`. -/
theorem cosDilationKernel_one_bounds_of_blind_of_le_five_halves_mul (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 5 / 2 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    7 / 18 * dilationAutocorr f 1 ≤ cosDilationKernel f 1 ∧
      cosDilationKernel f 1 ≤ 17 / 18 * dilationAutocorr f 1 := by
  have h3 := three_mul_cosDilationKernel_one_eq hf hα hαβ hβ hsupp h0 hblind
  have hb := abs_dilationAutocorr_le_of_pos hf hα hsupp (by norm_num : (0 : ℝ) < 3 / 2)
  have hb' : |dilationAutocorr f (3 / 2)| ≤ 5 / 6 * dilationAutocorr f 1 := by linarith
  have hbounds := abs_le.mp hb'
  constructor <;> linarith

/-- **Mandatory dyadic anti-correlation for `β ≤ 5α/2`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β ≤ (5/2)α`) with `Ψ_f(0) = 0`,
`A_f(2) ≤ −(1/18) A_f(1)`. -/
theorem dilationAutocorr_two_le_neg_one_div_eighteen (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 5 / 2 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    dilationAutocorr f 2 ≤ -(1 / 18) * dilationAutocorr f 1 := by
  have h1 := dilationAutocorr_one_add_two_eq_cosDilationKernel_one hf hα hαβ (by linarith)
    hsupp h0 hblind
  have h2 := (cosDilationKernel_one_bounds_of_blind_of_le_five_halves_mul
    hf hα hαβ hβ hsupp h0 hblind).2
  linarith

/-- **Medium-support rigidity under weak dyadic correlation (`β ≤ 5α/2`).**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β ≤ (5/2)α`) with `Ψ_f(0) = 0`
and `0 ≤ A_f(2)` (or more generally `0 ≤ A_f(2) + (1/18) A_f(1)`), then `f = 0`. -/
theorem eq_zero_of_cosDilationKernel_blind_of_le_five_halves_mul_of_dilationAutocorr_two_nonneg
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 5 / 2 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hA2 : 0 ≤ dilationAutocorr f 2) (y : ℝ) : f y = 0 := by
  have hle := dilationAutocorr_two_le_neg_one_div_eighteen hf hα hαβ hβ hsupp h0 hblind
  exact eq_zero_of_dilationAutocorr_one_le_zero hf hα hsupp (by linarith) y

/-! ### Three-term periodization at `x = 1/3` and rigidity for `β ≤ 7α/3` -/

/-- **Three-term periodization at `x = 1/3` for `β ≤ 7α/3`.**
If `f` is continuous and supported in `[α, β]` with `0 < α ≤ β ≤ (7/3)α`, `Ψ_f(0) = 0`, and
`Ψ_f(n) = 0` for all `n ≥ 2`, then
`(3/2) A_f(3/2) + A_f(4/3) + A_f(5/3) = −Ψ_f(1)`. -/
theorem dilationAutocorr_third_periodization_eq (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 7 / 3 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    3 / 2 * dilationAutocorr f (3 / 2) + dilationAutocorr f (4 / 3) +
      dilationAutocorr f (5 / 3) = -cosDilationKernel f 1 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 7 / 3 := by rw [div_le_iff₀ hα]; linarith
  have hlo : 3 / 7 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hZ : ∀ r : ℝ, (r ≤ 3 / 7 ∨ 7 / 3 ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have hP := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ (1 / 3)
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
  have a1 : |(1 / 3 : ℝ) + ((-2 : ℤ) : ℝ)| = 5 / 3 := by
    rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
  have a2 : |(1 / 3 : ℝ) + ((-1 : ℤ) : ℝ)| = 2 / 3 := by
    rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
  have a3 : |(1 / 3 : ℝ) + ((0 : ℤ) : ℝ)| = 1 / 3 := by
    rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
  have a4 : |(1 / 3 : ℝ) + ((1 : ℤ) : ℝ)| = 4 / 3 := by
    rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
  have h13 : dilationAutocorr f (1 / 3) = 0 := hZ _ (Or.inl (by norm_num))
  have h23 : dilationAutocorr f (2 / 3) = 3 / 2 * dilationAutocorr f (3 / 2) := by
    have hinv := dilationAutocorr_inv f (by norm_num : (0 : ℝ) < 3 / 2)
    rw [show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num] at hinv
    exact hinv
  have hcos : Real.cos (2 * π * (1 / 3)) = -(1 / 2) := by
    rw [show 2 * π * (1 / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    a1, a2, a3, a4, h13, h23, hcos, h0] at hP
  have e' : ((3 / 2 * dilationAutocorr f (3 / 2) + dilationAutocorr f (4 / 3) +
      dilationAutocorr f (5 / 3) : ℝ) : ℂ) = ((-cosDilationKernel f 1 : ℝ) : ℂ) := by
    push_cast
    rw [show (-(cosDilationKernel f 1 : ℂ)) =
      ((0 + 2 * cosDilationKernel f 1 * -(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← hP]
    push_cast; ring
  exact Complex.ofReal_injective e'

/-- **Medium-support rigidity at `x = 1/3` (`β ≤ 7α/3`).**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β ≤ (7/3)α`) with `Ψ_f(0) = 0`
and `0 ≤ (3/2) A_f(3/2) + A_f(4/3) + A_f(5/3)`, then `f = 0`. -/
theorem eq_zero_of_cosDilationKernel_blind_of_le_seven_thirds_mul_of_third_nonneg
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 7 / 3 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hthird : 0 ≤ 3 / 2 * dilationAutocorr f (3 / 2) + dilationAutocorr f (4 / 3) +
      dilationAutocorr f (5 / 3)) (y : ℝ) : f y = 0 := by
  have heq := dilationAutocorr_third_periodization_eq hf hα hαβ hβ hsupp h0 hblind
  have hb := (cosDilationKernel_one_bounds_of_blind_of_le_five_halves_mul
    hf hα hαβ (by linarith) hsupp h0 hblind).1
  exact eq_zero_of_dilationAutocorr_one_le_zero hf hα hsupp (by linarith) y

end

end RHTower
