import GaloisForLFunctions.RHTower.LiCayleyWindowLaw

/-!
# The first sixty-eight Li coefficients are nonnegative, unconditionally

Write `w_ρ = 1 - 1/ρ` and `2λ_n = Σ_ρ m_ρ (2 - w_ρⁿ - w_ρ⁻ⁿ)`. With `w = e^{x + iθ}`,

`Re(2 - wⁿ - w⁻ⁿ) = 2 - 2 cosh(nx) cos(nθ)`.

* On the critical line `x = 0`, and the term is `2 - 2cos(nθ) ≥ 0` for every `n`.
* Off the line, `|x| ≤ |θ|` (the modulus defect `≍ |1 - 2β|/|ρ|²` is smaller than the angle
  `≍ 1/|γ|`). So the term is nonnegative as long as `n|θ| ≤ 3π/2`: either `cos(nθ) ≤ 0`, or
  `n|θ| < π/2` and `cosh(nx)cos(nθ) ≤ cosh(nθ)cos(nθ) ≤ 1` (`cos_mul_cosh_le_one`).
* Every off-line zero has `γ² ≥ 431/2`, hence `|θ| ≤ |γ|/(γ² - 1/4)`, and `n ≤ 68` keeps
  `n|θ| ≤ 3π/2`.

**Theorem** (`re_xiLiPaired_nonneg_of_le_68`). `Re(2λ_n) ≥ 0` for every `n ≤ 68`. This
unconditionally discharges Li's criterion on its first sixty-eight coefficients, without computing
any zero.
-/

open Complex Real
noncomputable section
namespace RHTower

/-! ## An elementary inequality -/

/-- `sin x cosh x - cos x sinh x ≥ 0` on `[0, π/2]`. -/
theorem sin_mul_cosh_sub_cos_mul_sinh_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) :
    0 ≤ Real.sin x * Real.cosh x - Real.cos x * Real.sinh x := by
  set h : ℝ → ℝ := fun y => Real.sin y * Real.cosh y - Real.cos y * Real.sinh y with hh
  have hd : ∀ y, HasDerivAt h (2 * Real.sin y * Real.sinh y) y := by
    intro y
    have h1 := (Real.hasDerivAt_sin y).mul (Real.hasDerivAt_cosh y)
    have h2 := (Real.hasDerivAt_cos y).mul (Real.hasDerivAt_sinh y)
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono : MonotoneOn h (Set.Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    have hs : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1.le
      (by linarith [hy.2, Real.pi_pos])
    have hsh : 0 ≤ Real.sinh y := Real.sinh_nonneg_iff.mpr hy.1.le
    positivity
  have h0 : h 0 = 0 := by simp [hh]
  have := hmono ⟨le_refl 0, by positivity⟩ ⟨hx0, hx1⟩ hx0
  rw [h0] at this
  exact this

/-- **`cos x cosh x ≤ 1` on `[0, π/2]`.** -/
theorem cos_mul_cosh_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) :
    Real.cos x * Real.cosh x ≤ 1 := by
  set f : ℝ → ℝ := fun y => Real.cos y * Real.cosh y with hf
  have hd : ∀ y, HasDerivAt f (-(Real.sin y * Real.cosh y - Real.cos y * Real.sinh y)) y := by
    intro y
    have h1 := (Real.hasDerivAt_cos y).mul (Real.hasDerivAt_cosh y)
    exact h1.congr_deriv (by ring)
  have hanti : AntitoneOn f (Set.Icc 0 (π / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    have := sin_mul_cosh_sub_cos_mul_sinh_nonneg hy.1.le hy.2.le
    linarith
  have h0 : f 0 = 1 := by simp [hf]
  have := hanti ⟨le_refl 0, by positivity⟩ ⟨hx0, hx1⟩ hx0
  rw [h0] at this
  exact this

/-! ## The sign of one Li term -/

/-- `Re(2 - wⁿ - w⁻ⁿ) = 2 - (‖w‖ⁿ + ‖w‖⁻ⁿ) cos(n arg w)`. -/
theorem re_liTerm_eq {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (liTerm w n).re = 2 - (‖w‖ ^ n + (‖w‖ ^ n)⁻¹) * Real.cos (n * Complex.arg w) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hrep : w = (‖w‖ : ℂ) * Complex.exp (Complex.arg w * I) :=
    (Complex.norm_mul_exp_arg_mul_I w).symm
  have hpow : w ^ n = ((‖w‖ ^ n : ℝ) : ℂ) * Complex.exp (((n * Complex.arg w : ℝ) : ℂ) * I) := by
    conv_lhs => rw [hrep]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hipow : w⁻¹ ^ n = (((‖w‖ ^ n)⁻¹ : ℝ) : ℂ) *
      Complex.exp (((-(n * Complex.arg w)) : ℝ) * I) := by
    rw [inv_pow, hpow, mul_inv, ← Complex.exp_neg]
    push_cast
    ring_nf
  rw [liTerm, Complex.sub_re, Complex.sub_re, hpow, hipow, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re,
    Real.cos_neg]
  simp
  ring

/-- **One Li term is nonnegative** when the log-modulus is at most the angle and
`n|arg w| ≤ 3π/2`. -/
theorem re_liTerm_nonneg_of_angle {w : ℂ} (hw : w ≠ 0) {n : ℕ}
    (hx : |Real.log ‖w‖| ≤ |Complex.arg w|) (hn : n * |Complex.arg w| ≤ 3 * π / 2) :
    0 ≤ (liTerm w n).re := by
  rw [re_liTerm_eq hw n]
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set θ := Complex.arg w with hθ
  set x := Real.log ‖w‖ with hxdef
  have he : Real.exp (n * x) = ‖w‖ ^ n := by
    rw [hxdef, ← Real.log_pow, Real.exp_log (pow_pos hpos n)]
  have hP : ‖w‖ ^ n + (‖w‖ ^ n)⁻¹ = 2 * Real.cosh (n * x) := by
    rw [Real.cosh_eq, Real.exp_neg, he]
    ring
  rw [hP]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcosθ : Real.cos (n * θ) = Real.cos (n * |θ|) := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, Real.cos_neg]
  rcases le_or_gt (Real.cos (n * θ)) 0 with hc | hc
  · have : 0 ≤ Real.cosh (n * x) := (Real.cosh_pos _).le
    nlinarith
  · have hsmall : n * |θ| ≤ π / 2 := by
      by_contra hbig
      push Not at hbig
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hbig.le (by linarith)
      rw [← hcosθ] at this
      linarith
    have hcosh : Real.cosh (n * x) ≤ Real.cosh (n * |θ|) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_abs, abs_of_nonneg hn0]
      exact mul_le_mul_of_nonneg_left hx hn0
    have hone := cos_mul_cosh_le_one (by positivity) hsmall
    rw [hcosθ] at hc ⊢
    nlinarith

/-! ## Angle and modulus of `w_ρ` off the line -/

theorem xiRootW_re_eq {ρ : ℂ} (hN : 0 < ρ.re ^ 2 + ρ.im ^ 2) :
    (xiRootW ρ).re = (ρ.re ^ 2 - ρ.re + ρ.im ^ 2) / (ρ.re ^ 2 + ρ.im ^ 2) := by
  have hnormSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  rw [xiRootW, Complex.sub_re, one_div, Complex.inv_re, hnormSq, Complex.one_re]
  field_simp
  ring

theorem xiRootW_im_eq {ρ : ℂ} :
    (xiRootW ρ).im = ρ.im / (ρ.re ^ 2 + ρ.im ^ 2) := by
  have hnormSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  rw [xiRootW, Complex.sub_im, one_div, Complex.inv_im, hnormSq, Complex.one_im]
  ring

theorem norm_xiRootW_sq_eq {ρ : ℂ} (hN : 0 < ρ.re ^ 2 + ρ.im ^ 2) :
    ‖xiRootW ρ‖ ^ 2 = 1 + (1 - 2 * ρ.re) / (ρ.re ^ 2 + ρ.im ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_apply, xiRootW_re_eq hN, xiRootW_im_eq]
  field_simp
  ring

/-- `|arg w| ≤ |tan(arg w)|` when `Re w > 0`. -/
theorem abs_arg_le_abs_tan_arg {w : ℂ} (hw : 0 < w.re) :
    |Complex.arg w| ≤ |w.im / w.re| := by
  have harg_lt : |Complex.arg w| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  rw [← Complex.tan_arg]
  set φ := Complex.arg w
  rcases eq_or_lt_of_le (abs_nonneg φ) with h0 | hpos
  · rw [← h0]; exact abs_nonneg _
  · have hlt := Real.lt_tan hpos harg_lt
    rcases le_or_gt 0 φ with hφ0 | hφ0
    · rw [abs_of_nonneg hφ0] at hlt ⊢
      exact hlt.le.trans (le_abs_self _)
    · rw [abs_of_neg hφ0] at hlt ⊢
      rw [Real.tan_neg] at hlt
      exact hlt.le.trans (neg_le_abs _)

/-- `|sin(arg w)| ≤ |arg w|`, i.e. `|Im w|/‖w‖ ≤ |arg w|`. -/
theorem abs_im_div_norm_le_abs_arg (w : ℂ) : |w.im| / ‖w‖ ≤ |Complex.arg w| := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hs : Real.sin (Complex.arg w) = w.im / ‖w‖ := Complex.sin_arg w
  have hle := Complex.abs_arg_le_pi w
  set φ := Complex.arg w
  have hsabs : |Real.sin φ| ≤ |φ| := by
    rcases le_or_gt 0 φ with h | h
    · rw [abs_of_nonneg h] at hle ⊢
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h hle)]
      exact Real.sin_le h
    · rw [abs_of_neg h] at hle ⊢
      have hs0 : 0 ≤ Real.sin (-φ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hle
      rw [Real.sin_neg] at hs0
      rw [abs_of_nonpos (by linarith)]
      have := Real.sin_le (by linarith : 0 ≤ -φ)
      rw [Real.sin_neg] at this
      linarith
  rw [hs, abs_div, abs_of_pos hwpos] at hsabs
  exact hsabs

/-- `|log y| ≤ |y - 1|·(431/429)` for `|y - 1| ≤ 2/431`. -/
theorem abs_log_le_of_abs_sub_one_le {y : ℝ} (hy : |y - 1| ≤ 2 / 431) :
    |Real.log y| ≤ |y - 1| * (431 / 429) := by
  have hy0 : 0 < y := by have := neg_abs_le (y - 1); linarith
  have hup := Real.log_le_sub_one_of_pos hy0
  have hlow := Real.one_sub_inv_le_log_of_pos hy0
  rw [abs_le]
  constructor
  · have h1 : 1 - y⁻¹ = (y - 1) / y := by field_simp
    rw [h1] at hlow
    have h2 : -(|y - 1| * (431 / 429)) ≤ (y - 1) / y := by
      rw [le_div_iff₀ hy0]
      nlinarith [neg_abs_le (y - 1), le_abs_self (y - 1), abs_nonneg (y - 1)]
    linarith
  · have : y - 1 ≤ |y - 1| * (431 / 429) := by
      nlinarith [le_abs_self (y - 1), abs_nonneg (y - 1)]
    linarith

/-- For `w = 1 - 1/ρ` with `0 < β < 1` and `γ² ≥ 431/2`: `|arg w| ≤ |γ|/(γ² - 1/4)`. -/
theorem abs_arg_xiRootW_le {ρ : ℂ} (hβ0 : 0 < ρ.re) (hβ1 : ρ.re < 1)
    (hγ : 431 / 2 ≤ ρ.im ^ 2) :
    |Complex.arg (xiRootW ρ)| ≤ |ρ.im| / (ρ.im ^ 2 - 1 / 4) := by
  have hN : 0 < ρ.re ^ 2 + ρ.im ^ 2 := by nlinarith
  have hD : 0 < ρ.re ^ 2 - ρ.re + ρ.im ^ 2 := by nlinarith
  have hre := xiRootW_re_eq hN
  have hrepos : 0 < (xiRootW ρ).re := by rw [hre]; exact div_pos hD hN
  refine (abs_arg_le_abs_tan_arg hrepos).trans ?_
  rw [hre, xiRootW_im_eq, div_div_div_cancel_right₀ hN.ne', abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith)
    (by nlinarith [sq_nonneg (ρ.re - 1 / 2)])

/-- For `w = 1 - 1/ρ` with `0 < β < 1` and `γ² ≥ 431/2`: `|log‖w‖| ≤ |arg w|`. -/
theorem abs_log_norm_xiRootW_le_abs_arg {ρ : ℂ} (hβ0 : 0 < ρ.re) (hβ1 : ρ.re < 1)
    (hγ : 431 / 2 ≤ ρ.im ^ 2) :
    |Real.log ‖xiRootW ρ‖| ≤ |Complex.arg (xiRootW ρ)| := by
  have hN : 0 < ρ.re ^ 2 + ρ.im ^ 2 := by nlinarith
  have hw0 : xiRootW ρ ≠ 0 := by
    intro h
    have := xiRootW_re_eq hN
    rw [h, Complex.zero_re] at this
    have hD : 0 < ρ.re ^ 2 - ρ.re + ρ.im ^ 2 := by nlinarith
    have := div_pos hD hN
    linarith
  have hwpos : 0 < ‖xiRootW ρ‖ := norm_pos_iff.mpr hw0
  have hsq := norm_xiRootW_sq_eq hN
  have h1 : |1 - 2 * ρ.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : |‖xiRootW ρ‖ ^ 2 - 1| ≤ 1 / (ρ.re ^ 2 + ρ.im ^ 2) := by
    rw [hsq, add_sub_cancel_left, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right h1 hN.le
  have he2 : 1 / (ρ.re ^ 2 + ρ.im ^ 2) ≤ 2 / 431 := by
    rw [div_le_div_iff₀ hN (by norm_num)]; nlinarith
  have hlog := abs_log_le_of_abs_sub_one_le (he.trans he2)
  rw [Real.log_pow, abs_mul] at hlog
  simp only [Nat.cast_ofNat, abs_two] at hlog
  have hwle : ‖xiRootW ρ‖ ≤ 101 / 100 := by
    have : ‖xiRootW ρ‖ ^ 2 ≤ (101 / 100) ^ 2 := by
      have := le_abs_self (‖xiRootW ρ‖ ^ 2 - 1); nlinarith
    exact (pow_le_pow_iff_left₀ hwpos.le (by norm_num) two_ne_zero).mp this
  have hsin := abs_im_div_norm_le_abs_arg (xiRootW ρ)
  rw [xiRootW_im_eq, abs_div, abs_of_pos hN] at hsin
  have hγabs : 14 ≤ |ρ.im| := by
    by_contra h
    push Not at h
    nlinarith [sq_abs ρ.im, abs_nonneg ρ.im]
  have hlow : 1 / (ρ.re ^ 2 + ρ.im ^ 2) * (431 / 429) / 2 ≤
      |ρ.im| / (ρ.re ^ 2 + ρ.im ^ 2) / ‖xiRootW ρ‖ := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have : 1 / (ρ.re ^ 2 + ρ.im ^ 2) * (431 / 429) / 2 * ((ρ.re ^ 2 + ρ.im ^ 2) * ‖xiRootW ρ‖)
        = (431 / 858) * ‖xiRootW ρ‖ := by field_simp; ring
    rw [this]
    nlinarith
  calc |Real.log ‖xiRootW ρ‖| ≤ |‖xiRootW ρ‖ ^ 2 - 1| * (431 / 429) / 2 := by linarith
    _ ≤ 1 / (ρ.re ^ 2 + ρ.im ^ 2) * (431 / 429) / 2 := by gcongr
    _ ≤ _ := hlow
    _ ≤ _ := hsin

/-! ## The first sixty-eight coefficients -/

/-- **Every paired Li term with `n ≤ 68` is nonnegative.** -/
theorem re_liTerm_xiRootW_nonneg_of_le_68 {ρ : ℂ} (hρ : xi ρ = 0) (hβ0 : 0 < ρ.re)
    (hβ1 : ρ.re < 1) {n : ℕ} (hn : n ≤ 68) : 0 ≤ (liTerm (xiRootW ρ) n).re := by
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hβ0; simp at hβ0
  by_cases hoff : ρ.re = 1 / 2
  · exact re_liTerm_nonneg_of_norm_eq_one ((norm_xiRootW_eq_one_iff hρ0).mpr hoff) n
  · have hγ := im_sq_ge_of_xi_eq_zero_of_re_ne_half hρ hoff
    have hθ := abs_arg_xiRootW_le hβ0 hβ1 hγ
    have hx := abs_log_norm_xiRootW_le_abs_arg hβ0 hβ1 hγ
    have hw0 : xiRootW ρ ≠ 0 := by
      intro h
      have := norm_xiRootW_sub_one ρ
      rw [h, zero_sub, norm_neg, norm_one] at this
      have hρ1 : ‖ρ‖ = 1 := by field_simp at this; linarith
      have : ρ.im ^ 2 ≤ 1 := by
        have := Complex.abs_im_le_norm ρ
        rw [hρ1] at this
        nlinarith [abs_nonneg ρ.im, sq_abs ρ.im]
      linarith
    refine re_liTerm_nonneg_of_angle hw0 hx ?_
    have hn' : (n : ℝ) ≤ 68 := by exact_mod_cast hn
    set g := |ρ.im| with hg
    have hg2 : g ^ 2 = ρ.im ^ 2 := sq_abs _
    have hg0 : 0 ≤ g := abs_nonneg _
    have hgl : 1467 / 100 ≤ g := by nlinarith
    have hden : 0 < ρ.im ^ 2 - 1 / 4 := by linarith
    have hπ : (3 : ℝ) * 3.14 / 2 ≤ 3 * π / 2 := by linarith [Real.pi_gt_d2]
    calc (n : ℝ) * |Complex.arg (xiRootW ρ)| ≤ 68 * (g / (ρ.im ^ 2 - 1 / 4)) := by
          gcongr
      _ ≤ 3 * 3.14 / 2 := by
          rw [mul_div_assoc', div_le_iff₀ hden, ← hg2]
          nlinarith
      _ ≤ 3 * π / 2 := hπ

/-- **Li's criterion holds unconditionally for its first sixty-eight coefficients.** -/
theorem re_xiLiPaired_nonneg_of_le_68 {n : ℕ} (hn : n ≤ 68) : 0 ≤ (xiLiPaired n).re := by
  rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm n)]
  refine tsum_nonneg fun ρ => ?_
  rw [xiLiPairedTerm, Complex.re_ofReal_mul]
  have hstrip := xi_divisor_support_re_mem_open_unit ρ
  exact mul_nonneg (by have := xi_divisor_pos_on_support ρ; exact_mod_cast this.le)
    (re_liTerm_xiRootW_nonneg_of_le_68 (xi_eq_zero_of_mem_divisor_support ρ)
      hstrip.1 hstrip.2 hn)

end RHTower
