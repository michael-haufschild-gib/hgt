import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxDensity
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeCombination
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLineIsAShiftOfTheField

/-!
# Off the line, `log|ζ|` is the prime field up to a bounded error

Let `P_x(s) = Σ_n Λ(n) W_x(n) n^{−s}/log n` be the integrated Selberg polynomial (`logPoly`). At
`R = κ/log T`, `x = T^{1/30000}` and `κ ≥ 9600`, outside a set of `t ∈ [T, 2T]` of measure
`≪ T e^{−κ/60000} + T^{1/2}`,

`|log|ζ(½ + R + it)| − Re P_x(½ + R + it)| ≤ C₀`, with `C₀` absolute
(`exists_volume_log_norm_zeta_sub_logPoly_gt_le`).

**Mechanism.** Selberg's explicit formula holds on `½ ≤ Re s ≤ 3/2`
(`exists_selberg_explicit_formula_wide`), so integrating it horizontally from `Re s = 3/2`, where
both sides are bounded, leaves the integrated zero sum. Off the exclusion windows
`|γ − t| ≤ 12 R x^{3(β−½)}` each kernel `K_x(ρ − s)` is dominated along the whole segment by a
Lorentzian in `t` times an exponential in `σ` (`sum_norm_kernel_le`), and the integrated majorant
`G` has mean `≪ e^{−κ/60000}` over `[T, 2T]`. The zero sum is therefore typically smaller than `1`,
not merely smaller than a power of `log log T`.
-/

noncomputable section

open Complex Set MeasureTheory Filter ArithmeticFunction
open RHTower

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### The integrated polynomial -/

/-- The coefficient `Λ(n) W_x(n)/log n`. -/
def logPolyCoeff (x : ℝ) (n : ℕ) : ℝ := vonMangoldt n / Real.log n * selbergWeight x n

/-- The integrated Selberg polynomial `P_x(s) = Σ_n Λ(n) W_x(n) n^{−s}/log n`. -/
def logPoly (x : ℝ) (s : ℂ) : ℂ :=
  edPoly (fun n => ((logPolyCoeff x n : ℝ) : ℂ)) (Finset.Icc 1 (selbergPolyLength x)) s

theorem logPolyCoeff_mul_log (x : ℝ) (n : ℕ) :
    logPolyCoeff x n * Real.log n = vonMangoldt n * selbergWeight x n := by
  unfold logPolyCoeff
  by_cases h : Real.log n = 0
  · have hL : (vonMangoldt n : ℝ) = 0 := by
      have h1 := vonMangoldt_le_log (n := n)
      have h0 := vonMangoldt_nonneg (n := n)
      rw [h] at h1
      linarith
    rw [h, hL]
    simp
  · field_simp

theorem abs_logPolyCoeff_le {x : ℝ} (hx : 1 < x) (n : ℕ) : |logPolyCoeff x n| ≤ 1 := by
  unfold logPolyCoeff
  have hW0 := selbergWeight_nonneg hx n
  have hW1 := selbergWeight_le_one hx n
  have h0 : (0 : ℝ) ≤ vonMangoldt n := vonMangoldt_nonneg
  have hl : (vonMangoldt n : ℝ) ≤ Real.log n := vonMangoldt_le_log
  have hlog0 : 0 ≤ Real.log n := h0.trans hl
  have hdiv : vonMangoldt n / Real.log n ≤ 1 := div_le_one_of_le₀ hl hlog0
  rw [abs_of_nonneg (mul_nonneg (div_nonneg h0 hlog0) hW0)]
  exact mul_le_one₀ hdiv hW0 hW1

/-- The complex derivative of `P_x` is `−D_x`. -/
theorem hasDerivAt_logPoly {x : ℝ} (hx : 1 < x) (s : ℂ) :
    HasDerivAt (logPoly x) (-selbergVonMangoldtPoly x s) s := by
  rw [selbergVonMangoldtPoly_eq_edPoly hx]
  unfold logPoly edPoly
  have hterm : ∀ n ∈ Finset.Icc 1 (selbergPolyLength x),
      HasDerivAt (fun z : ℂ => ((logPolyCoeff x n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-z))
        (-(selbergPolyCoeff x n * ((n : ℝ) : ℂ) ^ (-s))) s := by
    intro n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hne : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hneg : HasDerivAt (fun z : ℂ => -z) (-1) s := (hasDerivAt_id' s).fun_neg
    have h := (hneg.const_cpow (c := ((n : ℝ) : ℂ)) (Or.inl hne)).const_mul
      ((logPolyCoeff x n : ℝ) : ℂ)
    refine h.congr_deriv ?_
    have hlog : Complex.log ((n : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) :=
      (Complex.ofReal_log hpos.le).symm
    have hc : ((logPolyCoeff x n : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ) = selbergPolyCoeff x n := by
      unfold selbergPolyCoeff
      rw [← Complex.ofReal_mul, logPolyCoeff_mul_log]
    rw [hlog, ← hc]
    ring
  have hs := HasDerivAt.fun_sum hterm
  rw [Finset.sum_neg_distrib] at hs
  exact hs

theorem hasDerivAt_re_logPoly_horizontal {x : ℝ} (hx : 1 < x) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => (logPoly x ((v : ℂ) + (t : ℂ) * I)).re)
      (-(selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)).re) u := by
  have hc := (hasDerivAt_logPoly hx ((u : ℂ) + (t : ℂ) * I)).comp_of_eq u
    (hasDerivAt_horizontal t u) rfl
  rw [mul_one] at hc
  have hc' : HasDerivAt (fun v : ℝ => logPoly x ((v : ℂ) + (t : ℂ) * I))
      (-selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)) u := hc
  have hre : HasDerivAt (fun v : ℝ => (logPoly x ((v : ℂ) + (t : ℂ) * I)).re)
      (-selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)).re u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hc'
  rwa [Complex.neg_re] at hre

/-- The constant `Σ_n n^{−3/2}`. -/
def threeHalvesSum : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ)

theorem summable_threeHalves : Summable fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ) :=
  Real.summable_nat_rpow.mpr (by norm_num)

theorem threeHalvesSum_nonneg : 0 ≤ threeHalvesSum :=
  tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- At `Re s = 3/2` the integrated polynomial is bounded. -/
theorem abs_re_logPoly_three_halves_le {x : ℝ} (hx : 1 < x) (t : ℝ) :
    |(logPoly x (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ threeHalvesSum := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold logPoly edPoly
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun n hn => ?_)
    (summable_threeHalves.sum_le_tsum (Finset.Icc 1 (selbergPolyLength x))
      fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-(((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re = -(3 / 2) := by simp
  rw [hre]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hpos.le _) (abs_logPolyCoeff_le hx n)

/-- At `Re s = 3/2` the logarithm of `|ζ|` is bounded, by the three-four-one inequality. -/
theorem abs_log_norm_zeta_three_halves_le (t : ℝ) :
    |Real.log ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ 8 := by
  have hre : ∀ τ : ℝ, (1 : ℝ) < (((3 / 2 : ℝ) : ℂ) + (τ : ℂ) * I).re := fun τ => by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, sub_self]
    norm_num
  have hval : (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = 3 / 2 := by simp
  have hup : Real.log ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Real.log 3 := by
    have h := Sieve.log_norm_riemannZeta_le (hre t)
    have h3 : (1 : ℝ) + 1 / (3 / 2 - 1) = 3 := by norm_num
    rwa [hval, h3] at h
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hB : ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (2 * t : ℂ) * I)‖ ≤ 3 := by
    have h := Sieve.norm_riemannZeta_le (s := ((3 / 2 : ℝ) : ℂ) + (2 * t : ℂ) * I) (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_mul, sub_self,
        Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
      norm_num)
    have hv : (((3 / 2 : ℝ) : ℂ) + (2 * t : ℂ) * I).re = 3 / 2 := by simp
    have h3 : (1 : ℝ) + 1 / (3 / 2 - 1) = 3 := by norm_num
    rwa [hv, h3] at h
  have hinv := Sieve.norm_inv_riemannZeta_le (σ := 3 / 2) (t := t) (by norm_num) hB
  have hne : riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (hre t).le
  have hpos : 0 < ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := norm_pos_iff.mpr hne
  have hlow : -Real.log ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 8 := by
    rw [norm_inv] at hinv
    have h2 := Real.log_le_log (inv_pos.mpr hpos) hinv
    rw [Real.log_inv, Real.log_exp] at h2
    have h3 : Real.log (1 + 1 / (3 / 2 - 1)) = Real.log 3 := by norm_num
    rw [h3] at h2
    linarith
  rw [abs_le]
  constructor <;> linarith

/-! ### The explicit formula up to `Re s = 3/2` -/

/-- Doubling the third term at most doubles a sum of nonnegative terms. -/
theorem div_add_le_two_mul {a b c d a' b' c' d' e e' p : ℝ} (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ 2 * c') (hd : d ≤ d') (ha0 : 0 ≤ a') (hb0 : 0 ≤ b') (hd0 : 0 ≤ d')
    (he : e ≤ e') (he0 : 0 ≤ e') (hp : 0 < p) :
    (a + b + c + d) / p + e ≤ 2 * ((a' + b' + c' + d') / p + e') := by
  have h1 : (a + b + c + d) / p ≤ 2 * ((a' + b' + c' + d') / p) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  linarith

/-- The first edge term of the wide explicit formula. -/
theorem selberg_wide_term_one {K t x σ σL BH : ℝ} (hK : 0 ≤ K) (ht : 64 ≤ t) (hx : 1 < x)
    (hσ₀ : 1 / 2 ≤ σ) (hσL0 : 0 < σL) (hσL2 : σL ≤ 2) (hBH0 : 0 ≤ BH)
    (hBH : BH ≤ K * (1 + Real.log t) ^ (2 : ℕ)) :
    2 * ((Real.exp (2 * (2 - σ) * Real.log x) + Real.exp ((2 - σ) * Real.log x)) /
        (Real.log x * (t / 4) ^ 2) * BH * (2 - σL)) ≤
      2 * (2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2)) *
        (K * (1 + Real.log t) ^ (2 : ℕ)) * 2 := by
  have hl : 0 < Real.log x := Real.log_pos hx
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.exp (2 * (2 - σ) * Real.log x) +
    Real.exp ((2 - σ) * Real.log x) := ⟨_, rfl⟩
  rw [← hA]
  have hA2 : A ≤ 2 * Real.exp (4 * Real.log x) := by
    have h1 : Real.exp (2 * (2 - σ) * Real.log x) ≤ Real.exp (4 * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp ((2 - σ) * Real.log x) ≤ Real.exp (4 * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [hA]
    linarith
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have h1 : A / (Real.log x * (t / 4) ^ 2) ≤
      2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2) :=
    div_le_div_of_nonneg_right hA2 (by positivity)
  have h2 : 2 - σL ≤ 2 := by linarith
  have h4 : 0 ≤ K * (1 + Real.log t) ^ (2 : ℕ) := by positivity
  have h3 : A / (Real.log x * (t / 4) ^ 2) * BH * (2 - σL) ≤
      2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 4) ^ 2) *
        (K * (1 + Real.log t) ^ (2 : ℕ)) * 2 := by
    apply mul_le_mul (mul_le_mul h1 hBH hBH0 (by positivity)) h2 (by linarith)
    positivity
  linarith

/-- The second and third edge terms of the wide explicit formula. -/
theorem selberg_wide_term_two {t x σ T₁ : ℝ} (ht : 64 ≤ t) (hx : 1 < x)
    (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 3 / 2) (hT₁ : t / 2 - 1 ≤ T₁) :
    8 / (2 - 1) ^ 2 * ((Real.exp (2 * (2 - σ) * Real.log x) + Real.exp ((2 - σ) * Real.log x)) /
        Real.log x) * (2 * Real.pi / (t / 4)) ≤
      8 * (2 * Real.exp (4 * Real.log x) / Real.log x) * (2 * Real.pi / (t / 4)) ∧
    (Real.exp (2 * (2 - σ) * Real.log x) + Real.exp ((2 - σ) * Real.log x)) /
        (Real.log x * T₁) * (Real.pi / (2 - σ)) ≤
      2 * (2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) * Real.pi) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.exp (2 * (2 - σ) * Real.log x) +
    Real.exp ((2 - σ) * Real.log x) := ⟨_, rfl⟩
  rw [← hA]
  have hA2 : A ≤ 2 * Real.exp (4 * Real.log x) := by
    have h1 : Real.exp (2 * (2 - σ) * Real.log x) ≤ Real.exp (4 * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp ((2 - σ) * Real.log x) ≤ Real.exp (4 * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [hA]
    linarith
  have hE0 : 0 ≤ 2 * Real.exp (4 * Real.log x) := by positivity
  have hT₁pos : 0 < t / 2 - 1 := by linarith
  refine ⟨?_, ?_⟩
  · norm_num
    gcongr
  · have h1 : A / (Real.log x * T₁) ≤
        2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) :=
      div_le_div₀ hE0 hA2 (by positivity) (mul_le_mul_of_nonneg_left hT₁ hl.le)
    have h2 : Real.pi / (2 - σ) ≤ 2 * Real.pi := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.pi_pos]
    calc A / (Real.log x * T₁) * (Real.pi / (2 - σ))
        ≤ 2 * Real.exp (4 * Real.log x) / (Real.log x * (t / 2 - 1)) * (2 * Real.pi) :=
          mul_le_mul h1 h2 (div_nonneg Real.pi_pos.le (by linarith)) (by positivity)
      _ = _ := by ring

/-- The left edge term of the wide explicit formula. -/
theorem selberg_wide_term_four {t x σ σL : ℝ} (hx : 1 < x) (hσ₀ : 1 / 2 ≤ σ) (hσL8 : σL ≤ 1 / 8)
    (hBL0 : 0 ≤ selbergLeftEdgeConstant (2 * t)) :
    selbergLeftEdgeConstant (2 * t) *
        (2 * Real.exp ((σL - σ) * Real.log x) / Real.log x) * (Real.pi / (σ - σL)) ≤
      selbergLeftEdgeConstant (2 * t) * (2 * Real.exp (-(3 / 8) * Real.log x) / Real.log x) *
        (Real.pi / (3 / 8)) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have h1 : Real.exp ((σL - σ) * Real.log x) ≤ Real.exp (-(3 / 8) * Real.log x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.pi / (σ - σL) ≤ Real.pi / (3 / 8) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  apply mul_le_mul (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (by linarith) hl.le) hBL0) h2
    (by have := Real.pi_pos; exact div_nonneg this.le (by linarith)) (by positivity)

/-- The edge terms of the explicit formula are at most twice the remainder at `Re s ≤ 1`. -/
theorem selberg_wide_terms_le {K t x σ σL BH T₁ : ℝ} (hK : 0 ≤ K) (ht : 64 ≤ t) (hx : 1 < x)
    (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 3 / 2) (hσL0 : 0 < σL) (hσL8 : σL ≤ 1 / 8) (hBH0 : 0 ≤ BH)
    (hBH : BH ≤ K * (1 + Real.log t) ^ (2 : ℕ)) (hT₁ : t / 2 - 1 ≤ T₁)
    (hBL0 : 0 ≤ selbergLeftEdgeConstant (2 * t)) :
    (2 * ((Real.exp (2 * (2 - σ) * Real.log x) + Real.exp ((2 - σ) * Real.log x)) /
          (Real.log x * (t / 4) ^ 2) * BH * (2 - σL)) +
        8 / (2 - 1) ^ 2 *
          ((Real.exp (2 * (2 - σ) * Real.log x) + Real.exp ((2 - σ) * Real.log x)) /
            Real.log x) * (2 * Real.pi / (t / 4)) +
        (Real.exp (2 * (2 - σ) * Real.log x) + Real.exp ((2 - σ) * Real.log x)) /
          (Real.log x * T₁) * (Real.pi / (2 - σ)) +
        selbergLeftEdgeConstant (2 * t) * (2 * Real.exp ((σL - σ) * Real.log x) / Real.log x) *
          (Real.pi / (σ - σL))) / (2 * Real.pi) + 1 / T₁ ≤
      2 * selbergHeightError K x t := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hT₁pos : 0 < t / 2 - 1 := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  obtain ⟨t2, t3⟩ := selberg_wide_term_two ht hx hσ₀ hσ₁ hT₁
  have h4 : 0 ≤ K * (1 + Real.log t) ^ (2 : ℕ) := by positivity
  unfold selbergHeightError
  refine div_add_le_two_mul (selberg_wide_term_one hK ht hx hσ₀ hσL0 (by linarith) hBH0 hBH) t2 t3
    (selberg_wide_term_four hx hσ₀ hσL8 hBL0) (by positivity) (by positivity)
    (by positivity) (one_div_le_one_div_of_le hT₁pos hT₁) (by positivity) (by positivity)

/-- **Selberg's explicit formula on `½ ≤ Re s ≤ 3/2`.** -/
theorem exists_selberg_explicit_formula_wide :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 64 ≤ t → ∃ T₁ T₂ : ℝ,
      t / 2 - 1 < T₁ ∧ T₁ < t / 2 + 1 ∧ 3 * t / 2 - 1 < T₂ ∧ T₂ < 3 * t / 2 + 1 ∧
      ∀ x : ℝ, 1 < x → ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 3 / 2 →
        riemannZeta s₀ ≠ 0 →
        ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
          ∑ w ∈ selbergHeightZeros t T₁ T₂,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤
          2 * selbergHeightError K x t := by
  obtain ⟨K, hK, hhor⟩ := exists_horizontal_height_polylog
  refine ⟨K, hK, fun t ht => ?_⟩
  set X : ℕ := ⌊t⌋₊ with hXdef
  have hXle : (X : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hXgt : t - 1 < X := by have := Nat.lt_floor_add_one t; linarith
  have hX12 : 12 ≤ X := by
    have : (12 : ℝ) < X + 1 := by linarith
    exact_mod_cast (show (11 : ℝ) < X by linarith)
  obtain ⟨T₁, hT₁, hb₁⟩ := hhor (X := X) (τ := t / 2) hX12
    (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨T₂, hT₂, hb₂⟩ := hhor (X := X) (τ := 3 * t / 2) hX12
    (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith)
  refine ⟨T₁, T₂, by linarith [hT₁.1], by linarith [hT₁.2], by linarith [hT₂.1],
    by linarith [hT₂.2], fun x hx s₀ hs₀t hσ₀ hσ₁ hs₀ => ?_⟩
  set σL : ℝ := reflectedLeftAbscissa (2 * t) with hσL
  have h2t : 16 ≤ 2 * t := by linarith
  have hσL0 : 0 < σL := reflectedLeftAbscissa_pos h2t
  have hl2 := log_ge_of_sixteen_le h2t
  have hσL8 : σL ≤ 1 / 8 := by
    refine (reflectedLeftAbscissa_le h2t).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 9 ≤ Real.log (2 * t) ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hl2 9
    nlinarith
  have hlogX : Real.log X ≤ Real.log t :=
    Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) hXle
  set BH : ℝ := K * (1 + Real.log X) ^ (2 : ℕ) with hBH
  have hBH' : BH ≤ K * (1 + Real.log t) ^ (2 : ℕ) := by
    have h0 : 0 ≤ 1 + Real.log (X : ℝ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ X by exact_mod_cast (show 1 ≤ X by omega))
      linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (by linarith) 2) hK
  have hs₀im : 7 * t / 8 ≤ s₀.im ∧ s₀.im ≤ 9 * t / 8 := by
    constructor <;> linarith [(abs_le.mp hs₀t).1, (abs_le.mp hs₀t).2]
  have hmain := norm_logDeriv_zeta_add_selberg_le (x := x) (c := 2) (σL := σL) (T₁ := T₁)
    (T₂ := T₂) (H := t / 4) (BH := BH) (BL := selbergLeftEdgeConstant (2 * t)) (s₀ := s₀)
    hx (by norm_num) le_rfl (by linarith) (by linarith) (by linarith [hT₁.1])
    (by linarith) (by linarith [hT₁.2, hs₀im.1]) (by linarith [hT₂.1, hs₀im.2]) hs₀
    (fun u hu => hb₁ u ⟨by linarith [hu.1], hu.2⟩)
    (fun u hu => hb₂ u ⟨by linarith [hu.1], hu.2⟩)
    (fun y hy => by
      have h := zetaResidueUnit_reflectedLeft_ne_zero_and_norm_logDeriv_le (T := 2 * t) (y := y)
        h2t (by rw [abs_of_pos (by linarith [hy.1, hT₁.1])]; linarith [hy.1, hT₁.1])
        (by rw [abs_of_pos (by linarith [hy.1, hT₁.1])]; linarith [hy.2, hT₂.2])
      exact ⟨h.1, h.2⟩)
  refine hmain.trans ?_
  have hBH0 : 0 ≤ BH := by rw [hBH]; positivity
  have hBL0 : 0 ≤ selbergLeftEdgeConstant (2 * t) := by
    unfold selbergLeftEdgeConstant
    have := zetaLowerA_pos
    positivity
  exact selberg_wide_terms_le hK ht hx hσ₀ hσ₁ hσL0 hσL8 hBH0 hBH' (by linarith [hT₁.1]) hBL0

/-! ### One zero along the segment -/

/-- A zero left of the threshold: decay in the abscissa, Lorentzian in the height. -/
theorem norm_selbergKernel_left_le {x R u t : ℝ} {w : ℂ} (hx : 1 < x) (hR : 0 < R)
    (hu : 1 / 2 + R ≤ u) (hw : w.re ≤ 1 / 2 + R / 2) :
    ‖selbergKernel x (w - ((u : ℂ) + (t : ℂ) * I))‖ ≤
      2 / Real.log x * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) *
        ((R / 2) ^ 2 + (w.im - t) ^ 2)⁻¹ := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hre : (w - ((u : ℂ) + (t : ℂ) * I)).re = w.re - u := by simp
  have him : (w - ((u : ℂ) + (t : ℂ) * I)).im = w.im - t := by simp
  have hK := norm_selbergKernel_le_line hx (w - ((u : ℂ) + (t : ℂ) * I))
  rw [hre, him] at hK
  have hr1 : w.re - u ≤ -((u - 1 / 2) / 2) := by linarith
  have hr2 : w.re - u ≤ -(R / 2) := by linarith
  have hexp : Real.exp (2 * (w.re - u) * Real.log x) + Real.exp ((w.re - u) * Real.log x) ≤
      2 * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) := by
    have h1 : Real.exp (2 * (w.re - u) * Real.log x) ≤
        Real.exp (-(Real.log x / 2 * (u - 1 / 2))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp ((w.re - u) * Real.log x) ≤
        Real.exp (-(Real.log x / 2 * (u - 1 / 2))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hden : (R / 2) ^ 2 + (w.im - t) ^ 2 ≤ (w.re - u) ^ 2 + (w.im - t) ^ 2 := by
    have : (R / 2) ^ 2 ≤ (w.re - u) ^ 2 := by nlinarith
    linarith
  have hpos : 0 < (R / 2) ^ 2 + (w.im - t) ^ 2 := by positivity
  refine hK.trans ?_
  calc (Real.exp (2 * (w.re - u) * Real.log x) + Real.exp ((w.re - u) * Real.log x)) /
        (Real.log x * ((w.re - u) ^ 2 + (w.im - t) ^ 2))
      ≤ 2 * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) /
        (Real.log x * ((R / 2) ^ 2 + (w.im - t) ^ 2)) :=
        div_le_div₀ (by positivity) hexp (by positivity)
          (mul_le_mul_of_nonneg_left hden hl.le)
    _ = _ := by
        field_simp

/-- A zero right of the threshold, outside its window. -/
theorem norm_selbergKernel_right_le {x W u t : ℝ} {w : ℂ} (hx : 1 < x) (hu : 1 / 2 ≤ u)
    (hw : 1 / 2 ≤ w.re) (hW0 : 0 < W) (hW : W < |w.im - t|) :
    ‖selbergKernel x (w - ((u : ℂ) + (t : ℂ) * I))‖ ≤
      Real.exp (-(Real.log x * (u - 1 / 2))) / 4 *
        (16 * Real.exp (2 * (w.re - 1 / 2) * Real.log x) / Real.log x *
          (W ^ 2 + (w.im - t) ^ 2)⁻¹) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hre : (w - ((u : ℂ) + (t : ℂ) * I)).re = w.re - u := by simp
  have him : (w - ((u : ℂ) + (t : ℂ) * I)).im = w.im - t := by simp
  have hK := norm_selbergKernel_le_line hx (w - ((u : ℂ) + (t : ℂ) * I))
  rw [hre, him] at hK
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = w.re - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u - 1 / 2 := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  have hr : w.re - u = b - v := by rw [hb, hv]; ring
  have hexp : Real.exp (2 * (w.re - u) * Real.log x) + Real.exp ((w.re - u) * Real.log x) ≤
      2 * Real.exp ((2 * b - v) * Real.log x) := by
    rw [hr]
    have h1 : Real.exp (2 * (b - v) * Real.log x) ≤ Real.exp ((2 * b - v) * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp ((b - v) * Real.log x) ≤ Real.exp ((2 * b - v) * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hy2 : W ^ 2 ≤ (w.im - t) ^ 2 := by
    rw [← sq_abs (w.im - t)]
    exact pow_le_pow_left₀ hW0.le hW.le 2
  have hden : (W ^ 2 + (w.im - t) ^ 2) / 2 ≤ (w.re - u) ^ 2 + (w.im - t) ^ 2 := by
    nlinarith [sq_nonneg (w.re - u)]
  have hpos : 0 < W ^ 2 + (w.im - t) ^ 2 := by positivity
  refine hK.trans ?_
  have hsplit : Real.exp ((2 * b - v) * Real.log x) =
      Real.exp (-(Real.log x * v)) * Real.exp (2 * b * Real.log x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hv, ← hb]
  calc (Real.exp (2 * (w.re - u) * Real.log x) + Real.exp ((w.re - u) * Real.log x)) /
        (Real.log x * ((w.re - u) ^ 2 + (w.im - t) ^ 2))
      ≤ 2 * Real.exp ((2 * b - v) * Real.log x) /
        (Real.log x * ((W ^ 2 + (w.im - t) ^ 2) / 2)) :=
        div_le_div₀ (by positivity) hexp (by positivity)
          (mul_le_mul_of_nonneg_left hden hl.le)
    _ = _ := by
        rw [hsplit]
        field_simp
        ring

/-- **The zero sum at one point of the segment.** -/
theorem sum_norm_kernel_le {x R u t : ℝ} (hx : 1 < x) (hR : 0 < R) (hu : 1 / 2 + R ≤ u)
    {Z Z' : Finset ℂ} (hZ : Z ⊆ Z')
    (hgood : ∀ w ∈ Z', 1 / 2 + R / 2 < w.re → selbergRightWindow x R w < |w.im - t|) :
    ∑ w ∈ Z, zeroMult w * ‖selbergKernel x (w - ((u : ℂ) + (t : ℂ) * I))‖ ≤
      2 / Real.log x * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) *
          selbergLorentzSum Z' (R / 2) t +
        Real.exp (-(Real.log x * (u - 1 / 2))) / 4 * selbergRightFar Z' x R t := by
  classical
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun w => w.re ≤ 1 / 2 + R / 2)]
  refine add_le_add ?_ ?_
  · have hc : 0 ≤ 2 / Real.log x * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) := by positivity
    calc ∑ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2),
          zeroMult w * ‖selbergKernel x (w - ((u : ℂ) + (t : ℂ) * I))‖
        ≤ ∑ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2),
            2 / Real.log x * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) *
              (zeroMult w * ((R / 2) ^ 2 + (w.im - t) ^ 2)⁻¹) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have h := norm_selbergKernel_left_le (t := t) hx hR hu (Finset.mem_filter.mp hw).2
          have h2 := mul_le_mul_of_nonneg_left h (zeroMult_nonneg w)
          refine h2.trans (le_of_eq ?_)
          ring
      _ = 2 / Real.log x * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) *
            ∑ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2),
              zeroMult w * ((R / 2) ^ 2 + (w.im - t) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          unfold selbergLorentzSum
          exact Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hZ)
            fun w _ _ => mul_nonneg (zeroMult_nonneg w) (by positivity)
  · have hc : 0 ≤ Real.exp (-(Real.log x * (u - 1 / 2))) / 4 := by positivity
    have hsub : Z.filter (fun w => ¬ w.re ≤ 1 / 2 + R / 2) ⊆
        Z'.filter (fun w => 1 / 2 + R / 2 < w.re) := by
      intro w hw
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hZ h1, not_le.mp h2⟩
    calc ∑ w ∈ Z.filter (fun w => ¬ w.re ≤ 1 / 2 + R / 2),
          zeroMult w * ‖selbergKernel x (w - ((u : ℂ) + (t : ℂ) * I))‖
        ≤ ∑ w ∈ Z.filter (fun w => ¬ w.re ≤ 1 / 2 + R / 2),
            Real.exp (-(Real.log x * (u - 1 / 2))) / 4 * (zeroMult w *
              (16 * Real.exp (2 * (w.re - 1 / 2) * Real.log x) / Real.log x) *
                (selbergRightWindow x R w ^ 2 + (w.im - t) ^ 2)⁻¹) := by
          refine Finset.sum_le_sum fun w hw => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hw
          have hwr := not_le.mp h2
          have h := norm_selbergKernel_right_le (u := u) (t := t) hx (by linarith)
            (show 1 / 2 ≤ w.re by linarith) (selbergRightWindow_pos hR w)
            (hgood w (hZ h1) hwr)
          have h3 := mul_le_mul_of_nonneg_left h (zeroMult_nonneg w)
          refine h3.trans (le_of_eq ?_)
          ring
      _ = Real.exp (-(Real.log x * (u - 1 / 2))) / 4 *
            ∑ w ∈ Z.filter (fun w => ¬ w.re ≤ 1 / 2 + R / 2), (zeroMult w *
              (16 * Real.exp (2 * (w.re - 1 / 2) * Real.log x) / Real.log x) *
                (selbergRightWindow x R w ^ 2 + (w.im - t) ^ 2)⁻¹) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          unfold selbergRightFar
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => ?_
          have := zeroMult_nonneg w
          have := selbergRightWindow_pos (x := x) hR w
          positivity

/-- The exponential integral over a segment. -/
theorem integral_exp_shift_le {c a b : ℝ} (hc : 0 < c) :
    ∫ u in a..b, Real.exp (-(c * (u - 1 / 2))) ≤ Real.exp (-(c * (a - 1 / 2))) / c := by
  have hd : ∀ u ∈ uIcc a b, HasDerivAt (fun u : ℝ => -Real.exp (-(c * (u - 1 / 2))) / c)
      (Real.exp (-(c * (u - 1 / 2)))) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -(c * (u - 1 / 2))) (-(c * 1)) u :=
      (((hasDerivAt_id' u).sub_const (1 / 2)).const_mul c).neg
    have h2 := (h1.exp.neg).div_const c
    refine h2.congr_deriv ?_
    field_simp
  have hc2 : Continuous fun u : ℝ => Real.exp (-(c * (u - 1 / 2))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.intervalIntegrable _ _)]
  have : 0 < Real.exp (-(c * (b - 1 / 2))) / c := by positivity
  have e : -Real.exp (-(c * (b - 1 / 2))) / c - -Real.exp (-(c * (a - 1 / 2))) / c =
      Real.exp (-(c * (a - 1 / 2))) / c - Real.exp (-(c * (b - 1 / 2))) / c := by ring
  rw [e]
  linarith

/-! ### The integrated zero sum at one height -/

/-- The majorant of the zero sum integrated along the segment from `½ + R + it` to `3/2 + it`. -/
def offLineMajorant (Z : Finset ℂ) (x R t : ℝ) : ℝ :=
  4 * Real.exp (-(Real.log x / 2 * R)) / Real.log x ^ 2 * selbergLorentzSum Z (R / 2) t +
    Real.exp (-(Real.log x * R)) / (4 * Real.log x) * selbergRightFar Z x R t

theorem offLineMajorant_nonneg (Z : Finset ℂ) {x R : ℝ} (hx : 1 < x) (hR : 0 < R) (t : ℝ) :
    0 ≤ offLineMajorant Z x R t := by
  have hl := Real.log_pos hx
  have h1 := selbergLorentzSum_nonneg Z (R / 2) t
  have h2 := selbergRightFar_nonneg Z hx hR t
  unfold offLineMajorant
  positivity

theorem continuous_offLineMajorant (Z : Finset ℂ) {x R : ℝ} (hR : 0 < R) :
    Continuous (offLineMajorant Z x R) := by
  unfold offLineMajorant
  exact (continuous_const.mul (continuous_selbergLorentzSum Z (by positivity))).add
    (continuous_const.mul (continuous_selbergRightFar Z hR))

/-- **Integrating the explicit formula from `Re s = 3/2`.** At a height off the exclusion windows,
`log|ζ(½ + R + it)|` equals `Re P_x(½ + R + it)` up to a constant and the majorant. -/
theorem abs_log_norm_zeta_sub_logPoly_le {T t x R T₁ T₂ : ℝ} (hT : 64 ≤ T)
    (ht : t ∈ Icc T (2 * T)) (hx : 1 < x) (hR : 0 < R) (hR1 : R ≤ 1 / 16)
    (hT₁ : t / 2 - 1 < T₁) (hT₂ : T₂ < 3 * t / 2 + 1) (hT12 : T₁ ≤ T₂)
    (hEF : ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 3 / 2 →
      riemannZeta s₀ ≠ 0 →
      ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
        ∑ w ∈ selbergHeightZeros t T₁ T₂,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤ 2)
    (hgood : ∀ w ∈ selbergMidZeros T, 1 / 2 + R / 2 < w.re →
      selbergRightWindow x R w < |w.im - t|) :
    |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
        (logPoly x (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤
      8 + threeHalvesSum + 2 + offLineMajorant (selbergMidZeros T) x R t := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hT16 : 16 ≤ T := by linarith
  have ht64 : 64 ≤ t := hT.trans ht.1
  have ht0 : t ≠ 0 := by linarith
  have hle : 1 / 2 + R ≤ 3 / 2 := by linarith
  -- the segment is zero-free
  have hz : ∀ u : ℝ, 1 / 2 + R ≤ u → riemannZeta ((u : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro u hu h
    have hre : ((u : ℂ) + (t : ℂ) * I).re = u := by simp
    have him : ((u : ℂ) + (t : ℂ) * I).im = t := by simp
    have hmem := mem_selbergMidZeros_of_zero hT16 ht h (by rw [hre]; linarith)
      (by rw [him, sub_self, abs_zero]; norm_num)
    have h1 := hgood _ hmem (by rw [hre]; linarith)
    rw [him, sub_self, abs_zero] at h1
    exact absurd h1 (not_lt.mpr (selbergRightWindow_pos hR _).le)
  obtain ⟨Lo, hLo⟩ : ∃ Lo : ℝ, Lo = selbergLorentzSum (selbergMidZeros T) (R / 2) t := ⟨_, rfl⟩
  obtain ⟨Fa, hFa⟩ : ∃ Fa : ℝ, Fa = selbergRightFar (selbergMidZeros T) x R t := ⟨_, rfl⟩
  have hLo0 : 0 ≤ Lo := hLo ▸ selbergLorentzSum_nonneg _ _ _
  have hFa0 : 0 ≤ Fa := hFa ▸ selbergRightFar_nonneg _ hx hR _
  have hderiv : ∀ u ∈ uIcc (1 / 2 + R) (3 / 2 : ℝ), HasDerivAt
      (fun v : ℝ => Real.log ‖riemannZeta ((v : ℂ) + (t : ℂ) * I)‖ -
        (logPoly x ((v : ℂ) + (t : ℂ) * I)).re)
      ((logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re +
        (selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)).re) u := by
    intro u hu
    rw [uIcc_of_le hle] at hu
    have h1 := hasDerivAt_log_norm_zeta_horizontal ht0 (hz u hu.1)
    have h2 := hasDerivAt_re_logPoly_horizontal hx t u
    have h3 := h1.fun_sub h2
    rwa [sub_neg_eq_add] at h3
  have hcontD : Continuous fun u : ℝ => (selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)).re :=
    Complex.continuous_re.comp
      ((differentiable_selbergVonMangoldtPoly hx).continuous.comp (continuous_horizontal t))
  have hcont : ContinuousOn (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re +
      (selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)).re) (uIcc (1 / 2 + R) (3 / 2 : ℝ)) := by
    refine (continuousOn_re_logDeriv_zeta_horizontal ht0 fun u hu => ?_).add hcontD.continuousOn
    rw [uIcc_of_le hle] at hu
    exact hz u hu.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  -- the integrand is dominated by the explicit formula
  have hpt : ∀ u ∈ Ioc (1 / 2 + R) (3 / 2 : ℝ),
      ‖(logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re +
        (selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)).re‖ ≤
      2 + (2 / Real.log x * Lo) * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) +
        (Fa / 4) * Real.exp (-(Real.log x * (u - 1 / 2))) := by
    intro u hu
    obtain ⟨A, hAdef⟩ : ∃ A : ℂ, A = logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I) +
      selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I) := ⟨_, rfl⟩
    obtain ⟨Zs, hZs⟩ : ∃ Zs : ℂ, Zs = ∑ w ∈ selbergHeightZeros t T₁ T₂,
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
        selbergKernel x (w - ((u : ℂ) + (t : ℂ) * I)) := ⟨_, rfl⟩
    have h1 : ‖A + Zs‖ ≤ 2 := by
      rw [hAdef, hZs]
      refine hEF _ ?_ ?_ ?_ (hz u hu.1.le)
      · have him : ((u : ℂ) + (t : ℂ) * I).im = t := by simp
        rw [him, sub_self, abs_zero]
        positivity
      · have hre : ((u : ℂ) + (t : ℂ) * I).re = u := by simp
        rw [hre]
        linarith [hu.1]
      · have hre : ((u : ℂ) + (t : ℂ) * I).re = u := by simp
        rw [hre]
        exact hu.2
    have h2 : ‖Zs‖ ≤ ∑ w ∈ selbergHeightZeros t T₁ T₂,
        zeroMult w * ‖selbergKernel x (w - ((u : ℂ) + (t : ℂ) * I))‖ := by
      rw [hZs]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      rw [norm_mul, Complex.norm_natCast]
      exact le_rfl
    have h3 := sum_norm_kernel_le (t := t) hx hR hu.1.le
      (selbergHeightZeros_subset_mid hT16 ht hT₁ hT₂ hT12) hgood
    rw [← hLo, ← hFa] at h3
    have hre : (logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re +
        (selbergVonMangoldtPoly x ((u : ℂ) + (t : ℂ) * I)).re = A.re := by
      rw [hAdef, Complex.add_re]
    rw [hre, Real.norm_eq_abs]
    have h4 : ‖A‖ ≤ ‖A + Zs‖ + ‖Zs‖ := by
      have := norm_sub_le (A + Zs) Zs
      rwa [add_sub_cancel_right] at this
    have h5 := Complex.abs_re_le_norm A
    have e : 2 / Real.log x * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) * Lo +
        Real.exp (-(Real.log x * (u - 1 / 2))) / 4 * Fa =
        (2 / Real.log x * Lo) * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) +
        (Fa / 4) * Real.exp (-(Real.log x * (u - 1 / 2))) := by ring
    rw [e] at h3
    linarith
  have he1 : Continuous fun u : ℝ => Real.exp (-(Real.log x / 2 * (u - 1 / 2))) := by fun_prop
  have he2 : Continuous fun u : ℝ => Real.exp (-(Real.log x * (u - 1 / 2))) := by fun_prop
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hle
    (g := fun u => 2 + (2 / Real.log x * Lo) * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) +
        (Fa / 4) * Real.exp (-(Real.log x * (u - 1 / 2))))
    (Eventually.of_forall fun u hu => hpt u hu)
    (((continuous_const.add (continuous_const.mul he1)).add
      (continuous_const.mul he2)).intervalIntegrable _ _)
  -- the integral of the majorant
  have hI : ∫ u in (1 / 2 + R)..(3 / 2 : ℝ),
      (2 + (2 / Real.log x * Lo) * Real.exp (-(Real.log x / 2 * (u - 1 / 2))) +
        (Fa / 4) * Real.exp (-(Real.log x * (u - 1 / 2)))) ≤
      2 + offLineMajorant (selbergMidZeros T) x R t := by
    have hi1 : IntervalIntegrable (fun u : ℝ => 2 + (2 / Real.log x * Lo) *
        Real.exp (-(Real.log x / 2 * (u - 1 / 2)))) volume (1 / 2 + R) (3 / 2) :=
      (continuous_const.add (continuous_const.mul he1)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => (Fa / 4) *
        Real.exp (-(Real.log x * (u - 1 / 2)))) volume (1 / 2 + R) (3 / 2) :=
      (continuous_const.mul he2).intervalIntegrable _ _
    have hi3 : IntervalIntegrable (fun u : ℝ => (2 / Real.log x * Lo) *
        Real.exp (-(Real.log x / 2 * (u - 1 / 2)))) volume (1 / 2 + R) (3 / 2) :=
      (continuous_const.mul he1).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_add intervalIntegrable_const hi3,
      intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have h1 := integral_exp_shift_le (c := Real.log x / 2) (a := 1 / 2 + R) (b := 3 / 2)
      (by positivity)
    have h2 := integral_exp_shift_le (c := Real.log x) (a := 1 / 2 + R) (b := 3 / 2) hl
    have e1 : (1 / 2 + R - 1 / 2 : ℝ) = R := by ring
    rw [e1] at h1 h2
    have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / Real.log x * Lo by positivity)
    have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ Fa / 4 by positivity)
    have e2 : 2 / Real.log x * Lo * (Real.exp (-(Real.log x / 2 * R)) / (Real.log x / 2)) =
        4 * Real.exp (-(Real.log x / 2 * R)) / Real.log x ^ 2 * Lo := by
      field_simp
      ring
    have e3 : Fa / 4 * (Real.exp (-(Real.log x * R)) / Real.log x) =
        Real.exp (-(Real.log x * R)) / (4 * Real.log x) * Fa := by
      field_simp
    rw [e2] at h3
    rw [e3] at h4
    unfold offLineMajorant
    rw [← hLo, ← hFa]
    have h5 : (3 / 2 - (1 / 2 + R)) * 2 ≤ 2 := by nlinarith
    linarith
  rw [hftc, Real.norm_eq_abs] at hnorm
  have hbase : |Real.log ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ -
      (logPoly x (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ 8 + threeHalvesSum := by
    refine (abs_sub _ _).trans (add_le_add (abs_log_norm_zeta_three_halves_le t)
      (abs_re_logPoly_three_halves_le hx t))
  have htri := abs_sub_abs_le_abs_sub
    (Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
      (logPoly x (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re)
    (Real.log ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ -
      (logPoly x (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re)
  rw [abs_sub_comm (Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
      (logPoly x (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re)
    (Real.log ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ -
      (logPoly x (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re)] at htri
  linarith

/-! ### The measure of the exceptional heights -/

/-- The exclusion windows have total measure `≪ T e^{−κ/60000} + T^{1/2}` at `κ = R L ≥ 9600`. -/
theorem windows_sum_le {T L R x A Kw S : ℝ} (hT0 : 0 < T) (hL : L = Real.log T) (hA : 0 < A)
    (hRL : 9600 ≤ R * L) (hlx : Real.log x = L / 30000)
    (hE5 : 144 * Kw / Real.pi * (L + 3) ^ 2 ≤ Real.exp ((1 / 2 - 1 / 10000) * L))
    (hS : S ≤ 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) +
      144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi) :
    S ≤ 336 * A / Real.pi * T * Real.exp (-(R * L / 60000)) + T ^ ((1 : ℝ) / 2) := by
  have hπ := Real.pi_pos
  have hexp1 : Real.exp (-(R * L / 9600)) ≤ Real.exp (-(R * L / 60000)) := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ R * L := by linarith
    linarith
  have hfrac : 1 + 9600 / (R * L) ≤ 2 := by
    have : 9600 / (R * L) ≤ 1 := (div_le_one (by linarith)).mpr hRL
    linarith
  have hE3 : Real.exp (3 * Real.log x) = Real.exp (L / 10000) := by
    rw [hlx]
    congr 1
    ring
  have hsqrt : T ^ ((1 : ℝ) / 2) = Real.exp (L / 2) := by
    rw [Real.rpow_def_of_pos hT0, ← hL]
    congr 1
    ring
  have hw2 : 144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi ≤ T ^ ((1 : ℝ) / 2) := by
    rw [hE3, hsqrt]
    have e : Real.exp (L / 2) = Real.exp ((1 / 2 - 1 / 10000) * L) * Real.exp (L / 10000) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    calc 144 * (L + 3) ^ 2 * Kw * Real.exp (L / 10000) / Real.pi
        = 144 * Kw / Real.pi * (L + 3) ^ 2 * Real.exp (L / 10000) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hE5 (Real.exp_pos _).le
  have hw1 : 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) ≤
      336 * A / Real.pi * T * Real.exp (-(R * L / 60000)) := by
    have hc : 0 ≤ 168 * T * A / Real.pi := by positivity
    calc 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600))
        ≤ 168 * T * A / Real.pi * 2 * Real.exp (-(R * L / 60000)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hfrac hc) hexp1 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  exact hS.trans (add_le_add hw1 hw2)

/-- Arithmetic of the two integrals of the majorant. -/
theorem majorant_terms_le {L R E S T C₁ : ℝ} (hL0 : 0 < L) (hR : 0 < R) (hE : 0 < E)
    (hT0 : 0 < T) (hC₁ : 0 < C₁) (hRL : 1 ≤ R * L) (hSle : S ≤ 10 * C₁ * T * L) :
    4 * E / (L / 30000) ^ 2 * (Real.pi / (R / 2) * S) +
        E / (4 * (L / 30000)) * (4 * Real.pi / (3 * R * (L / 30000)) * S) ≤
      81 * 10 ^ 9 * Real.pi * C₁ * T * E := by
  have hπ := Real.pi_pos
  have e1 : 4 * E / (L / 30000) ^ 2 * (Real.pi / (R / 2) * S) +
      E / (4 * (L / 30000)) * (4 * Real.pi / (3 * R * (L / 30000)) * S) =
      (8 + 1 / 3) * (9 * 10 ^ 8) * (Real.pi * E * S) / (L * (L * R)) := by
    field_simp
    ring
  rw [e1, div_le_iff₀ (by positivity)]
  have hc : 0 ≤ (8 + 1 / 3) * (9 * 10 ^ 8) * (Real.pi * E) := by positivity
  have h4 := mul_le_mul_of_nonneg_left hSle hc
  have hpos : 0 ≤ 81 * 10 ^ 9 * Real.pi * C₁ * T * E * L := by positivity
  have h5 : 81 * 10 ^ 9 * Real.pi * C₁ * T * E * L * 1 ≤
      81 * 10 ^ 9 * Real.pi * C₁ * T * E * L * (L * R) := by
    refine mul_le_mul_of_nonneg_left ?_ hpos
    linarith [mul_comm L R]
  calc (8 + 1 / 3) * (9 * 10 ^ 8) * (Real.pi * E * S)
      = (8 + 1 / 3) * (9 * 10 ^ 8) * (Real.pi * E) * S := by ring
    _ ≤ (8 + 1 / 3) * (9 * 10 ^ 8) * (Real.pi * E) * (10 * C₁ * T * L) := h4
    _ ≤ 81 * 10 ^ 9 * Real.pi * C₁ * T * E * L * 1 := by
        have h6 : 0 ≤ Real.pi * E * C₁ * T * L := by positivity
        nlinarith
    _ ≤ _ := h5
    _ = _ := by ring

/-- **The majorant integrates to `≪ T e^{−κ/60000}`.** -/
theorem integral_offLineMajorant_le {Mid : Finset ℂ} {T L R x C₁ : ℝ} (hT : 0 < T) (hx : 1 < x)
    (hR : 0 < R) (hL0 : 0 < L) (hC₁ : 0 < C₁) (hRL : 1 ≤ R * L) (hlx : Real.log x = L / 30000)
    (hSle : ∑ w ∈ Mid, zeroMult w ≤ 10 * C₁ * T * L) :
    ∫ t in T..(2 * T), offLineMajorant Mid x R t ≤
      81 * 10 ^ 9 * Real.pi * C₁ * T * Real.exp (-(R * L / 60000)) := by
  have hl0 : 0 < Real.log x := Real.log_pos hx
  have hπ := Real.pi_pos
  have hTle : T ≤ 2 * T := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (-(R * L / 60000)) := ⟨_, rfl⟩
  rw [← hEdef]
  have hEpos : 0 < E := hEdef ▸ Real.exp_pos _
  have he₁ : Real.exp (-(Real.log x / 2 * R)) = E := by
    rw [hEdef, hlx]
    congr 1
    ring
  have he₂ : Real.exp (-(Real.log x * R)) ≤ E := by
    rw [hEdef, hlx]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ R * L := by linarith
    linarith
  have hS0 : 0 ≤ ∑ w ∈ Mid, zeroMult w := Finset.sum_nonneg fun w _ => zeroMult_nonneg w
  have hIL := integral_selbergLorentzSum_le Mid (show 0 < R / 2 by positivity) hTle
  have hIF := integral_selbergRightFar_le Mid hx hR hTle
  have hIF2 : ∫ t in T..(2 * T), selbergRightFar Mid x R t ≤
      4 * Real.pi / (3 * R * Real.log x) * ∑ w ∈ Mid, zeroMult w := by
    refine hIF.trans ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun w hw => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun w _ _ => ?_)
    · have hb : 0 ≤ w.re - 1 / 2 := by
        have := (Finset.mem_filter.mp hw).2
        linarith
      have hexp : Real.exp (-((w.re - 1 / 2) * Real.log x)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      have hc : 0 ≤ zeroMult w * (4 * Real.pi / (3 * R * Real.log x)) :=
        mul_nonneg (zeroMult_nonneg w) (by positivity)
      calc zeroMult w * (4 * Real.pi / (3 * R * Real.log x)) *
            Real.exp (-((w.re - 1 / 2) * Real.log x))
          ≤ zeroMult w * (4 * Real.pi / (3 * R * Real.log x)) * 1 :=
            mul_le_mul_of_nonneg_left hexp hc
        _ = 4 * Real.pi / (3 * R * Real.log x) * zeroMult w := by ring
    · exact mul_nonneg (by positivity) (zeroMult_nonneg w)
  unfold offLineMajorant
  have hi1 : IntervalIntegrable (fun t : ℝ => 4 * Real.exp (-(Real.log x / 2 * R)) / Real.log x ^ 2 *
      selbergLorentzSum Mid (R / 2) t) volume T (2 * T) :=
    (continuous_const.mul (continuous_selbergLorentzSum Mid (by positivity))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => Real.exp (-(Real.log x * R)) / (4 * Real.log x) *
      selbergRightFar Mid x R t) volume T (2 * T) :=
    (continuous_const.mul (continuous_selbergRightFar Mid hR)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, he₁]
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ w ∈ Mid, zeroMult w := ⟨_, rfl⟩
  rw [← hSdef] at hS0 hSle hIF2 hIL
  have h1 := mul_le_mul_of_nonneg_left hIL (show 0 ≤ 4 * E / Real.log x ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hIF2
    (show 0 ≤ Real.exp (-(Real.log x * R)) / (4 * Real.log x) by positivity)
  have h3 : Real.exp (-(Real.log x * R)) / (4 * Real.log x) *
      (4 * Real.pi / (3 * R * Real.log x) * S) ≤
      E / (4 * Real.log x) * (4 * Real.pi / (3 * R * Real.log x) * S) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact div_le_div_of_nonneg_right he₂ (by positivity)
  have h4 := majorant_terms_le hL0 hR hEpos hT hC₁ hRL hSle
  rw [← hlx] at h4
  linarith

/-- The multiplicity of the fixed rectangle is `≤ 10 C T log T` at large heights. -/
theorem sum_mult_le_of_log {T L C₁ : ℝ} (hT64 : 64 ≤ T) (hL : L = Real.log T) (hC₁ : 0 < C₁)
    (hmid : ∑ w ∈ selbergMidZeros T, zeroMult w ≤ C₁ * (4 * T + 4) * Real.log (4 * T + 5)) :
    ∑ w ∈ selbergMidZeros T, zeroMult w ≤ 10 * C₁ * T * L := by
  refine hmid.trans ?_
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith)
  have h1 : Real.log (4 * T + 5) ≤ 2 * L := by
    have h : Real.log (4 * T + 5) ≤ Real.log (T ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow, ← hL] at h
    push_cast at h
    exact h
  have h2 : 0 ≤ Real.log (4 * T + 5) := Real.log_nonneg (by linarith)
  have h3 : 4 * T + 4 ≤ 5 * T := by linarith
  calc C₁ * (4 * T + 4) * Real.log (4 * T + 5)
      ≤ C₁ * (5 * T) * (2 * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h3 hC₁.le) h1 h2 (by positivity)
    _ = _ := by ring

/-- The remainder of the wide formula is at most `2` at `x = T^{1/30000}` for heights in `[T, 2T]`. -/
theorem selbergHeightError_le_of_block {KE T L t t₀ x : ℝ} (hT64 : 64 ≤ T) (hL : L = Real.log T)
    (hTt₀ : t₀ ≤ T) (ht : t ∈ Icc T (2 * T)) (hxdef : x = Real.exp (L / 30000))
    (ht₀ : ∀ b ≥ t₀, ∀ x : ℝ, Real.log b ^ (40 : ℕ) ≤ x → x ≤ b ^ ((1 : ℝ) / 8) →
      selbergHeightError KE x b ≤ 1)
    (hE2 : 1 * (L + 3) ^ 40 ≤ Real.exp (1 / 30000 * L)) :
    selbergHeightError KE x t ≤ 1 := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have hL0 : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith)
  have hlogt : Real.log t ≤ L + 3 := by
    have h1 : Real.log t ≤ Real.log (2 * T) := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num) hT0.ne', ← hL] at h1
    have := Real.log_two_lt_d9
    linarith
  have hlogT : L ≤ Real.log t := by
    rw [hL]
    exact Real.log_le_log hT0 ht.1
  have hlogt0 : 0 ≤ Real.log t := by linarith
  refine ht₀ t (hTt₀.trans ht.1) x ?_ ?_
  · have h1 : Real.log t ^ (40 : ℕ) ≤ (L + 3) ^ (40 : ℕ) := pow_le_pow_left₀ hlogt0 hlogt 40
    rw [one_mul, show (1 : ℝ) / 30000 * L = L / 30000 by ring, ← hxdef] at hE2
    exact h1.trans hE2
  · rw [Real.rpow_def_of_pos ht0, hxdef]
    refine Real.exp_le_exp.mpr ?_
    nlinarith

/-- **Off the line, `log|ζ|` is the prime field.** At `R log T ≥ 9600`, `R ≤ 1/16` and
`x = T^{1/30000}`, the heights `t ∈ [T, 2T]` with `|log|ζ(½ + R + it)| − Re P_x(½ + R + it)| > C₀`
have measure `≤ C T e^{−R log T/60000} + C T^{1/2}`, with `C₀` and `C` absolute. -/
theorem exists_volume_log_norm_zeta_sub_logPoly_gt_le :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 →
      9600 ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧
        C₀ < |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
          (logPoly (Real.exp (Real.log T / 30000)) (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re|} ≤
        ENNReal.ofReal (C * T * Real.exp (-(R * Real.log T / 60000)) + C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨KE, hKE, hEFall⟩ := exists_selberg_explicit_formula_wide
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (eventually_selbergHeightError_le_one hKE)
  obtain ⟨A, Kw, hA, hKw, hwin⟩ := exists_sum_selbergRightWindow_le
  obtain ⟨C₁, hC₁, hmid⟩ := exists_sum_mult_selbergMidZeros_le
  have hπ := Real.pi_pos
  have hZ0 := threeHalvesSum_nonneg
  refine ⟨8 + threeHalvesSum + 3, 336 * A / Real.pi + 81 * 10 ^ 9 * Real.pi * C₁ + 1,
    by positivity, by positivity, ?_⟩
  have hE2 := eventually_mul_log_add_pow_le_exp 40 1 (show (0 : ℝ) < 1 / 30000 by norm_num)
  have hE5 := eventually_mul_log_add_pow_le_exp 2 (144 * Kw / Real.pi)
    (show (0 : ℝ) < 1 / 2 - 1 / 10000 by norm_num)
  filter_upwards [hwin, eventually_ge_atTop (max t₀ 64), hE2, hE5]
    with T hTwin hTt hE2 hE5 R hR hR16 hκ
  have hT64 : 64 ≤ T := le_of_max_le_right hTt
  have hTt₀ : t₀ ≤ T := le_of_max_le_left hTt
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log T := ⟨_, rfl⟩
  rw [← hL] at hκ hE2 hE5 ⊢
  have hL0 : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith)
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Real.exp (L / 30000) := ⟨_, rfl⟩
  have hlx : Real.log x = L / 30000 := by rw [hxdef, Real.log_exp]
  have hx : 1 < x := by
    rw [hxdef]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  rw [← hxdef]
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (-(R * L / 60000)) := ⟨_, rfl⟩
  rw [← hEdef]
  have hEpos : 0 < E := hEdef ▸ Real.exp_pos _
  -- the exceptional sets
  have hsub : {t | t ∈ Icc T (2 * T) ∧
      8 + threeHalvesSum + 3 < |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
        (logPoly x (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re|} ⊆
      {t | t ∈ Icc T (2 * T) ∧ ∃ w ∈ selbergMidZeros T, 1 / 2 + R / 2 < w.re ∧
        |w.im - t| ≤ selbergRightWindow x R w} ∪
      {t | t ∈ Icc T (2 * T) ∧ 1 ≤ offLineMajorant (selbergMidZeros T) x R t} := by
    rintro t ⟨ht, hlt⟩
    by_cases hw : ∃ w ∈ selbergMidZeros T, 1 / 2 + R / 2 < w.re ∧
        |w.im - t| ≤ selbergRightWindow x R w
    · exact Or.inl ⟨ht, hw⟩
    · refine Or.inr ⟨ht, ?_⟩
      by_contra hG
      have hgood : ∀ w ∈ selbergMidZeros T, 1 / 2 + R / 2 < w.re →
          selbergRightWindow x R w < |w.im - t| := by
        intro w hwM hwr
        by_contra hle
        exact hw ⟨w, hwM, hwr, not_lt.mp hle⟩
      obtain ⟨T₁, T₂, a1, a2, a3, a4, hb⟩ := hEFall t (hT64.trans ht.1)
      have hsmall := selbergHeightError_le_of_block hT64 hL hTt₀ ht hxdef ht₀ hE2
      have hEF2 : ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 3 / 2 →
          riemannZeta s₀ ≠ 0 →
          ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
            ∑ w ∈ selbergHeightZeros t T₁ T₂,
              ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤ 2 :=
        fun s₀ h1 h2 h3 h4 => (hb x hx s₀ h1 h2 h3 h4).trans (by linarith)
      have hmain := abs_log_norm_zeta_sub_logPoly_le hT64 ht hx hR hR16 a1 a4
        (by linarith [ht.1]) hEF2 hgood
      linarith [not_le.mp hG]
  -- the windows
  have hS := hTwin x R hx hR (by linarith) (by rw [← hL]; linarith) (by
    have h6 : 6 * Real.log x / Real.log T = 1 / 5000 := by
      rw [hlx, ← hL]
      field_simp
      norm_num
    rw [h6]
    norm_num)
  rw [← hL] at hS
  have hS2 := windows_sum_le hT0 hL hA hκ hlx hE5 hS
  rw [← hEdef] at hS2
  have hV1 := (volume_selbergRightExceptional_le (T := T) (selbergMidZeros T) (x := x) hR).trans
    (ENNReal.ofReal_le_ofReal hS2)
  -- the majorant
  have hGint := integral_offLineMajorant_le (Mid := selbergMidZeros T) hT0 hx hR hL0 hC₁
    (by linarith) hlx (sum_mult_le_of_log hT64 hL hC₁ (hmid T (by linarith)))
  rw [← hEdef] at hGint
  have hV2 := volume_Icc_setOf_le_le_of_integral (show T ≤ 2 * T by linarith) one_pos
    (fun t => offLineMajorant_nonneg (selbergMidZeros T) hx hR t)
    (continuous_offLineMajorant _ hR) hGint
  rw [div_one] at hV2
  -- assemble
  have hsqrt0 : 0 ≤ T ^ ((1 : ℝ) / 2) := by positivity
  have hTE : 0 ≤ T * E := by positivity
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add hV1 hV2
    _ = ENNReal.ofReal (336 * A / Real.pi * T * E + T ^ ((1 : ℝ) / 2) +
          81 * 10 ^ 9 * Real.pi * C₁ * T * E) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (1 : ℝ) ≤ 336 * A / Real.pi + 81 * 10 ^ 9 * Real.pi * C₁ + 1 := by
          have : 0 ≤ 336 * A / Real.pi + 81 * 10 ^ 9 * Real.pi * C₁ := by positivity
          linarith
        have h2 := mul_le_mul_of_nonneg_right h1 hsqrt0
        rw [one_mul] at h2
        nlinarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
