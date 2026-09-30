import GaloisForLFunctions.RHTower.PerronVonMangoldtSwap
import GaloisForLFunctions.RHTower.AnalyticDividedDifference

/-!
# Selberg's kernel and the smoothed von Mangoldt polynomial

For `x > 1`, `ℓ = log x`, Selberg's kernel is `K_x(w) = (x^{2w} − x^w)/(ℓ w²)`. It equals
`φ_x(w)/w` with `φ_x = dslope F_x 0`, `F_x(w) = (x^{2w} − x^w)/ℓ`, an entire function with
`φ_x(0) = 1` (`analyticAt_selbergKernelPhi`, `selbergKernelPhi_zero`). The Perron integral of
`K_x` against `n^{−w}` on a line `Re w = a > 0` is the weight
`W_x(n) = (log⁺(x²/n) − log⁺(x/n))/ℓ ∈ [0, 1]`, equal to `1` for `n ≤ x` and `0` for `n ≥ x²`.

Consequently, for every `s₀` and `a > 0` with `Re s₀ + a > 1`,

`∫ (−ζ'/ζ)(s₀ + a + 2πiw) K_x(a + 2πiw) dw = Σ_n Λ(n) W_x(n) n^{−s₀}`
(`integral_neg_logDeriv_zeta_mul_selbergKernel`), the right-edge value of the contour identity
for `ζ'/ζ(s₀)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter ArithmeticFunction

namespace RHTower

/-- Selberg's kernel numerator `F_x(w) = (x^{2w} − x^w)/log x`. -/
def selbergKernelNum (x : ℝ) (w : ℂ) : ℂ :=
  (Complex.exp (2 * w * (Real.log x : ℂ)) - Complex.exp (w * (Real.log x : ℂ))) /
    (Real.log x : ℂ)

/-- The entire factor `φ_x = F_x/w`, `φ_x(0) = 1`. -/
def selbergKernelPhi (x : ℝ) : ℂ → ℂ := dslope (selbergKernelNum x) 0

/-- Selberg's kernel `K_x(w) = (x^{2w} − x^w)/(log x · w²)`. -/
def selbergKernel (x : ℝ) (w : ℂ) : ℂ := selbergKernelNum x w / w ^ 2

/-- Selberg's weight `W_x(n) = (log⁺(x²/n) − log⁺(x/n))/log x`. -/
def selbergWeight (x : ℝ) (n : ℕ) : ℝ :=
  (max (Real.log (x ^ 2 / n)) 0 - max (Real.log (x / n)) 0) / Real.log x

theorem differentiable_selbergKernelNum (x : ℝ) : Differentiable ℂ (selbergKernelNum x) := by
  unfold selbergKernelNum
  fun_prop

theorem analyticAt_selbergKernelPhi (x : ℝ) (z : ℂ) : AnalyticAt ℂ (selbergKernelPhi x) z :=
  analyticAt_dslope_of_analyticAt ((differentiable_selbergKernelNum x).analyticAt 0)
    ((differentiable_selbergKernelNum x).analyticAt z)

theorem analyticOnNhd_selbergKernelPhi (x : ℝ) :
    AnalyticOnNhd ℂ (selbergKernelPhi x) Set.univ :=
  fun z _ => analyticAt_selbergKernelPhi x z

theorem selbergKernelNum_zero (x : ℝ) : selbergKernelNum x 0 = 0 := by
  simp [selbergKernelNum]

theorem selbergKernelPhi_zero {x : ℝ} (hx : 1 < x) : selbergKernelPhi x 0 = 1 := by
  set ℓ : ℂ := (Real.log x : ℂ) with hℓ
  have hl : ℓ ≠ 0 := by rw [hℓ]; exact_mod_cast (Real.log_pos hx).ne'
  unfold selbergKernelPhi
  rw [dslope_same]
  have h1 : HasDerivAt (fun y : ℂ => Complex.exp (2 * y * ℓ)) (2 * ℓ) 0 := by
    have h := (Complex.hasDerivAt_exp (2 * 0 * ℓ)).comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_mul (2 : ℂ) |>.mul_const ℓ)
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun y : ℂ => Complex.exp (y * ℓ)) ℓ 0 := by
    have h := (Complex.hasDerivAt_exp (0 * ℓ)).comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).mul_const ℓ)
    simpa [Function.comp_def] using h
  have hd : HasDerivAt (selbergKernelNum x) ((2 * ℓ - ℓ) / ℓ) 0 := (h1.sub h2).div_const ℓ
  rw [hd.deriv]
  field_simp
  ring

theorem selbergKernelPhi_mul_inv {x : ℝ} {w : ℂ} (hw : w ≠ 0) :
    selbergKernelPhi x w * w⁻¹ = selbergKernel x w := by
  unfold selbergKernelPhi selbergKernel
  rw [dslope_of_ne _ hw, slope_def_field, selbergKernelNum_zero, sub_zero, sub_zero]
  field_simp

/-- `‖F_x(w)‖ ≤ (e^{2ℓ Re w} + e^{ℓ Re w})/ℓ`. -/
theorem norm_selbergKernelNum_le {x : ℝ} (hx : 1 < x) (w : ℂ) :
    ‖selbergKernelNum x w‖ ≤
      (Real.exp (2 * w.re * Real.log x) + Real.exp (w.re * Real.log x)) / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  unfold selbergKernelNum
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  refine div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (le_of_eq ?_)) hl.le
  rw [Complex.norm_exp, Complex.norm_exp]
  congr 2 <;> simp [Complex.mul_re]

/-- `‖K_x(w)‖ ≤ (e^{2ℓ Re w} + e^{ℓ Re w})/(ℓ ‖w‖²)`. -/
theorem norm_selbergKernel_le {x : ℝ} (hx : 1 < x) (w : ℂ) :
    ‖selbergKernel x w‖ ≤
      (Real.exp (2 * w.re * Real.log x) + Real.exp (w.re * Real.log x)) /
        (Real.log x * ‖w‖ ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rcases eq_or_ne w 0 with rfl | hw
  · simp [selbergKernel]
  unfold selbergKernel
  rw [norm_div, norm_pow]
  have hw2 : 0 < ‖w‖ ^ 2 := by positivity
  calc ‖selbergKernelNum x w‖ / ‖w‖ ^ 2
      ≤ ((Real.exp (2 * w.re * Real.log x) + Real.exp (w.re * Real.log x)) / Real.log x) /
          ‖w‖ ^ 2 := div_le_div_of_nonneg_right (norm_selbergKernelNum_le hx w) hw2.le
    _ = _ := by rw [div_div]

theorem selbergWeight_nonneg {x : ℝ} (hx : 1 < x) (n : ℕ) : 0 ≤ selbergWeight x n := by
  have hl : 0 < Real.log x := Real.log_pos hx
  unfold selbergWeight
  refine div_nonneg ?_ hl.le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hmono : Real.log (x / n) ≤ Real.log (x ^ 2 / n) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ hn0.le
    nlinarith
  have : max (Real.log (x / n)) 0 ≤ max (Real.log (x ^ 2 / n)) 0 := max_le_max hmono le_rfl
  linarith

theorem selbergWeight_le_one {x : ℝ} (hx : 1 < x) (n : ℕ) : selbergWeight x n ≤ 1 := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  unfold selbergWeight
  rw [div_le_one hl]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hl.le]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : Real.log (x ^ 2 / n) = Real.log x + Real.log (x / n) := by
    rw [show x ^ 2 / n = x * (x / n) by ring, Real.log_mul hx0.ne' (by positivity)]
  rw [hsplit]
  rcases le_total 0 (Real.log (x / n)) with h | h
  · rw [max_eq_left (by linarith), max_eq_left h]; linarith
  · rw [max_eq_right h]
    rcases le_total 0 (Real.log x + Real.log (x / n)) with h' | h'
    · rw [max_eq_left h']; linarith
    · rw [max_eq_right h']; linarith

theorem selbergWeight_eq_zero {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : x ^ 2 ≤ n) :
    selbergWeight x n = 0 := by
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  unfold selbergWeight
  have h1 : Real.log (x ^ 2 / n) ≤ 0 :=
    Real.log_nonpos (by positivity) (by rw [div_le_one hn0]; exact hn)
  have h2 : Real.log (x / n) ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    rw [div_le_one hn0]
    nlinarith
  rw [max_eq_right h1, max_eq_right h2]
  simp

/-! ## The Perron evaluation -/

/-- The Perron term `Λ(n) n^{−(s₀+w)} K_x(w)`, `w = a + 2πiθ`. -/
def selbergPerronTerm (x : ℝ) (s₀ : ℂ) (a : ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ))
      (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) n *
    selbergKernel x ((a : ℂ) + 2 * Real.pi * θ * Complex.I)

theorem perronLine_ne_zero {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    ((a : ℂ) + 2 * Real.pi * θ * Complex.I) ≠ 0 := by
  intro h
  have h2 := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im] at h2
  linarith

/-- The Perron term as a difference of two weighted Perron kernels. -/
theorem selbergPerronTerm_eq {x : ℝ} (hx : 1 < x) (s₀ : ℂ) {a : ℝ} (ha : 0 < a) {n : ℕ}
    (hn : 0 < n) (θ : ℝ) :
    selbergPerronTerm x s₀ a n θ =
      ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀) / (Real.log x : ℂ) *
        (Complex.exp (((a : ℂ) + 2 * Real.pi * θ * Complex.I) * ((Real.log (x ^ 2 / n) : ℝ) : ℂ))
            / ((a : ℂ) + 2 * Real.pi * θ * Complex.I) ^ 2 -
          Complex.exp (((a : ℂ) + 2 * Real.pi * θ * Complex.I) * ((Real.log (x / n) : ℝ) : ℂ))
            / ((a : ℂ) + 2 * Real.pi * θ * Complex.I) ^ 2) := by
  set w : ℂ := (a : ℂ) + 2 * Real.pi * θ * Complex.I with hwdef
  have hw : w ≠ 0 := perronLine_ne_zero ha θ
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hx).ne'
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
  have hcpow : ∀ z : ℂ, (n : ℂ) ^ z = Complex.exp (z * ((Real.log n : ℝ) : ℂ)) := by
    intro z
    rw [Complex.cpow_def_of_ne_zero hnc, hlogn, mul_comm]
  have hL2 : ((Real.log (x ^ 2 / n) : ℝ) : ℂ) =
      2 * (Real.log x : ℂ) - ((Real.log n : ℝ) : ℂ) := by
    rw [Real.log_div (by positivity) hn0.ne', Real.log_pow]
    push_cast; ring
  have hL1 : ((Real.log (x / n) : ℝ) : ℂ) = (Real.log x : ℂ) - ((Real.log n : ℝ) : ℂ) := by
    rw [Real.log_div hx0.ne' hn0.ne']
    push_cast; ring
  unfold selbergPerronTerm selbergKernel selbergKernelNum
  rw [LSeries.term_def, if_neg hn.ne', hL2, hL1, ← hwdef]
  rw [show (n : ℂ) ^ (s₀ + w) = (n : ℂ) ^ s₀ * (n : ℂ) ^ w by
    rw [Complex.cpow_add _ _ hnc]]
  rw [Complex.cpow_neg, hcpow w, hcpow s₀]
  have e1 : Complex.exp (w * (2 * (Real.log x : ℂ) - ((Real.log n : ℝ) : ℂ))) =
      Complex.exp (2 * w * (Real.log x : ℂ)) / Complex.exp (w * ((Real.log n : ℝ) : ℂ)) := by
    rw [← Complex.exp_sub]; ring_nf
  have e2 : Complex.exp (w * ((Real.log x : ℂ) - ((Real.log n : ℝ) : ℂ))) =
      Complex.exp (w * (Real.log x : ℂ)) / Complex.exp (w * ((Real.log n : ℝ) : ℂ)) := by
    rw [← Complex.exp_sub]; ring_nf
  rw [e1, e2]
  have hE1 : Complex.exp (w * ((Real.log n : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hE2 : Complex.exp (s₀ * ((Real.log n : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- **The Perron term integrates to the Selberg weight.** -/
theorem integral_selbergPerronTerm {x : ℝ} (hx : 1 < x) (s₀ : ℂ) {a : ℝ} (ha : 0 < a)
    (n : ℕ) :
    ∫ θ : ℝ, selbergPerronTerm x s₀ a n θ =
      ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀) * (selbergWeight x n : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [selbergPerronTerm, LSeries.term_def]
  simp_rw [selbergPerronTerm_eq hx s₀ ha hn]
  rw [integral_const_mul, integral_sub (integrable_perron_integrand ha _)
    (integrable_perron_integrand ha _)]
  have k1 := perron_weighted_kernel ha (Real.log (x ^ 2 / n))
  have k2 := perron_weighted_kernel ha (Real.log (x / n))
  simp only [pow_two] at k1 k2 ⊢
  rw [k1, k2]
  unfold selbergWeight
  have hl : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hx).ne'
  push_cast
  field_simp

/-- The norm of the Perron term. -/
theorem norm_selbergPerronTerm_le {x : ℝ} (hx : 1 < x) (s₀ : ℂ) {a : ℝ} (ha : 0 < a) (n : ℕ)
    (θ : ℝ) :
    ‖selbergPerronTerm x s₀ a n θ‖ ≤
      vonMangoldt n / (n : ℝ) ^ (s₀.re + a) *
        ((Real.exp (2 * a * Real.log x) + Real.exp (a * Real.log x)) / Real.log x) *
          (a ^ 2 + (2 * Real.pi * θ) ^ 2)⁻¹ := by
  set w : ℂ := (a : ℂ) + 2 * Real.pi * θ * Complex.I with hwdef
  have hwre : w.re = a := by simp [hwdef]
  have hwn : ‖w‖ ^ 2 = a ^ 2 + (2 * Real.pi * θ) ^ 2 := by
    rw [hwdef, show (a : ℂ) + 2 * Real.pi * θ * Complex.I =
      ((a : ℝ) : ℂ) + ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have hl : 0 < Real.log x := Real.log_pos hx
  unfold selbergPerronTerm
  rw [← hwdef, norm_mul]
  have hK := norm_selbergKernel_le hx w
  rw [hwre, hwn] at hK
  have hT : ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (s₀ + w) n‖ ≤
      vonMangoldt n / (n : ℝ) ^ (s₀.re + a) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_def]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.term_def, if_neg hn.ne', norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg,
      show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp [hwre]
  have hpos : 0 < a ^ 2 + (2 * Real.pi * θ) ^ 2 := by positivity
  calc ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (s₀ + w) n‖ *
        ‖selbergKernel x w‖
      ≤ (vonMangoldt n / (n : ℝ) ^ (s₀.re + a)) *
          ((Real.exp (2 * a * Real.log x) + Real.exp (a * Real.log x)) /
            (Real.log x * (a ^ 2 + (2 * Real.pi * θ) ^ 2))) :=
        mul_le_mul hT hK (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

/-- **The right-edge Perron identity.** For `a > 0` with `Re s₀ + a > 1`,
`∫ (−ζ'/ζ)(s₀ + a + 2πiθ) K_x(a + 2πiθ) dθ = Σ_n Λ(n) W_x(n) n^{−s₀}`. -/
theorem integral_neg_logDeriv_zeta_mul_selbergKernel {x : ℝ} (hx : 1 < x) (s₀ : ℂ) {a : ℝ}
    (ha : 0 < a) (hc : 1 < s₀.re + a) :
    ∫ θ : ℝ, -(deriv riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) /
        riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I))) *
        selbergKernel x ((a : ℂ) + 2 * Real.pi * θ * Complex.I) =
      ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀) * (selbergWeight x n : ℂ) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hint : ∀ n : ℕ, Integrable (selbergPerronTerm x s₀ a n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : selbergPerronTerm x s₀ a 0 = fun _ => 0 := by
        funext θ
        simp [selbergPerronTerm, LSeries.term_def]
      rw [h0]
      exact MeasureTheory.integrable_zero ℝ ℂ _
    have hexp := ((integrable_perron_integrand ha (Real.log (x ^ 2 / n))).sub
      (integrable_perron_integrand ha (Real.log (x / n)))).const_mul
      (((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀) / (Real.log x : ℂ))
    exact hexp.congr (Eventually.of_forall fun θ => (selbergPerronTerm_eq hx s₀ ha hn θ).symm)
  set B : ℝ := (Real.exp (2 * a * Real.log x) + Real.exp (a * Real.log x)) / Real.log x with hB
  have hB0 : 0 ≤ B := by positivity
  have hIa : Integrable (fun θ : ℝ => (a ^ 2 + (2 * Real.pi * θ) ^ 2)⁻¹) := by
    have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
    set C : ℝ := 1 / a ^ 2 + 1 / (4 * Real.pi ^ 2) with hC
    refine (integrable_inv_one_add_sq.const_mul C).mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun θ => ?_)
    have hA : 0 < a ^ 2 + (2 * Real.pi * θ) ^ 2 := by positivity
    have h1 : 0 < 1 + θ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA),
      show C * (1 + θ ^ 2)⁻¹ = C / (1 + θ ^ 2) by ring, le_div_iff₀ h1, inv_mul_le_iff₀ hA]
    have e1 : C * a ^ 2 = 1 + a ^ 2 / (4 * Real.pi ^ 2) := by rw [hC]; field_simp
    have e2 : C * (2 * Real.pi * θ) ^ 2 = (2 * Real.pi * θ) ^ 2 / a ^ 2 + θ ^ 2 := by
      rw [hC]; field_simp; ring
    have h3 : 0 ≤ a ^ 2 / (4 * Real.pi ^ 2) := by positivity
    have h4 : 0 ≤ (2 * Real.pi * θ) ^ 2 / a ^ 2 := by positivity
    nlinarith
  have hnormint : ∀ n : ℕ, (∫ θ : ℝ, ‖selbergPerronTerm x s₀ a n θ‖) ≤
      vonMangoldt n / (n : ℝ) ^ (s₀.re + a) * B *
        ∫ θ : ℝ, (a ^ 2 + (2 * Real.pi * θ) ^ 2)⁻¹ := by
    intro n
    rw [← integral_const_mul]
    refine integral_mono (hint n).norm (hIa.const_mul _) fun θ => ?_
    exact norm_selbergPerronTerm_le hx s₀ ha n θ
  have hsum : Summable (fun n : ℕ => ∫ θ : ℝ, ‖selbergPerronTerm x s₀ a n θ‖) := by
    have hLS := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (((s₀.re + a) : ℝ) : ℂ)) (by rwa [Complex.ofReal_re])
    have hns : Summable (fun n : ℕ =>
        ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (((s₀.re + a) : ℝ) : ℂ) n‖) :=
      summable_norm_iff.2 hLS
    have hterm_norm : ∀ n : ℕ,
        ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (((s₀.re + a) : ℝ) : ℂ) n‖ =
          vonMangoldt n / (n : ℝ) ^ (s₀.re + a) := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [LSeries.term_def]
      · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
        rw [LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.1 hn), norm_div,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
          show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
          Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.ofReal_re]
    have hreal : Summable (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ (s₀.re + a)) :=
      hns.congr hterm_norm
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun θ => norm_nonneg _)
      hnormint ?_
    exact (hreal.mul_right B).mul_right _
  have hpt : ∀ θ : ℝ, ∑' n : ℕ, selbergPerronTerm x s₀ a n θ =
      -(deriv riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) /
        riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I))) *
        selbergKernel x ((a : ℂ) + 2 * Real.pi * θ * Complex.I) := by
    intro θ
    have hre : (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)).re = s₀.re + a := by
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
    unfold selbergPerronTerm
    rw [tsum_mul_right]
    rw [show (∑' n : ℕ, LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ))
        (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) n) =
        LSeries (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ))
          (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) from rfl]
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by rw [hre]; exact hc)]
    ring
  calc ∫ θ : ℝ, -(deriv riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) /
          riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I))) *
          selbergKernel x ((a : ℂ) + 2 * Real.pi * θ * Complex.I)
      = ∫ θ : ℝ, ∑' n : ℕ, selbergPerronTerm x s₀ a n θ :=
        integral_congr_ae (Eventually.of_forall fun θ => (hpt θ).symm)
    _ = ∑' n : ℕ, ∫ θ : ℝ, selbergPerronTerm x s₀ a n θ :=
        (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = _ := tsum_congr fun n => integral_selbergPerronTerm hx s₀ ha n

end RHTower
