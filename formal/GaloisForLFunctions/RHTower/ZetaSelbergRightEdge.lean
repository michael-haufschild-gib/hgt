import GaloisForLFunctions.RHTower.ZetaSelbergKernel
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound

/-!
# The right edge of the Selberg contour

On the line `Re z = c > 1`, with `s₀ = σ₀ + it₀`, `σ₀ < c`, the full-line integral of Selberg's
kernel against the zeta logarithmic derivative is the smoothed von Mangoldt polynomial:

`∫ K_x(c + iy − s₀) ζ'/ζ(c + iy) dy = −2π Σ_n Λ(n) W_x(n) n^{−s₀}`
(`integral_selbergKernel_mul_logDeriv_zeta_line`).

The integrand is dominated by `B_c (x^{2a} + x^a)/(log x · (a² + (y − t₀)²))`, `a = c − σ₀`,
`B_c = Σ Λ(n) n^{−c}`, so the part of the line outside a window `[T₁, T₂] ∋ t₀` contributes at
most `2π B_c (x^{2a} + x^a)/(log x · H)`, `H = min(t₀ − T₁, T₂ − t₀)`
(`norm_integral_selbergRightEdge_sub_window_le`).
-/

noncomputable section

open Complex MeasureTheory Set Filter ArithmeticFunction

namespace RHTower

/-! ## Lorentzian integrals -/

theorem integrable_lorentz {d : ℝ} (hd : 0 < d) (t₀ : ℝ) :
    Integrable (fun y : ℝ => (d ^ 2 + (y - t₀) ^ 2)⁻¹) := by
  have h := (integrable_inv_one_add_sq.comp_div (ne_of_gt hd)).const_mul (d⁻¹ ^ 2)
  have h' : Integrable (fun y : ℝ => d⁻¹ ^ 2 * (1 + ((y - t₀) / d) ^ 2)⁻¹) :=
    (h.comp_sub_right t₀)
  refine h'.congr (Eventually.of_forall fun y => ?_)
  simp only
  field_simp

theorem integral_lorentz {d : ℝ} (hd : 0 < d) (t₀ : ℝ) :
    ∫ y : ℝ, (d ^ 2 + (y - t₀) ^ 2)⁻¹ = Real.pi / d := by
  have e : ∀ y : ℝ, (d ^ 2 + (y - t₀) ^ 2)⁻¹ = d⁻¹ ^ 2 * (1 + ((y - t₀) / d) ^ 2)⁻¹ := by
    intro y
    field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => (1 + (y / d) ^ 2)⁻¹) t₀,
    Measure.integral_comp_div (fun y => (1 + y ^ 2)⁻¹), integral_univ_inv_one_add_sq]
  rw [abs_of_pos hd, smul_eq_mul]
  field_simp

theorem integral_lorentz_window_le {d : ℝ} (hd : 0 < d) (t₀ : ℝ) {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    ∫ y in T₁..T₂, (d ^ 2 + (y - t₀) ^ 2)⁻¹ ≤ Real.pi / d := by
  rw [intervalIntegral.integral_of_le h, ← integral_lorentz hd t₀]
  exact setIntegral_le_integral (integrable_lorentz hd t₀)
    (Eventually.of_forall fun y => by positivity)

/-! ## The zeta logarithmic derivative on `Re z = c > 1` -/

/-- `‖ζ'/ζ(c + iy)‖ ≤ 8/(c − 1)²` for `1 < c ≤ 2`. -/
theorem norm_logDeriv_riemannZeta_line_le {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) (y : ℝ) :
    ‖logDeriv riemannZeta ((c : ℂ) + (y : ℂ) * I)‖ ≤ 8 / (c - 1) ^ 2 := by
  have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
  rw [logDeriv_apply]
  have h := norm_zeta_logDeriv_le_line (s := (c : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hc)
    (by rw [hre]; exact hc2)
  rwa [hre] at h

theorem continuousOn_logDeriv_riemannZeta_re_gt_one :
    ContinuousOn (logDeriv riemannZeta) {z : ℂ | 1 < z.re} := by
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have han : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := hdiff.analyticOnNhd hopen
  intro z hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  have hd : ContinuousAt (deriv riemannZeta) z := (han.deriv z hz1).continuousAt
  have hc : ContinuousAt riemannZeta z := (differentiableAt_riemannZeta hz1).continuousAt
  exact (hd.div hc hζ).continuousWithinAt

/-! ## The full-line identity -/

/-- The right-edge integrand `K_x(c + iy − s₀) ζ'/ζ(c + iy)`. -/
def selbergRightEdge (x c : ℝ) (s₀ : ℂ) (y : ℝ) : ℂ :=
  selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀) * logDeriv riemannZeta ((c : ℂ) + (y : ℂ) * I)

theorem norm_selbergRightEdge_le {x c : ℝ} (hx : 1 < x) (hc : 1 < c) (hc2 : c ≤ 2) (s₀ : ℂ)
    (y : ℝ) :
    ‖selbergRightEdge x c s₀ y‖ ≤
      (8 / (c - 1) ^ 2) *
        ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
          Real.log x) * ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2)⁻¹ := by
  have hl : 0 < Real.log x := Real.log_pos hx
  set w : ℂ := (c : ℂ) + (y : ℂ) * I - s₀ with hw
  have hwre : w.re = c - s₀.re := by simp [hw]
  have hwim : w.im = y - s₀.im := by simp [hw]
  have hwn : ‖w‖ ^ 2 = (c - s₀.re) ^ 2 + (y - s₀.im) ^ 2 := by
    rw [← hwre, ← hwim, Complex.sq_norm, Complex.normSq_apply]
    ring
  unfold selbergRightEdge
  rw [← hw, norm_mul, mul_comm]
  have hK := norm_selbergKernel_le hx w
  rw [hwre, hwn] at hK
  have hB := norm_logDeriv_riemannZeta_line_le hc hc2 y
  rcases eq_or_lt_of_le (show 0 ≤ (c - s₀.re) ^ 2 + (y - s₀.im) ^ 2 by positivity) with h0 | hpos
  · rw [← h0] at hK ⊢
    simp only [mul_zero, div_zero, inv_zero] at hK ⊢
    have : ‖selbergKernel x w‖ = 0 := le_antisymm hK (norm_nonneg _)
    rw [this, mul_zero]
  calc ‖logDeriv riemannZeta ((c : ℂ) + (y : ℂ) * I)‖ * ‖selbergKernel x w‖
      ≤ (8 / (c - 1) ^ 2) *
          ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
            (Real.log x * ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2))) :=
        mul_le_mul hB hK (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

theorem continuous_selbergRightEdge {x c : ℝ} (hc : 1 < c) {s₀ : ℂ} (hs₀ : s₀.re < c) :
    Continuous (selbergRightEdge x c s₀) := by
  have hw : ∀ y : ℝ, (c : ℂ) + (y : ℂ) * I - s₀ ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hnum : Continuous (fun y : ℝ => selbergKernelNum x ((c : ℂ) + (y : ℂ) * I - s₀)) :=
    (differentiable_selbergKernelNum x).continuous.comp (by fun_prop)
  have hden : Continuous (fun y : ℝ => ((c : ℂ) + (y : ℂ) * I - s₀) ^ 2) := by fun_prop
  have hK : Continuous (fun y : ℝ => selbergKernel x ((c : ℂ) + (y : ℂ) * I - s₀)) :=
    hnum.div hden (fun y => pow_ne_zero 2 (hw y))
  have hL : Continuous (fun y : ℝ => logDeriv riemannZeta ((c : ℂ) + (y : ℂ) * I)) :=
    continuousOn_logDeriv_riemannZeta_re_gt_one.comp_continuous (by fun_prop)
      (fun y => by simp [hc])
  exact hK.mul hL

theorem integrable_selbergRightEdge {x c : ℝ} (hx : 1 < x) (hc : 1 < c) (hc2 : c ≤ 2) {s₀ : ℂ}
    (hs₀ : s₀.re < c) : Integrable (selbergRightEdge x c s₀) := by
  have ha : 0 < c - s₀.re := by linarith
  refine ((integrable_lorentz ha s₀.im).const_mul ((8 / (c - 1) ^ 2) *
    ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
      Real.log x))).mono' (continuous_selbergRightEdge hc hs₀).aestronglyMeasurable
    (Eventually.of_forall fun y => norm_selbergRightEdge_le hx hc hc2 s₀ y)

/-- **The full-line right edge is the smoothed von Mangoldt polynomial.** -/
theorem integral_selbergRightEdge {x c : ℝ} (hx : 1 < x) (hc : 1 < c) {s₀ : ℂ}
    (hs₀ : s₀.re < c) :
    ∫ y : ℝ, selbergRightEdge x c s₀ y =
      -(2 * Real.pi) *
        ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀) * (selbergWeight x n : ℂ) := by
  set a : ℝ := c - s₀.re with hadef
  have ha : 0 < a := by rw [hadef]; linarith
  have hca : 1 < s₀.re + a := by rw [hadef]; linarith
  have hP := integral_neg_logDeriv_zeta_mul_selbergKernel hx s₀ ha hca
  have hpt : ∀ θ : ℝ, selbergRightEdge x c s₀ (s₀.im + 2 * Real.pi * θ) =
      -(-(deriv riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) /
        riemannZeta (s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I))) *
        selbergKernel x ((a : ℂ) + 2 * Real.pi * θ * Complex.I)) := by
    intro θ
    have e1 : (c : ℂ) + ((s₀.im + 2 * Real.pi * θ : ℝ) : ℂ) * I - s₀ =
        (a : ℂ) + 2 * Real.pi * θ * Complex.I := by
      rw [hadef]
      apply Complex.ext <;> simp
    have e2 : (c : ℂ) + ((s₀.im + 2 * Real.pi * θ : ℝ) : ℂ) * I =
        s₀ + ((a : ℂ) + 2 * Real.pi * θ * Complex.I) := by
      rw [hadef]
      apply Complex.ext <;> simp
    unfold selbergRightEdge
    rw [e1, e2, logDeriv_apply]
    ring
  have hsub : ∫ θ : ℝ, selbergRightEdge x c s₀ (s₀.im + 2 * Real.pi * θ) =
      -∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀) * (selbergWeight x n : ℂ) := by
    simp_rw [hpt]
    rw [integral_neg, hP]
  have hscale : ∫ θ : ℝ, selbergRightEdge x c s₀ (s₀.im + 2 * Real.pi * θ) =
      (2 * Real.pi)⁻¹ * ∫ y : ℝ, selbergRightEdge x c s₀ y := by
    have h1 := Measure.integral_comp_mul_left
      (fun u : ℝ => selbergRightEdge x c s₀ (s₀.im + u)) (2 * Real.pi)
    have h2 := integral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => selbergRightEdge x c s₀ y) s₀.im
    rw [h1, h2, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), Complex.real_smul]
  rw [hscale] at hsub
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  calc ∫ y : ℝ, selbergRightEdge x c s₀ y
      = (2 * (Real.pi : ℂ)) * ((2 * Real.pi)⁻¹ * ∫ y : ℝ, selbergRightEdge x c s₀ y) := by
        push_cast
        field_simp
    _ = _ := by rw [hsub]; ring

/-- **The right edge outside a window around `t₀`.** -/
theorem norm_integral_selbergRightEdge_sub_window_le {x c : ℝ} (hx : 1 < x) (hc : 1 < c)
    (hc2 : c ≤ 2)
    {s₀ : ℂ} (hs₀ : s₀.re < c) {T₁ T₂ H : ℝ} (hH : 0 < H) (hH1 : H ≤ s₀.im - T₁)
    (hH2 : H ≤ T₂ - s₀.im) :
    ‖(∫ y : ℝ, selbergRightEdge x c s₀ y) - ∫ y in T₁..T₂, selbergRightEdge x c s₀ y‖ ≤
      (8 / (c - 1) ^ 2) *
        ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
          Real.log x) * (2 * Real.pi / H) := by
  have hT : T₁ ≤ T₂ := by linarith
  set M : ℝ := (8 / (c - 1) ^ 2) *
    ((Real.exp (2 * (c - s₀.re) * Real.log x) + Real.exp ((c - s₀.re) * Real.log x)) /
      Real.log x) with hM
  have hl : 0 < Real.log x := Real.log_pos hx
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hint := integrable_selbergRightEdge hx hc hc2 hs₀
  set S : Set ℝ := Ioc T₁ T₂ with hS
  have hsplit := integral_add_compl (s := S) measurableSet_Ioc hint
  rw [intervalIntegral.integral_of_le hT, ← hsplit, add_sub_cancel_left]
  set g : ℝ → ℝ := fun y => M * (2 * (H ^ 2 + (y - s₀.im) ^ 2)⁻¹) with hg
  have hgint : Integrable g := ((integrable_lorentz hH s₀.im).const_mul 2).const_mul M
  have hbound : ∀ y ∈ Sᶜ, ‖selbergRightEdge x c s₀ y‖ ≤ g y := by
    intro y hy
    have hy' : H ≤ |y - s₀.im| := by
      simp only [hS, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hy
      rcases hy with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hsq : H ^ 2 ≤ (y - s₀.im) ^ 2 := by
      rw [← sq_abs (y - s₀.im)]
      exact pow_le_pow_left₀ hH.le hy' 2
    refine (norm_selbergRightEdge_le hx hc hc2 s₀ y).trans ?_
    rw [hg]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have hA : 0 < H ^ 2 + (y - s₀.im) ^ 2 := by positivity
    have hB : 0 < (c - s₀.re) ^ 2 + (y - s₀.im) ^ 2 := by
      have : 0 < (y - s₀.im) ^ 2 := lt_of_lt_of_le (by positivity) hsq
      positivity
    have key : H ^ 2 + (y - s₀.im) ^ 2 ≤ 2 * ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2) := by
      nlinarith [sq_nonneg (c - s₀.re)]
    have h2B : ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2)⁻¹ =
        2 * (2 * ((c - s₀.re) ^ 2 + (y - s₀.im) ^ 2))⁻¹ := by
      field_simp
    rw [h2B]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hA key) (by norm_num)
  calc ‖∫ y in Sᶜ, selbergRightEdge x c s₀ y‖
      ≤ ∫ y in Sᶜ, g y :=
        norm_integral_le_of_norm_le hgint.integrableOn
          ((ae_restrict_iff' measurableSet_Ioc.compl).mpr (Eventually.of_forall hbound))
    _ ≤ ∫ y, g y := setIntegral_le_integral hgint
        (Eventually.of_forall fun y => by rw [hg]; positivity)
    _ = M * (2 * Real.pi / H) := by
        rw [hg, integral_const_mul, integral_const_mul, integral_lorentz hH]
        ring

end RHTower
