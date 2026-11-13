import GaloisForLFunctions.GaloisTheoryOfZeros.TheHeatFamilyAtForwardTimesIsAComplexGaussianAverageOfXi
import GaloisForLFunctions.RHTower.XiSlopeInTheRightHalfPlane

/-!
# The Gaussian concentrates at the saddle point

Against an exponential `e^{au}` the complex Gaussian `g_τ` concentrates at the complex point
`2τa` (completing the square). Let `p = s + 2τa` be the saddle point and let `η` bound
`‖ξ'/ξ − a‖` on segments issued from `p`, so that `ξ` is the exponential `ξ(p) e^{a(· − p)}` up to
the relative error `e^{η‖· − p‖} − 1`. Then:

* `g_τ(w) ξ(s + w)` is `ξ(p) e^{−τa²} g_τ(w − 2τa)` up to the same relative error
  (`norm_complexGauss_mul_xi_sub_le`);
* the integral over a ray through the saddle is the saddle value `ξ(p) e^{−τa²}`, as soon as `η`
  is small on a long window around the saddle and grows more slowly than the Gaussian decays
  beyond it (`norm_integral_ray_sub_saddle_le`);
* the exponent of the Gaussian is concave along vertical segments (`re_sq_div_concave`), which
  bounds a vertical side by its two ends.

The bounds are uniform for `τ` in a box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` through the rate `gaussRate` and
the height `gaussHeight`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Elementary bounds -/

/-- A Gaussian beats every exponential: `e^{−ax² + bx + c} ≤ ε` for `x ≥ A`. -/
theorem exists_forall_exp_neg_quadratic_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (b c : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, A ≤ x → Real.exp (-a * x ^ 2 + b * x + c) ≤ ε := by
  refine ⟨max 1 ((|b| + |c| + 1 + |Real.log ε|) / a), le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : (|b| + |c| + 1 + |Real.log ε|) / a ≤ x := (le_max_right _ _).trans hx
  rw [div_le_iff₀ ha] at hx2
  refine (Real.exp_le_exp.2 ?_).trans_eq (Real.exp_log hε)
  have h1 : b * x ≤ |b| * x := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
  have h2 : c ≤ |c| * x := (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) hx1)
  have h3 : -|Real.log ε| ≤ Real.log ε := neg_abs_le _
  have h4 : |Real.log ε| ≤ |Real.log ε| * x := le_mul_of_one_le_right (abs_nonneg _) hx1
  have h5 := mul_le_mul_of_nonneg_right hx2 (by linarith : (0 : ℝ) ≤ x)
  have h6 : x * a * x = a * x ^ 2 := by ring
  nlinarith

theorem two_rpow_neg_le {x : ℝ} (hx : 0 < x) : (2 : ℝ) ^ (-x) ≤ 2 / x := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h1 : Real.exp (Real.log 2 * -x) ≤ Real.exp (-(x / 2)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : Real.exp (-(x / 2)) ≤ 2 / x := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    linarith [Real.add_one_le_exp (x / 2)]
  exact h1.trans h2

theorem mul_two_rpow_neg_le {x : ℝ} (hx : 0 < x) : x * (2 : ℝ) ^ (-x) ≤ 2 := by
  calc x * (2 : ℝ) ^ (-x) ≤ x * (2 / x) := mul_le_mul_of_nonneg_left (two_rpow_neg_le hx) hx.le
    _ = 2 := by field_simp

/-- A point of the interval between `0` and `c` is `θc` with `0 ≤ θ ≤ 1`. -/
theorem exists_mul_of_mem_uIoc {c v : ℝ} (hv : v ∈ Set.uIoc (0 : ℝ) c) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ v = θ * c := by
  rcases le_total 0 c with h | h
  · rw [uIoc_of_le h] at hv
    have hc : 0 < c := hv.1.trans_le hv.2
    exact ⟨v / c, div_nonneg hv.1.le hc.le, (div_le_one hc).2 hv.2, (div_mul_cancel₀ v hc.ne').symm⟩
  · rw [uIoc_of_ge h] at hv
    have hc : c < 0 := hv.1.trans_le hv.2
    exact ⟨v / c, div_nonneg_of_nonpos hv.2 hc.le, (div_le_one_of_neg hc).2 hv.1.le,
      (div_mul_cancel₀ v hc.ne).symm⟩

/-! ## The integrand against the saddle value -/

/-- **The Gaussian concentrates at `2τa`.** If `‖ξ'/ξ − a‖ ≤ η` on the segment from the saddle
point `p = s + 2τa` to `s + w`, then `g_τ(w) ξ(s + w)` is `ξ(p) e^{−τa²} g_τ(w − 2τa)` up to the
relative error `e^{η‖w − 2τa‖} − 1`. -/
theorem norm_complexGauss_mul_xi_sub_le {τ : ℂ} (hτ : τ ≠ 0) (s a w : ℂ) {η : ℝ} (hη : 0 < η)
    (hseg : ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + w), 1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ η) :
    ‖complexGauss τ w * xi (s + w) -
        xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)) * complexGauss τ (w - 2 * τ * a)‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ (w - 2 * τ * a)‖ *
        (Real.exp (η * ‖w - 2 * τ * a‖) - 1) := by
  set d : ℂ := w - 2 * τ * a with hd
  have hsad : complexGauss τ w = cexp (-(τ * a ^ 2) - a * d) * complexGauss τ d := by
    rw [← complexGauss_add_saddle hτ a d, hd]
    congr 1
    ring
  have h2 := norm_xi_sub_mul_exp_le (p := s + 2 * τ * a) (q := s + w) (a := a) hη hseg
  have hqp : s + w - (s + 2 * τ * a) = d := by
    rw [hd]
    ring
  rw [hqp] at h2
  have hone : cexp (-(a * d)) * cexp (d * a) = 1 := by
    rw [← Complex.exp_add, show -(a * d) + d * a = 0 by ring, Complex.exp_zero]
  have hfac : complexGauss τ w * xi (s + w) -
      xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)) * complexGauss τ d =
      cexp (-(τ * a ^ 2)) * complexGauss τ d * cexp (-(a * d)) *
        (xi (s + w) - xi (s + 2 * τ * a) * cexp (d * a)) := by
    rw [hsad, sub_eq_add_neg (-(τ * a ^ 2)) (a * d), Complex.exp_add]
    linear_combination (xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)) * complexGauss τ d) * hone
  have he : ‖cexp (-(a * d))‖ = Real.exp (-(d * a).re) := by
    rw [Complex.norm_exp, Complex.neg_re, mul_comm]
  have hcancel : Real.exp (-(d * a).re) * Real.exp ((d * a).re) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hfac, norm_mul, norm_mul, norm_mul, norm_mul (xi (s + 2 * τ * a)), he]
  calc ‖cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ d‖ * Real.exp (-(d * a).re) *
        ‖xi (s + w) - xi (s + 2 * τ * a) * cexp (d * a)‖
      ≤ ‖cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ d‖ * Real.exp (-(d * a).re) *
          (‖xi (s + 2 * τ * a)‖ * Real.exp ((d * a).re) * (Real.exp (η * ‖d‖) - 1)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ‖xi (s + 2 * τ * a)‖ * ‖cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ d‖ *
          (Real.exp (η * ‖d‖) - 1) := by
        linear_combination (‖cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ d‖ * ‖xi (s + 2 * τ * a)‖ *
          (Real.exp (η * ‖d‖) - 1)) * hcancel

/-- Upper form of the comparison with the saddle value. -/
theorem norm_complexGauss_mul_xi_le {τ : ℂ} (hτ : τ ≠ 0) (s a w : ℂ) {η : ℝ} (hη : 0 < η)
    (hseg : ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + w), 1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ η) :
    ‖complexGauss τ w * xi (s + w)‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ (w - 2 * τ * a)‖ *
        Real.exp (η * ‖w - 2 * τ * a‖) := by
  have h := norm_complexGauss_mul_xi_sub_le hτ s a w hη hseg
  have ht := norm_le_norm_add_norm_sub' (complexGauss τ w * xi (s + w))
    (xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)) * complexGauss τ (w - 2 * τ * a))
  rw [norm_mul (xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)))] at ht
  have e : ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ (w - 2 * τ * a)‖ *
      (Real.exp (η * ‖w - 2 * τ * a‖) - 1) =
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ (w - 2 * τ * a)‖ *
        Real.exp (η * ‖w - 2 * τ * a‖) -
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * ‖complexGauss τ (w - 2 * τ * a)‖ := by ring
  linarith

/-! ## Uniform Gaussian bounds -/

/-- The uniform Gaussian rate on `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`. -/
def gaussRate (t₀ T₀ : ℝ) : ℝ := t₀ / (4 * T₀ ^ 2)

/-- The uniform Gaussian height on `{t₀ ≤ Re τ}`. -/
def gaussHeight (t₀ : ℝ) : ℝ := 1 / Real.sqrt (4 * Real.pi * t₀)

theorem gaussHeight_pos {t₀ : ℝ} (ht₀ : 0 < t₀) : 0 < gaussHeight t₀ := by
  unfold gaussHeight
  exact one_div_pos.2 (Real.sqrt_pos.2 (by positivity))

theorem gaussRate_le {τ : ℂ} {t₀ T₀ : ℝ} (ht₀ : 0 < t₀) (hτt : t₀ ≤ τ.re) (hτT : ‖τ‖ ≤ T₀) :
    gaussRate t₀ T₀ ≤ τ.re / (4 * ‖τ‖ ^ 2) := by
  have hτ : 0 < τ.re := ht₀.trans_le hτt
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  have hT : 0 < T₀ := hn.trans_le hτT
  have h1 : 4 * ‖τ‖ ^ 2 ≤ 4 * T₀ ^ 2 := by nlinarith
  rw [gaussRate]
  exact (div_le_div_of_nonneg_right hτt (by positivity)).trans
    (div_le_div_of_nonneg_left hτ.le (by positivity) h1)

theorem one_div_sqrt_le_gaussHeight {τ : ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀) (hτt : t₀ ≤ τ.re) :
    1 / Real.sqrt (4 * Real.pi * ‖τ‖) ≤ gaussHeight t₀ := by
  have hnre : τ.re ≤ ‖τ‖ := Complex.re_le_norm τ
  rw [gaussHeight]
  refine one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt ?_)
  have := Real.pi_pos
  nlinarith

theorem norm_complexGauss_ofReal_le {τ : ℂ} {t₀ T₀ : ℝ} (ht₀ : 0 < t₀) (hτt : t₀ ≤ τ.re)
    (hτT : ‖τ‖ ≤ T₀) (v : ℝ) :
    ‖complexGauss τ v‖ ≤ gaussHeight t₀ * Real.exp (-gaussRate t₀ T₀ * v ^ 2) := by
  have hτ : 0 < τ.re := ht₀.trans_le hτt
  rw [norm_complexGauss_ofReal hτ]
  have h2 : Real.exp (-(τ.re / (4 * ‖τ‖ ^ 2)) * v ^ 2) ≤ Real.exp (-gaussRate t₀ T₀ * v ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg v, gaussRate_le ht₀ hτt hτT]
  calc Real.exp (-(τ.re / (4 * ‖τ‖ ^ 2)) * v ^ 2) / Real.sqrt (4 * Real.pi * ‖τ‖)
      = 1 / Real.sqrt (4 * Real.pi * ‖τ‖) * Real.exp (-(τ.re / (4 * ‖τ‖ ^ 2)) * v ^ 2) := by ring
    _ ≤ _ := mul_le_mul (one_div_sqrt_le_gaussHeight ht₀ hτt) h2 (Real.exp_pos _).le
        (gaussHeight_pos ht₀).le

theorem re_ofReal_sq_div {τ : ℂ} (hτ : 0 < τ.re) (x : ℝ) :
    ((x : ℂ) ^ 2 / (4 * τ)).re = τ.re / (4 * ‖τ‖ ^ 2) * x ^ 2 := by
  rw [re_sq_div_four_mul hτ]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The exponent of the Gaussian is concave along a vertical segment.** -/
theorem re_sq_div_concave {τ : ℂ} (hτ : 0 < τ.re) (x c θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * (((x : ℂ) + ((0 - c : ℝ) : ℂ) * I) ^ 2 / (4 * τ)).re +
        θ * ((x : ℂ) ^ 2 / (4 * τ)).re ≤
      (((x : ℂ) + ((θ * c - c : ℝ) : ℂ) * I) ^ 2 / (4 * τ)).re := by
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  rw [re_sq_div_four_mul hτ, re_sq_div_four_mul hτ, re_sq_div_four_mul hτ]
  have e1 : ((x : ℂ) + ((0 - c : ℝ) : ℂ) * I).re = x := by simp
  have e2 : ((x : ℂ) + ((0 - c : ℝ) : ℂ) * I).im = 0 - c := by simp
  have e3 : ((x : ℂ) + ((θ * c - c : ℝ) : ℂ) * I).re = x := by simp
  have e4 : ((x : ℂ) + ((θ * c - c : ℝ) : ℂ) * I).im = θ * c - c := by simp
  rw [e1, e2, e3, e4, Complex.ofReal_re, Complex.ofReal_im, ← sub_nonneg]
  have key : ((x ^ 2 - (θ * c - c) ^ 2) * τ.re + 2 * x * (θ * c - c) * τ.im) / (4 * ‖τ‖ ^ 2) -
      ((1 - θ) * (((x ^ 2 - (0 - c) ^ 2) * τ.re + 2 * x * (0 - c) * τ.im) / (4 * ‖τ‖ ^ 2)) +
        θ * (((x ^ 2 - 0 ^ 2) * τ.re + 2 * x * 0 * τ.im) / (4 * ‖τ‖ ^ 2))) =
      τ.re * c ^ 2 * θ * (1 - θ) / (4 * ‖τ‖ ^ 2) := by
    field_simp
    ring
  rw [key]
  have h1 : 0 ≤ 1 - θ := by linarith
  have h2 : 0 ≤ τ.re * c ^ 2 * θ * (1 - θ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hτ.le (sq_nonneg c)) hθ0) h1
  exact div_nonneg h2 (by positivity)

/-! ## The saddle-point lemma on a ray -/

/-- **The ray through the saddle.** Let `2τa = w₀ + ic`, and let the ray `[u₂, ∞)` at height `c`
contain the window `|u − w₀| ≤ L`. If `‖ξ'/ξ − a‖ ≤ η₁` on the window and
`‖ξ'/ξ − a‖ ≤ 1 + (λ/2)|u − w₀|` on the ray, then the integral over the ray is the saddle value
`ξ(s + 2τa) e^{−τa²}` up to the relative error
`κ₀ ((e^{η₁L} − 1) ∫ e^{−λv²} + 2 e^{−λL²/8} ∫ e^{−λv²/8})`. -/
theorem norm_integral_ray_sub_saddle_le {τ : ℂ} {t₀ T₀ : ℝ} (ht₀ : 0 < t₀) (hτt : t₀ ≤ τ.re)
    (hτT : ‖τ‖ ≤ T₀) (s a : ℂ) {w₀ c u₂ L η₁ : ℝ} (hsad : 2 * τ * a = w₀ + c * I)
    (hL : 4 / gaussRate t₀ T₀ ≤ L) (hu₂ : u₂ + L ≤ w₀) (hη₁ : 0 < η₁)
    (hnear : ∀ u : ℝ, u₂ ≤ u → |u - w₀| ≤ L →
      ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + (u + c * I)),
        1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ η₁)
    (hfar : ∀ u : ℝ, u₂ ≤ u → ∀ w' ∈ segment ℝ (s + 2 * τ * a) (s + (u + c * I)),
      1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ 1 + gaussRate t₀ T₀ / 2 * |u - w₀|) :
    ‖(∫ u in Ioi u₂, complexGauss τ (u + c * I) * xi (s + (u + c * I))) -
        xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (gaussHeight t₀ *
        ((Real.exp (η₁ * L) - 1) * (∫ v : ℝ, Real.exp (-gaussRate t₀ T₀ * v ^ 2)) +
          2 * (Real.exp (-gaussRate t₀ T₀ * L ^ 2 / 8) *
            ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 8) * v ^ 2)))) := by
  have hτ : 0 < τ.re := ht₀.trans_le hτt
  have hτ0 := ne_zero_of_re_pos hτ
  have hT : 0 < T₀ := (norm_pos_iff.2 hτ0).trans_le hτT
  set lam : ℝ := gaussRate t₀ T₀ with hlam
  have hlam0 : 0 < lam := by
    rw [hlam, gaussRate]
    positivity
  set kap : ℝ := gaussHeight t₀ with hkap
  have hkap0 : 0 < kap := gaussHeight_pos ht₀
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  set M : ℂ := xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)) with hM
  set G : ℝ → ℂ := fun u => complexGauss τ (u + c * I) * xi (s + (u + c * I)) with hG
  set γ : ℝ → ℂ := fun u => complexGauss τ ((u - w₀ : ℝ) : ℂ) with hγ
  set δ : ℝ := Real.exp (η₁ * L) - 1 with hδ
  have hδ0 : 0 ≤ δ := by
    have := Real.add_one_le_exp (η₁ * L)
    have := mul_pos hη₁ hL0
    rw [hδ]
    linarith
  set e8 : ℝ := Real.exp (-lam * L ^ 2 / 8) with he8
  have he80 : 0 < e8 := Real.exp_pos _
  -- on the ray the distance to the saddle is real
  have hdiff : ∀ u : ℝ, ((u : ℂ) + c * I) - 2 * τ * a = ((u - w₀ : ℝ) : ℂ) := by
    intro u
    rw [hsad]
    push_cast
    ring
  have hγle : ∀ u : ℝ, ‖γ u‖ ≤ kap * Real.exp (-lam * (u - w₀) ^ 2) := fun u =>
    norm_complexGauss_ofReal_le ht₀ hτt hτT (u - w₀)
  -- the integrand against `M γ` on the ray
  have hpt : ∀ u : ℝ, u₂ < u → ‖G u - M * γ u‖ ≤ ‖M‖ * (kap *
      (δ * Real.exp (-lam * (u - w₀) ^ 2) + e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2))) := by
    intro u hu
    have hnv : ‖((u : ℂ) + c * I) - 2 * τ * a‖ = |u - w₀| := by
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖γ u‖ ≤ kap * Real.exp (-lam * (u - w₀) ^ 2) := hγle u
    have hM0 : 0 ≤ ‖M‖ := norm_nonneg M
    have hEa : 0 ≤ Real.exp (-lam * (u - w₀) ^ 2) := (Real.exp_pos _).le
    have hEb : 0 ≤ Real.exp (-(lam / 8) * (u - w₀) ^ 2) := (Real.exp_pos _).le
    rcases le_or_gt |u - w₀| L with hvL | hvL
    · have h := norm_complexGauss_mul_xi_sub_le hτ0 s a (u + c * I) hη₁ (hnear u hu.le hvL)
      rw [hnv, hdiff] at h
      have h1 : Real.exp (η₁ * |u - w₀|) - 1 ≤ δ := by
        have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hvL hη₁.le)
        rw [hδ]
        linarith
      have h0 : 0 ≤ Real.exp (η₁ * |u - w₀|) - 1 := by
        have := Real.add_one_le_exp (η₁ * |u - w₀|)
        have := mul_nonneg hη₁.le (abs_nonneg (u - w₀))
        linarith
      calc ‖G u - M * γ u‖ ≤ ‖M‖ * ‖γ u‖ * (Real.exp (η₁ * |u - w₀|) - 1) := h
        _ ≤ ‖M‖ * (kap * Real.exp (-lam * (u - w₀) ^ 2)) * δ :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 hM0) h1 h0 (by positivity)
        _ ≤ _ := by
            have h3 : 0 ≤ ‖M‖ * (kap * (e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2))) := by
              positivity
            nlinarith
    · have hη : 0 < 1 + lam / 2 * |u - w₀| := by positivity
      have h := norm_complexGauss_mul_xi_sub_le hτ0 s a (u + c * I) hη (hfar u hu.le)
      rw [hnv, hdiff] at h
      have h0 : 0 ≤ Real.exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|) - 1 := by
        have := Real.add_one_le_exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|)
        have := mul_nonneg hη.le (abs_nonneg (u - w₀))
        linarith
      have hexp : Real.exp (-lam * (u - w₀) ^ 2) *
          (Real.exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|) - 1) ≤
          e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2) := by
        have hv2 : (u - w₀) ^ 2 = |u - w₀| ^ 2 := (sq_abs _).symm
        have h4 : 4 ≤ lam * |u - w₀| := by
          have h5 : 4 / lam < |u - w₀| := lt_of_le_of_lt hL hvL
          rw [div_lt_iff₀ hlam0] at h5
          linarith
        have habs := abs_nonneg (u - w₀)
        calc Real.exp (-lam * (u - w₀) ^ 2) *
              (Real.exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|) - 1)
            ≤ Real.exp (-lam * (u - w₀) ^ 2) *
                Real.exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|) :=
              mul_le_mul_of_nonneg_left (by linarith) hEa
          _ = Real.exp (-lam * (u - w₀) ^ 2 + (1 + lam / 2 * |u - w₀|) * |u - w₀|) :=
              (Real.exp_add _ _).symm
          _ ≤ Real.exp (-lam * L ^ 2 / 8 + -(lam / 8) * (u - w₀) ^ 2) := by
              apply Real.exp_le_exp.2
              rw [hv2]
              nlinarith [mul_nonneg (sub_nonneg.2 h4) habs,
                mul_nonneg hlam0.le (mul_nonneg (sub_nonneg.2 hvL.le) (add_nonneg habs hL0.le))]
          _ = _ := by rw [Real.exp_add]
      calc ‖G u - M * γ u‖
          ≤ ‖M‖ * ‖γ u‖ * (Real.exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|) - 1) := h
        _ ≤ ‖M‖ * (kap * Real.exp (-lam * (u - w₀) ^ 2)) *
              (Real.exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|) - 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM0) h0
        _ = ‖M‖ * (kap * (Real.exp (-lam * (u - w₀) ^ 2) *
              (Real.exp ((1 + lam / 2 * |u - w₀|) * |u - w₀|) - 1))) := by ring
        _ ≤ ‖M‖ * (kap * (e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hkap0.le) hM0
        _ ≤ _ := by
            have h3 : 0 ≤ ‖M‖ * (kap * (δ * Real.exp (-lam * (u - w₀) ^ 2))) := by positivity
            nlinarith
  -- to the left of the ray the Gaussian is in its tail
  have hγ2 : ∀ u : ℝ, u ≤ u₂ → ‖γ u‖ ≤ kap * (e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2)) := by
    intro u hu
    refine (hγle u).trans (mul_le_mul_of_nonneg_left ?_ hkap0.le)
    rw [he8, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hvL : L ≤ w₀ - u := by linarith
    nlinarith [mul_nonneg hlam0.le (mul_nonneg (sub_nonneg.2 hvL)
      (add_nonneg (sub_nonneg.2 (hL0.le.trans hvL)) hL0.le))]
  -- integrability
  have hGi : Integrable G := integrable_complexGauss_mul_xi_line hτ s c
  have h0i : Integrable fun u : ℝ => complexGauss τ (u : ℂ) := by
    have := integrable_complexGauss_mul_exp hτ 0
    simpa using this
  have hγi : Integrable γ := h0i.comp_sub_right w₀
  have hγint : ∫ u, γ u = 1 := by
    have h0 : ∫ u : ℝ, complexGauss τ (u : ℂ) = 1 := by
      have := integral_complexGauss_mul_exp hτ 0
      simpa using this
    rw [← h0]
    exact integral_sub_right_eq_self (fun u : ℝ => complexGauss τ (u : ℂ)) w₀
  have hI1 : Integrable fun u : ℝ => Real.exp (-lam * (u - w₀) ^ 2) :=
    (integrable_exp_neg_mul_sq hlam0).comp_sub_right w₀
  have hI8 : Integrable fun u : ℝ => Real.exp (-(lam / 8) * (u - w₀) ^ 2) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < lam / 8)).comp_sub_right w₀
  have hint1 : ∫ u : ℝ, Real.exp (-lam * (u - w₀) ^ 2) = ∫ v : ℝ, Real.exp (-lam * v ^ 2) :=
    integral_sub_right_eq_self (fun v : ℝ => Real.exp (-lam * v ^ 2)) w₀
  have hint8 : ∫ u : ℝ, Real.exp (-(lam / 8) * (u - w₀) ^ 2) =
      ∫ v : ℝ, Real.exp (-(lam / 8) * v ^ 2) :=
    integral_sub_right_eq_self (fun v : ℝ => Real.exp (-(lam / 8) * v ^ 2)) w₀
  -- the two pieces
  have hsplit : (∫ u in Ioi u₂, G u) - M =
      (∫ u in Ioi u₂, (G u - M * γ u)) - M * ∫ u in Iic u₂, γ u := by
    have h1 : ∫ u in Ioi u₂, (G u - M * γ u) =
        (∫ u in Ioi u₂, G u) - M * ∫ u in Ioi u₂, γ u := by
      rw [integral_sub hGi.integrableOn (hγi.integrableOn.const_mul M), integral_const_mul]
    have h2 : (∫ u in Ioi u₂, γ u) + ∫ u in Iic u₂, γ u = 1 := by
      rw [← hγint, ← integral_add_compl (s := Ioi u₂) measurableSet_Ioi hγi, compl_Ioi]
    rw [h1]
    linear_combination M * h2
  have hA : ‖∫ u in Ioi u₂, (G u - M * γ u)‖ ≤ ‖M‖ * (kap *
      (δ * (∫ v : ℝ, Real.exp (-lam * v ^ 2)) + e8 * ∫ v : ℝ, Real.exp (-(lam / 8) * v ^ 2))) := by
    have hbi : Integrable fun u : ℝ => ‖M‖ * (kap *
        (δ * Real.exp (-lam * (u - w₀) ^ 2) + e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2))) :=
      (((hI1.const_mul δ).add (hI8.const_mul e8)).const_mul kap).const_mul ‖M‖
    calc ‖∫ u in Ioi u₂, (G u - M * γ u)‖
        ≤ ∫ u in Ioi u₂, ‖M‖ * (kap *
            (δ * Real.exp (-lam * (u - w₀) ^ 2) + e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2))) :=
          norm_integral_le_of_norm_le hbi.integrableOn
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => hpt u hu))
      _ ≤ ∫ u, ‖M‖ * (kap *
            (δ * Real.exp (-lam * (u - w₀) ^ 2) + e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2))) :=
          setIntegral_le_integral hbi (Eventually.of_forall fun u => by positivity)
      _ = _ := by
          rw [integral_const_mul, integral_const_mul,
            integral_add (hI1.const_mul δ) (hI8.const_mul e8), integral_const_mul,
            integral_const_mul, hint1, hint8]
  have hB : ‖M * ∫ u in Iic u₂, γ u‖ ≤
      ‖M‖ * (kap * (e8 * ∫ v : ℝ, Real.exp (-(lam / 8) * v ^ 2))) := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg M)
    have hg : Integrable fun u : ℝ => kap * (e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2)) :=
      (hI8.const_mul e8).const_mul kap
    calc ‖∫ u in Iic u₂, γ u‖
        ≤ ∫ u in Iic u₂, kap * (e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2)) :=
          norm_integral_le_of_norm_le hg.integrableOn
            ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun u hu => hγ2 u hu))
      _ ≤ ∫ u, kap * (e8 * Real.exp (-(lam / 8) * (u - w₀) ^ 2)) :=
          setIntegral_le_integral hg (Eventually.of_forall fun u => by positivity)
      _ = _ := by rw [integral_const_mul, integral_const_mul, hint8]
  show ‖(∫ u in Ioi u₂, G u) - M‖ ≤ ‖M‖ * (kap * (δ * (∫ v : ℝ, Real.exp (-lam * v ^ 2)) +
    2 * (e8 * ∫ v : ℝ, Real.exp (-(lam / 8) * v ^ 2))))
  rw [hsplit]
  calc ‖(∫ u in Ioi u₂, (G u - M * γ u)) - M * ∫ u in Iic u₂, γ u‖
      ≤ ‖∫ u in Ioi u₂, (G u - M * γ u)‖ + ‖M * ∫ u in Iic u₂, γ u‖ := norm_sub_le _ _
    _ ≤ ‖M‖ * (kap * (δ * (∫ v : ℝ, Real.exp (-lam * v ^ 2)) +
          e8 * ∫ v : ℝ, Real.exp (-(lam / 8) * v ^ 2))) +
        ‖M‖ * (kap * (e8 * ∫ v : ℝ, Real.exp (-(lam / 8) * v ^ 2))) := add_le_add hA hB
    _ = _ := by ring

end

end GaloisForLFunctions.GaloisTheoryOfZeros
