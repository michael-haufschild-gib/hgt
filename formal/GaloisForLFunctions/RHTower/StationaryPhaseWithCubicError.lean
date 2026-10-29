import GaloisForLFunctions.RHTower.QuadraticPhaseStationary
import GaloisForLFunctions.RHTower.VanDerCorputSecond
import GaloisForLFunctions.HTGeometry.MonotonePhaseFirstDerivativeTest

/-!
# Stationary phase with a cubic error

Let `F` be real on `[a, b]` with `λ₂ ≤ F″`, `|F‴| ≤ λ₃`, and a stationary point `F′(c) = 0`,
`a < c < b` (`norm_integral_cexp_sub_stationary_le`).  Then

  `‖∫_a^b e^{iF} − √(2π/F″(c)) e^{i(F(c) + π/4)}‖ ≤ λ₃δ⁴/3 + 14/(λ₂δ) + 4/(λ₂(c − a)) + 4/(λ₂(b − c))`

for every cut radius `δ > 0`; the choice `δ = (λ₂λ₃)^{−1/5}` makes the first two terms
`O(λ₂^{−4/5}λ₃^{1/5})`.

**Proof.**  Cut `[a, b]` at `c − δ₁`, `c + δ₂`, `δ₁ = min(δ, c − a)`, `δ₂ = min(δ, b − c)`.
* Near `c`, Taylor gives `|F(c + u) − F(c) − F″(c)u²/2| ≤ λ₃|u|³/6`
  (`abs_sub_taylor_two_le`), so the integral differs from `e^{iF(c)}` times the quadratic phase
  integral by `≤ λ₃δ⁴/3`.  The quadratic phase integral over `[−δ₁, δ₂]` is within
  `4/(μδ₁) + 4/(μδ₂)` of `√(2π/μ) e^{iπ/4}`, `μ = F″(c)` (`norm_integral_quadPhase_sub_le`).
* Away from `c`, `|F′| ≥ λ₂δ` and `F′` is monotone, so each side contributes `≤ 3/(λ₂δ)`
  (`norm_integral_mul_exp_le_of_monotone_phase`).

`norm_integral_cexp_sub_main_le_crude` is the companion bound `9/√λ₂`, valid wherever the
stationary point sits.
-/

open Complex MeasureTheory Set intervalIntegral
open scoped Interval

namespace RHTower

noncomputable section

/-! ## Taylor with a cubic error -/

/-- Forward cubic Taylor bound: on `[c, x]`, `|F(x) − F(c) − F″(c)(x − c)²/2| ≤ λ₃(x − c)³/6`. -/
theorem abs_sub_taylor_two_le_forward {F F' F'' F''' : ℝ → ℝ} {c x lam₃ : ℝ} (hcx : c ≤ x)
    (hF : ∀ y ∈ Icc c x, HasDerivAt F (F' y) y)
    (hF' : ∀ y ∈ Icc c x, HasDerivAt F' (F'' y) y)
    (hF'' : ∀ y ∈ Icc c x, HasDerivAt F'' (F''' y) y)
    (hF''' : ∀ y ∈ Icc c x, |F''' y| ≤ lam₃) (hc : F' c = 0) :
    |F x - F c - F'' c * (x - c) ^ 2 / 2| ≤ lam₃ * (x - c) ^ 3 / 6 := by
  have hB1 : ∀ z, HasDerivAt (fun w : ℝ => lam₃ * (w - c)) lam₃ z := fun z =>
    (((hasDerivAt_id' z).sub_const c).const_mul lam₃).congr_deriv (by ring)
  have hB2 : ∀ z, HasDerivAt (fun w : ℝ => lam₃ * (w - c) ^ 2 / 2) (lam₃ * (z - c)) z := fun z =>
    ((((hasDerivAt_id' z).sub_const c).pow 2).const_mul lam₃).div_const 2 |>.congr_deriv
      (by norm_num; ring)
  have hB3 : ∀ z, HasDerivAt (fun w : ℝ => lam₃ * (w - c) ^ 3 / 6) (lam₃ * (z - c) ^ 2 / 2) z :=
    fun z => ((((hasDerivAt_id' z).sub_const c).pow 3).const_mul lam₃).div_const 6 |>.congr_deriv
      (by norm_num; ring)
  -- `|F″(y) − F″(c)| ≤ λ₃ (y − c)`
  have h2 : ∀ y ∈ Icc c x, ‖F'' y - F'' c‖ ≤ lam₃ * (y - c) := by
    intro y hy
    have hseg : ∀ z ∈ Icc c y, z ∈ Icc c x := fun z hz => ⟨hz.1, hz.2.trans hy.2⟩
    have hd : ∀ z ∈ Icc c y, HasDerivAt (fun w => F'' w - F'' c) (F''' z) z := fun z hz =>
      ((hF'' z (hseg z hz)).sub_const _)
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun z => F'' z - F'' c)
      (f' := F''') (a := c) (b := y) (B := fun z => lam₃ * (z - c)) (B' := fun _ => lam₃)
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hd z (Ico_subset_Icc_self hz)).hasDerivWithinAt)
      (by simp) hB1
      (fun z hz => by
        rw [Real.norm_eq_abs]; exact hF''' z (hseg z (Ico_subset_Icc_self hz)))
      (right_mem_Icc.mpr hy.1)
    simpa using this
  -- `|F′(y) − F″(c)(y − c)| ≤ λ₃ (y − c)²/2`
  have h1 : ∀ y ∈ Icc c x, ‖F' y - F'' c * (y - c)‖ ≤ lam₃ * (y - c) ^ 2 / 2 := by
    intro y hy
    have hseg : ∀ z ∈ Icc c y, z ∈ Icc c x := fun z hz => ⟨hz.1, hz.2.trans hy.2⟩
    have hd : ∀ z ∈ Icc c y, HasDerivAt (fun w => F' w - F'' c * (w - c))
        (F'' z - F'' c) z := fun z hz =>
      ((hF' z (hseg z hz)).fun_sub (((hasDerivAt_id' z).sub_const c).const_mul (F'' c))).congr_deriv
        (by ring)
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun w => F' w - F'' c * (w - c)) (f' := fun z => F'' z - F'' c) (a := c) (b := y)
      (B := fun z => lam₃ * (z - c) ^ 2 / 2) (B' := fun z => lam₃ * (z - c))
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hd z (Ico_subset_Icc_self hz)).hasDerivWithinAt)
      (by simp [hc]) hB2
      (fun z hz => h2 z (hseg z (Ico_subset_Icc_self hz))) (right_mem_Icc.mpr hy.1)
    simpa using this
  have hd : ∀ z ∈ Icc c x, HasDerivAt (fun w => F w - F c - F'' c * (w - c) ^ 2 / 2)
      (F' z - F'' c * (z - c)) z := fun z hz =>
    (((hF z hz).sub_const (F c)).fun_sub
      ((((hasDerivAt_id' z).sub_const c).pow 2).const_mul (F'' c) |>.div_const 2)).congr_deriv
      (by norm_num; ring)
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun w => F w - F c - F'' c * (w - c) ^ 2 / 2) (f' := fun z => F' z - F'' c * (z - c))
    (a := c) (b := x) (B := fun z => lam₃ * (z - c) ^ 3 / 6) (B' := fun z => lam₃ * (z - c) ^ 2 / 2)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (Ico_subset_Icc_self hz)).hasDerivWithinAt)
    (by simp) hB3
    (fun z hz => h1 z (Ico_subset_Icc_self hz)) (right_mem_Icc.mpr hcx)
  simpa [Real.norm_eq_abs] using this

/-- Two-sided cubic Taylor bound around a stationary point. -/
theorem abs_sub_taylor_two_le {F F' F'' F''' : ℝ → ℝ} {a b c lam₃ : ℝ}
    (hF : ∀ y ∈ Icc a b, HasDerivAt F (F' y) y)
    (hF' : ∀ y ∈ Icc a b, HasDerivAt F' (F'' y) y)
    (hF'' : ∀ y ∈ Icc a b, HasDerivAt F'' (F''' y) y)
    (hF''' : ∀ y ∈ Icc a b, |F''' y| ≤ lam₃) (hc : c ∈ Icc a b) (hc0 : F' c = 0)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |F x - F c - F'' c * (x - c) ^ 2 / 2| ≤ lam₃ * |x - c| ^ 3 / 6 := by
  rcases le_total c x with hcx | hxc
  · have hsub : Icc c x ⊆ Icc a b := Icc_subset_Icc hc.1 hx.2
    have := abs_sub_taylor_two_le_forward hcx (fun y hy => hF y (hsub hy))
      (fun y hy => hF' y (hsub hy)) (fun y hy => hF'' y (hsub hy))
      (fun y hy => hF''' y (hsub hy)) hc0
    rwa [abs_of_nonneg (by linarith : 0 ≤ x - c)]
  · -- reflect: `G(y) = F(−y)`
    have hsub : ∀ y ∈ Icc (-c) (-x), -y ∈ Icc a b := fun y hy =>
      ⟨by linarith [hy.2, hx.1], by linarith [hy.1, hc.2]⟩
    have hG : ∀ y ∈ Icc (-c) (-x), HasDerivAt (fun w => F (-w)) (-F' (-y)) y := fun y hy => by
      have := (hF (-y) (hsub y hy)).comp y (hasDerivAt_neg y)
      exact this.congr_deriv (by ring)
    have hG' : ∀ y ∈ Icc (-c) (-x), HasDerivAt (fun w => -F' (-w)) (F'' (-y)) y := fun y hy => by
      have := ((hF' (-y) (hsub y hy)).comp y (hasDerivAt_neg y)).neg
      exact this.congr_deriv (by ring)
    have hG'' : ∀ y ∈ Icc (-c) (-x), HasDerivAt (fun w => F'' (-w)) (-F''' (-y)) y :=
      fun y hy => by
        have := (hF'' (-y) (hsub y hy)).comp y (hasDerivAt_neg y)
        exact this.congr_deriv (by ring)
    have := abs_sub_taylor_two_le_forward (F := fun w => F (-w)) (F' := fun w => -F' (-w))
      (F'' := fun w => F'' (-w)) (F''' := fun w => -F''' (-w)) (c := -c) (x := -x)
      (by linarith) hG hG' hG'' (fun y hy => by rw [abs_neg]; exact hF''' _ (hsub y hy))
      (by simp [hc0])
    simp only [neg_neg] at this
    rw [abs_of_nonpos (by linarith : x - c ≤ 0)]
    have e1 : (-x - -c) ^ 2 = (x - c) ^ 2 := by ring
    have e2 : (-x - -c) ^ 3 = (-(x - c)) ^ 3 := by ring
    rwa [e1, e2] at this

/-- Unimodular exponentials are `1`-Lipschitz in the phase. -/
theorem norm_cexp_mul_I_sub_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * I) - Complex.exp ((y : ℂ) * I)‖ ≤ |x - y| := by
  have h : Complex.exp ((x : ℂ) * I) - Complex.exp ((y : ℂ) * I)
      = Complex.exp ((y : ℂ) * I) * (Complex.exp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  rwa [Real.norm_eq_abs] at this

/-! ## The quadratic model on a half-line -/

/-- Half of the quadratic phase integral: `∫_0^R` is within `4/(μR)` of half the main term. -/
theorem norm_integral_quadPhase_half_sub_le {μ R : ℝ} (hμ : 0 < μ) (hR : 0 < R) :
    ‖(∫ t in (0 : ℝ)..R, GaloisForLFunctions.RHTower.quadPhase μ t)
        - (Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
            * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)) / 2‖ ≤ 4 / (μ * R) := by
  have h := GaloisForLFunctions.RHTower.norm_integral_quadPhase_sub_le hμ hR
  rw [GaloisForLFunctions.RHTower.integral_quadPhase_symm] at h
  set J := ∫ t in (0 : ℝ)..R, GaloisForLFunctions.RHTower.quadPhase μ t
  set M := Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
    * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)
  have e : J - M / 2 = (2 * J - M) / 2 := by ring
  rw [e, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  calc ‖2 * J - M‖ / 2 ≤ (8 / (μ * R)) / 2 := by gcongr
    _ = 4 / (μ * R) := by ring

/-- The quadratic phase is even, so `∫_{−R}^0 = ∫_0^R`. -/
theorem integral_quadPhase_neg_half (μ R : ℝ) :
    (∫ t in (-R)..0, GaloisForLFunctions.RHTower.quadPhase μ t)
      = ∫ t in (0 : ℝ)..R, GaloisForLFunctions.RHTower.quadPhase μ t := by
  have := intervalIntegral.integral_comp_neg (a := 0) (b := R)
    (GaloisForLFunctions.RHTower.quadPhase μ)
  simp only [GaloisForLFunctions.RHTower.quadPhase_neg, neg_zero] at this
  exact this.symm

/-- The quadratic phase integral over `[−δ₁, δ₂]` is within `4/(μδ₁) + 4/(μδ₂)` of the full main
term `√(2π/μ) e^{iπ/4}`. -/
theorem norm_integral_quadPhase_asymm_sub_le {μ δ₁ δ₂ : ℝ} (hμ : 0 < μ) (hδ₁ : 0 < δ₁)
    (hδ₂ : 0 < δ₂) :
    ‖(∫ t in (-δ₁)..δ₂, GaloisForLFunctions.RHTower.quadPhase μ t)
        - Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
            * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)‖
      ≤ 4 / (μ * δ₁) + 4 / (μ * δ₂) := by
  have hI : ∀ p q : ℝ, IntervalIntegrable (GaloisForLFunctions.RHTower.quadPhase μ) volume p q :=
    fun p q => (GaloisForLFunctions.RHTower.continuous_quadPhase μ).intervalIntegrable p q
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-δ₁) 0) (hI 0 δ₂),
    integral_quadPhase_neg_half]
  have h1 := norm_integral_quadPhase_half_sub_le hμ hδ₁
  have h2 := norm_integral_quadPhase_half_sub_le hμ hδ₂
  set M := Complex.ofReal (Real.sqrt (2 * Real.pi / μ))
    * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)
  set J₁ := ∫ t in (0 : ℝ)..δ₁, GaloisForLFunctions.RHTower.quadPhase μ t
  set J₂ := ∫ t in (0 : ℝ)..δ₂, GaloisForLFunctions.RHTower.quadPhase μ t
  have e : J₁ + J₂ - M = (J₁ - M / 2) + (J₂ - M / 2) := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-! ## The pieces of the integral -/

/-- The integral over `[c − δ₁, c + δ₂]` is `e^{iF(c)}` times the quadratic phase integral, up to
`λ₃ δ⁴/3` when `δ₁, δ₂ ≤ δ`. -/
theorem norm_integral_middle_sub_le {F F' F'' F''' : ℝ → ℝ} {a b c lam₃ δ δ₁ δ₂ : ℝ}
    (hF : ∀ y ∈ Icc a b, HasDerivAt F (F' y) y)
    (hF' : ∀ y ∈ Icc a b, HasDerivAt F' (F'' y) y)
    (hF'' : ∀ y ∈ Icc a b, HasDerivAt F'' (F''' y) y)
    (hF''' : ∀ y ∈ Icc a b, |F''' y| ≤ lam₃) (hc0 : F' c = 0)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₁δ : δ₁ ≤ δ) (hδ₂δ : δ₂ ≤ δ)
    (ha : a ≤ c - δ₁) (hb : c + δ₂ ≤ b) :
    ‖(∫ x in (c - δ₁)..(c + δ₂), Complex.exp ((F x : ℂ) * I))
        - Complex.exp ((F c : ℂ) * I)
          * ∫ u in (-δ₁)..δ₂, GaloisForLFunctions.RHTower.quadPhase (F'' c) u‖
      ≤ lam₃ * δ ^ 4 / 3 := by
  have hcI : c ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hlam₃ : 0 ≤ lam₃ := (abs_nonneg _).trans (hF''' c hcI)
  have hδ : 0 ≤ δ := hδ₁.trans hδ₁δ
  have hmem : ∀ u ∈ uIcc (-δ₁) δ₂, c + u ∈ Icc a b := by
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hFc : ContinuousOn (fun u => F (c + u)) (uIcc (-δ₁) δ₂) := fun u hu =>
    ((hF _ (hmem u hu)).continuousAt.comp
      (continuous_const_add c).continuousAt).continuousWithinAt
  have hshift : (∫ x in (c - δ₁)..(c + δ₂), Complex.exp ((F x : ℂ) * I))
      = ∫ u in (-δ₁)..δ₂, Complex.exp ((F (c + u) : ℂ) * I) := by
    rw [intervalIntegral.integral_comp_add_left (fun x => Complex.exp ((F x : ℂ) * I)) c]
    congr 1
  have hi1 : IntervalIntegrable (fun u => Complex.exp ((F (c + u) : ℂ) * I)) volume (-δ₁) δ₂ :=
    ((Complex.continuous_ofReal.comp_continuousOn hFc).mul
      continuousOn_const).cexp.intervalIntegrable
  have hi2 : IntervalIntegrable
      (fun u => Complex.exp ((F c : ℂ) * I) * GaloisForLFunctions.RHTower.quadPhase (F'' c) u)
      volume (-δ₁) δ₂ :=
    (continuous_const.mul (GaloisForLFunctions.RHTower.continuous_quadPhase _)).intervalIntegrable
      _ _
  rw [hshift, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1 hi2]
  have hbound : ∀ u ∈ Ι (-δ₁) δ₂, ‖Complex.exp ((F (c + u) : ℂ) * I)
      - Complex.exp ((F c : ℂ) * I) * GaloisForLFunctions.RHTower.quadPhase (F'' c) u‖
        ≤ lam₃ * δ ^ 3 / 6 := by
    intro u hu
    have hu' : u ∈ uIcc (-δ₁) δ₂ := uIoc_subset_uIcc hu
    have hprod : Complex.exp ((F c : ℂ) * I) * GaloisForLFunctions.RHTower.quadPhase (F'' c) u
        = Complex.exp (((F c + F'' c * u ^ 2 / 2 : ℝ) : ℂ) * I) := by
      rw [GaloisForLFunctions.RHTower.quadPhase, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hprod]
    refine (norm_cexp_mul_I_sub_le _ _).trans ?_
    have ht := abs_sub_taylor_two_le hF hF' hF'' hF''' hcI hc0 (hmem u hu')
    simp only [add_sub_cancel_left] at ht
    have e : F (c + u) - (F c + F'' c * u ^ 2 / 2) = F (c + u) - F c - F'' c * u ^ 2 / 2 := by
      ring
    rw [e]
    refine ht.trans ?_
    rw [uIcc_of_le (by linarith)] at hu'
    have hu3 : |u| ≤ δ := abs_le.mpr ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    have := pow_le_pow_left₀ (abs_nonneg u) hu3 3
    nlinarith
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  refine hI.trans ?_
  have hlen : |δ₂ - -δ₁| ≤ 2 * δ := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have h3 : 0 ≤ lam₃ * δ ^ 3 / 6 := by positivity
  calc lam₃ * δ ^ 3 / 6 * |δ₂ - -δ₁| ≤ lam₃ * δ ^ 3 / 6 * (2 * δ) :=
        mul_le_mul_of_nonneg_left hlen h3
    _ = lam₃ * δ ^ 4 / 3 := by ring

/-- A side of the stationary point: a convex phase with `|F′| ≥ m` contributes at most `3/m`. -/
theorem norm_integral_cexp_side_le {F F' F'' : ℝ → ℝ} {p q m : ℝ} (hpq : p ≤ q) (hm : 0 < m)
    (hF : ∀ y ∈ Icc p q, HasDerivAt F (F' y) y)
    (hF' : ∀ y ∈ Icc p q, HasDerivAt F' (F'' y) y)
    (hF''c : ContinuousOn F'' (Icc p q)) (hpos : ∀ y ∈ Icc p q, 0 ≤ F'' y)
    (hlow : ∀ y ∈ Icc p q, m ≤ |F' y|) :
    ‖∫ x in p..q, Complex.exp ((F x : ℂ) * I)‖ ≤ 3 / m := by
  have h := GaloisForLFunctions.HTGeometry.norm_integral_mul_exp_le_of_monotone_phase
    (g := fun _ => (1 : ℂ)) (g' := fun _ => 0) (G := 1) (V := 0) hpq hm
    (fun x _ => hasDerivAt_const x _) continuousOn_const hF hF' hF''c hpos hlow
    (fun _ _ => by simp) (by simp)
  simp only [one_mul, norm_one] at h
  refine h.trans (le_of_eq ?_)
  ring

theorem one_div_min_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 1 / min x y ≤ 1 / x + 1 / y := by
  rcases min_choice x y with h | h <;> rw [h]
  · have : 0 ≤ 1 / y := by positivity
    linarith
  · have : 0 ≤ 1 / x := by positivity
    linarith

/-! ## Stationary phase -/

/-- **Stationary phase with a cubic error.**  For a real phase on `[a, b]` with `λ₂ ≤ F″`,
`|F‴| ≤ λ₃` and an interior stationary point `F′(c) = 0`, the oscillatory integral equals
`e^{iF(c)} √(2π/F″(c)) e^{iπ/4}` up to `λ₃δ⁴/3 + 14/(λ₂δ) + 4/(λ₂(c − a)) + 4/(λ₂(b − c))`, for
every cut radius `δ > 0`. -/
theorem norm_integral_cexp_sub_stationary_le {F F' F'' F''' : ℝ → ℝ} {a b c lam₂ lam₃ δ : ℝ}
    (hF : ∀ y ∈ Icc a b, HasDerivAt F (F' y) y)
    (hF' : ∀ y ∈ Icc a b, HasDerivAt F' (F'' y) y)
    (hF'' : ∀ y ∈ Icc a b, HasDerivAt F'' (F''' y) y)
    (hlam₂ : 0 < lam₂) (hF''lb : ∀ y ∈ Icc a b, lam₂ ≤ F'' y)
    (hF''' : ∀ y ∈ Icc a b, |F''' y| ≤ lam₃) (hδ : 0 < δ)
    (hac : a < c) (hcb : c < b) (hc0 : F' c = 0) :
    ‖(∫ x in a..b, Complex.exp ((F x : ℂ) * I))
        - Complex.exp ((F c : ℂ) * I) * (Complex.ofReal (Real.sqrt (2 * Real.pi / F'' c))
            * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I))‖
      ≤ lam₃ * δ ^ 4 / 3 + 14 / (lam₂ * δ) + 4 / (lam₂ * (c - a)) + 4 / (lam₂ * (b - c)) := by
  have hcI : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  have hμ : lam₂ ≤ F'' c := hF''lb c hcI
  have hμpos : 0 < F'' c := lt_of_lt_of_le hlam₂ hμ
  set δ₁ := min δ (c - a) with hδ₁def
  set δ₂ := min δ (b - c) with hδ₂def
  have hδ₁pos : 0 < δ₁ := lt_min hδ (by linarith)
  have hδ₂pos : 0 < δ₂ := lt_min hδ (by linarith)
  have hδ₁le : δ₁ ≤ c - a := min_le_right _ _
  have hδ₂le : δ₂ ≤ b - c := min_le_right _ _
  have hFcont : ContinuousOn F (Icc a b) := fun y hy => (hF y hy).continuousAt.continuousWithinAt
  have hF''cont : ContinuousOn F'' (Icc a b) := fun y hy =>
    (hF'' y hy).continuousAt.continuousWithinAt
  have hexpcont : ContinuousOn (fun x => Complex.exp ((F x : ℂ) * I)) (Icc a b) :=
    ((Complex.continuous_ofReal.comp_continuousOn hFcont).mul continuousOn_const).cexp
  have hint : ∀ p q, p ∈ Icc a b → q ∈ Icc a b →
      IntervalIntegrable (fun x => Complex.exp ((F x : ℂ) * I)) volume p q := fun p q hp hq =>
    (hexpcont.mono (uIcc_subset_Icc hp hq)).intervalIntegrable
  have hpI : c - δ₁ ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hqI : c + δ₂ ∈ Icc a b := ⟨by linarith, by linarith⟩
  have haI : a ∈ Icc a b := ⟨le_rfl, by linarith⟩
  have hbI : b ∈ Icc a b := ⟨by linarith, le_rfl⟩
  have hsplit : (∫ x in a..b, Complex.exp ((F x : ℂ) * I))
      = (∫ x in a..(c - δ₁), Complex.exp ((F x : ℂ) * I))
        + (∫ x in (c - δ₁)..(c + δ₂), Complex.exp ((F x : ℂ) * I))
        + ∫ x in (c + δ₂)..b, Complex.exp ((F x : ℂ) * I) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _ haI hpI) (hint _ _ hpI hqI),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _ haI hqI) (hint _ _ hqI hbI)]
  -- the derivative grows at rate `λ₂`
  have hgrow : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → lam₂ * (y - x) ≤ F' y - F' x := by
    refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      (fun y hy => (hF' y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hF' y (interior_subset hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => ?_)
    rw [(hF' y (interior_subset hy)).deriv]
    exact hF''lb y (interior_subset hy)
  have hpos : ∀ y ∈ Icc a b, 0 ≤ F'' y := fun y hy => hlam₂.le.trans (hF''lb y hy)
  have hm : 0 < lam₂ * δ := mul_pos hlam₂ hδ
  have hleft : ‖∫ x in a..(c - δ₁), Complex.exp ((F x : ℂ) * I)‖ ≤ 3 / (lam₂ * δ) := by
    by_cases h : δ ≤ c - a
    · have hδ₁eq : δ₁ = δ := min_eq_left h
      have hsub : Icc a (c - δ₁) ⊆ Icc a b := Icc_subset_Icc le_rfl hpI.2
      refine norm_integral_cexp_side_le hpI.1 hm (fun y hy => hF y (hsub hy))
        (fun y hy => hF' y (hsub hy)) (hF''cont.mono hsub) (fun y hy => hpos y (hsub hy))
        (fun y hy => ?_)
      have := hgrow y (hsub hy) c hcI (by linarith [hy.2])
      rw [hc0] at this
      rw [abs_of_nonpos (by nlinarith [hy.2])]
      nlinarith [hy.2]
    · have hδ₁eq : δ₁ = c - a := min_eq_right (le_of_not_ge h)
      rw [hδ₁eq, show c - (c - a) = a by ring, intervalIntegral.integral_same, norm_zero]
      positivity
  have hright : ‖∫ x in (c + δ₂)..b, Complex.exp ((F x : ℂ) * I)‖ ≤ 3 / (lam₂ * δ) := by
    by_cases h : δ ≤ b - c
    · have hδ₂eq : δ₂ = δ := min_eq_left h
      have hsub : Icc (c + δ₂) b ⊆ Icc a b := Icc_subset_Icc hqI.1 le_rfl
      refine norm_integral_cexp_side_le hqI.2 hm (fun y hy => hF y (hsub hy))
        (fun y hy => hF' y (hsub hy)) (hF''cont.mono hsub) (fun y hy => hpos y (hsub hy))
        (fun y hy => ?_)
      have := hgrow c hcI y (hsub hy) (by linarith [hy.1])
      rw [hc0] at this
      rw [abs_of_nonneg (by nlinarith [hy.1])]
      nlinarith [hy.1]
    · have hδ₂eq : δ₂ = b - c := min_eq_right (le_of_not_ge h)
      rw [hδ₂eq, show c + (b - c) = b by ring, intervalIntegral.integral_same, norm_zero]
      positivity
  have hmid := norm_integral_middle_sub_le hF hF' hF'' hF''' hc0 hδ₁pos.le hδ₂pos.le
    (min_le_left _ _) (min_le_left _ _) hpI.1 hqI.2
  have hquad := norm_integral_quadPhase_asymm_sub_le hμpos hδ₁pos hδ₂pos
  set M := Complex.ofReal (Real.sqrt (2 * Real.pi / F'' c))
    * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)
  set E := Complex.exp ((F c : ℂ) * I)
  set Q := ∫ u in (-δ₁)..δ₂, GaloisForLFunctions.RHTower.quadPhase (F'' c) u
  set L := ∫ x in a..(c - δ₁), Complex.exp ((F x : ℂ) * I)
  set Mid := ∫ x in (c - δ₁)..(c + δ₂), Complex.exp ((F x : ℂ) * I)
  set R := ∫ x in (c + δ₂)..b, Complex.exp ((F x : ℂ) * I)
  have hE : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have e : L + Mid + R - E * M = L + (Mid - E * Q) + E * (Q - M) + R := by ring
  rw [hsplit, e]
  have hEQ : ‖E * (Q - M)‖ ≤ 4 / (F'' c * δ₁) + 4 / (F'' c * δ₂) := by
    rw [norm_mul, hE, one_mul]; exact hquad
  -- `4/(μ δᵢ) ≤ 4/(λ₂ δ) + 4/(λ₂ · gap)`
  have hq1 : 4 / (F'' c * δ₁) ≤ 4 / (lam₂ * δ) + 4 / (lam₂ * (c - a)) := by
    have h1 : 4 / (F'' c * δ₁) ≤ 4 / (lam₂ * δ₁) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hlam₂ hδ₁pos)
        (mul_le_mul_of_nonneg_right hμ hδ₁pos.le)
    have h2 := one_div_min_le hδ (by linarith : 0 < c - a)
    have e1 : 4 / (lam₂ * δ₁) = (4 / lam₂) * (1 / min δ (c - a)) := by
      rw [hδ₁def]; field_simp
    have e2 : 4 / (lam₂ * δ) + 4 / (lam₂ * (c - a)) = (4 / lam₂) * (1 / δ + 1 / (c - a)) := by
      field_simp
    rw [e2]
    refine h1.trans ?_
    rw [e1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hq2 : 4 / (F'' c * δ₂) ≤ 4 / (lam₂ * δ) + 4 / (lam₂ * (b - c)) := by
    have h1 : 4 / (F'' c * δ₂) ≤ 4 / (lam₂ * δ₂) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hlam₂ hδ₂pos)
        (mul_le_mul_of_nonneg_right hμ hδ₂pos.le)
    have h2 := one_div_min_le hδ (by linarith : 0 < b - c)
    have e1 : 4 / (lam₂ * δ₂) = (4 / lam₂) * (1 / min δ (b - c)) := by
      rw [hδ₂def]; field_simp
    have e2 : 4 / (lam₂ * δ) + 4 / (lam₂ * (b - c)) = (4 / lam₂) * (1 / δ + 1 / (b - c)) := by
      field_simp
    rw [e2]
    refine h1.trans ?_
    rw [e1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have htri : ‖L + (Mid - E * Q) + E * (Q - M) + R‖
      ≤ ‖L‖ + ‖Mid - E * Q‖ + ‖E * (Q - M)‖ + ‖R‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  have e3 : 14 / (lam₂ * δ) = 3 / (lam₂ * δ) + 3 / (lam₂ * δ) + 4 / (lam₂ * δ)
      + 4 / (lam₂ * δ) := by ring
  rw [e3]
  linarith [htri, hleft, hright, hmid, hEQ, hq1, hq2]

/-- **The crude form**, valid with the stationary point anywhere (or nowhere): both the integral and
the main term are `O(λ₂^{−1/2})`. -/
theorem norm_integral_cexp_sub_main_le_crude {F F' F'' : ℝ → ℝ} {a b c lam₂ θ : ℝ} (hab : a ≤ b)
    (hF : ∀ y ∈ uIcc a b, HasDerivAt F (F' y) y)
    (hF' : ∀ y ∈ uIcc a b, HasDerivAt F' (F'' y) y)
    (hF''c : ContinuousOn F'' (uIcc a b)) (hlam₂ : 0 < lam₂)
    (hF''lb : ∀ y ∈ uIcc a b, lam₂ ≤ F'' y) (hc : lam₂ ≤ F'' c) :
    ‖(∫ x in a..b, Complex.exp ((F x : ℂ) * I))
        - Complex.exp ((θ : ℂ) * I) * (Complex.ofReal (Real.sqrt (2 * Real.pi / F'' c))
            * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I))‖
      ≤ 9 / Real.sqrt lam₂ := by
  have h1 := norm_integral_cexp_secondDeriv hab hlam₂ hF hF' hF''c hF''lb
  have hsq : 0 < Real.sqrt lam₂ := Real.sqrt_pos.mpr hlam₂
  have hμ : 0 < F'' c := lt_of_lt_of_le hlam₂ hc
  have h2 : ‖Complex.exp ((θ : ℂ) * I) * (Complex.ofReal (Real.sqrt (2 * Real.pi / F'' c))
      * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I))‖ ≤ 3 / Real.sqrt lam₂ := by
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul, mul_one]
    have hle : Real.sqrt (2 * Real.pi / F'' c) ≤ Real.sqrt (2 * Real.pi / lam₂) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) hlam₂ hc)
    refine hle.trans ?_
    rw [Real.sqrt_div' _ hlam₂.le, div_le_div_iff_of_pos_right hsq]
    have : 2 * Real.pi ≤ 9 := by linarith [Real.pi_lt_d2]
    calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt this
      _ = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc _ ≤ ‖∫ x in a..b, Complex.exp ((F x : ℂ) * I)‖ + _ := norm_sub_le _ _
    _ ≤ 6 / Real.sqrt lam₂ + 3 / Real.sqrt lam₂ := add_le_add h1 h2
    _ = 9 / Real.sqrt lam₂ := by ring

end

end RHTower
