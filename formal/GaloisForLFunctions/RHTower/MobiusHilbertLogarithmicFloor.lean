import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw
import GaloisForLFunctions.RHTower.MoebiusMollifiedZetaField
import GaloisForLFunctions.RHTower.FiniteExponentialSumMellin
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# The Möbius Hilbert form is at least logarithmic for every large `N`

For `E_N = Σ_{m,n≤N} μ(m)μ(n)/(m+n)` there are `c > 0` and `N₀` with `E_N ≥ c log N` for all
`N ≥ N₀` (`exists_forall_mul_log_le_finiteMobiusGammaHankelEnergy_one`).  Under RH and simple zeros
`E_N` is of order `log N`, so this is the sharp order; unconditionally `E_N ≤ N^{2Θ-1+o(1)}`.

* Plancherel: `2π E_N = ∫ |Γ(1/2+iu) M_N(1/2+iu)|² du`, `M_N(s) = Σ_{n≤N} μ(n) n^{-s}`
  (`integral_norm_sq_gamma_mul_edPoly_mobCoeff_line`).
* At a critical zero `1/2 + iγ` the zero absorbs one factor `(u-γ)²`, so
  `e^{-(u-γ)²}|ζ|² ≤ B (u-γ)² |Γ|²` on the whole line (`exists_exp_mul_normSq_zeta_line_le`).
* On the line `z(z-1) = -(1/4+u²)` and `(z+3)(z-4) = -(49/4+u²)`.  Hence
  `P_N = z² mobField_N / ((z+3)(z-4))` equals `a(u)(ζM_N − 1)` with `a ∈ [1/49, 1]`, and
  `|ζM_N|² ≥ a + 2 Re P_N` (`criticalLineRatio_add_two_mul_re_le`).  Only the linear term in
  `ζM_N − 1` enters.
* The window `sinc(-iL(z-ρ₀))⁴ exp((z-ρ₀)²)` has width `1/L` on the line and grows only like
  `e^{10L}` at `Re z = 3`.  There `ζM_N − 1 = O(1/N)`, so with `L = log N/20` the shifted
  integral is `O(N^{-1/2})` (`integral_mobHilbertFloorWindowField_shift`).  A Gaussian window of
  width `w` would cost `e^{c/w²}` and reach only `w ≍ 1/√log N`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ### The complex sinc kernel -/

/-- The entire function `sin w / w`. -/
def complexSinc : ℂ → ℂ := dslope Complex.sin 0

theorem differentiable_complexSinc : Differentiable ℂ complexSinc := by
  have h := (Complex.differentiableOn_dslope (f := Complex.sin) (s := univ) (c := 0)
    Filter.univ_mem).mpr Complex.differentiable_sin.differentiableOn
  exact fun w => (h w (mem_univ w)).differentiableAt Filter.univ_mem

theorem complexSinc_ofReal (x : ℝ) : complexSinc (x : ℂ) = (Real.sinc x : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [complexSinc, dslope_same, Real.sinc_zero]
  · rw [complexSinc, dslope_of_ne _ (by exact_mod_cast hx), slope_def_field,
      Real.sinc_of_ne_zero hx]
    push_cast
    simp

theorem norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h1 : ‖Complex.exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simp; exact le_abs_self _)
  have h2 : ‖Complex.exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simp; exact neg_le_abs _)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  linarith

theorem norm_complexSinc_le_of_one_le {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖complexSinc w‖ ≤ Real.exp |w.im| := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith
  rw [complexSinc, dslope_of_ne _ hw0, slope_def_field, sub_zero, Complex.sin_zero, sub_zero,
    norm_div]
  exact (div_le_self (norm_nonneg _) hw).trans (norm_sin_le_exp_abs_im w)

theorem exists_norm_complexSinc_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ w : ℂ, ‖complexSinc w‖ ≤ C * Real.exp |w.im| := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_complexSinc.continuous.continuousOn
  refine ⟨max C₀ 1, le_max_right _ _, fun w => ?_⟩
  have he : 1 ≤ Real.exp |w.im| := Real.one_le_exp (abs_nonneg _)
  rcases le_or_gt ‖w‖ 1 with h | h
  · have hw := hC₀ w (by rwa [Metric.mem_closedBall, dist_zero_right])
    calc ‖complexSinc w‖ ≤ C₀ := hw
      _ ≤ max C₀ 1 := le_max_left _ _
      _ ≤ max C₀ 1 * Real.exp |w.im| := le_mul_of_one_le_right (by positivity) he
  · calc ‖complexSinc w‖ ≤ Real.exp |w.im| := norm_complexSinc_le_of_one_le h.le
      _ ≤ max C₀ 1 * Real.exp |w.im| :=
        le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _)

/-! ### The band-limited Gaussian window -/

/-- The window `sinc(-iL(z-ρ₀))⁴ exp((z-ρ₀)²)` at `ρ₀ = 1/2 + iγ`.  On the critical line it is
`sinc(L(u-γ))⁴ e^{-(u-γ)²}`, of width `1/L`; off the line it grows only like `e^{4L|Re z - 1/2|}`. -/
def sincGaussWindow (L γ : ℝ) (z : ℂ) : ℂ :=
  complexSinc (-I * (L : ℂ) * (z - (1 / 2 + (γ : ℂ) * I))) ^ 4 *
    Complex.exp ((z - (1 / 2 + (γ : ℂ) * I)) ^ 2)

theorem differentiable_sincGaussWindow (L γ : ℝ) : Differentiable ℂ (sincGaussWindow L γ) := by
  unfold sincGaussWindow
  have h1 : Differentiable ℂ fun z : ℂ => -I * (L : ℂ) * (z - (1 / 2 + (γ : ℂ) * I)) := by
    fun_prop
  exact ((differentiable_complexSinc.comp h1).pow 4).mul (by fun_prop)

/-- The real window on the critical line. -/
def sincGaussWeight (L γ u : ℝ) : ℝ :=
  Real.sinc (L * (u - γ)) ^ 4 * Real.exp (-(u - γ) ^ 2)

theorem sincGaussWindow_line (L γ u : ℝ) :
    sincGaussWindow L γ (1 / 2 + (u : ℂ) * I) = (sincGaussWeight L γ u : ℂ) := by
  unfold sincGaussWindow sincGaussWeight
  have h1 : (1 / 2 + (u : ℂ) * I) - (1 / 2 + (γ : ℂ) * I) = ((u - γ : ℝ) : ℂ) * I := by
    push_cast; ring
  have h2 : -I * (L : ℂ) * (((u - γ : ℝ) : ℂ) * I) = ((L * (u - γ) : ℝ) : ℂ) := by
    have : -I * (L : ℂ) * (((u - γ : ℝ) : ℂ) * I) = -(I * I) * ((L : ℂ) * ((u - γ : ℝ) : ℂ)) := by
      ring
    rw [this, I_mul_I]
    push_cast
    ring
  have h3 : (((u - γ : ℝ) : ℂ) * I) ^ 2 = ((-(u - γ) ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]
    push_cast
    ring
  rw [h1, h2, h3, complexSinc_ofReal, ← Complex.ofReal_exp]
  push_cast
  ring

theorem sincGaussWeight_nonneg (L γ u : ℝ) : 0 ≤ sincGaussWeight L γ u := by
  unfold sincGaussWeight
  have : 0 ≤ Real.sinc (L * (u - γ)) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    positivity
  positivity

/-- On the strip `1/2 ≤ Re z ≤ 3` the window is a Gaussian in `Im z` of height `e^{10L}`. -/
theorem norm_sincGaussWindow_le {C L γ : ℝ}
    (hC : ∀ w : ℂ, ‖complexSinc w‖ ≤ C * Real.exp |w.im|) (hL : 0 ≤ L) {z : ℂ}
    (hz : 1 / 2 ≤ z.re) (hz' : z.re ≤ 3) :
    ‖sincGaussWindow L γ z‖ ≤
      C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * Real.exp (-(z.im - γ) ^ 2) := by
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have := Real.exp_pos |(0 : ℂ).im|
    nlinarith [norm_nonneg (complexSinc 0)]
  unfold sincGaussWindow
  set w : ℂ := z - (1 / 2 + (γ : ℂ) * I) with hw
  have hwre : w.re = z.re - 1 / 2 := by simp [hw]
  have hwim : w.im = z.im - γ := by simp [hw]
  have harg : |(-I * (L : ℂ) * w).im| ≤ 5 / 2 * L := by
    have : (-I * (L : ℂ) * w).im = -(L * w.re) := by simp
    rw [this, abs_neg, abs_mul, abs_of_nonneg hL, hwre, abs_of_nonneg (by linarith)]
    nlinarith
  have hs : ‖complexSinc (-I * (L : ℂ) * w)‖ ≤ C * Real.exp (5 / 2 * L) :=
    (hC _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hC0)
  have hs4 : ‖complexSinc (-I * (L : ℂ) * w)‖ ^ 4 ≤ C ^ 4 * Real.exp (10 * L) := by
    calc ‖complexSinc (-I * (L : ℂ) * w)‖ ^ 4 ≤ (C * Real.exp (5 / 2 * L)) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) hs 4
      _ = C ^ 4 * Real.exp (10 * L) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; norm_num; ring
  have he : ‖Complex.exp (w ^ 2)‖ ≤ Real.exp (25 / 4) * Real.exp (-(z.im - γ) ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [sq]
    rw [this, hwre, hwim]
    nlinarith
  rw [norm_mul, norm_pow]
  calc ‖complexSinc (-I * (L : ℂ) * w)‖ ^ 4 * ‖Complex.exp (w ^ 2)‖
      ≤ (C ^ 4 * Real.exp (10 * L)) * (Real.exp (25 / 4) * Real.exp (-(z.im - γ) ^ 2)) :=
        mul_le_mul hs4 he (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-! ### Elementary sinc bounds -/

theorem sq_mul_sinc_pow_four_le {L t : ℝ} (hL : 0 < L) (ht : t ≠ 0) :
    L ^ 2 * Real.sinc (L * t) ^ 4 ≤ 1 / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := by positivity
  have hs4 : Real.sinc (L * t) ^ 4 = |Real.sinc (L * t)| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rcases le_or_gt ((L * t) ^ 2) 1 with hx | hx
  · have h1 : |Real.sinc (L * t)| ^ 4 ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)
    rw [hs4, le_div_iff₀ ht2]
    have : L ^ 2 * t ^ 2 ≤ 1 := by rw [← mul_pow]; exact hx
    calc L ^ 2 * |Real.sinc (L * t)| ^ 4 * t ^ 2 = |Real.sinc (L * t)| ^ 4 * (L ^ 2 * t ^ 2) := by
          ring
      _ ≤ 1 * 1 := mul_le_mul h1 this (by positivity) zero_le_one
      _ = 1 := by ring
  · have hx0 : L * t ≠ 0 := mul_ne_zero hL.ne' ht
    have habs : |Real.sinc (L * t)| ≤ 1 / |L * t| := by
      rw [Real.sinc_of_ne_zero hx0, abs_div]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
    have hpos : 0 < |L * t| := abs_pos.mpr hx0
    have h4 : |Real.sinc (L * t)| ^ 4 ≤ 1 / ((L * t) ^ 2) ^ 2 := by
      calc |Real.sinc (L * t)| ^ 4 ≤ (1 / |L * t|) ^ 4 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 4
        _ = 1 / ((L * t) ^ 2) ^ 2 := by
            rw [div_pow, one_pow, ← sq_abs (L * t), ← pow_mul]
    rw [hs4]
    calc L ^ 2 * |Real.sinc (L * t)| ^ 4 ≤ L ^ 2 * (1 / ((L * t) ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 1 / t ^ 2 * (1 / (L * t) ^ 2) := by field_simp
      _ ≤ 1 / t ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]
          exact hx.le
      _ = 1 / t ^ 2 := mul_one _

theorem five_sixths_le_sinc {x : ℝ} (hx : |x| ≤ 1) : 5 / 6 ≤ Real.sinc x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Real.sinc_zero]; norm_num
  have hpos : 0 < |x| := abs_pos.mpr hx0
  have heven : Real.sinc x = Real.sinc |x| := by
    rcases abs_choice x with h | h
    · rw [h]
    · rw [h, Real.sinc_neg]
  rw [heven, Real.sinc_of_ne_zero hpos.ne', le_div_iff₀ hpos]
  have h := Real.sin_gt_sub_cube hpos
  have hx2 : |x| ^ 3 ≤ |x| := by
    calc |x| ^ 3 = |x| * |x| ^ 2 := by ring
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx) hpos.le
      _ = |x| := mul_one _
  linarith

/-! ### The Gamma weight dominates zeta near a critical zero -/

theorem one_half_add_mul_I_ne_one (u : ℝ) : (1 / 2 + (u : ℂ) * I) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem differentiable_riemannZeta_half_line :
    Differentiable ℝ fun u : ℝ => riemannZeta (1 / 2 + (u : ℂ) * I) := by
  intro u
  have hz : DifferentiableAt ℂ riemannZeta (1 / 2 + (u : ℂ) * I) :=
    differentiableAt_riemannZeta (one_half_add_mul_I_ne_one u)
  have hl : DifferentiableAt ℝ (fun u : ℝ => (1 / 2 + (u : ℂ) * I)) u := by fun_prop
  exact (hz.restrictScalars ℝ).comp u hl

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- **Local domination at a critical zero.**  If `ζ(1/2 + iγ) = 0`, then
`e^{-(u-γ)²} |ζ(1/2+iu)|² ≤ B (u-γ)² |Γ(1/2+iu)|²` on the whole critical line: near `γ` the zero
supplies the factor `(u-γ)²`, far away the Gaussian beats `|ζ|² cosh(πu)`. -/
theorem exists_exp_mul_normSq_zeta_line_le {γ : ℝ}
    (hζ : riemannZeta (1 / 2 + (γ : ℂ) * I) = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ,
      Real.exp (-(u - γ) ^ 2) * ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2 ≤
        B * ((u - γ) ^ 2 * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2) := by
  set g : ℝ → ℂ := fun u => riemannZeta (1 / 2 + (u : ℂ) * I) with hg
  have hgd : Differentiable ℝ g := differentiable_riemannZeta_half_line
  set h : ℝ → ℂ := dslope g γ with hh
  have hcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro u
    rcases eq_or_ne u γ with rfl | hne
    · exact continuousAt_dslope_same.mpr (hgd u)
    · exact (continuousAt_dslope_of_ne hne).mpr (hgd u).continuousAt
  have hgh : ∀ u, g u = ((u - γ : ℝ) : ℂ) * h u := by
    intro u
    have := sub_smul_dslope g γ u
    rw [show g γ = 0 from hζ, sub_zero] at this
    rw [← this, Complex.real_smul]
  have hnorm : ∀ u, ‖g u‖ ^ 2 = (u - γ) ^ 2 * ‖h u‖ ^ 2 := by
    intro u
    rw [hgh u, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  set r : ℝ → ℝ := fun u => Real.exp (-(u - γ) ^ 2) * ‖h u‖ ^ 2 * Real.cosh (Real.pi * u)
    with hr
  have hrc : Continuous r := by
    rw [hr]
    exact ((Real.continuous_exp.comp (by fun_prop)).mul ((continuous_norm.comp hcont).pow 2)).mul
      (Real.continuous_cosh.comp (by fun_prop))
  set R : ℝ := |γ| + 2 with hR
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hrc.continuousOn
  set B₂ : ℝ := 25 * 720 * Real.exp 8 * Real.exp (5 * |γ| + 25 / 4) with hB₂
  have hB₂0 : 0 < B₂ := by positivity
  have hfar : ∀ u, R ≤ |u| → r u ≤ B₂ := by
    intro u hu
    have hγu : |u| ≤ |γ| + |u - γ| := by
      have := abs_sub_abs_le_abs_sub u γ
      linarith
    have ht2 : 2 ≤ |u - γ| := by rw [hR] at hu; linarith
    have hu2 : 2 ≤ |u| := by rw [hR] at hu; linarith [abs_nonneg γ]
    -- zeta on the line
    have hzeta : ‖g u‖ ≤ 5 * Real.exp 2 * (4 + |u|) ^ 3 := by
      set z : ℂ := 1 / 2 + (u : ℂ) * I with hz
      have hzre : z.re = 1 / 2 := by simp [hz]
      have hzim : z.im = u := by simp [hz]
      have hE := norm_zetaEntire_strip_le (z := z) (by rw [hzre]; norm_num)
        (by rw [hzre]; norm_num) (by rw [hzim]; exact hu2)
      rw [zetaEntire_eq (one_half_add_mul_I_ne_one u), norm_mul, hzim] at hE
      have hz1 : 1 ≤ ‖z - 1‖ := by
        have : |(z - 1).im| ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
        have him : (z - 1).im = u := by simp [hz]
        rw [him] at this
        linarith
      have hζ0 : 0 ≤ ‖riemannZeta z‖ := norm_nonneg _
      calc ‖g u‖ = ‖riemannZeta z‖ := rfl
        _ ≤ ‖z - 1‖ * ‖riemannZeta z‖ := le_mul_of_one_le_left hζ0 hz1
        _ ≤ _ := hE
    have hhg : ‖h u‖ ≤ ‖g u‖ := by
      have h1 : ‖g u‖ = |u - γ| * ‖h u‖ := by
        rw [hgh u, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [h1]
      nlinarith [norm_nonneg (h u)]
    have hh2 : ‖h u‖ ^ 2 ≤ 25 * Real.exp 4 * (4 + |u|) ^ 6 := by
      have h0 : 0 ≤ ‖h u‖ := norm_nonneg _
      calc ‖h u‖ ^ 2 ≤ (5 * Real.exp 2 * (4 + |u|) ^ 3) ^ 2 :=
            pow_le_pow_left₀ h0 (hhg.trans hzeta) 2
        _ = 25 * Real.exp 4 * (4 + |u|) ^ 6 := by
            rw [mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]; norm_num
    have hpow : (4 + |u|) ^ 6 ≤ 720 * Real.exp (4 + |u|) := by
      have := Real.pow_div_factorial_le_exp (x := 4 + |u|) (by positivity) 6
      norm_num [Nat.factorial] at this
      linarith
    have hcosh : Real.cosh (Real.pi * u) ≤ Real.exp (4 * |u|) := by
      refine (cosh_le_exp_abs _).trans (Real.exp_le_exp.mpr ?_)
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_right Real.pi_lt_four.le (abs_nonneg u)
    have hexp : -(u - γ) ^ 2 + (4 + |u|) + 4 * |u| ≤ 4 + (5 * |γ| + 25 / 4) := by
      nlinarith [sq_abs (u - γ), sq_nonneg (|u - γ| - 5 / 2)]
    calc r u = Real.exp (-(u - γ) ^ 2) * ‖h u‖ ^ 2 * Real.cosh (Real.pi * u) := rfl
      _ ≤ Real.exp (-(u - γ) ^ 2) * (25 * Real.exp 4 * (720 * Real.exp (4 + |u|))) *
            Real.exp (4 * |u|) := by
          gcongr
          exact hh2.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = 25 * 720 * Real.exp 4 *
            Real.exp (-(u - γ) ^ 2 + (4 + |u|) + 4 * |u|) := by
          rw [Real.exp_add (-(u - γ) ^ 2 + (4 + |u|)), Real.exp_add (-(u - γ) ^ 2)]; ring
      _ ≤ 25 * 720 * Real.exp 4 * Real.exp (4 + (5 * |γ| + 25 / 4)) := by
          gcongr
      _ = B₂ := by
          rw [hB₂, Real.exp_add 4 (5 * |γ| + 25 / 4),
            show Real.exp 8 = Real.exp 4 * Real.exp 4 by rw [← Real.exp_add]; norm_num]
          ring
  set M : ℝ := max B₁ B₂ with hM
  have hM0 : 0 < M := lt_of_lt_of_le hB₂0 (le_max_right _ _)
  have hall : ∀ u, r u ≤ M := by
    intro u
    rcases le_or_gt R |u| with hu | hu
    · exact (hfar u hu).trans (le_max_right _ _)
    · have hmem : u ∈ Icc (-R) R := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
      have := hB₁ u hmem
      rw [Real.norm_eq_abs] at this
      exact ((le_abs_self _).trans this).trans (le_max_left _ _)
  refine ⟨M / Real.pi + 1, by positivity, fun u => ?_⟩
  have hΓ := GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq u
  have hc : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
  have hru := hall u
  have hkey : Real.exp (-(u - γ) ^ 2) * ‖h u‖ ^ 2 ≤ M / Real.pi * (Real.pi / Real.cosh (Real.pi * u)) := by
    rw [div_mul_div_cancel₀ Real.pi_pos.ne', le_div_iff₀ hc]
    exact hru
  have ht2 : 0 ≤ (u - γ) ^ 2 := sq_nonneg _
  have hΓ0 : 0 ≤ ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 := by positivity
  calc Real.exp (-(u - γ) ^ 2) * ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2
      = (u - γ) ^ 2 * (Real.exp (-(u - γ) ^ 2) * ‖h u‖ ^ 2) := by
        rw [show ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2 = ‖g u‖ ^ 2 from rfl, hnorm u]; ring
    _ ≤ (u - γ) ^ 2 * (M / Real.pi * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2) := by
        rw [hΓ]; exact mul_le_mul_of_nonneg_left hkey ht2
    _ ≤ (u - γ) ^ 2 * ((M / Real.pi + 1) * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2) := by
        gcongr; linarith
    _ = (M / Real.pi + 1) * ((u - γ) ^ 2 * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2) := by ring

/-! ### Plancherel on the critical line -/

theorem mobiusDiscreteLaplaceFiniteSection_eq_expDecaySum (N : ℕ) :
    mobiusDiscreteLaplaceFiniteSection N = fun x : ℝ =>
      ((expDecaySum (Finset.range N) shiftedMobiusRealCoefficient (fun n => (n : ℝ) + 1) x : ℝ)
        : ℂ) := by
  funext x
  rw [mobiusDiscreteLaplaceFiniteSection_eq_finiteMobiusLaplacePencil]
  unfold finiteMobiusLaplacePencil finiteRealLaplacePencil expDecaySum
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring_nf

/-- The Mellin transform of the finite Möbius--Laplace section is `Γ(s) Σ_{n≤N} μ(n) n^{-s}`. -/
theorem mellin_mobiusDiscreteLaplaceFiniteSection (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (mobiusDiscreteLaplaceFiniteSection N) s =
      Complex.Gamma s * edPoly mobCoeff (Finset.Icc 1 N) s := by
  rw [mobiusDiscreteLaplaceFiniteSection_eq_expDecaySum,
    mellin_expDecaySum _ _ _ (fun n _ => by positivity) hs]
  congr 1
  unfold edPoly
  have hterm : ∀ n ∈ Finset.range N,
      ((shiftedMobiusRealCoefficient n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
        mobCoeff (n + 1) * (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) := by
    intro n _
    unfold shiftedMobiusRealCoefficient mobCoeff
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun k => mobCoeff k * (((k : ℕ) : ℝ) : ℂ) ^ (-s)), zero_add,
    Finset.Ico_add_one_right_eq_Icc]

theorem integrable_logMellinLineSource_mobiusDiscreteLaplaceFiniteSection (N : ℕ) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Integrable (logMellinLineSource (mobiusDiscreteLaplaceFiniteSection N) sigma) := by
  rw [mobiusDiscreteLaplaceFiniteSection_eq_expDecaySum]
  refine integrable_logMellinLineSource_of_exp_bound (C := ∑ n ∈ Finset.range N,
    |shiftedMobiusRealCoefficient n|) (a := 1) hsigma one_pos
    (Complex.continuous_ofReal.comp (continuous_expDecaySum _ _ _)) fun x hx => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_expDecaySum_le _ _ _ (fun n _ => by simp) hx.le

/-- **Plancherel for finite Möbius sections.**
`∫ |Γ(1/2+iu) Σ_{n≤N} μ(n) n^{-1/2-iu}|² du = 2π E_N(1)`. -/
theorem integral_norm_sq_gamma_mul_edPoly_mobCoeff_line (N : ℕ) :
    ∫ u : ℝ, ‖Complex.Gamma (1 / 2 + (u : ℂ) * I) *
        edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)‖ ^ 2 =
      2 * Real.pi * finiteMobiusGammaHankelEnergy N 1 := by
  have h1 := integrable_logMellinLineSource_mobiusDiscreteLaplaceFiniteSection N
    (sigma := 1 / 2) (by norm_num)
  have h2 : MemLp (logMellinLineSource (mobiusDiscreteLaplaceFiniteSection N) (1 / 2)) 2 volume :=
    mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two N (by norm_num)
  have hP := integral_norm_sq_mellin_line_eq_logMellinLineSource h1 h2
  have hE := integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource N
    (sigma := 1 / 2) (by norm_num)
  have hm : ∀ y : ℝ, mellin (mobiusDiscreteLaplaceFiniteSection N) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) =
      Complex.Gamma (1 / 2 + (y : ℂ) * I) * edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (y : ℂ) * I) := by
    intro y
    rw [mellin_mobiusDiscreteLaplaceFiniteSection N (by simp)]
    push_cast
    ring_nf
  simp_rw [hm] at hP
  rw [hP]
  have hE' : (∫ u : ℝ, ‖logMellinLineSource (mobiusDiscreteLaplaceFiniteSection N) (1 / 2) u‖ ^ 2) =
      finiteMobiusGammaHankelEnergy N 1 := by
    rw [show finiteMobiusGammaHankelEnergy N 1 = finiteMobiusGammaHankelEnergy N (2 * (1 / 2)) by
      norm_num, ← hE]
    rfl
  rw [hE']

/-! ### The holomorphic lower-bound field -/

/-- `P_N(z) = z² · mobField_N(z) / ((z+3)(z-4))`.  On the critical line it is
`a(u) (ζ M_N − 1)` with `a(u) = (1/4+u²)/(49/4+u²) ∈ [1/49, 1]`, and it is holomorphic on
`1/2 ≤ Re z ≤ 3`. -/
def mobHilbertFloorField (N : ℕ) (z : ℂ) : ℂ := z ^ 2 * mobField N z / ((z + 3) * (z - 4))

theorem differentiableOn_mobHilbertFloorField (N : ℕ) :
    DifferentiableOn ℂ (mobHilbertFloorField N)
      (GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2) 3) := by
  intro z hz
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hz
  have hre : 0 < z.re := by linarith [hz.1]
  have hden : (z + 3) * (z - 4) ≠ 0 := by
    apply mul_ne_zero
    · intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hz.1]
    · intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hz.2]
  have hFa : DifferentiableAt ℂ (mobField N) z :=
    (differentiableOn_mobField N z hre).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre)
  exact (((differentiableAt_id.pow 2).mul hFa).div (by fun_prop) hden).differentiableWithinAt

/-- The weight `a(u) = (1/4 + u²)/(49/4 + u²)`. -/
def criticalLineRatio (u : ℝ) : ℝ := (1 / 4 + u ^ 2) / (49 / 4 + u ^ 2)

theorem criticalLineRatio_le_one (u : ℝ) : criticalLineRatio u ≤ 1 := by
  unfold criticalLineRatio
  rw [div_le_one (by positivity)]
  linarith

theorem inv_fortyNine_le_criticalLineRatio (u : ℝ) : 1 / 49 ≤ criticalLineRatio u := by
  unfold criticalLineRatio
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg u]

theorem mobHilbertFloorField_line (N : ℕ) (u : ℝ) :
    mobHilbertFloorField N (1 / 2 + (u : ℂ) * I) =
      (criticalLineRatio u : ℂ) * (riemannZeta (1 / 2 + (u : ℂ) * I) *
        edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I) - 1) := by
  set z : ℂ := 1 / 2 + (u : ℂ) * I with hz
  have hz0 : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hz] at this
  have hz1 : z ≠ 1 := one_half_add_mul_I_ne_one u
  have hA : z * (z - 1) = -((1 / 4 + u ^ 2 : ℝ) : ℂ) := by
    have : z * (z - 1) = -(1 / 4 : ℂ) + (u : ℂ) ^ 2 * I ^ 2 := by rw [hz]; ring
    rw [this, I_sq]
    push_cast
    ring
  have hB : (z + 3) * (z - 4) = -((49 / 4 + u ^ 2 : ℝ) : ℂ) := by
    have : (z + 3) * (z - 4) = -(49 / 4 : ℂ) + (u : ℂ) ^ 2 * I ^ 2 := by rw [hz]; ring
    rw [this, I_sq]
    push_cast
    ring
  have hd : ((49 / 4 + u ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (49 / 4 + u ^ 2 : ℝ) ≠ 0 by positivity)
  unfold mobHilbertFloorField
  rw [mobField_eq hz0 hz1]
  unfold mobMollifiedError
  set E : ℂ := riemannZeta z * edPoly mobCoeff (Finset.Icc 1 N) z - 1
  have key : z ^ 2 * ((z - 1) / z * E) = z * (z - 1) * E := by
    field_simp
  rw [key, hA, hB, criticalLineRatio]
  push_cast
  field_simp

/-- **Pointwise lower bound on the critical line.**  With `A = ζ M_N`,
`|A|² ≥ a (2 Re A − 1) = a + 2 Re P_N`. -/
theorem criticalLineRatio_add_two_mul_re_le (N : ℕ) (u : ℝ) :
    criticalLineRatio u + 2 * (mobHilbertFloorField N (1 / 2 + (u : ℂ) * I)).re ≤
      ‖riemannZeta (1 / 2 + (u : ℂ) * I) *
        edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)‖ ^ 2 := by
  rw [mobHilbertFloorField_line]
  set A : ℂ := riemannZeta (1 / 2 + (u : ℂ) * I) *
    edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)
  set a : ℝ := criticalLineRatio u with ha
  have ha0 : 0 ≤ a := le_trans (by norm_num) (inv_fortyNine_le_criticalLineRatio u)
  have ha1 : a ≤ 1 := criticalLineRatio_le_one u
  have hre : ((a : ℂ) * (A - 1)).re = a * (A.re - 1) := by simp
  rw [hre]
  have h1 : 2 * A.re - 1 ≤ ‖A‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (A.re - 1), sq_nonneg A.im]
  have h2 : a * (2 * A.re - 1) ≤ a * ‖A‖ ^ 2 := mul_le_mul_of_nonneg_left h1 ha0
  have h3 : a * ‖A‖ ^ 2 ≤ ‖A‖ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) ha1
  linarith

/-- On the strip the rational prefactor of `P_N` is at most `10`. -/
theorem norm_mobHilbertFloorField_le (N : ℕ) {z : ℂ} (hz : 1 / 2 ≤ z.re) (hz' : z.re ≤ 3) :
    ‖mobHilbertFloorField N z‖ ≤ 10 * ‖mobField N z‖ := by
  unfold mobHilbertFloorField
  have hp : z.re + 3 ≤ ‖z + 3‖ := by
    have := Complex.abs_re_le_norm (z + 3)
    simp at this
    linarith [le_abs_self (z.re + 3)]
  have hp' : |z.im| ≤ ‖z + 3‖ := by
    have := Complex.abs_im_le_norm (z + 3)
    simpa using this
  have hq : 4 - z.re ≤ ‖z - 4‖ := by
    have := Complex.abs_re_le_norm (z - 4)
    simp at this
    linarith [neg_abs_le (z.re - 4)]
  have hq' : |z.im| ≤ ‖z - 4‖ := by
    have := Complex.abs_im_le_norm (z - 4)
    simpa using this
  have hpq : 0 < ‖z + 3‖ * ‖z - 4‖ := by
    have : 0 < ‖z + 3‖ := by linarith
    have : 0 < ‖z - 4‖ := by linarith
    positivity
  have hz2 : ‖z‖ ^ 2 ≤ 10 * (‖z + 3‖ * ‖z - 4‖) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have him : z.im * z.im ≤ ‖z + 3‖ * ‖z - 4‖ := by
      have := mul_le_mul hp' hq' (abs_nonneg _) (by linarith [abs_nonneg z.im])
      nlinarith [abs_mul_abs_self z.im]
    have hone : 1 ≤ ‖z + 3‖ * ‖z - 4‖ := by nlinarith
    nlinarith
  rw [norm_div, norm_mul, norm_mul, norm_pow, div_le_iff₀ hpq]
  calc ‖z‖ ^ 2 * ‖mobField N z‖ ≤ (10 * (‖z + 3‖ * ‖z - 4‖)) * ‖mobField N z‖ :=
        mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)
    _ = 10 * ‖mobField N z‖ * (‖z + 3‖ * ‖z - 4‖) := by ring

theorem one_add_abs_mul_exp_neg_sq_le (y γ : ℝ) :
    (1 + |y|) * Real.exp (-(y - γ) ^ 2) ≤ (2 + |γ|) * Real.exp (-(y - γ) ^ 2 / 2) := by
  set x : ℝ := y - γ with hx
  have hy : |y| ≤ |γ| + |x| := by
    have := abs_sub_abs_le_abs_sub y γ
    linarith
  have hsplit : Real.exp (-x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hxe : |x| * Real.exp (-x ^ 2 / 2) ≤ 1 := by
    have h1 : |x| ≤ Real.exp (x ^ 2 / 2) := by
      have := Real.add_one_le_exp (x ^ 2 / 2)
      nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
    have h2 : Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc |x| * Real.exp (-x ^ 2 / 2) ≤ Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := h2
  have he1 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hE0 : 0 ≤ Real.exp (-x ^ 2 / 2) := (Real.exp_pos _).le
  calc (1 + |y|) * Real.exp (-x ^ 2) ≤ (1 + |γ| + |x|) * Real.exp (-x ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = (1 + |γ|) * Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) +
          (|x| * Real.exp (-x ^ 2 / 2)) * Real.exp (-x ^ 2 / 2) := by rw [hsplit]; ring
    _ ≤ (1 + |γ|) * Real.exp (-x ^ 2 / 2) * 1 + 1 * Real.exp (-x ^ 2 / 2) := by
        gcongr
    _ = (2 + |γ|) * Real.exp (-x ^ 2 / 2) := by ring

/-! ### The windowed field and the shift to `Re z = 3` -/

/-- The window times the lower-bound field. -/
def mobHilbertFloorWindowField (N : ℕ) (L γ : ℝ) (z : ℂ) : ℂ :=
  sincGaussWindow L γ z * mobHilbertFloorField N z

theorem differentiableOn_mobHilbertFloorWindowField (N : ℕ) (L γ : ℝ) :
    DifferentiableOn ℂ (mobHilbertFloorWindowField N L γ)
      (GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2) 3) :=
  (differentiable_sincGaussWindow L γ).differentiableOn.mul
    (differentiableOn_mobHilbertFloorField N)

theorem norm_mobHilbertFloorWindowField_le {C CF L γ : ℝ}
    (hC : ∀ w : ℂ, ‖complexSinc w‖ ≤ C * Real.exp |w.im|)
    (hCF0 : 0 ≤ CF)
    (hF : ∀ X : ℕ, 1 ≤ X → ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 →
      ‖mobField X z‖ ≤ CF * X * (1 + |z.im|))
    {N : ℕ} (hN : 1 ≤ N) (hL : 0 ≤ L) {z : ℂ} (hz : 1 / 2 ≤ z.re) (hz' : z.re ≤ 3) :
    ‖mobHilbertFloorWindowField N L γ z‖ ≤
      C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (10 * CF * N * (2 + |γ|)) *
        Real.exp (-(z.im - γ) ^ 2 / 2) := by
  unfold mobHilbertFloorWindowField
  rw [norm_mul]
  have hW := norm_sincGaussWindow_le (γ := γ) hC hL hz hz'
  have hP := (norm_mobHilbertFloorField_le N hz hz').trans
    (mul_le_mul_of_nonneg_left (hF N hN z (by linarith) hz') (by norm_num))
  have hK : 0 ≤ C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) := by
    have : 0 ≤ C ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; positivity
    positivity
  have hG := one_add_abs_mul_exp_neg_sq_le z.im γ
  calc ‖sincGaussWindow L γ z‖ * ‖mobHilbertFloorField N z‖
      ≤ (C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * Real.exp (-(z.im - γ) ^ 2)) *
          (10 * (CF * N * (1 + |z.im|))) :=
        mul_le_mul hW hP (norm_nonneg _) (by positivity)
    _ = C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (10 * CF * N) *
          ((1 + |z.im|) * Real.exp (-(z.im - γ) ^ 2)) := by ring
    _ ≤ C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (10 * CF * N) *
          ((2 + |γ|) * Real.exp (-(z.im - γ) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
    _ = _ := by ring

/-- On the right edge the field is `O(1/N)` times the window. -/
theorem norm_mobHilbertFloorWindowField_three_le {C L γ : ℝ}
    (hC : ∀ w : ℂ, ‖complexSinc w‖ ≤ C * Real.exp |w.im|) {N : ℕ} (hN : 1 ≤ N) (hL : 0 ≤ L)
    (y : ℝ) :
    ‖mobHilbertFloorWindowField N L γ ((3 : ℂ) + (y : ℂ) * I)‖ ≤
      C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (20 / N) * Real.exp (-(y - γ) ^ 2) := by
  have hre : ((3 : ℂ) + (y : ℂ) * I).re = 3 := by simp
  have him : ((3 : ℂ) + (y : ℂ) * I).im = y := by simp
  unfold mobHilbertFloorWindowField
  rw [norm_mul]
  have hW := norm_sincGaussWindow_le (γ := γ) hC hL (z := (3 : ℂ) + (y : ℂ) * I)
    (by rw [hre]; norm_num) (by rw [hre])
  rw [him] at hW
  have hP := (norm_mobHilbertFloorField_le N (z := (3 : ℂ) + (y : ℂ) * I)
    (by rw [hre]; norm_num) (by rw [hre])).trans
    (mul_le_mul_of_nonneg_left (norm_mobField_three_le hN y) (by norm_num))
  calc ‖sincGaussWindow L γ ((3 : ℂ) + (y : ℂ) * I)‖ *
        ‖mobHilbertFloorField N ((3 : ℂ) + (y : ℂ) * I)‖
      ≤ (C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * Real.exp (-(y - γ) ^ 2)) *
          (10 * (2 / N)) := mul_le_mul hW hP (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem tendsto_exp_neg_sub_sq_half (γ : ℝ) :
    Tendsto (fun T : ℝ => Real.exp (-(T - γ) ^ 2 / 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => -T + (γ + 1 / 2)) atTop atBot :=
    tendsto_atBot_add_const_right _ _ tendsto_neg_atTop_atBot
  have h2 : Tendsto (fun T : ℝ => -(T - γ) ^ 2 / 2) atTop atBot :=
    tendsto_atBot_mono (fun T => by nlinarith [sq_nonneg (T - γ - 1)]) h1
  exact Real.tendsto_exp_atBot.comp h2

theorem integrable_exp_neg_sub_sq_half (γ : ℝ) :
    Integrable fun y : ℝ => Real.exp (-(y - γ) ^ 2 / 2) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).comp_sub_right γ
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring_nf

theorem integrable_exp_neg_sub_sq (γ : ℝ) :
    Integrable fun y : ℝ => Real.exp (-(y - γ) ^ 2) := by
  have h := (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).comp_sub_right γ
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring_nf

theorem integral_exp_neg_sub_sq (γ : ℝ) :
    ∫ y : ℝ, Real.exp (-(y - γ) ^ 2) = Real.sqrt Real.pi := by
  have h := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => Real.exp (-1 * y ^ 2)) γ
  rw [integral_gaussian, div_one] at h
  rw [← h]
  congr 1
  funext y
  ring_nf

/-- Continuity of the field along a vertical line inside the strip. -/
theorem continuous_mobHilbertFloorWindowField_line (N : ℕ) (L γ : ℝ) {c : ℝ}
    (hc : 1 / 2 ≤ c) (hc' : c ≤ 3) :
    Continuous fun y : ℝ => mobHilbertFloorWindowField N L γ ((c : ℂ) + (y : ℂ) * I) := by
  refine (differentiableOn_mobHilbertFloorWindowField N L γ).continuousOn.comp_continuous
    (by fun_prop) fun y => ?_
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip]
  constructor <;> simp <;> linarith

/-- **Contour shift.**  The windowed field has the same integral on `Re z = 1/2` and `Re z = 3`. -/
theorem integral_mobHilbertFloorWindowField_shift {C CF L γ : ℝ}
    (hC : ∀ w : ℂ, ‖complexSinc w‖ ≤ C * Real.exp |w.im|)
    (hCF0 : 0 ≤ CF)
    (hF : ∀ X : ℕ, 1 ≤ X → ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 →
      ‖mobField X z‖ ≤ CF * X * (1 + |z.im|))
    {N : ℕ} (hN : 1 ≤ N) (hL : 0 ≤ L) :
    Integrable (fun y : ℝ => mobHilbertFloorWindowField N L γ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) ∧
      (∫ y : ℝ, mobHilbertFloorWindowField N L γ (((3 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ, mobHilbertFloorWindowField N L γ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  set K : ℝ := C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (10 * CF * N * (2 + |γ|)) with hK
  have hbound : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 →
      ‖mobHilbertFloorWindowField N L γ z‖ ≤ K * Real.exp (-(z.im - γ) ^ 2 / 2) :=
    fun z hz hz' => norm_mobHilbertFloorWindowField_le hC hCF0 hF hN hL hz hz'
  have hline : ∀ c : ℝ, 1 / 2 ≤ c → c ≤ 3 →
      Integrable fun y : ℝ => mobHilbertFloorWindowField N L γ ((c : ℂ) + (y : ℂ) * I) := by
    intro c hc hc'
    refine ((integrable_exp_neg_sub_sq_half γ).const_mul K).mono'
      (continuous_mobHilbertFloorWindowField_line N L γ hc hc').aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have := hbound ((c : ℂ) + (y : ℂ) * I) (by simp; linarith) (by simp [hc'])
    simpa using this
  have hhor : ∀ hgt : ℝ → ℝ, Tendsto (fun T => K * Real.exp (-(hgt T - γ) ^ 2 / 2)) atTop (𝓝 0) →
      Tendsto (fun T : ℝ => ∫ u in (1 / 2 : ℝ)..3,
        mobHilbertFloorWindowField N L γ ((u : ℂ) + ((hgt T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    intro hgt hM
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (Filter.Eventually.of_forall fun T u hu => ?_) hM
    rw [uIoc_of_le (by norm_num)] at hu
    have := hbound ((u : ℂ) + ((hgt T : ℝ) : ℂ) * I) (by simp; linarith [hu.1]) (by simp [hu.2])
    simpa using this
  have htop := hhor (fun T => T) (by simpa using (tendsto_exp_neg_sub_sq_half γ).const_mul K)
  have hbot := hhor (fun T => -T) (by
    have h := (tendsto_exp_neg_sub_sq_half (-γ)).const_mul K
    simp only [mul_zero] at h
    refine h.congr fun T => ?_
    congr 3
    ring)
  refine ⟨hline (1 / 2) le_rfl (by norm_num), ?_⟩
  exact GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (by norm_num) (differentiableOn_mobHilbertFloorWindowField N L γ)
    (hline (1 / 2) le_rfl (by norm_num)) (hline 3 (by norm_num) le_rfl) hbot htop

/-- **The shifted integral is `O(e^{10L}/N)`.** -/
theorem norm_integral_mobHilbertFloorWindowField_three_le {C L γ : ℝ}
    (hC : ∀ w : ℂ, ‖complexSinc w‖ ≤ C * Real.exp |w.im|) {N : ℕ} (hN : 1 ≤ N) (hL : 0 ≤ L) :
    ‖∫ y : ℝ, mobHilbertFloorWindowField N L γ (((3 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (20 / N) * Real.sqrt Real.pi := by
  set K : ℝ := C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (20 / N) with hK
  have hint : Integrable fun y : ℝ => K * Real.exp (-(y - γ) ^ 2) :=
    (integrable_exp_neg_sub_sq γ).const_mul K
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun y => ?_)).trans
    (le_of_eq ?_)
  · have := norm_mobHilbertFloorWindowField_three_le (γ := γ) hC hN hL y
    simpa using this
  · rw [integral_const_mul, integral_exp_neg_sub_sq]

/-! ### Main term, integrability and assembly -/

theorem continuous_sincGaussWeight (L γ : ℝ) : Continuous (sincGaussWeight L γ) := by
  unfold sincGaussWeight
  exact ((Real.continuous_sinc.comp (by fun_prop)).pow 4).mul
    (Real.continuous_exp.comp (by fun_prop))

theorem continuous_criticalLineRatio : Continuous criticalLineRatio := by
  unfold criticalLineRatio
  exact (by fun_prop : Continuous fun u : ℝ => 1 / 4 + u ^ 2).div (by fun_prop)
    fun u => by positivity

theorem sincGaussWeight_le (L γ u : ℝ) : sincGaussWeight L γ u ≤ Real.exp (-(u - γ) ^ 2) := by
  unfold sincGaussWeight
  have h : Real.sinc (L * (u - γ)) ^ 4 ≤ 1 := by
    have hs4 : Real.sinc (L * (u - γ)) ^ 4 = |Real.sinc (L * (u - γ))| ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    rw [hs4]
    exact pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)
  calc Real.sinc (L * (u - γ)) ^ 4 * Real.exp (-(u - γ) ^ 2) ≤ 1 * Real.exp (-(u - γ) ^ 2) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := one_mul _

theorem integrable_sincGaussWeight_mul_ratio (L γ : ℝ) :
    Integrable fun u : ℝ => sincGaussWeight L γ u * criticalLineRatio u := by
  refine (integrable_exp_neg_sub_sq γ).mono'
    ((continuous_sincGaussWeight L γ).mul continuous_criticalLineRatio).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have h0 := sincGaussWeight_nonneg L γ u
  have ha0 : 0 ≤ criticalLineRatio u := le_trans (by norm_num) (inv_fortyNine_le_criticalLineRatio u)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 ha0)]
  calc sincGaussWeight L γ u * criticalLineRatio u ≤ sincGaussWeight L γ u * 1 :=
        mul_le_mul_of_nonneg_left (criticalLineRatio_le_one u) h0
    _ ≤ Real.exp (-(u - γ) ^ 2) := by rw [mul_one]; exact sincGaussWeight_le L γ u

/-- **Main term.**  The window of width `1/L` carries mass `≫ 1/L` against `a ≥ 1/49`. -/
theorem integral_sincGaussWeight_mul_ratio_ge {L γ : ℝ} (hL : 1 ≤ L) :
    2 / L * ((5 / 6) ^ 4 * Real.exp (-1) / 49) ≤
      ∫ u : ℝ, sincGaussWeight L γ u * criticalLineRatio u := by
  have hL0 : 0 < L := by linarith
  set m : ℝ := (5 / 6) ^ 4 * Real.exp (-1) / 49 with hm
  have hab : γ - 1 / L ≤ γ + 1 / L := by
    have : 0 ≤ 1 / L := by positivity
    linarith
  have hint := integrable_sincGaussWeight_mul_ratio L γ
  have hcont : Continuous fun u : ℝ => sincGaussWeight L γ u * criticalLineRatio u :=
    (continuous_sincGaussWeight L γ).mul continuous_criticalLineRatio
  have hpt : ∀ u ∈ Icc (γ - 1 / L) (γ + 1 / L),
      m ≤ sincGaussWeight L γ u * criticalLineRatio u := by
    intro u hu
    have ht : |u - γ| ≤ 1 / L := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hLt : |L * (u - γ)| ≤ 1 := by
      rw [abs_mul, abs_of_pos hL0]
      calc L * |u - γ| ≤ L * (1 / L) := mul_le_mul_of_nonneg_left ht hL0.le
        _ = 1 := by field_simp
    have hs := five_sixths_le_sinc hLt
    have hs4 : (5 / 6 : ℝ) ^ 4 ≤ Real.sinc (L * (u - γ)) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hs 4
    have ht1 : (u - γ) ^ 2 ≤ 1 := by
      have h1L : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL
      nlinarith [sq_abs (u - γ), abs_nonneg (u - γ)]
    have he : Real.exp (-1) ≤ Real.exp (-(u - γ) ^ 2) := Real.exp_le_exp.mpr (by linarith)
    have ha := inv_fortyNine_le_criticalLineRatio u
    unfold sincGaussWeight
    calc m = (5 / 6) ^ 4 * Real.exp (-1) * (1 / 49) := by rw [hm]; ring
      _ ≤ Real.sinc (L * (u - γ)) ^ 4 * Real.exp (-(u - γ) ^ 2) * criticalLineRatio u := by
          gcongr
  have hII : IntervalIntegrable (fun u : ℝ => sincGaussWeight L γ u * criticalLineRatio u)
      volume (γ - 1 / L) (γ + 1 / L) := hcont.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hab intervalIntegrable_const hII hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hsub : ∫ u in (γ - 1 / L)..(γ + 1 / L), sincGaussWeight L γ u * criticalLineRatio u ≤
      ∫ u : ℝ, sincGaussWeight L γ u * criticalLineRatio u := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun u =>
      mul_nonneg (sincGaussWeight_nonneg L γ u)
        (le_trans (by norm_num) (inv_fortyNine_le_criticalLineRatio u)))
  calc 2 / L * m = (γ + 1 / L - (γ - 1 / L)) * m := by ring
    _ ≤ _ := hmono.trans hsub

theorem continuous_gamma_half_line : Continuous fun u : ℝ => Complex.Gamma (1 / 2 + (u : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hs : ∀ m : ℕ, (1 / 2 + (u : ℂ) * I) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hl : ContinuousAt (fun u : ℝ => (1 / 2 + (u : ℂ) * I)) u := by fun_prop
  exact ContinuousAt.comp (g := Complex.Gamma) (Complex.differentiableAt_Gamma _ hs).continuousAt hl

theorem norm_Gamma_half_line_sq_le (u : ℝ) :
    ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 ≤ 2 * Real.pi * (1 + u ^ 2)⁻¹ := by
  rw [GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq]
  have hc : (1 + u ^ 2) / 2 ≤ Real.cosh (Real.pi * u) := by
    have h1 : Real.exp (Real.pi * |u|) / 2 ≤ Real.cosh (Real.pi * u) := by
      rw [Real.cosh_eq]
      rcases le_or_gt 0 u with hu | hu
      · rw [abs_of_nonneg hu]; linarith [Real.exp_pos (-(Real.pi * u))]
      · rw [abs_of_neg hu]
        have : Real.pi * -u = -(Real.pi * u) := by ring
        rw [this]; linarith [Real.exp_pos (Real.pi * u)]
    have h2 := Real.quadratic_le_exp_of_nonneg (x := Real.pi * |u|) (by positivity)
    have hpi : 1 ≤ Real.pi ^ 2 / 2 := by nlinarith [Real.pi_gt_three]
    have hu2 : (Real.pi * |u|) ^ 2 / 2 ≥ u ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith [sq_nonneg u]
    have : 0 ≤ Real.pi * |u| := by positivity
    linarith
  have hc0 : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
  rw [div_le_iff₀ hc0]
  have h1 : 0 < 1 + u ^ 2 := by positivity
  calc Real.pi = 2 * Real.pi * (1 + u ^ 2)⁻¹ * ((1 + u ^ 2) / 2) := by field_simp
    _ ≤ 2 * Real.pi * (1 + u ^ 2)⁻¹ * Real.cosh (Real.pi * u) :=
        mul_le_mul_of_nonneg_left hc (by positivity)

theorem integrable_norm_sq_gamma_mul_edPoly_line (N : ℕ) :
    Integrable fun u : ℝ => ‖Complex.Gamma (1 / 2 + (u : ℂ) * I) *
      edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)‖ ^ 2 := by
  have hD : Continuous fun u : ℝ => edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I) :=
    (differentiable_edPoly mobCoeff (fun n hn => (Finset.mem_Icc.mp hn).1)).continuous.comp
      (by fun_prop)
  refine (integrable_inv_one_add_sq.const_mul (2 * Real.pi * (N : ℝ) ^ 2)).mono'
    ((continuous_norm.comp (continuous_gamma_half_line.mul hD)).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have hDn : ‖edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)‖ ≤ N :=
    norm_edPoly_mobCoeff_le N (by simp)
  have hG := norm_Gamma_half_line_sq_le u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_pow]
  calc ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 *
        ‖edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)‖ ^ 2
      ≤ (2 * Real.pi * (1 + u ^ 2)⁻¹) * (N : ℝ) ^ 2 :=
        mul_le_mul hG (pow_le_pow_left₀ (norm_nonneg _) hDn 2) (by positivity) (by positivity)
    _ = 2 * Real.pi * (N : ℝ) ^ 2 * (1 + u ^ 2)⁻¹ := by ring

/-- The weight inequality: `L² κ_L(u) |ζ(1/2+iu)|² ≤ B |Γ(1/2+iu)|²`. -/
theorem sq_mul_sincGaussWeight_mul_normSq_zeta_le {γ B L : ℝ} (hL : 0 < L) (hB0 : 0 < B)
    (hζ : riemannZeta (1 / 2 + (γ : ℂ) * I) = 0)
    (hB : ∀ u : ℝ, Real.exp (-(u - γ) ^ 2) * ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2 ≤
      B * ((u - γ) ^ 2 * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2)) (u : ℝ) :
    L ^ 2 * sincGaussWeight L γ u * ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2 ≤
      B * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 := by
  rcases eq_or_ne u γ with rfl | hne
  · rw [hζ, norm_zero]; simp; positivity
  have ht : u - γ ≠ 0 := sub_ne_zero.mpr hne
  have ht2 : 0 < (u - γ) ^ 2 := by positivity
  have hs := sq_mul_sinc_pow_four_le hL ht
  have hZ := hB u
  unfold sincGaussWeight
  have hE : 0 ≤ Real.exp (-(u - γ) ^ 2) * ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2 := by positivity
  calc L ^ 2 * (Real.sinc (L * (u - γ)) ^ 4 * Real.exp (-(u - γ) ^ 2)) *
        ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2
      = (L ^ 2 * Real.sinc (L * (u - γ)) ^ 4) *
          (Real.exp (-(u - γ) ^ 2) * ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖ ^ 2) := by ring
    _ ≤ (1 / (u - γ) ^ 2) *
          (B * ((u - γ) ^ 2 * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2)) :=
        mul_le_mul hs hZ hE (by positivity)
    _ = B * ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 := by field_simp

theorem log_mul_exp_neg_half_le (y : ℝ) :
    y * Real.exp (-(y / 2)) ≤ 4 * Real.exp (-(y / 4)) := by
  have h1 : y / 4 ≤ Real.exp (y / 4) := by linarith [Real.add_one_le_exp (y / 4)]
  have h2 : Real.exp (-(y / 2)) = Real.exp (-(y / 4)) * Real.exp (-(y / 4)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (y / 4) * Real.exp (-(y / 4)) = 1 := by
    rw [← Real.exp_add]; simp
  have he : 0 ≤ Real.exp (-(y / 4)) := (Real.exp_pos _).le
  calc y * Real.exp (-(y / 2)) = y * Real.exp (-(y / 4)) * Real.exp (-(y / 4)) := by
        rw [h2]; ring
    _ ≤ (4 * Real.exp (y / 4)) * Real.exp (-(y / 4)) * Real.exp (-(y / 4)) := by
        gcongr; linarith
    _ = 4 * Real.exp (-(y / 4)) := by rw [mul_assoc 4, h3]; ring

/-- **The Möbius Hilbert form is at least logarithmic for every large `N`.**
There are `c > 0` and `N₀` with `Σ_{m,n≤N} μ(m)μ(n)/(m+n) ≥ c log N` for all `N ≥ N₀`.

Plancherel writes `2π E_N = ∫ |Γ(1/2+iu) M_N(1/2+iu)|² du`.  At a critical zero `1/2 + iγ`
(Hardy) the weight `L² κ_L`, with `κ_L(u) = sinc(L(u-γ))⁴ e^{-(u-γ)²}` and `L = log N / 20`, is
dominated by `|Γ/ζ|²`.  On the line `|ζ M_N|² ≥ a + 2 Re P_N`, and `∫ κ_L P_N` moves to `Re z = 3`,
where `ζ M_N − 1 = O(1/N)` and the band-limited window costs only `e^{10L} = √N`.  The window mass
against `a ≥ 1/49` is `≫ 1/L`, so `2π E_N ≫ L² · (1/L) ≫ log N`. -/
theorem exists_forall_mul_log_le_finiteMobiusGammaHankelEnergy_one :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * Real.log N ≤ finiteMobiusGammaHankelEnergy N 1 := by
  obtain ⟨T₀, _, hT₀⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨γ, _, hζl⟩ := hT₀ T₀ le_rfl
  have hζ : riemannZeta (1 / 2 + (γ : ℂ) * I) = 0 := by
    have : linePt γ = 1 / 2 + (γ : ℂ) * I := by simp [linePt]
    rwa [this] at hζl
  obtain ⟨B, hB0, hB⟩ := exists_exp_mul_normSq_zeta_line_le hζ
  obtain ⟨C, hC1, hC⟩ := exists_norm_complexSinc_le
  obtain ⟨CF, hCF0, hF⟩ := exists_norm_mobField_le
  set m₀ : ℝ := 2 * ((5 / 6) ^ 4 * Real.exp (-1) / 49) with hm₀
  have hm₀0 : 0 < m₀ := by positivity
  set K₁ : ℝ := C ^ 4 * Real.exp (25 / 4) * Real.sqrt Real.pi with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set Y₀ : ℝ := max 20 (4 * Real.log (16 * K₁ / m₀ + 1)) with hY₀
  refine ⟨m₀ / (80 * Real.pi * B), by positivity, ⌈Real.exp Y₀⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNexp : Real.exp Y₀ ≤ N := by
    have h1 : Real.exp Y₀ ≤ ⌈Real.exp Y₀⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp Y₀⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (Nat.le_succ _).trans hN
    linarith
  set y : ℝ := Real.log N with hy
  have hyY : Y₀ ≤ y := by
    rw [hy, ← Real.log_exp Y₀]
    exact Real.log_le_log (Real.exp_pos _) hNexp
  have hy20 : 20 ≤ y := le_trans (le_max_left _ _) hyY
  set L : ℝ := y / 20 with hL
  have hL1 : 1 ≤ L := by rw [hL, le_div_iff₀ (by norm_num)]; linarith
  have hL0 : 0 < L := by linarith
  have hexpN : Real.exp (10 * L) / N = Real.exp (-(y / 2)) := by
    have hNy : (N : ℝ) = Real.exp y := by rw [hy, Real.exp_log hNpos]
    rw [div_eq_iff hNpos.ne', hNy, ← Real.exp_add]
    congr 1
    rw [hL]
    ring
  -- the windowed field on the critical line
  set W : ℝ → ℂ := fun u => mobHilbertFloorWindowField N L γ (1 / 2 + (u : ℂ) * I) with hW
  have hWre : ∀ u : ℝ, (W u).re =
      sincGaussWeight L γ u * (mobHilbertFloorField N (1 / 2 + (u : ℂ) * I)).re := by
    intro u
    simp only [hW, mobHilbertFloorWindowField, sincGaussWindow_line]
    simp
  obtain ⟨hWint, hshift⟩ := integral_mobHilbertFloorWindowField_shift (γ := γ) hC hCF0.le hF hN1
    hL0.le
  have hcast : ∀ u : ℝ, (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) = 1 / 2 + (u : ℂ) * I := by
    intro u; push_cast; ring
  have hWint' : Integrable W := by
    simp only [hcast] at hWint
    exact hWint
  have hshift' : (∫ u : ℝ, W u) =
      ∫ y : ℝ, mobHilbertFloorWindowField N L γ (((3 : ℝ) : ℂ) + (y : ℂ) * I) := by
    rw [hshift]
    simp only [hcast, hW]
  have hcross := norm_integral_mobHilbertFloorWindowField_three_le (γ := γ) hC hN1 hL0.le
  -- the lower-bound integrand
  set F₂ : ℝ → ℝ := fun u => L ^ 2 / B * (sincGaussWeight L γ u * criticalLineRatio u) +
    L ^ 2 / B * (2 * (W u).re) with hF₂
  have hWre_int : Integrable fun u => (W u).re := hWint'.re
  have hI1 : Integrable fun u => L ^ 2 / B * (sincGaussWeight L γ u * criticalLineRatio u) :=
    (integrable_sincGaussWeight_mul_ratio L γ).const_mul _
  have hI2 : Integrable fun u => L ^ 2 / B * (2 * (W u).re) := (hWre_int.const_mul 2).const_mul _
  have hF₂int : Integrable F₂ := hI1.add hI2
  have hF₂le : ∀ u, F₂ u ≤ ‖Complex.Gamma (1 / 2 + (u : ℂ) * I) *
      edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)‖ ^ 2 := by
    intro u
    have hpt := criticalLineRatio_add_two_mul_re_le N u
    have hwt := sq_mul_sincGaussWeight_mul_normSq_zeta_le hL0 hB0 hζ hB u
    have hk := sincGaussWeight_nonneg L γ u
    simp only [hF₂]
    rw [hWre u]
    rw [norm_mul, mul_pow] at hpt ⊢
    set κ := sincGaussWeight L γ u
    set a := criticalLineRatio u
    set p := (mobHilbertFloorField N (1 / 2 + (u : ℂ) * I)).re
    set Z := ‖riemannZeta (1 / 2 + (u : ℂ) * I)‖
    set D := ‖edPoly mobCoeff (Finset.Icc 1 N) (1 / 2 + (u : ℂ) * I)‖
    set G := ‖Complex.Gamma (1 / 2 + (u : ℂ) * I)‖
    have h1 : L ^ 2 / B * (κ * a) + L ^ 2 / B * (2 * (κ * p)) = L ^ 2 / B * κ * (a + 2 * p) := by
      ring
    rw [h1]
    have hLB : 0 ≤ L ^ 2 / B * κ := by positivity
    have hD2 : 0 ≤ D ^ 2 := sq_nonneg _
    calc L ^ 2 / B * κ * (a + 2 * p) ≤ L ^ 2 / B * κ * (Z ^ 2 * D ^ 2) :=
          mul_le_mul_of_nonneg_left hpt hLB
      _ = (L ^ 2 * κ * Z ^ 2) / B * D ^ 2 := by ring
      _ ≤ (B * G ^ 2) / B * D ^ 2 := by gcongr
      _ = G ^ 2 * D ^ 2 := by field_simp
  have hmono : ∫ u, F₂ u ≤ 2 * Real.pi * finiteMobiusGammaHankelEnergy N 1 := by
    rw [← integral_norm_sq_gamma_mul_edPoly_mobCoeff_line N]
    exact integral_mono hF₂int (integrable_norm_sq_gamma_mul_edPoly_line N) hF₂le
  have hF₂eq : ∫ u, F₂ u = L ^ 2 / B * (∫ u, sincGaussWeight L γ u * criticalLineRatio u) +
      L ^ 2 / B * (2 * (∫ u, W u).re) := by
    have hre : ∫ u, (W u).re = (∫ u, W u).re := by
      have := integral_re hWint'
      simpa using this
    simp only [hF₂]
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_const_mul, hre]
  have hmain := integral_sincGaussWeight_mul_ratio_ge (γ := γ) hL1
  have hcross2 : C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (20 / N) * Real.sqrt Real.pi =
      20 * K₁ * Real.exp (-(y / 2)) := by
    rw [← hexpN, hK₁]; ring
  have hre_ge : -(20 * K₁ * Real.exp (-(y / 2))) ≤ (∫ u, W u).re := by
    rw [hshift', ← hcross2]
    have h1 := Complex.abs_re_le_norm
      (∫ y : ℝ, mobHilbertFloorWindowField N L γ (((3 : ℝ) : ℂ) + (y : ℂ) * I))
    have h2 := neg_abs_le
      ((∫ y : ℝ, mobHilbertFloorWindowField N L γ (((3 : ℝ) : ℂ) + (y : ℂ) * I)).re)
    linarith
  have hsmall : 2 * K₁ * y * Real.exp (-(y / 2)) ≤ m₀ / 2 := by
    have h1 := log_mul_exp_neg_half_le y
    have hlog : Real.log (16 * K₁ / m₀ + 1) ≤ y / 4 := by
      have := le_trans (le_max_right _ _) hyY
      linarith
    have h2 : 16 * K₁ / m₀ + 1 ≤ Real.exp (y / 4) :=
      calc 16 * K₁ / m₀ + 1 = Real.exp (Real.log (16 * K₁ / m₀ + 1)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (y / 4) := Real.exp_le_exp.mpr hlog
    have h3 : Real.exp (-(y / 4)) * Real.exp (y / 4) = 1 := by rw [← Real.exp_add]; simp
    have h16 : 16 * K₁ ≤ m₀ * Real.exp (y / 4) := by
      have := mul_le_mul_of_nonneg_left h2 hm₀0.le
      rw [mul_add, mul_div_cancel₀ _ hm₀0.ne'] at this
      linarith
    have he : 0 < Real.exp (-(y / 4)) := Real.exp_pos _
    have h4 : 8 * K₁ * Real.exp (-(y / 4)) ≤ m₀ / 2 := by
      calc 8 * K₁ * Real.exp (-(y / 4)) ≤ (m₀ * Real.exp (y / 4)) / 2 * Real.exp (-(y / 4)) :=
            mul_le_mul_of_nonneg_right (by linarith) he.le
        _ = m₀ / 2 * (Real.exp (-(y / 4)) * Real.exp (y / 4)) := by ring
        _ = m₀ / 2 := by rw [h3, mul_one]
    calc 2 * K₁ * y * Real.exp (-(y / 2)) = 2 * K₁ * (y * Real.exp (-(y / 2))) := by ring
      _ ≤ 2 * K₁ * (4 * Real.exp (-(y / 4))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 8 * K₁ * Real.exp (-(y / 4)) := by ring
      _ ≤ m₀ / 2 := h4
  have hLm : m₀ / L ≤ ∫ u, sincGaussWeight L γ u * criticalLineRatio u := by
    have : 2 / L * ((5 / 6) ^ 4 * Real.exp (-1) / 49) = m₀ / L := by rw [hm₀]; ring
    linarith
  have hLB : 0 ≤ L ^ 2 / B := by positivity
  have hfinal : L / B * (m₀ / 2) ≤ ∫ u, F₂ u := by
    rw [hF₂eq]
    have h1 : L ^ 2 / B * (m₀ / L) ≤
        L ^ 2 / B * ∫ u, sincGaussWeight L γ u * criticalLineRatio u :=
      mul_le_mul_of_nonneg_left hLm hLB
    have h2 : L ^ 2 / B * (2 * (-(20 * K₁ * Real.exp (-(y / 2))))) ≤
        L ^ 2 / B * (2 * (∫ u, W u).re) :=
      mul_le_mul_of_nonneg_left (by linarith) hLB
    have hLy : L ^ 2 / B * (2 * (-(20 * K₁ * Real.exp (-(y / 2))))) =
        -(L / B * (2 * K₁ * y * Real.exp (-(y / 2)))) := by
      rw [hL]; field_simp
    have hLL : L ^ 2 / B * (m₀ / L) = L / B * m₀ := by field_simp
    have h3 : L / B * (2 * K₁ * y * Real.exp (-(y / 2))) ≤ L / B * (m₀ / 2) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    linarith
  have hE : L / B * (m₀ / 2) ≤ 2 * Real.pi * finiteMobiusGammaHankelEnergy N 1 :=
    hfinal.trans hmono
  have hgoal : m₀ / (80 * Real.pi * B) * y = (L / B * (m₀ / 2)) / (2 * Real.pi) := by
    rw [hL]; field_simp; ring
  rw [hgoal, div_le_iff₀ (by positivity)]
  linarith

end RHTower
