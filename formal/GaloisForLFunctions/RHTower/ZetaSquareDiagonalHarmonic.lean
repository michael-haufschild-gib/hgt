import GaloisForLFunctions.RHTower.ZetaSquareStirlingAFE
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.RectangleDerivativeFormula
import GaloisForLFunctions.RHTower.EstermannHorizontalDecay
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The smoothed harmonic sum of the `|ζ|²` diagonal

With `V` the Gaussian cutoff, for `x ≥ 1`

`𝓗(x) = Σ_{s ≥ 1} s^{−1} V(s²/x) = ½ log x + γ + O(x^{−1/4})`  (`exists_norm_diagHarm_sub_le`).

This is the diagonal of the symmetric approximate functional equation: a pair `(m,n) = (k's, h's)`
with `h/k = h'/k'` reduced contributes `((h,k)/(hk)) 𝓗(t(h,k)²/(2πhk))`.  The constant `γ` matters:
an `O(1)` error per pair is not summable against the mollifier.

**Proof.**  Inserting the Mellin integral of `V` (`Re w = 1`) and summing over `s`,
`𝓗(x) = (1/2π) ∫ x^w e^{w²} ζ(1+2w)/w dv` (`diagHarm_eq_integral`).  The integrand is
`N(w)/w²` with `N(w) = x^w e^{w²} ζ₁(1+2w)/2` entire (`ζ₁ = (s−1)ζ`), and `N'(0) = ½ log x + γ`.
Shifting to `Re w = −1/4` across the double pole at `w = 0` (Cauchy's derivative formula on
rectangles, horizontal edges killed by `e^{−T²}`) leaves an integral `≪ x^{−1/4}`.
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace RHTower.ZetaNotch

/-! ## The entire numerator -/

/-- `N_x(w) = x^w e^{w²} ζ₁(1 + 2w)/2`. -/
def diagHarmNum (x : ℝ) (w : ℂ) : ℂ :=
  ((x : ℝ) : ℂ) ^ w * Complex.exp (w ^ 2) * riemannZeta₁ (1 + 2 * w) / 2

/-- The Mellin integrand `x^w e^{w²} ζ(1+2w)/w = N_x(w)/w²`. -/
def diagHarmIntegrand (x : ℝ) (w : ℂ) : ℂ := diagHarmNum x w / w ^ 2

theorem differentiable_diagHarmNum {x : ℝ} (hx : 0 < x) : Differentiable ℂ (diagHarmNum x) := by
  have hc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  intro w
  unfold diagHarmNum
  refine DifferentiableAt.div_const (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_) 2
  · exact (differentiableAt_id.const_cpow (Or.inl hc))
  · exact (differentiableAt_id.pow 2).cexp
  · exact differentiable_riemannZeta₁.differentiableAt.comp w
      ((differentiableAt_const _).add (differentiableAt_id.const_mul _))

theorem deriv_diagHarmNum_zero {x : ℝ} (hx : 0 < x) :
    deriv (diagHarmNum x) 0 = (Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant := by
  have hc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h1 : HasDerivAt (fun w : ℂ => ((x : ℝ) : ℂ) ^ w)
      (((x : ℝ) : ℂ) ^ (0 : ℂ) * Complex.log ((x : ℝ) : ℂ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (w ^ 2)) 0 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).pow 2).cexp
    simpa using this
  have hlin : HasDerivAt (fun w : ℂ => 1 + 2 * w) 2 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (2 : ℂ)).const_add 1
  have hR : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ 1) ((fun w : ℂ => 1 + 2 * w) 0) := by
    simpa using (differentiable_riemannZeta₁ 1).hasDerivAt
  have h3 : HasDerivAt (riemannZeta₁ ∘ fun w : ℂ => 1 + 2 * w) (deriv riemannZeta₁ 1 * 2) 0 :=
    hR.comp (0 : ℂ) hlin
  have h := ((h1.mul h2).mul h3).div_const 2
  have hfun : diagHarmNum x = fun y => (((fun w : ℂ => ((x : ℝ) : ℂ) ^ w) *
      fun w => Complex.exp (w ^ 2)) * (riemannZeta₁ ∘ fun w : ℂ => 1 + 2 * w)) y / 2 := by
    funext y; rfl
  rw [hfun, h.deriv]
  simp only [Pi.mul_apply, Function.comp_apply, Complex.cpow_zero, mul_zero, add_zero,
    zero_pow two_ne_zero, Complex.exp_zero, riemannZeta₁_one, deriv_riemannZeta₁_one, mul_one,
    one_mul]
  rw [← Complex.ofReal_log hx.le]
  ring

theorem diagHarmIntegrand_eq (x : ℝ) {w : ℂ} (hw : w ≠ 0) :
    diagHarmIntegrand x w =
      ((x : ℝ) : ℂ) ^ w * Complex.exp (w ^ 2) * riemannZeta (1 + 2 * w) / w := by
  have h2w : (1 + 2 * w) - 1 ≠ 0 := by
    rw [add_sub_cancel_left]; exact mul_ne_zero two_ne_zero hw
  have hne : (1 + 2 * w) ≠ 1 := fun h => h2w (by rw [h, sub_self])
  rw [riemannZeta_eq_inv_sub_mul hne]
  unfold diagHarmIntegrand diagHarmNum
  rw [add_sub_cancel_left]
  field_simp

/-! ## A polynomial envelope for `ζ₁` on the strip -/

theorem exists_bound_norm_riemannZeta₁_strip :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ‖riemannZeta₁ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨C₁, N, hC₁, hb⟩ := exists_bound_norm_riemannZeta_strip 3
  -- the compact part
  have hK : IsCompact ((fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) '' (Icc (1 / 2 : ℝ) 3 ×ˢ
      Icc (-1 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  refine ⟨max B 0 + C₁ * 4, N + 1, by positivity, fun σ t h1 h2 => ?_⟩
  have hpow : (1 : ℝ) ≤ (1 + |t|) ^ (N + 1) := one_le_pow₀ (by linarith [abs_nonneg t])
  rcases le_or_gt |t| 1 with ht | ht
  · have hmem : ((σ : ℂ) + (t : ℂ) * I) ∈ (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) ''
        (Icc (1 / 2 : ℝ) 3 ×ˢ Icc (-1 : ℝ) 1) :=
      ⟨(σ, t), ⟨⟨h1, h2⟩, abs_le.mp ht⟩, rfl⟩
    have := hB _ hmem
    have hB0 : B ≤ max B 0 := le_max_left _ _
    have : ‖riemannZeta₁ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max B 0 * (1 + |t|) ^ (N + 1) := by
      calc _ ≤ B := this
        _ ≤ max B 0 := hB0
        _ ≤ max B 0 * (1 + |t|) ^ (N + 1) := le_mul_of_one_le_right (le_max_right _ _) hpow
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 + |t| by positivity) (N + 1)]
  · have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; rw [this] at ht; norm_num at ht
    have hz := hb σ t (by rw [abs_le]; constructor <;> linarith) ht.le
    have hR : riemannZeta₁ ((σ : ℂ) + (t : ℂ) * I) =
        ((σ : ℂ) + (t : ℂ) * I - 1) * riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
      rw [riemannZeta_eq_inv_sub_mul hne]
      field_simp [sub_ne_zero.mpr hne]
    have hn : ‖(σ : ℂ) + (t : ℂ) * I - 1‖ ≤ 4 * (1 + |t|) := by
      calc ‖(σ : ℂ) + (t : ℂ) * I - 1‖ ≤ ‖((σ - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := by
            rw [show (σ : ℂ) + (t : ℂ) * I - 1 = ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I by push_cast; ring]
            exact norm_add_le _ _
        _ = |σ - 1| + |t| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              Complex.norm_I, mul_one]
        _ ≤ 4 * (1 + |t|) := by
            have : |σ - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
            linarith [abs_nonneg t]
    rw [hR, norm_mul]
    have htN : |t| ^ N ≤ (1 + |t|) ^ N := pow_le_pow_left₀ (abs_nonneg t) (by linarith) N
    calc ‖(σ : ℂ) + (t : ℂ) * I - 1‖ * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ (4 * (1 + |t|)) * (C₁ * (1 + |t|) ^ N) :=
          mul_le_mul hn (hz.trans (mul_le_mul_of_nonneg_left htN hC₁)) (norm_nonneg _)
            (by positivity)
      _ = C₁ * 4 * (1 + |t|) ^ (N + 1) := by ring
      _ ≤ (max B 0 + C₁ * 4) * (1 + |t|) ^ (N + 1) := by
          gcongr
          linarith [le_max_right B 0]

/-! ## The integrand on vertical and horizontal segments -/

theorem integrable_one_add_abs_pow_mul_exp_neg_sq (N : ℕ) :
    Integrable (fun v : ℝ => (1 + |v|) ^ N * Real.exp (-(v ^ 2))) := by
  have hg : Integrable (fun v : ℝ => Real.exp (-(1 / 2) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine (hg.const_mul ((N.factorial : ℝ) * Real.exp (3 / 2))).mono' (by fun_prop)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : (1 + |v|) ^ N ≤ N.factorial * Real.exp (1 + |v|) := by
    have := Real.pow_div_factorial_le_exp (1 + |v|) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rw [div_le_iff₀ hf] at this
    linarith
  have h2 : Real.exp (1 + |v|) * Real.exp (-(v ^ 2)) ≤
      Real.exp (3 / 2) * Real.exp (-(1 / 2) * v ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [sq_nonneg (|v| - 1), sq_abs v]
  calc (1 + |v|) ^ N * Real.exp (-(v ^ 2)) ≤ (N.factorial * Real.exp (1 + |v|)) *
        Real.exp (-(v ^ 2)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = N.factorial * (Real.exp (1 + |v|) * Real.exp (-(v ^ 2))) := by ring
    _ ≤ N.factorial * (Real.exp (3 / 2) * Real.exp (-(1 / 2) * v ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem norm_diagHarmIntegrand_le {C : ℝ} {N : ℕ}
    (hb : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ‖riemannZeta₁ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N)
    {x : ℝ} (hx : 0 < x) {u v : ℝ} (hu1 : -1 / 4 ≤ u) (hu2 : u ≤ 1) (hw : (u : ℂ) + (v : ℂ) * I ≠ 0) :
    ‖diagHarmIntegrand x ((u : ℂ) + (v : ℂ) * I)‖ ≤
      x ^ u * Real.exp (u ^ 2 - v ^ 2) * (C * (1 + 2 * |v|) ^ N) /
        (2 * ‖(u : ℂ) + (v : ℂ) * I‖ ^ 2) := by
  unfold diagHarmIntegrand diagHarmNum
  have hpow : ‖((x : ℝ) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I)‖ = x ^ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hexp : ‖Complex.exp (((u : ℂ) + (v : ℂ) * I) ^ 2)‖ = Real.exp (u ^ 2 - v ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [sq]
  have harg : (1 : ℂ) + 2 * ((u : ℂ) + (v : ℂ) * I) = ((1 + 2 * u : ℝ) : ℂ) + ((2 * v : ℝ) : ℂ) * I := by
    push_cast; ring
  have hR := hb (1 + 2 * u) (2 * v) (by linarith) (by linarith)
  rw [← harg, abs_mul, abs_two] at hR
  rw [norm_div, norm_div, norm_mul, norm_mul, hpow, hexp, norm_pow, Complex.norm_ofNat]
  have hw0 : 0 < ‖(u : ℂ) + (v : ℂ) * I‖ := norm_pos_iff.mpr hw
  rw [div_div, mul_comm (2 : ℝ) _]
  gcongr

/-- The vertical integrand is integrable on `Re w = c` for `c ∈ {1, −1/4}`. -/
theorem integrable_diagHarmIntegrand_line {x : ℝ} (hx : 0 < x) {c : ℝ} (hc1 : -1 / 4 ≤ c)
    (hc2 : c ≤ 1) (hc0 : c ≠ 0) :
    Integrable (fun v : ℝ => diagHarmIntegrand x ((c : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, N, hC, hb⟩ := exists_bound_norm_riemannZeta₁_strip
  have hw : ∀ v : ℝ, (c : ℂ) + (v : ℂ) * I ≠ 0 := fun v h => hc0 (by
    have := congrArg Complex.re h; simpa using this)
  have hnorm : ∀ v : ℝ, c ^ 2 ≤ ‖(c : ℂ) + (v : ℂ) * I‖ ^ 2 := fun v => by
    have := Complex.abs_re_le_norm ((c : ℂ) + (v : ℂ) * I)
    have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    rw [hre] at this
    nlinarith [abs_nonneg c, sq_abs c]
  have hc2pos : 0 < c ^ 2 := by positivity
  have hcont : Continuous (fun v : ℝ => diagHarmIntegrand x ((c : ℂ) + (v : ℂ) * I)) := by
    unfold diagHarmIntegrand
    refine Continuous.div ((differentiable_diagHarmNum hx).continuous.comp (by fun_prop))
      (by fun_prop) fun v => pow_ne_zero 2 (hw v)
  have hmaj : Integrable (fun v : ℝ => x ^ c * Real.exp (c ^ 2) * C / (2 * c ^ 2) *
      ((1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2)))) := by
    have h := (integrable_one_add_abs_pow_mul_exp_neg_sq N)
    have h2 : Integrable (fun v : ℝ => (1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2))) := by
      refine (h.const_mul (2 ^ N)).mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : (1 + 2 * |v|) ^ N ≤ 2 ^ N * (1 + |v|) ^ N := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg v]) N
      nlinarith [Real.exp_pos (-(v ^ 2))]
    exact h2.const_mul _
  refine hmaj.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  refine (norm_diagHarmIntegrand_le hb hx hc1 hc2 (hw v)).trans ?_
  rw [div_le_iff₀ (mul_pos two_pos (lt_of_lt_of_le hc2pos (hnorm v)))]
  have hexp : Real.exp (c ^ 2 - v ^ 2) = Real.exp (c ^ 2) * Real.exp (-(v ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  have hA : 0 ≤ x ^ c * (Real.exp (c ^ 2) * Real.exp (-(v ^ 2))) * (C * (1 + 2 * |v|) ^ N) := by
    positivity
  have hkey : x ^ c * (Real.exp (c ^ 2) * Real.exp (-(v ^ 2))) * (C * (1 + 2 * |v|) ^ N) ≤
      x ^ c * Real.exp (c ^ 2) * C / (2 * c ^ 2) * ((1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2))) *
        (2 * ‖(c : ℂ) + (v : ℂ) * I‖ ^ 2) := by
    rw [show x ^ c * Real.exp (c ^ 2) * C / (2 * c ^ 2) * ((1 + 2 * |v|) ^ N *
        Real.exp (-(v ^ 2))) * (2 * ‖(c : ℂ) + (v : ℂ) * I‖ ^ 2) =
        (x ^ c * (Real.exp (c ^ 2) * Real.exp (-(v ^ 2))) * (C * (1 + 2 * |v|) ^ N)) *
          (‖(c : ℂ) + (v : ℂ) * I‖ ^ 2 / c ^ 2) by field_simp]
    exact le_mul_of_one_le_right hA (by rw [le_div_iff₀ hc2pos]; linarith [hnorm v])
  exact hkey

/-! ## The contour shift -/

theorem rectIntegral_diagHarmIntegrand {x T : ℝ} (hx : 0 < x) (hT : 0 < T) :
    rectIntegral (diagHarmIntegrand x) (((-(1 / 4) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((1 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I) =
      2 * Real.pi * I * deriv (diagHarmNum x) 0 := by
  have hfun : diagHarmIntegrand x = fun s => diagHarmNum x s / (s - 0) ^ 2 := by
    funext s; simp [diagHarmIntegrand]
  rw [hfun]
  exact rectIntegral_div_sub_sq_eq_deriv isOpen_univ (differentiable_diagHarmNum hx).differentiableOn
    (mem_univ _) (subset_univ _) (by simp) (by simp) (by simp; linarith) (by simp; linarith)

/-- The horizontal edges vanish. -/
theorem tendsto_diagHarm_horizontal {x : ℝ} (hx : 0 < x) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u in (-(1 / 4) : ℝ)..1,
      diagHarmIntegrand x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, hC, hb⟩ := exists_bound_norm_riemannZeta₁_strip
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  set X : ℝ := max (x ^ (-(1 / 4) : ℝ)) x with hX
  have hX0 : 0 ≤ X := le_max_of_le_right hx.le
  have hxu : ∀ u : ℝ, -(1 / 4) ≤ u → u ≤ 1 → x ^ u ≤ X := by
    intro u h1 h2
    rcases le_or_gt 1 x with hx1 | hx1
    · exact le_max_of_le_right (by
        calc x ^ u ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 h2
          _ = x := Real.rpow_one x)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hx hx1.le h1)
  -- the envelope `M(T) = (5/4) X e (C (1+2T)^N) / (2 T²) e^{−T²}`
  have hbound : ∀ T : ℝ, 1 ≤ T → ∀ u ∈ uIoc (-(1 / 4) : ℝ) 1,
      ‖diagHarmIntegrand x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ ≤
        X * Real.exp 1 * C * (1 + 2 * T) ^ N * Real.exp (-T) := by
    intro T hT u hu
    rw [uIoc_of_le (by norm_num)] at hu
    have hw : ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this
      rcases hε with rfl | rfl <;> simp at this <;> linarith
    have h := norm_diagHarmIntegrand_le hb hx (by linarith [hu.1]) hu.2 hw
    have hnorm : T ≤ ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)
      have him : ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I).im = ε * T := by simp
      rw [him, abs_mul, hεabs, one_mul, abs_of_pos (by linarith)] at this
      exact this
    rw [abs_mul, hεabs, one_mul, abs_of_pos (by linarith)] at h
    refine h.trans ?_
    have hexp : Real.exp (u ^ 2 - (ε * T) ^ 2) ≤ Real.exp 1 * Real.exp (-T) := by
      rw [← Real.exp_add, Real.exp_le_exp, mul_pow, show ε ^ 2 = 1 by
        rcases hε with rfl | rfl <;> norm_num, one_mul]
      have : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
      nlinarith
    have hden : 1 ≤ 2 * ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖ ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    have hA : 0 ≤ X * Real.exp 1 * C * (1 + 2 * T) ^ N * Real.exp (-T) := by positivity
    calc x ^ u * Real.exp (u ^ 2 - (ε * T) ^ 2) * (C * (1 + 2 * T) ^ N)
        ≤ X * (Real.exp 1 * Real.exp (-T)) * (C * (1 + 2 * T) ^ N) := by
          gcongr
          exact hxu u hu.1.le hu.2
      _ = X * Real.exp 1 * C * (1 + 2 * T) ^ N * Real.exp (-T) := by ring
      _ ≤ X * Real.exp 1 * C * (1 + 2 * T) ^ N * Real.exp (-T) *
            (2 * ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖ ^ 2) := le_mul_of_one_le_right hA hden
  have hlim : Tendsto (fun T : ℝ => X * Real.exp 1 * C * 2 ^ N * ((1 + T) ^ N * Real.exp (-(1 * T))) *
      |1 - (-(1 / 4) : ℝ)|) atTop (𝓝 0) := by
    have := (RHTower.tendsto_poly_mul_exp_neg_zero N one_pos).const_mul (X * Real.exp 1 * C * 2 ^ N)
    simpa using this.mul_const |1 - (-(1 / 4) : ℝ)|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => hbound T hT u hu).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hpow : (1 + 2 * T) ^ N ≤ 2 ^ N * (1 + T) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) N
  have : 0 ≤ X * Real.exp 1 * C := by positivity
  calc X * Real.exp 1 * C * (1 + 2 * T) ^ N * Real.exp (-T)
      ≤ X * Real.exp 1 * C * (2 ^ N * (1 + T) ^ N) * Real.exp (-T) := by gcongr
    _ = _ := by ring_nf

/-- **The contour shift**: `∫_{Re w=1} F − ∫_{Re w=−1/4} F = 2π (½ log x + γ)`. -/
theorem diagHarm_vertical_difference {x : ℝ} (hx : 0 < x) :
    (∫ v : ℝ, diagHarmIntegrand x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        ∫ v : ℝ, diagHarmIntegrand x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) =
      2 * Real.pi * ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant) := by
  have hint1 := integrable_diagHarmIntegrand_line hx (c := 1) (by norm_num) le_rfl one_ne_zero
  have hint2 := integrable_diagHarmIntegrand_line hx (c := -(1 / 4)) (by norm_num) (by norm_num)
    (by norm_num)
  have hrect : ∀ T : ℝ, 0 < T →
      (((∫ u in (-(1 / 4) : ℝ)..1, diagHarmIntegrand x ((u : ℂ) + ((-1 * T : ℝ) : ℂ) * I)) -
        ∫ u in (-(1 / 4) : ℝ)..1, diagHarmIntegrand x ((u : ℂ) + ((1 * T : ℝ) : ℂ) * I)) +
        I * ∫ v in (-T : ℝ)..T, diagHarmIntegrand x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I * ∫ v in (-T : ℝ)..T, diagHarmIntegrand x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) =
      2 * Real.pi * I * deriv (diagHarmNum x) 0 := by
    intro T hT
    have h := rectIntegral_diagHarmIntegrand hx hT
    rw [rectIntegral] at h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.add_im, Complex.mul_im,
      zero_add, add_zero, smul_eq_mul] at h
    simpa only [neg_mul, one_mul] using h
  have hbot := tendsto_diagHarm_horizontal hx (-1) (Or.inr rfl)
  have htop := tendsto_diagHarm_horizontal hx 1 (Or.inl rfl)
  have hright := MeasureTheory.intervalIntegral_tendsto_integral hint1 tendsto_neg_atTop_atBot
    tendsto_id
  have hleft := MeasureTheory.intervalIntegral_tendsto_integral hint2 tendsto_neg_atTop_atBot
    tendsto_id
  have hlim := ((hbot.sub htop).add (hright.const_mul I)).sub (hleft.const_mul I)
  have hconst : Tendsto (fun T : ℝ =>
      (((∫ u in (-(1 / 4) : ℝ)..1, diagHarmIntegrand x ((u : ℂ) + ((-1 * T : ℝ) : ℂ) * I)) -
        ∫ u in (-(1 / 4) : ℝ)..1, diagHarmIntegrand x ((u : ℂ) + ((1 * T : ℝ) : ℂ) * I)) +
        I * ∫ v in (-T : ℝ)..T, diagHarmIntegrand x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I * ∫ v in (-T : ℝ)..T, diagHarmIntegrand x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (2 * Real.pi * I * deriv (diagHarmNum x) 0)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (hrect T hT).symm
  have huniq := tendsto_nhds_unique hlim hconst
  rw [deriv_diagHarmNum_zero hx] at huniq
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  rw [mul_sub]
  linear_combination huniq

/-! ## The Mellin representation and the asymptotic -/

/-- `𝓗(x) = Σ_{s ≥ 1} s^{−1} V(s²/x)`. -/
def diagHarm (x : ℝ) : ℂ :=
  ∑' s : ℕ, (((s : ℝ) + 1)⁻¹ : ℂ) * smoothAFECutoff (((s : ℝ) + 1) ^ 2 / x)

/-- One term of the Mellin expansion. -/
def diagHarmTerm (x : ℝ) (s : ℕ) (v : ℝ) : ℂ :=
  (((s : ℝ) + 1)⁻¹ : ℂ) * smoothAFEMellinIntegrand (((s : ℝ) + 1) ^ 2 / x)
    (((1 : ℝ) : ℂ) + (v : ℂ) * I)

theorem norm_inv_natCast_add_one (s : ℕ) : ‖(((s : ℝ) + 1)⁻¹ : ℂ)‖ = ((s : ℝ) + 1)⁻¹ := by
  rw [norm_inv, show ((s : ℝ) : ℂ) + 1 = (((s : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem norm_diagHarmTerm_le {x : ℝ} (hx : 0 < x) (s : ℕ) (v : ℝ) :
    ‖diagHarmTerm x s v‖ ≤ x * Real.exp 1 * (((s : ℝ) + 1) ^ 3)⁻¹ * Real.exp (-(v ^ 2)) := by
  unfold diagHarmTerm
  have hy : 0 < ((s : ℝ) + 1) ^ 2 / x := by positivity
  have h := norm_smoothAFEMellinIntegrand_vertical_le hy one_pos v
  have hpow : (((s : ℝ) + 1) ^ 2 / x) ^ (-(1 : ℝ)) = x / ((s : ℝ) + 1) ^ 2 := by
    rw [Real.rpow_neg_one, inv_div]
  rw [hpow, one_pow, div_one] at h
  rw [norm_mul, norm_inv_natCast_add_one]
  calc ((s : ℝ) + 1)⁻¹ * ‖smoothAFEMellinIntegrand (((s : ℝ) + 1) ^ 2 / x)
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ ((s : ℝ) + 1)⁻¹ * (x / ((s : ℝ) + 1) ^ 2 * Real.exp 1 * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = x * Real.exp 1 * (((s : ℝ) + 1) ^ 3)⁻¹ * Real.exp (-(v ^ 2)) := by
        field_simp

theorem continuous_diagHarmTerm {x : ℝ} (hx : 0 < x) (s : ℕ) :
    Continuous (diagHarmTerm x s) := by
  unfold diagHarmTerm
  exact continuous_const.mul (continuous_smoothAFEMellinIntegrand_line one_ne_zero (by positivity))

/-- `s^{−1}(s²/x)^{−w} e^{w²}/w = x^w e^{w²} s^{−(1+2w)}/w`. -/
theorem diagHarm_term_eq {x : ℝ} (hx : 0 < x) (s : ℕ) {w : ℂ} :
    (((s : ℝ) + 1)⁻¹ : ℂ) * smoothAFEMellinIntegrand (((s : ℝ) + 1) ^ 2 / x) w =
      (x : ℂ) ^ w * Complex.exp (w ^ 2) * (1 / ((s : ℂ) + 1) ^ (1 + 2 * w)) / w := by
  unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
  have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  set L : ℝ := Real.log ((s : ℝ) + 1) with hL
  have e1 : (((s : ℝ) + 1)⁻¹ : ℂ) = Complex.exp (-(L : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, hL, Real.exp_log hs]; push_cast; ring
  have e2 : ((((s : ℝ) + 1) ^ 2 / x : ℝ) : ℂ) ^ (-w) =
      Complex.exp (-((2 * L - Real.log x : ℝ) : ℂ) * w) := by
    rw [ofReal_cpow_eq_exp (by positivity), Real.log_div (by positivity) hx.ne', Real.log_pow, hL]
    congr 1; push_cast; ring
  have e3 : 1 / ((s : ℂ) + 1) ^ (1 + 2 * w) = Complex.exp (-((L : ℂ) * (1 + 2 * w))) := by
    rw [show ((s : ℂ) + 1) = (((s : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, ofReal_cpow_eq_exp hs,
      one_div, ← Complex.exp_neg]
  have key : Complex.exp (-(L : ℂ)) * Complex.exp (-((2 * L - Real.log x : ℝ) : ℂ) * w) *
      Complex.exp (w ^ 2) = Complex.exp ((Real.log x : ℂ) * w) * Complex.exp (w ^ 2) *
        Complex.exp (-((L : ℂ) * (1 + 2 * w))) := by
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e1, e2, e3, ofReal_cpow_eq_exp hx, div_eq_mul_inv, div_eq_mul_inv]
  linear_combination w⁻¹ * key

theorem tsum_diagHarmTerm {x : ℝ} (hx : 0 < x) (v : ℝ) :
    ∑' s : ℕ, diagHarmTerm x s v = diagHarmIntegrand x (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hw0 : (((1 : ℝ) : ℂ) + (v : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hre : 1 < (1 + 2 * (((1 : ℝ) : ℂ) + (v : ℂ) * I)).re := by simp
  rw [diagHarmIntegrand_eq x hw0, zeta_eq_tsum_one_div_nat_add_one_cpow hre, ← tsum_mul_left,
    ← tsum_div_const]
  exact tsum_congr fun s => diagHarm_term_eq hx s

/-- **The Mellin representation of `𝓗`.** -/
theorem diagHarm_eq_integral {x : ℝ} (hx : 0 < x) :
    diagHarm x = (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ, diagHarmIntegrand x (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hint : ∀ s : ℕ, Integrable (diagHarmTerm x s) := by
    intro s
    refine ((integrable_exp_neg_mul_sq one_pos).const_mul
      (x * Real.exp 1 * (((s : ℝ) + 1) ^ 3)⁻¹)).mono'
        (continuous_diagHarmTerm hx s).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    simpa using norm_diagHarmTerm_le hx s v
  have hsum : Summable (fun s : ℕ => ∫ v : ℝ, ‖diagHarmTerm x s v‖) := by
    set G : ℝ := ∫ v : ℝ, Real.exp (-(v ^ 2)) with hG
    have hb : ∀ s : ℕ, ∫ v : ℝ, ‖diagHarmTerm x s v‖ ≤
        x * Real.exp 1 * G * (((s : ℝ) + 1) ^ 3)⁻¹ := by
      intro s
      have hmaj : Integrable (fun v : ℝ => x * Real.exp 1 * (((s : ℝ) + 1) ^ 3)⁻¹ *
          Real.exp (-(v ^ 2))) := by
        simpa using (integrable_exp_neg_mul_sq one_pos).const_mul
          (x * Real.exp 1 * (((s : ℝ) + 1) ^ 3)⁻¹)
      calc ∫ v : ℝ, ‖diagHarmTerm x s v‖ ≤ ∫ v : ℝ, x * Real.exp 1 * (((s : ℝ) + 1) ^ 3)⁻¹ *
            Real.exp (-(v ^ 2)) :=
            integral_mono (hint s).norm hmaj fun v => norm_diagHarmTerm_le hx s v
        _ = x * Real.exp 1 * G * (((s : ℝ) + 1) ^ 3)⁻¹ := by
            rw [integral_const_mul, hG]; ring
    have hcube : Summable (fun s : ℕ => (((s : ℝ) + 1) ^ 3)⁻¹) := by
      have := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 3)).comp_injective
        (add_left_injective 1)
      simpa [Function.comp_def] using this
    exact Summable.of_nonneg_of_le (fun s => integral_nonneg fun v => norm_nonneg _) hb
      (hcube.mul_left _)
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  have hterm : ∀ s : ℕ, (((s : ℝ) + 1)⁻¹ : ℂ) * smoothAFECutoff (((s : ℝ) + 1) ^ 2 / x) =
      (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, diagHarmTerm x s v := by
    intro s
    have hcut : ∀ y : ℝ, smoothAFECutoff y = (1 / (2 * Real.pi) : ℂ) *
        ∫ v : ℝ, smoothAFEMellinIntegrand y (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
      intro y
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.real_smul]
      rfl
    unfold diagHarmTerm
    rw [integral_const_mul, hcut]
    ring
  unfold diagHarm
  rw [show (fun s : ℕ => (((s : ℝ) + 1)⁻¹ : ℂ) * smoothAFECutoff (((s : ℝ) + 1) ^ 2 / x)) =
    fun s => (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, diagHarmTerm x s v from funext hterm,
    tsum_mul_left, hHS.tsum_eq]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun v => tsum_diagHarmTerm hx v)

/-- **`𝓗(x) = ½ log x + γ + O(x^{−1/4})`.** -/
theorem exists_norm_diagHarm_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖diagHarm x - ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant)‖ ≤
        C * x ^ (-(1 / 4) : ℝ) := by
  obtain ⟨C, N, hC, hb⟩ := exists_bound_norm_riemannZeta₁_strip
  set I₀ : ℝ := ∫ v : ℝ, (1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2)) with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun v => by positivity
  have hint2 : Integrable (fun v : ℝ => (1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2))) := by
    refine ((integrable_one_add_abs_pow_mul_exp_neg_sq N).const_mul (2 ^ N)).mono' (by fun_prop)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 + 2 * |v|) ^ N ≤ 2 ^ N * (1 + |v|) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg v]) N
    nlinarith [Real.exp_pos (-(v ^ 2))]
  refine ⟨(1 / (2 * Real.pi)) * (Real.exp (1 / 16) * C * 8 * I₀), by positivity, fun x hx => ?_⟩
  have hdiff := diagHarm_vertical_difference hx
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have h2 : (1 / (2 * Real.pi) : ℂ) * (2 * Real.pi) = 1 := one_div_mul_cancel hpi
  have key : diagHarm x - ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ v : ℝ, diagHarmIntegrand x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) := by
    rw [diagHarm_eq_integral hx]
    linear_combination (1 / (2 * Real.pi) : ℂ) * hdiff +
      ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant) * h2
  rw [key, norm_mul]
  have hbound : ∀ v : ℝ, ‖diagHarmIntegrand x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      x ^ (-(1 / 4) : ℝ) * (Real.exp (1 / 16) * C * 8) *
        ((1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2))) := by
    intro v
    have hw : (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h := norm_diagHarmIntegrand_le hb hx (by norm_num) (by norm_num) hw
    have hn : (1 / 16 : ℝ) ≤ ‖(((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2 := by
      have hre := Complex.abs_re_le_norm (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)
      have hr : (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I).re = -(1 / 4) := by simp
      rw [hr, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hre
      nlinarith
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hexp : Real.exp ((-(1 / 4) : ℝ) ^ 2 - v ^ 2) =
        Real.exp (1 / 16) * Real.exp (-(v ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    calc x ^ (-(1 / 4) : ℝ) * (Real.exp (1 / 16) * Real.exp (-(v ^ 2))) * (C * (1 + 2 * |v|) ^ N)
        = x ^ (-(1 / 4) : ℝ) * (Real.exp (1 / 16) * C * 8) *
            ((1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2))) * (2 * (1 / 16)) := by ring
      _ ≤ x ^ (-(1 / 4) : ℝ) * (Real.exp (1 / 16) * C * 8) *
            ((1 + 2 * |v|) ^ N * Real.exp (-(v ^ 2))) *
            (2 * ‖(((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2) := by
          gcongr
  have hI := norm_integral_le_of_norm_le (hint2.const_mul _) (Eventually.of_forall hbound)
  rw [integral_const_mul, ← hI₀] at hI
  rw [show ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) by
    rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
  calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, diagHarmIntegrand x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * (x ^ (-(1 / 4) : ℝ) * (Real.exp (1 / 16) * C * 8) * I₀) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

end RHTower.ZetaNotch
