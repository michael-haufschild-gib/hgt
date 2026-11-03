import GaloisForLFunctions.RHTower.RectangleLocalCauchyFormula

/-!
# Newman's analytic theorem

**Theorem** (`newman_analytic_theorem`). Let `f : ℝ → ℂ` be measurable and bounded by `B` on
`(0, ∞)`, and let `g` be analytic on a neighbourhood of the closed half-plane `Re z ≥ 0` with
`g(z) = ∫_0^∞ f(t) e^{−zt} dt` for `Re z > 0`. Then `∫_0^T f(t) dt → g(0)` as `T → ∞`.

The proof is Zagier's, on a rectangle instead of a circle. With `g_T(z) = ∫_0^T f(t)e^{−zt} dt`
(entire, `differentiable_truncLaplace`) and the kernel `k(z)e^{zT}`, `k(z) = 1 + z²/R²`, the
Cauchy formula on the rectangle `[−δ, R] × [−R, R]` (inside the domain of `g`) and on
`[−R, R] × [−R, R]` (for `g_T`) gives

`2πi (g(0) − g_T(0)) = ∮_right (g − g_T) k e^{zT}/z + ∮_{left, δ} g k e^{zT}/z − ∮_{left, R} g_T k e^{zT}/z`.

* On the right edges (`Re z = x > 0`) `|g − g_T| ≤ B e^{−xT}/x`; on the left edges of the big
  rectangle (`x < 0`) `|g_T| ≤ B e^{−xT}/|x|`. On horizontal edges `|k(x ± iR)| ≤ 3|x|/R`, which
  cancels the `1/|x|`, and on vertical edges `|k| ≤ 5`: both contributions are `≤ 16B/R`
  (`norm_rightPart_le`, `norm_leftPart_trunc_le`).
* The left edges of the small rectangle carry `e^{xT}`, `x ≤ 0`, with `k = 0` at `x = 0`: they
  vanish as `T → ∞` (`tendsto_leftPart_zero`).

Hence `limsup |g(0) − g_T(0)| ≤ 16B/(πR)` for every `R`.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set intervalIntegral
open scoped Interval

namespace GaloisForLFunctions.ArtinMertens

/-! ### Truncated Laplace transforms -/

/-- The truncated Laplace transform `g_T(z) = ∫_0^T f(t) e^{−zt} dt`. -/
def truncLaplace (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ := ∫ t in (0 : ℝ)..T, f t * cexp (-(z * t))

variable {f : ℝ → ℂ} {B : ℝ}

theorem norm_cexp_neg_mul (z : ℂ) (t : ℝ) : ‖cexp (-(z * t))‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- `∫_0^T e^{ct} dt ≤ e^{cT}/c` for `c > 0`. -/
theorem integral_exp_mul_le {c : ℝ} (hc : 0 < c) {T : ℝ} :
    ∫ t in (0 : ℝ)..T, Real.exp (c * t) ≤ Real.exp (c * T) / c := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t => Real.exp (c * t) / c) (Real.exp (c * t)) t :=
    fun t _ => by
      have hc' : c ≠ 0 := hc.ne'
      have := (((hasDerivAt_id' t).const_mul c).exp).div_const c
      rw [mul_one, mul_div_assoc, div_self hc', mul_one] at this
      exact this
  rw [integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  have : 0 < Real.exp (c * 0) / c := by positivity
  linarith

/-- For `Re z < 0`: `‖g_T(z)‖ ≤ B e^{−Re z·T}/(−Re z)`. -/
theorem norm_truncLaplace_le_of_re_neg (hB : ∀ t, 0 < t → ‖f t‖ ≤ B) {z : ℂ} (hz : z.re < 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖truncLaplace f T z‖ ≤ B * Real.exp (-z.re * T) / (-z.re) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 one_pos)
  unfold truncLaplace
  have hb : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) T →
      ‖f t * cexp (-(z * t))‖ ≤ B * Real.exp (-z.re * t) := Eventually.of_forall fun t ht => by
    rw [norm_mul, norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (hB t ht.1) (Real.exp_pos _).le
  refine (intervalIntegral.norm_integral_le_of_norm_le hT hb
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _)).trans ?_
  rw [intervalIntegral.integral_const_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (integral_exp_mul_le (by linarith)) hB0

/-- For `Re z > 0`: `‖∫_0^∞ f e^{−zt} − g_T(z)‖ ≤ B e^{−Re z·T}/Re z`. -/
theorem norm_laplace_sub_truncLaplace_le (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 < t → ‖f t‖ ≤ B) {z : ℂ} (hz : 0 < z.re) {T : ℝ} (hT : 0 ≤ T) :
    ‖(∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t))) - truncLaplace f T z‖ ≤
      B * Real.exp (-z.re * T) / z.re := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 one_pos)
  set F : ℝ → ℂ := fun t => f t * cexp (-(z * t)) with hF
  have hFm : AEStronglyMeasurable F (volume.restrict (Ioi 0)) :=
    hfm.mul (Continuous.aestronglyMeasurable (by fun_prop))
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖F t‖ ≤ B * Real.exp (-z.re * t) := fun t ht => by
    simp only [hF]
    rw [norm_mul, norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (hB t ht) (Real.exp_pos _).le
  have hexp : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hz).const_mul B
  have hint : IntegrableOn F (Ioi 0) :=
    Integrable.mono' hexp hFm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall hbound))
  have hdisj : Disjoint (Ioc (0 : ℝ) T) (Ioi T) :=
    Set.disjoint_left.mpr fun t h1 h2 => (not_lt.mpr h1.2) h2
  have hsplit : (∫ t in Ioi (0 : ℝ), F t) = (∫ t in Ioc (0 : ℝ) T, F t) + ∫ t in Ioi T, F t := by
    conv_lhs => rw [← Ioc_union_Ioi_eq_Ioi hT]
    exact setIntegral_union hdisj measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self)
      (hint.mono_set (Ioi_subset_Ioi hT))
  have htrunc : truncLaplace f T z = ∫ t in Ioc (0 : ℝ) T, F t := by
    unfold truncLaplace; rw [intervalIntegral.integral_of_le hT]
  rw [hsplit, htrunc, add_sub_cancel_left]
  have hexpT : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Ioi T) :=
    (exp_neg_integrableOn_Ioi T hz).const_mul B
  refine (norm_integral_le_of_norm_le hexpT ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => hbound t (lt_of_le_of_lt hT ht)))).trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith : -z.re < 0),
    neg_div_neg_eq, mul_div_assoc]

/-- `g_T` is entire. -/
theorem differentiable_truncLaplace (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 < t → ‖f t‖ ≤ B) {T : ℝ} (hT : 0 ≤ T) : Differentiable ℂ (truncLaplace f T) := by
  intro z₀
  have hfm' : AEStronglyMeasurable f (volume.restrict (Ι (0 : ℝ) T)) := by
    rw [uIoc_of_le hT]; exact hfm.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  set C := Real.exp ((‖z₀‖ + 1) * T) with hC
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => f t * cexp (-(z * t)))
      (volume.restrict (Ι (0 : ℝ) T)) := fun z =>
    hfm'.mul (Continuous.aestronglyMeasurable (by fun_prop))
  have hexp_le : ∀ z ∈ Metric.ball z₀ 1, ∀ t ∈ Ι (0 : ℝ) T, Real.exp (-z.re * t) ≤ C := by
    intro z hz t ht
    rw [uIoc_of_le hT] at ht
    rw [hC]
    refine Real.exp_le_exp.mpr ?_
    have h1 : -z.re ≤ ‖z₀‖ + 1 := by
      have := Complex.abs_re_le_norm z
      have : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_sub_norm_le z z₀
        rw [Metric.mem_ball, dist_eq_norm] at hz
        linarith
      linarith [neg_abs_le z.re]
    have ht0 : 0 ≤ t := ht.1.le
    calc -z.re * t ≤ (‖z₀‖ + 1) * t := mul_le_mul_of_nonneg_right h1 ht0
      _ ≤ (‖z₀‖ + 1) * T := mul_le_mul_of_nonneg_left ht.2 (by positivity)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z (t : ℝ) => f t * cexp (-(z * t)))
    (F' := fun z (t : ℝ) => f t * (cexp (-(z * t)) * (-(t : ℂ))))
    (x₀ := z₀) (bound := fun _ => B * C * T) (s := Metric.ball z₀ 1)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => hmeas z)
    (by
      refine (intervalIntegrable_const (c := B * C)).mono_fun' (hmeas z₀) ?_
      refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
      have ht' := ht
      rw [uIoc_of_le hT] at ht'
      show ‖f t * cexp (-(z₀ * t))‖ ≤ B * C
      rw [norm_mul, norm_cexp_neg_mul]
      exact mul_le_mul (hB t ht'.1) (hexp_le z₀ (Metric.mem_ball_self one_pos) t ht)
        (Real.exp_pos _).le ((norm_nonneg _).trans (hB t ht'.1)))
    (hfm'.mul (Continuous.aestronglyMeasurable (by fun_prop)))
    (Eventually.of_forall fun t ht z hz => by
      have ht' := ht
      rw [uIoc_of_le hT] at ht'
      rw [norm_mul, norm_mul, norm_cexp_neg_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht'.1]
      have hBt := hB t ht'.1
      have hE := hexp_le z hz t ht
      have hC0 : 0 ≤ C := by rw [hC]; exact (Real.exp_pos _).le
      calc ‖f t‖ * (Real.exp (-z.re * t) * t) ≤ B * (C * T) :=
            mul_le_mul hBt (mul_le_mul hE ht'.2 ht'.1.le hC0)
              (mul_nonneg (Real.exp_pos _).le ht'.1.le) ((norm_nonneg _).trans hBt)
        _ = B * C * T := by ring)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ z _ => by
      have h1 : HasDerivAt (fun x : ℂ => -(x * (t : ℂ))) (-(t : ℂ)) z := by
        have := ((hasDerivAt_id' z).mul_const (t : ℂ)).neg
        rw [one_mul] at this
        exact this
      exact h1.cexp.const_mul (f t))
  exact h.2.differentiableAt

/-! ### The rectangle split into a right and a left part -/

/-- Zagier's kernel `k(z) e^{zT}`, `k(z) = 1 + z²/R²`. -/
def newmanKernel (R T : ℝ) (z : ℂ) : ℂ := (1 + z ^ 2 / (R : ℂ) ^ 2) * cexp (z * T)

theorem newmanKernel_zero (R T : ℝ) : newmanKernel R T 0 = 1 := by simp [newmanKernel]

theorem norm_newmanKernel (R T : ℝ) (z : ℂ) :
    ‖newmanKernel R T z‖ = ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ * Real.exp (z.re * T) := by
  rw [newmanKernel, norm_mul, Complex.norm_exp]; congr 2; simp

theorem differentiable_newmanKernel (R T : ℝ) : Differentiable ℂ (newmanKernel R T) := by
  unfold newmanKernel; fun_prop

/-- The right part of the contour of `[−a, R] × [−R, R]`: the horizontal edges over `[0, R]` and
the right edge. -/
def rightPart (F : ℂ → ℂ) (R : ℝ) : ℂ :=
  ((∫ x in (0 : ℝ)..R, F ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) -
      ∫ x in (0 : ℝ)..R, F ((x : ℂ) + (R : ℂ) * I)) +
    I • ∫ y in (-R)..R, F ((R : ℂ) + (y : ℂ) * I)

/-- The left part of the contour of `[−a, R] × [−R, R]`: the horizontal edges over `[−a, 0]` and
the left edge. -/
def leftPart (F : ℂ → ℂ) (a R : ℝ) : ℂ :=
  ((∫ x in (-a)..0, F ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) -
      ∫ x in (-a)..0, F ((x : ℂ) + (R : ℂ) * I)) -
    I • ∫ y in (-R)..R, F (((-a : ℝ) : ℂ) + (y : ℂ) * I)

theorem rectIntegral_eq_rightPart_add_leftPart (F : ℂ → ℂ) {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hbot : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) volume (-a) R)
    (htop : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (R : ℂ) * I)) volume (-a) R) :
    RHTower.rectIntegral F ⟨-a, -R⟩ ⟨R, R⟩ = rightPart F R + leftPart F a R := by
  have hs1 : uIcc (-a) 0 ⊆ uIcc (-a) R := uIcc_subset_uIcc_left (by
    rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, hR⟩)
  have hs2 : uIcc 0 R ⊆ uIcc (-a) R := uIcc_subset_uIcc_right (by
    rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, hR⟩)
  unfold RHTower.rectIntegral rightPart leftPart
  dsimp only
  rw [← intervalIntegral.integral_add_adjacent_intervals (hbot.mono_set hs1) (hbot.mono_set hs2),
    ← intervalIntegral.integral_add_adjacent_intervals (htop.mono_set hs1) (htop.mono_set hs2)]
  ring

/-! ### Bounds on the kernel along the edges -/

/-- On a horizontal edge `z = x ± iR`, `|x| ≤ R`: `|1 + z²/R²| ≤ 3|x|/R`. -/
theorem norm_kernel_horizontal_le {R x s : ℝ} (hR : 0 < R) (hx : |x| ≤ R) (hs : s = R ∨ s = -R) :
    ‖1 + ((x : ℂ) + (s : ℂ) * I) ^ 2 / (R : ℂ) ^ 2‖ ≤ 3 * |x| / R := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hs2 : (s : ℂ) ^ 2 = (R : ℂ) ^ 2 := by rcases hs with rfl | rfl <;> push_cast <;> ring
  have e : 1 + ((x : ℂ) + (s : ℂ) * I) ^ 2 / (R : ℂ) ^ 2 =
      (x : ℂ) * ((x : ℂ) + 2 * (s : ℂ) * I) / (R : ℂ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hRC), add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hRC), one_mul]
    linear_combination (-1 : ℂ) * hs2 + (s : ℂ) ^ 2 * Complex.I_sq
  rw [e, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  have hsn : ‖(x : ℂ) + 2 * (s : ℂ) * I‖ ≤ 3 * R := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one, Complex.norm_ofNat]
    have : |s| = R := by rcases hs with rfl | rfl <;> simp [abs_of_pos hR]
    rw [this]; linarith
  rw [div_le_div_iff₀ (by positivity) hR]
  nlinarith [mul_le_mul_of_nonneg_left hsn (mul_nonneg (abs_nonneg x) hR.le)]

/-- On a vertical edge `z = s + iy`, `|s|, |y| ≤ R`: `|1 + z²/R²| ≤ 5`. -/
theorem norm_kernel_vertical_le {R s y : ℝ} (hR : 0 < R) (hs : |s| ≤ R) (hy : |y| ≤ R) :
    ‖1 + ((s : ℂ) + (y : ℂ) * I) ^ 2 / (R : ℂ) ^ 2‖ ≤ 5 := by
  have hz : ‖(s : ℂ) + (y : ℂ) * I‖ ≤ 2 * R := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs]
    linarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have : ‖(s : ℂ) + (y : ℂ) * I‖ ^ 2 / R ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- An edge integrand `Φ k e^{zT}/z` with `|Φ| ≤ B e^{−xT}/|x|`, `|k| ≤ K`, `|z| ≥ R`. -/
theorem norm_edge_le {Φ : ℂ → ℂ} {R T K : ℝ} {z : ℂ} (hR : 0 < R) (hB : 0 ≤ B) (hx : z.re ≠ 0)
    (hΦ : ‖Φ z‖ ≤ B * Real.exp (-z.re * T) / |z.re|) (hk : ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ K)
    (hz : R ≤ ‖z‖) :
    ‖Φ z * newmanKernel R T z * (z - 0)⁻¹‖ ≤ B * K / (|z.re| * R) := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hR hz
  have hx0 : 0 < |z.re| := abs_pos.mpr hx
  have hK : 0 ≤ K := (norm_nonneg _).trans hk
  rw [sub_zero, norm_mul, norm_mul, norm_inv, norm_newmanKernel]
  have h1 : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖Φ z‖ * (‖1 + z ^ 2 / (R : ℂ) ^ 2‖ * Real.exp (z.re * T)) * ‖z‖⁻¹
      ≤ (B * Real.exp (-z.re * T) / |z.re|) * (K * Real.exp (z.re * T)) * R⁻¹ := by
        gcongr
    _ = B * K * (Real.exp (-z.re * T) * Real.exp (z.re * T)) / (|z.re| * R) := by
        field_simp
    _ = B * K / (|z.re| * R) := by rw [h1, mul_one]

/-- A horizontal edge `z = x ± iR`, `|x| ≤ R`: the integrand is `≤ 3B/R²` (for `x = 0` it vanishes,
since `k(±iR) = 0`). -/
theorem norm_horizontal_le {Φ : ℂ → ℂ} {R T x s : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (hx : |x| ≤ R)
    (hs : s = R ∨ s = -R)
    (hΦ : x ≠ 0 → ‖Φ ((x : ℂ) + (s : ℂ) * I)‖ ≤ B * Real.exp (-x * T) / |x|) :
    ‖Φ ((x : ℂ) + (s : ℂ) * I) * newmanKernel R T ((x : ℂ) + (s : ℂ) * I) *
      ((x : ℂ) + (s : ℂ) * I - 0)⁻¹‖ ≤ 3 * B / R ^ 2 := by
  have hk := norm_kernel_horizontal_le hR hx hs
  have hre : ((x : ℂ) + (s : ℂ) * I).re = x := by simp
  have him : |((x : ℂ) + (s : ℂ) * I).im| = R := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
    rcases hs with rfl | rfl <;> simp [abs_of_pos hR]
  have hzR : R ≤ ‖(x : ℂ) + (s : ℂ) * I‖ := him ▸ Complex.abs_im_le_norm _
  rcases eq_or_ne x 0 with rfl | hx0
  · have hk0 : ‖1 + (((0 : ℝ) : ℂ) + (s : ℂ) * I) ^ 2 / (R : ℂ) ^ 2‖ = 0 := by
      have := hk; simp only [abs_zero, mul_zero, zero_div] at this
      exact le_antisymm this (norm_nonneg _)
    rw [newmanKernel, sub_zero, norm_mul, norm_mul, norm_mul, hk0]
    simp only [zero_mul, mul_zero]
    positivity
  · have h := norm_edge_le (Φ := Φ) (T := T) hR hB (by rw [hre]; exact hx0)
      (by rw [hre]; exact hΦ hx0) hk hzR
    rw [hre] at h
    refine h.trans (le_of_eq ?_)
    field_simp

/-- A vertical edge `z = ±R + iy`, `|y| ≤ R`: the integrand is `≤ 5B/R²`. -/
theorem norm_vertical_le {Φ : ℂ → ℂ} {R T s y : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (hy : |y| ≤ R)
    (hs : |s| = R) (hΦ : ‖Φ ((s : ℂ) + (y : ℂ) * I)‖ ≤ B * Real.exp (-s * T) / |s|) :
    ‖Φ ((s : ℂ) + (y : ℂ) * I) * newmanKernel R T ((s : ℂ) + (y : ℂ) * I) *
      ((s : ℂ) + (y : ℂ) * I - 0)⁻¹‖ ≤ 5 * B / R ^ 2 := by
  have hk := norm_kernel_vertical_le hR hs.le hy
  have hre : ((s : ℂ) + (y : ℂ) * I).re = s := by simp
  have hzR : R ≤ ‖(s : ℂ) + (y : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((s : ℂ) + (y : ℂ) * I); rw [hre, hs] at this; exact this
  have hs0 : s ≠ 0 := fun h => by rw [h, abs_zero] at hs; exact hR.ne' hs.symm
  have h := norm_edge_le (Φ := Φ) (T := T) hR hB (by rw [hre]; exact hs0) (by rw [hre]; exact hΦ)
    hk hzR
  rw [hre, hs] at h
  refine h.trans (le_of_eq ?_)
  field_simp

/-! ### The edge integrals -/

/-- **The right part**: if `‖Φ(z)‖ ≤ B e^{−xT}/x` for `x = Re z > 0`, then the right part of the
contour integral of `Φ k e^{zT}/z` is at most `16B/R`. -/
theorem norm_rightPart_le {Φ : ℂ → ℂ} {R T : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hΦ : ∀ z : ℂ, 0 < z.re → ‖Φ z‖ ≤ B * Real.exp (-z.re * T) / z.re) :
    ‖rightPart (fun z => Φ z * newmanKernel R T z * (z - 0)⁻¹) R‖ ≤ 16 * B / R := by
  have hbot : ‖∫ x in (0 : ℝ)..R, Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * I) *
      newmanKernel R T ((x : ℂ) + ((-R : ℝ) : ℂ) * I) *
        ((x : ℂ) + ((-R : ℝ) : ℂ) * I - 0)⁻¹‖ ≤ 3 * B / R ^ 2 * |R - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hR.le] at hx
    refine norm_horizontal_le hR hB (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩) (Or.inr rfl)
      fun _ => ?_
    have h := hΦ ((x : ℂ) + ((-R : ℝ) : ℂ) * I) (by simpa using hx.1)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero] at h
    rwa [abs_of_pos hx.1]
  have htop : ‖∫ x in (0 : ℝ)..R, Φ ((x : ℂ) + (R : ℂ) * I) * newmanKernel R T ((x : ℂ) + (R : ℂ) * I) *
      ((x : ℂ) + (R : ℂ) * I - 0)⁻¹‖ ≤ 3 * B / R ^ 2 * |R - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hR.le] at hx
    refine norm_horizontal_le hR hB (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩) (Or.inl rfl)
      fun _ => ?_
    have h := hΦ ((x : ℂ) + (R : ℂ) * I) (by simpa using hx.1)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero] at h
    rwa [abs_of_pos hx.1]
  have hright : ‖∫ y in (-R)..R, Φ ((R : ℂ) + (y : ℂ) * I) * newmanKernel R T ((R : ℂ) + (y : ℂ) * I) *
      ((R : ℂ) + (y : ℂ) * I - 0)⁻¹‖ ≤ 5 * B / R ^ 2 * |R - -R| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [uIoc_of_le (by linarith)] at hy
    refine norm_vertical_le hR hB (abs_le.mpr ⟨hy.1.le, hy.2⟩) (abs_of_pos hR) ?_
    have h := hΦ ((R : ℂ) + (y : ℂ) * I) (by simpa using hR)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero] at h
    rwa [abs_of_pos hR]
  unfold rightPart
  rw [sub_zero, show R - -R = 2 * R by ring, abs_of_pos hR, abs_of_pos (by positivity)] at *
  calc ‖_ - _ + I • _‖ ≤ ‖_‖ + ‖_‖ + ‖I‖ * ‖_‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_smul _ _).le)
    _ ≤ 3 * B / R ^ 2 * R + 3 * B / R ^ 2 * R + 1 * (5 * B / R ^ 2 * (2 * R)) := by
        rw [Complex.norm_I]; gcongr
    _ = 16 * B / R := by field_simp; ring

/-- **The left part of the large rectangle**: if `‖Φ(z)‖ ≤ B e^{−xT}/(−x)` for `x = Re z < 0`,
then the left part of the contour integral of `Φ k e^{zT}/z` over `[−R, R] × [−R, R]` is at most
`16B/R`. -/
theorem norm_leftPart_le {Φ : ℂ → ℂ} {R T : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hΦ : ∀ z : ℂ, z.re < 0 → ‖Φ z‖ ≤ B * Real.exp (-z.re * T) / (-z.re)) :
    ‖leftPart (fun z => Φ z * newmanKernel R T z * (z - 0)⁻¹) R R‖ ≤ 16 * B / R := by
  have hhor : ∀ s : ℝ, (s = R ∨ s = -R) → ‖∫ x in (-R)..0, Φ ((x : ℂ) + (s : ℂ) * I) *
      newmanKernel R T ((x : ℂ) + (s : ℂ) * I) * ((x : ℂ) + (s : ℂ) * I - 0)⁻¹‖ ≤
      3 * B / R ^ 2 * |0 - -R| := by
    intro s hs
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le (by linarith)] at hx
    refine norm_horizontal_le hR hB (abs_le.mpr ⟨hx.1.le, by linarith [hx.2]⟩) hs fun hx0 => ?_
    have hxn : x < 0 := lt_of_le_of_ne hx.2 hx0
    have h := hΦ ((x : ℂ) + (s : ℂ) * I) (by simpa using hxn)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero] at h
    rwa [abs_of_neg hxn]
  have hbot := hhor (-R) (Or.inr rfl)
  have htop := hhor R (Or.inl rfl)
  have hleft : ‖∫ y in (-R)..R, Φ (((-R : ℝ) : ℂ) + (y : ℂ) * I) *
      newmanKernel R T (((-R : ℝ) : ℂ) + (y : ℂ) * I) * (((-R : ℝ) : ℂ) + (y : ℂ) * I - 0)⁻¹‖ ≤
      5 * B / R ^ 2 * |R - -R| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [uIoc_of_le (by linarith)] at hy
    refine norm_vertical_le hR hB (abs_le.mpr ⟨hy.1.le, hy.2⟩) (by rw [abs_neg, abs_of_pos hR])
      ?_
    have h := hΦ (((-R : ℝ) : ℂ) + (y : ℂ) * I) (by simpa using hR)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero] at h
    rw [abs_neg, abs_of_pos hR]
    simpa using h
  unfold leftPart
  rw [show (0 : ℝ) - -R = R by ring, show R - -R = 2 * R by ring, abs_of_pos hR,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * R)] at *
  calc ‖_ - _ - I • _‖ ≤ ‖_‖ + ‖_‖ + ‖I‖ * ‖_‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_smul _ _).le)
    _ ≤ 3 * B / R ^ 2 * R + 3 * B / R ^ 2 * R + 1 * (5 * B / R ^ 2 * (2 * R)) := by
        rw [Complex.norm_I]; gcongr
    _ = 16 * B / R := by field_simp; ring

/-! ### The left edges of the small rectangle vanish -/

/-- `|x| e^{xT} → 0` as `T → ∞` for `x ≤ 0`. -/
theorem tendsto_abs_mul_exp_mul {x : ℝ} (hx : x ≤ 0) :
    Tendsto (fun T : ℝ => |x| * Real.exp (x * T)) atTop (𝓝 0) := by
  rcases hx.lt_or_eq with hx | rfl
  · have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hx)
    simpa using h.const_mul |x|
  · simp

/-- An edge integrand is continuous along a horizontal segment off the origin. -/
theorem continuousOn_edge {G : ℂ → ℂ} {R T s a b : ℝ} (hs : s ≠ 0)
    (hG : ContinuousOn (fun x : ℝ => G ((x : ℂ) + (s : ℂ) * I)) (uIcc a b)) :
    ContinuousOn (fun x : ℝ => G ((x : ℂ) + (s : ℂ) * I) * newmanKernel R T ((x : ℂ) + (s : ℂ) * I) *
      ((x : ℂ) + (s : ℂ) * I - 0)⁻¹) (uIcc a b) := by
  refine (hG.mul ((differentiable_newmanKernel R T).continuous.comp
    (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (s : ℂ) * I)).continuousOn).mul ?_
  refine ContinuousOn.inv₀ (by fun_prop) fun x _ h => hs ?_
  have := congrArg Complex.im h
  simpa using this

/-- The same along a vertical segment off the origin. -/
theorem continuousOn_edge_vertical {G : ℂ → ℂ} {R T s a b : ℝ} (hs : s ≠ 0)
    (hG : ContinuousOn (fun y : ℝ => G ((s : ℂ) + (y : ℂ) * I)) (uIcc a b)) :
    ContinuousOn (fun y : ℝ => G ((s : ℂ) + (y : ℂ) * I) * newmanKernel R T ((s : ℂ) + (y : ℂ) * I) *
      ((s : ℂ) + (y : ℂ) * I - 0)⁻¹) (uIcc a b) := by
  refine (hG.mul ((differentiable_newmanKernel R T).continuous.comp
    (by fun_prop : Continuous fun y : ℝ => (s : ℂ) + (y : ℂ) * I)).continuousOn).mul ?_
  refine ContinuousOn.inv₀ (by fun_prop) fun y _ h => hs ?_
  have := congrArg Complex.re h
  simpa using this

/-- **The left edges of the small rectangle vanish**: for `g` continuous on `[−δ, 0] × [−R, R]`,
`0 < δ ≤ R`, the left part of the contour integral of `g k e^{zT}/z` tends to `0` as `T → ∞`. -/
theorem tendsto_leftPart_zero {g : ℂ → ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hg : ContinuousOn g (Icc (-δ) 0 ×ℂ Icc (-R) R)) :
    Tendsto (fun T : ℝ => leftPart (fun z => g z * newmanKernel R T z * (z - 0)⁻¹) δ R) atTop
      (𝓝 0) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn hg
  have hmem : ∀ x y : ℝ, x ∈ Icc (-δ) 0 → y ∈ Icc (-R) R →
      (x : ℂ) + (y : ℂ) * I ∈ Icc (-δ) 0 ×ℂ Icc (-R) R := fun x y hx hy => by
    rw [Complex.mem_reProdIm]; simpa using ⟨hx, hy⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (hmem 0 0 ⟨by linarith, le_rfl⟩
    ⟨by linarith, hR.le⟩))
  -- the horizontal edges
  have hhor : ∀ s : ℝ, (s = R ∨ s = -R) → Tendsto (fun T : ℝ => ∫ x in (-δ)..0,
      g ((x : ℂ) + (s : ℂ) * I) * newmanKernel R T ((x : ℂ) + (s : ℂ) * I) *
        ((x : ℂ) + (s : ℂ) * I - 0)⁻¹) atTop (𝓝 0) := by
    intro s hs
    have hsR : s ∈ Icc (-R) R := by rcases hs with rfl | rfl <;> constructor <;> linarith
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> [exact hR.ne'; exact (neg_neg_of_pos hR).ne]
    have hcont : ∀ T : ℝ, ContinuousOn (fun x : ℝ => g ((x : ℂ) + (s : ℂ) * I) *
        newmanKernel R T ((x : ℂ) + (s : ℂ) * I) * ((x : ℂ) + (s : ℂ) * I - 0)⁻¹)
        (uIcc (-δ) 0) := fun T => by
      refine continuousOn_edge hs0 (hg.comp (by fun_prop : Continuous fun x : ℝ =>
        (x : ℂ) + (s : ℂ) * I).continuousOn fun x hx => ?_)
      rw [uIcc_of_le (by linarith)] at hx
      exact hmem x s hx hsR
    -- pointwise bound `M (3|x|/R) e^{xT}/R`
    have hpt : ∀ T : ℝ, ∀ x ∈ Ι (-δ) 0, ‖g ((x : ℂ) + (s : ℂ) * I) *
        newmanKernel R T ((x : ℂ) + (s : ℂ) * I) * ((x : ℂ) + (s : ℂ) * I - 0)⁻¹‖ ≤
        M * 3 / R ^ 2 * (|x| * Real.exp (x * T)) := by
      intro T x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hgx := hM _ (hmem x s ⟨hx.1.le, hx.2⟩ hsR)
      have hk := norm_kernel_horizontal_le (x := x) hR
        (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hs
      have him : |((x : ℂ) + (s : ℂ) * I).im| = R := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
        rcases hs with rfl | rfl <;> simp [abs_of_pos hR]
      have hzR : R ≤ ‖(x : ℂ) + (s : ℂ) * I‖ := him ▸ Complex.abs_im_le_norm _
      have hre : ((x : ℂ) + (s : ℂ) * I).re = x := by simp
      rw [sub_zero, norm_mul, norm_mul, norm_inv, norm_newmanKernel, hre]
      have hz0 : 0 < ‖(x : ℂ) + (s : ℂ) * I‖ := lt_of_lt_of_le hR hzR
      calc ‖g ((x : ℂ) + (s : ℂ) * I)‖ * (‖1 + ((x : ℂ) + (s : ℂ) * I) ^ 2 / (R : ℂ) ^ 2‖ *
            Real.exp (x * T)) * ‖(x : ℂ) + (s : ℂ) * I‖⁻¹
          ≤ M * (3 * |x| / R * Real.exp (x * T)) * R⁻¹ := by
            gcongr
        _ = M * 3 / R ^ 2 * (|x| * Real.exp (x * T)) := by field_simp
    have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (a := -δ) (b := 0)
      (F := fun T x => g ((x : ℂ) + (s : ℂ) * I) * newmanKernel R T ((x : ℂ) + (s : ℂ) * I) *
        ((x : ℂ) + (s : ℂ) * I - 0)⁻¹) (f := fun _ => 0) (fun _ => M * 3 / R ^ 2 * δ)
      (Eventually.of_forall fun T => (hcont T).mono uIoc_subset_uIcc |>.aestronglyMeasurable
        measurableSet_uIoc)
      (by
        filter_upwards [eventually_ge_atTop 0] with T hT
        refine Eventually.of_forall fun x hx => (hpt T x hx).trans ?_
        have hx' := hx
        rw [uIoc_of_le (by linarith)] at hx'
        have h1 : |x| ≤ δ := abs_le.mpr ⟨hx'.1.le, by linarith [hx'.2]⟩
        have h2 : Real.exp (x * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx'.2])
        have h3 : |x| * Real.exp (x * T) ≤ δ :=
          (mul_le_mul h1 h2 (Real.exp_pos _).le hδ.le).trans (by rw [mul_one])
        exact mul_le_mul_of_nonneg_left h3 (by positivity))
      intervalIntegrable_const
      (Eventually.of_forall fun x hx => by
        have hx' := hx
        rw [uIoc_of_le (by linarith)] at hx'
        refine squeeze_zero_norm (fun T => hpt T x hx) ?_
        simpa using (tendsto_abs_mul_exp_mul hx'.2).const_mul (M * 3 / R ^ 2))
    simpa using hlim
  -- the left edge
  have hvert : Tendsto (fun T : ℝ => ∫ y in (-R)..R,
      g (((-δ : ℝ) : ℂ) + (y : ℂ) * I) * newmanKernel R T (((-δ : ℝ) : ℂ) + (y : ℂ) * I) *
        (((-δ : ℝ) : ℂ) + (y : ℂ) * I - 0)⁻¹) atTop (𝓝 0) := by
    have hb : ∀ T : ℝ, ‖∫ y in (-R)..R,
        g (((-δ : ℝ) : ℂ) + (y : ℂ) * I) * newmanKernel R T (((-δ : ℝ) : ℂ) + (y : ℂ) * I) *
          (((-δ : ℝ) : ℂ) + (y : ℂ) * I - 0)⁻¹‖ ≤ M * 5 / δ * Real.exp (-δ * T) * |R - -R| := by
      intro T
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      rw [uIoc_of_le (by linarith)] at hy
      have hgy := hM _ (hmem (-δ) y ⟨le_rfl, by linarith⟩ ⟨hy.1.le, hy.2⟩)
      have hk := norm_kernel_vertical_le hR (by rw [abs_neg, abs_of_pos hδ]; exact hδR)
        (abs_le.mpr ⟨hy.1.le, hy.2⟩) (s := -δ)
      have hre : (((-δ : ℝ) : ℂ) + (y : ℂ) * I).re = -δ := by simp
      have hzδ : δ ≤ ‖((-δ : ℝ) : ℂ) + (y : ℂ) * I‖ := by
        have := Complex.abs_re_le_norm (((-δ : ℝ) : ℂ) + (y : ℂ) * I)
        rwa [hre, abs_neg, abs_of_pos hδ] at this
      rw [sub_zero, norm_mul, norm_mul, norm_inv, norm_newmanKernel, hre]
      calc ‖g (((-δ : ℝ) : ℂ) + (y : ℂ) * I)‖ *
            (‖1 + (((-δ : ℝ) : ℂ) + (y : ℂ) * I) ^ 2 / (R : ℂ) ^ 2‖ * Real.exp (-δ * T)) *
            ‖((-δ : ℝ) : ℂ) + (y : ℂ) * I‖⁻¹
          ≤ M * (5 * Real.exp (-δ * T)) * δ⁻¹ := by gcongr
        _ = M * 5 / δ * Real.exp (-δ * T) := by field_simp
    have hexp : Tendsto (fun T : ℝ => M * 5 / δ * Real.exp (-δ * T) * |R - -R|) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by linarith : -δ < 0))
      simpa using (h.const_mul (M * 5 / δ)).mul_const |R - -R|
    exact squeeze_zero_norm hb hexp
  have hbot := hhor (-R) (Or.inr rfl)
  have htop := hhor R (Or.inl rfl)
  unfold leftPart
  have := (hbot.sub htop).sub (hvert.const_smul I)
  simpa using this

/-! ### The assembly -/

theorem rightPart_sub (F G : ℂ → ℂ) {R : ℝ}
    (hF1 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) volume 0 R)
    (hF2 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (R : ℂ) * I)) volume 0 R)
    (hF3 : IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-R) R)
    (hG1 : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + ((-R : ℝ) : ℂ) * I)) volume 0 R)
    (hG2 : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + (R : ℂ) * I)) volume 0 R)
    (hG3 : IntervalIntegrable (fun y : ℝ => G ((R : ℂ) + (y : ℂ) * I)) volume (-R) R) :
    rightPart F R - rightPart G R = rightPart (fun z => F z - G z) R := by
  unfold rightPart
  rw [intervalIntegral.integral_sub hF1 hG1, intervalIntegral.integral_sub hF2 hG2,
    intervalIntegral.integral_sub hF3 hG3, smul_sub]
  ring

/-- **The key inequality**: for `g` analytic on the rectangle `[−δ, R] × [−R, R]`,
`2π|g(0) − g_T(0)| ≤ 32B/R + |left part over the small rectangle|`. -/
theorem norm_sub_truncLaplace_zero_le {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hB : ∀ t, 0 < t → ‖f t‖ ≤ B)
    {g : ℂ → ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hg : ∀ z ∈ uIcc (-δ) R ×ℂ uIcc (-R) R, AnalyticAt ℂ g z)
    (hlap : ∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t)))
    {T : ℝ} (hT : 0 ≤ T) :
    ‖(2 * Real.pi * I : ℂ) * (g 0 - truncLaplace f T 0)‖ ≤
      32 * B / R + ‖leftPart (fun z => g z * newmanKernel R T z * (z - 0)⁻¹) δ R‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 one_pos)
  set Q := uIcc (-δ) R ×ℂ uIcc (-R) R with hQ
  have hgc : ContinuousOn g Q := fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hTd := differentiable_truncLaplace hfm hB hT
  -- Cauchy's formula for `g` on the small rectangle and for `g_T` on the large one
  have hCg := RHTower.rectIntegral_cauchyFormula_of_analyticOnNhd
    (g := fun z => g z * newmanKernel R T z) (p := 0) (z₁ := ⟨-δ, -R⟩) (z₂ := ⟨R, R⟩) (U := Q)
    (fun z hz => (hg z hz).mul ((differentiable_newmanKernel R T).analyticAt z))
    (fun z hz => hz) (by show -δ < 0; linarith) (by show (0 : ℝ) < R; exact hR)
    (by show -R < 0; linarith) (by show (0 : ℝ) < R; exact hR)
  have hCT := RHTower.rectIntegral_cauchyFormula_entire
    (g := fun z => truncLaplace f T z * newmanKernel R T z) (p := 0) (z₁ := ⟨-R, -R⟩)
    (z₂ := ⟨R, R⟩) (fun z _ => (hTd.mul (differentiable_newmanKernel R T)).analyticAt z)
    (by show -R < 0; linarith) (by show (0 : ℝ) < R; exact hR)
    (by show -R < 0; linarith) (by show (0 : ℝ) < R; exact hR)
  simp only [newmanKernel_zero, mul_one] at hCg hCT
  -- continuity of the edge integrands
  have hmemQ : ∀ x y : ℝ, x ∈ uIcc (-δ) R → y ∈ uIcc (-R) R → (x : ℂ) + (y : ℂ) * I ∈ Q :=
    fun x y hx hy => by rw [hQ, Complex.mem_reProdIm]; simpa using ⟨hx, hy⟩
  have hRu : R ∈ uIcc (-R) R := by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, le_rfl⟩
  have hRu' : -R ∈ uIcc (-R) R := by rw [uIcc_of_le (by linarith)]; exact ⟨le_rfl, by linarith⟩
  have hgh : ∀ s : ℝ, s ∈ uIcc (-R) R → ContinuousOn (fun x : ℝ => g ((x : ℂ) + (s : ℂ) * I))
      (uIcc (-δ) R) := fun s hs =>
    hgc.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (s : ℂ) * I).continuousOn
      fun x hx => hmemQ x s hx hs
  have hRδ : R ∈ uIcc (-δ) R := by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, le_rfl⟩
  have hgv : ContinuousOn (fun y : ℝ => g ((R : ℂ) + (y : ℂ) * I)) (uIcc (-R) R) :=
    hgc.comp (by fun_prop : Continuous fun y : ℝ => (R : ℂ) + (y : ℂ) * I).continuousOn
      fun y hy => hmemQ R y hRδ hy
  have hRne : R ≠ 0 := hR.ne'
  have hRne' : -R ≠ 0 := by linarith
  have hsubR : uIcc (0 : ℝ) R ⊆ uIcc (-δ) R := uIcc_subset_uIcc_right (by
    rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩)
  have hsubR' : uIcc (0 : ℝ) R ⊆ uIcc (-R) R := uIcc_subset_uIcc_right (by
    rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩)
  have hTc : ∀ s : ℝ, ∀ a b : ℝ, ContinuousOn (fun x : ℝ => truncLaplace f T ((x : ℂ) + (s : ℂ) * I))
      (uIcc a b) := fun s a b =>
    (hTd.continuous.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (s : ℂ) * I)).continuousOn
  have hTv : ContinuousOn (fun y : ℝ => truncLaplace f T ((R : ℂ) + (y : ℂ) * I)) (uIcc (-R) R) :=
    (hTd.continuous.comp (by fun_prop : Continuous fun y : ℝ => (R : ℂ) + (y : ℂ) * I)).continuousOn
  -- split the two contours
  rw [rectIntegral_eq_rightPart_add_leftPart _ hδ.le hR.le
    (continuousOn_edge hRne' (hgh (-R) hRu')).intervalIntegrable
    (continuousOn_edge hRne (hgh R hRu)).intervalIntegrable] at hCg
  rw [rectIntegral_eq_rightPart_add_leftPart _ hR.le hR.le
    (continuousOn_edge hRne' (hTc (-R) (-R) R)).intervalIntegrable
    (continuousOn_edge hRne (hTc R (-R) R)).intervalIntegrable] at hCT
  have hsub := rightPart_sub (fun z => g z * newmanKernel R T z * (z - 0)⁻¹)
    (fun z => truncLaplace f T z * newmanKernel R T z * (z - 0)⁻¹) (R := R)
    ((continuousOn_edge hRne' (hgh (-R) hRu')).mono hsubR).intervalIntegrable
    ((continuousOn_edge hRne (hgh R hRu)).mono hsubR).intervalIntegrable
    (continuousOn_edge_vertical hRne hgv).intervalIntegrable
    ((continuousOn_edge hRne' (hTc (-R) 0 R))).intervalIntegrable
    ((continuousOn_edge hRne (hTc R 0 R))).intervalIntegrable
    (continuousOn_edge_vertical hRne hTv).intervalIntegrable
  have hfun : (fun z => g z * newmanKernel R T z * (z - 0)⁻¹ -
      truncLaplace f T z * newmanKernel R T z * (z - 0)⁻¹) =
      fun z => (g z - truncLaplace f T z) * newmanKernel R T z * (z - 0)⁻¹ := by
    funext z; ring
  rw [hfun] at hsub
  have hid : (2 * Real.pi * I : ℂ) * (g 0 - truncLaplace f T 0) =
      rightPart (fun z => (g z - truncLaplace f T z) * newmanKernel R T z * (z - 0)⁻¹) R +
        leftPart (fun z => g z * newmanKernel R T z * (z - 0)⁻¹) δ R -
          leftPart (fun z => truncLaplace f T z * newmanKernel R T z * (z - 0)⁻¹) R R := by
    rw [← hsub, mul_sub, ← hCg, ← hCT]
    ring
  rw [hid]
  have h1 := norm_rightPart_le (Φ := fun z => g z - truncLaplace f T z) (T := T) hR hB0
    (fun z hz => by
      have := norm_laplace_sub_truncLaplace_le hfm hB hz hT
      rwa [← hlap z hz] at this)
  have h2 := norm_leftPart_le (Φ := truncLaplace f T) (T := T) hR hB0
    (fun z hz => norm_truncLaplace_le_of_re_neg hB hz hT)
  calc ‖rightPart (fun z => (g z - truncLaplace f T z) * newmanKernel R T z * (z - 0)⁻¹) R +
        leftPart (fun z => g z * newmanKernel R T z * (z - 0)⁻¹) δ R -
          leftPart (fun z => truncLaplace f T z * newmanKernel R T z * (z - 0)⁻¹) R R‖
      ≤ ‖rightPart (fun z => (g z - truncLaplace f T z) * newmanKernel R T z * (z - 0)⁻¹) R‖ +
          ‖leftPart (fun z => g z * newmanKernel R T z * (z - 0)⁻¹) δ R‖ +
          ‖leftPart (fun z => truncLaplace f T z * newmanKernel R T z * (z - 0)⁻¹) R R‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 16 * B / R + ‖leftPart (fun z => g z * newmanKernel R T z * (z - 0)⁻¹) δ R‖ +
          16 * B / R := by gcongr
    _ = _ := by ring

/-- **Newman's analytic theorem.** Let `f` be measurable and bounded by `B` on `(0, ∞)`, and let
`g` be analytic at every point of the closed half-plane `Re z ≥ 0` with
`g(z) = ∫_0^∞ f(t) e^{−zt} dt` for `Re z > 0`. Then `∫_0^T f → g(0)` as `T → ∞`. -/
theorem newman_analytic_theorem {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hB : ∀ t, 0 < t → ‖f t‖ ≤ B)
    {g : ℂ → ℂ} (hg : ∀ z : ℂ, 0 ≤ z.re → AnalyticAt ℂ g z)
    (hlap : ∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t))) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (g 0)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 one_pos)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hπ := Real.pi_pos
  -- a radius with `32B/R < πε`
  set R := 64 * (B + 1) / (Real.pi * ε) with hRdef
  have hR : 0 < R := by positivity
  have hRε : 32 * B / R < Real.pi * ε := by
    rw [hRdef, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hπ hε]
  -- a strip of width `δ` left of the axis inside the domain of analyticity
  set U := {z : ℂ | AnalyticAt ℂ g z} with hU
  have hUo : IsOpen U := isOpen_analyticAt ℂ g
  have hK : Icc 0 R ×ℂ Icc (-R) R ⊆ U := fun z hz => by
    rw [Complex.mem_reProdIm] at hz
    exact hg z hz.1.1
  obtain ⟨δ₀, hδ₀, hthick⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_cthickening_subset_open
    hUo hK
  set δ := min δ₀ R with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hR
  have hδR : δ ≤ R := min_le_right _ _
  have hrect : ∀ z ∈ uIcc (-δ) R ×ℂ uIcc (-R) R, AnalyticAt ℂ g z := by
    intro z hz
    rw [Complex.mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hz
    rcases le_or_gt 0 z.re with h0 | h0
    · exact hK (Complex.mem_reProdIm.mpr ⟨⟨h0, hz.1.2⟩, hz.2⟩)
    · refine hthick (Metric.mem_cthickening_of_dist_le z ⟨0, z.im⟩ δ₀ _
        (Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hR.le⟩, hz.2⟩) ?_)
      rw [Complex.dist_eq]
      have : z - ⟨0, z.im⟩ = (z.re : ℂ) := by apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h0]
      linarith [hz.1.1, min_le_left δ₀ R]
  have hgleft : ContinuousOn g (Icc (-δ) 0 ×ℂ Icc (-R) R) := fun z hz => by
    refine (hrect z ?_).continuousAt.continuousWithinAt
    rw [Complex.mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    rw [Complex.mem_reProdIm] at hz
    exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
  have hleft := tendsto_leftPart_zero hR hδ hδR hgleft
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hleft) (Real.pi * ε) (by positivity)
  refine ⟨max T₀ 0, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  have hkey := norm_sub_truncLaplace_zero_le hfm hB hR hδ hrect hlap hT0
  have hl := hT₀ T (le_trans (le_max_left _ _) hT)
  rw [dist_zero_right] at hl
  have htr : truncLaplace f T 0 = ∫ t in (0 : ℝ)..T, f t := by
    unfold truncLaplace; simp
  rw [htr, norm_mul] at hkey
  have h2π : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ, Complex.norm_ofNat]; ring
  rw [h2π] at hkey
  rw [dist_eq_norm, norm_sub_rev]
  have : 2 * Real.pi * ‖g 0 - ∫ t in (0 : ℝ)..T, f t‖ < 2 * Real.pi * ε := by linarith
  exact lt_of_mul_lt_mul_left this (by positivity)

end GaloisForLFunctions.ArtinMertens
