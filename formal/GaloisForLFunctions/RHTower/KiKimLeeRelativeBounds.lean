import GaloisForLFunctions.RHTower.XiLineHalfGaussInstance

/-!
# Relative size of the error terms in the one-sided Gaussian average of `ξ`

Fix `0 < t ≤ 1/8`, a height `X ≥ 200`, `|y| ≤ ½`, and put `α = ½ log(X/2π)`, `a = α + iπ/4`,
`u = y + 2tα` (the centre of the tilted Gaussian `g_t(w − y) e^{wα}`), `W = 2tα + α²`, and
`F(w) = ξ(½ + w + iX)`. With `N = ‖F(u)‖` the natural scale is `P = N e^{−tα²}`: the main term has
modulus `P e^{−tπ²/16}`. Every other contribution to `Q` and to `D − aQ` is bounded by `P` times an
explicit function of `α` alone (`kklR1`, …, `kklRB`), each of which tends to `0` as `α → ∞`:

* the Gaussian tails of the model outside `[9/2, W]` (Chernoff bounds);
* the strip `0 < w ≤ 9/2`, where `‖F(w)‖ ≤ 200(6 + X)‖F(9/2)‖` and the model carries `F(9/2)` back
  to `F(u)`, at the price `e^{(9/2 − u)α}`, against `P ∝ e^{−tα²}`;
* the far region `w > W`, where Grönwall with `‖F'‖ ≤ (α + 2 + (w + ½)/(2X))‖F‖` and absorption of
  the quadratic term into half of the Gaussian leave `e^{−(15/8 − t)α²}`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- Lower Gaussian tail of the model. -/
def kklR1 (t α : ℝ) : ℝ := Real.exp (5 / 2 * α - 3 / 4 * t * α ^ 2)

/-- Upper Gaussian tail of the model. -/
def kklR2 (t α : ℝ) : ℝ := Real.exp (-α ^ 2 + 1 / 2 + t)

/-- The strip `0 < w ≤ 9/2`. -/
def kklRA (t α : ℝ) : ℝ :=
  9 / 2 * (5 / (2 * t) + α + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 *
    (6 + 2 * Real.pi * Real.exp (2 * α)) *
    Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8)

/-- The far region `w > 2tα + α²`. -/
def kklRC (t α : ℝ) : ℝ :=
  2 * Real.exp 1 * 2 * (1 / (2 * t) + α + 1) *
    Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)

/-- The boundary value at `w = 2tα + α²`. -/
def kklRB (t α : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
    Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2)

/-- The total relative error. -/
def kklError (t α : ℝ) : ℝ := kklR1 t α + kklR2 t α + 2 * kklRA t α + 2 * kklRC t α + kklRB t α

theorem scale_identity (t α y : ℝ) :
    -((y + 2 * t * α) * α) + (y * α + t * α ^ 2) = -(t * α ^ 2) := by ring

/-- **Lower tail.** -/
theorem lowerTail_le {t α y N : ℝ} (ht : 0 < t) (hy : |y| ≤ 1 / 2) (hα : 0 ≤ α) (hN : 0 ≤ N) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w in Iic (9 / 2 : ℝ), gaussDensity t (w - y) * Real.exp (w * α) ≤
      N * Real.exp (-(t * α ^ 2)) * kklR1 t α := by
  have h := setIntegral_Iic_gaussDensity_sub_mul_rexp_le ht y α (9 / 2) (α / 2) (by linarith)
  have hy' := neg_abs_le y
  calc N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w in Iic (9 / 2 : ℝ), gaussDensity t (w - y) * Real.exp (w * α)
      ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
          Real.exp (α / 2 * (9 / 2) + y * (α - α / 2) + t * (α - α / 2) ^ 2) := by gcongr
    _ = N * Real.exp (-(t * α ^ 2) + (9 / 4 * α - y * α / 2 - 3 / 4 * t * α ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ N * Real.exp (-(t * α ^ 2) + (5 / 2 * α - 3 / 4 * t * α ^ 2)) := by
        gcongr
        nlinarith [abs_le.mp hy]
    _ = _ := by rw [kklR1, mul_assoc N, ← Real.exp_add]

/-- **Upper tail.** -/
theorem upperTail_le {t α y N : ℝ} (ht : 0 < t) (hy : |y| ≤ 1 / 2) (hN : 0 ≤ N) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w in Ioi (2 * t * α + α ^ 2), gaussDensity t (w - y) * Real.exp (w * α) ≤
      N * Real.exp (-(t * α ^ 2)) * kklR2 t α := by
  rw [← integral_Ici_eq_integral_Ioi]
  have h := setIntegral_Ici_gaussDensity_sub_mul_rexp_le ht y α (2 * t * α + α ^ 2) 1 zero_le_one
  calc N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w in Ici (2 * t * α + α ^ 2), gaussDensity t (w - y) * Real.exp (w * α)
      ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
          Real.exp (-(1 * (2 * t * α + α ^ 2)) + y * (α + 1) + t * (α + 1) ^ 2) := by gcongr
    _ = N * Real.exp (-(t * α ^ 2) + (-α ^ 2 + y + t)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ N * Real.exp (-(t * α ^ 2) + (-α ^ 2 + 1 / 2 + t)) := by
        gcongr
        linarith [abs_le.mp hy]
    _ = _ := by rw [kklR2, mul_assoc N, ← Real.exp_add]

/-- **Model error.** -/
theorem modelError_le {t α y N : ℝ} (ht : 0 < t) (hN : 0 ≤ N) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
          (Real.exp (1 / 8 * |w - (y + 2 * t * α)|) - 1) ≤
      N * Real.exp (-(t * α ^ 2)) * (2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2)) := by
  have h := integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le ht y α
    (η := 1 / 8) (by norm_num)
  calc N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
          (Real.exp (1 / 8 * |w - (y + 2 * t * α)|) - 1)
      ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
          (2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2) * Real.exp (y * α + t * α ^ 2)) := by
        gcongr
    _ = N * (Real.exp (-((y + 2 * t * α) * α)) * Real.exp (y * α + t * α ^ 2)) *
          (2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2)) := by ring
    _ = _ := by rw [← Real.exp_add, scale_identity]

/-- The full-line tilted mass. -/
theorem tiltedMass_eq {t α y N : ℝ} (ht : 0 < t) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w, gaussDensity t (w - y) * Real.exp (w * α) = N * Real.exp (-(t * α ^ 2)) := by
  rw [integral_gaussDensity_sub_mul_rexp ht, mul_assoc, ← Real.exp_add, scale_identity]

/-- **The window mass.** -/
theorem windowMass_le {t X y : ℝ} (ht : 0 < t) (hX : 200 ≤ X)
    (hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2))
    {W : ℝ} (hW : W ≤ X / 32 - 1 / 2) :
    ∫ w in Ioc (9 / 2 : ℝ) W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        (1 + 2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2)) := by
  set α := (horizontalSlope X).re with hα
  set u := y + 2 * t * α with hu_def
  set N := ‖xiLine X u‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hint1 := integrable_gaussDensity_sub_mul_rexp ht y α
  have hint2 := integrable_modelError ht y α u (1 / 8) (by norm_num)
  have hmaj : Integrable (fun w => N * Real.exp (-(u * α)) *
      (gaussDensity t (w - y) * Real.exp (w * α) +
        gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (1 / 8 * |w - u|) - 1))) :=
    (hint1.add hint2).const_mul _
  have hnonneg : ∀ w, 0 ≤ N * Real.exp (-(u * α)) *
      (gaussDensity t (w - y) * Real.exp (w * α) +
        gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (1 / 8 * |w - u|) - 1)) := by
    intro w
    have h1 : 1 ≤ Real.exp (1 / 8 * |w - u|) := Real.one_le_exp (by positivity)
    have := gaussDensity_sub_mul_rexp_nonneg ht y α w
    positivity
  calc ∫ w in Ioc (9 / 2 : ℝ) W, gaussDensity t (w - y) * ‖xiLine X w‖
      ≤ ∫ w in Ioc (9 / 2 : ℝ) W, N * Real.exp (-(u * α)) *
          (gaussDensity t (w - y) * Real.exp (w * α) +
            gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (1 / 8 * |w - u|) - 1)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w =>
          mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hmaj.integrableOn ?_
        refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun w hw => ?_)
        have hwW : w ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) := ⟨hw.1.le, hw.2.trans hW⟩
        have hm := norm_xiLine_le_model hX hu hwW
        have hsplit : Real.exp ((w - u) * α) = Real.exp (-(u * α)) * Real.exp (w * α) := by
          rw [← Real.exp_add]; ring_nf
        rw [← hα, hsplit] at hm
        have hG := (gaussDensity_pos ht (w - y)).le
        calc gaussDensity t (w - y) * ‖xiLine X w‖
            ≤ gaussDensity t (w - y) * (N * (Real.exp (-(u * α)) * Real.exp (w * α)) *
                Real.exp (1 / 8 * |w - u|)) := by gcongr
          _ = _ := by ring
    _ ≤ ∫ w, N * Real.exp (-(u * α)) *
          (gaussDensity t (w - y) * Real.exp (w * α) +
            gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (1 / 8 * |w - u|) - 1)) :=
        setIntegral_le_integral hmaj (Eventually.of_forall hnonneg)
    _ = N * Real.exp (-(u * α)) * (∫ w, gaussDensity t (w - y) * Real.exp (w * α)) +
          N * Real.exp (-(u * α)) * ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
            (Real.exp (1 / 8 * |w - u|) - 1) := by
        rw [integral_const_mul, integral_add hint1 hint2]; ring
    _ ≤ N * Real.exp (-(t * α ^ 2)) +
          N * Real.exp (-(t * α ^ 2)) * (2 * (1 / 8) * Real.exp (t * (1 + 1 / 8) ^ 2)) := by
        rw [hu_def, tiltedMass_eq ht]
        exact add_le_add le_rfl (modelError_le ht hN0)
    _ = _ := by ring

theorem norm_horizontalSlope_le {X : ℝ} (hα : 0 ≤ (horizontalSlope X).re) :
    ‖horizontalSlope X‖ ≤ (horizontalSlope X).re + 1 := by
  rw [horizontalSlope_re] at hα ⊢
  unfold horizontalSlope
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα, norm_mul, Complex.norm_I, mul_one,
    norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  linarith [Real.pi_lt_d2]

theorem le_norm_horizontalSlope (X : ℝ) : (horizontalSlope X).re ≤ ‖horizontalSlope X‖ :=
  Complex.re_le_norm _

theorem gaussDensity_le {t : ℝ} (ht : 0 < t) (u : ℝ) :
    gaussDensity t u ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
  unfold gaussDensity
  have h : Real.exp (-(u ^ 2 / (4 * t))) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ u ^ 2 / (4 * t) := by positivity
    linarith)
  have hc : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
  calc _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 1 := by gcongr
    _ = _ := mul_one _

theorem height_eq {X : ℝ} (hX : 0 < X) :
    X = 2 * Real.pi * Real.exp (2 * (horizontalSlope X).re) := by
  rw [horizontalSlope_re, show 2 * (Real.log (X / (2 * Real.pi)) / 2) = Real.log (X / (2 * Real.pi))
    by ring, Real.exp_log (by positivity)]
  field_simp

/-- The model carries `F(9/2)` back to the centre `u`. -/
theorem norm_xiLine_nine_halves_le {t X y : ℝ} (hX : 200 ≤ X)
    (hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2)) :
    ‖xiLine X (9 / 2)‖ ≤ ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp ((9 / 2 - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re +
        ((y + 2 * t * (horizontalSlope X).re) - 9 / 2) / 8) := by
  have h := norm_xiLine_le_model hX hu ⟨le_rfl, hu.1.trans hu.2⟩
  rw [abs_of_nonpos (by linarith [hu.1]), mul_assoc, ← Real.exp_add] at h
  refine h.trans (le_of_eq ?_)
  congr 2
  ring

/-- **The strip integrand.** -/
theorem strip_integrand_le {t X y w : ℝ} (ht : 0 < t) (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2)
    (hα : 0 ≤ (horizontalSlope X).re)
    (hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2))
    (hw : w ∈ Icc (0 : ℝ) (9 / 2)) :
    (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖ ≤
      (5 / (2 * t) + (horizontalSlope X).re + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        (200 * (6 + X)) * (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp ((9 / 2 - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re +
            ((y + 2 * t * (horizontalSlope X).re) - 9 / 2) / 8)) := by
  have hwt : |(w - y) / (2 * t)| ≤ 5 / (2 * t) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
    gcongr
    rw [abs_le] at hy ⊢
    constructor <;> linarith [hw.1, hw.2]
  have ha := norm_horizontalSlope_le hα
  have hG := gaussDensity_le ht (w - y)
  have hF := (norm_xiLine_le_strip (by linarith) hw.1 hw.2).trans
    (mul_le_mul_of_nonneg_left (norm_xiLine_nine_halves_le hX hu) (by positivity))
  have hAB : |(w - y) / (2 * t)| + ‖horizontalSlope X‖ ≤ 5 / (2 * t) + (horizontalSlope X).re + 1 := by
    linarith
  have hC0 : 0 ≤ 5 / (2 * t) + (horizontalSlope X).re + 1 := by
    have : 0 ≤ 5 / (2 * t) := by positivity
    linarith
  have hG0 := (gaussDensity_pos ht (w - y)).le
  calc (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖
      ≤ ((5 / (2 * t) + (horizontalSlope X).re + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) *
          (200 * (6 + X) * (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
            Real.exp ((9 / 2 - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re +
              ((y + 2 * t * (horizontalSlope X).re) - 9 / 2) / 8))) :=
        mul_le_mul (mul_le_mul hAB hG hG0 hC0) hF (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- **The strip part of `D − aQ`, of `Q`, and the boundary value at `9/2`.** -/
theorem strip_terms_le {t X y : ℝ} (ht : 0 < t) (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2)
    (hα : 0 ≤ (horizontalSlope X).re)
    (hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2)) :
    (∫ w in Ioc (0 : ℝ) (9 / 2), (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) *
        gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRA t (horizontalSlope X).re ∧
    (∫ w in Ioc (0 : ℝ) (9 / 2), gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRA t (horizontalSlope X).re ∧
    gaussDensity t (9 / 2 - y) * ‖xiLine X (9 / 2)‖ ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRA t (horizontalSlope X).re := by
  set α := (horizontalSlope X).re with hαdef
  set u := y + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set c := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := by positivity
  set E := Real.exp ((9 / 2 - u) * α + (u - 9 / 2) / 8) with hE
  set K := (5 / (2 * t) + α + 1) * c * (200 * (6 + X)) * (N * E) with hK
  have hm1 : 1 ≤ 5 / (2 * t) + α + 1 := by
    have : 0 ≤ 5 / (2 * t) := by positivity
    linarith
  have hm2 : 1 ≤ 200 * (6 + X) := by linarith
  have hNE : 0 ≤ N * E := by positivity
  have hcNE : c * (N * E) ≤ K := by
    have : c * (N * E) = 1 * c * 1 * (N * E) := by ring
    rw [this, hK]
    gcongr
  have hFstrip : ∀ w ∈ Icc (0 : ℝ) (9 / 2), ‖xiLine X w‖ ≤ 200 * (6 + X) * (N * E) := fun w hw =>
    (norm_xiLine_le_strip (by linarith) hw.1 hw.2).trans
      (mul_le_mul_of_nonneg_left (norm_xiLine_nine_halves_le hX hu) (by positivity))
  have hpoint2 : ∀ w ∈ Icc (0 : ℝ) (9 / 2), gaussDensity t (w - y) * ‖xiLine X w‖ ≤ K := by
    intro w hw
    calc gaussDensity t (w - y) * ‖xiLine X w‖ ≤ c * (200 * (6 + X) * (N * E)) :=
          mul_le_mul (gaussDensity_le ht _) (hFstrip w hw) (norm_nonneg _) hc0
      _ = 1 * c * (200 * (6 + X)) * (N * E) := by ring
      _ ≤ K := by rw [hK]; gcongr
  have hvol : volume.real (Ioc (0 : ℝ) (9 / 2)) = 9 / 2 := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hint_bound : ∀ f : ℝ → ℝ, (∀ w, 0 ≤ f w) → (∀ w ∈ Icc (0 : ℝ) (9 / 2), f w ≤ K) →
      ∫ w in Ioc (0 : ℝ) (9 / 2), f w ≤ 9 / 2 * K := by
    intro f hf0 hfK
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := f) (C := K)
      measure_Ioc_lt_top (fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]; exact hfK w (Ioc_subset_Icc_self hw))
    rw [hvol] at h
    have := le_abs_self (∫ w in Ioc (0 : ℝ) (9 / 2), f w)
    rw [← Real.norm_eq_abs] at this
    linarith
  have hfinal : 9 / 2 * K ≤ N * Real.exp (-(t * α ^ 2)) * kklRA t α := by
    have hXe := height_eq (show 0 < X by linarith)
    rw [← hαdef] at hXe
    have hexp : E ≤ Real.exp (-(t * α ^ 2)) *
        Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8) := by
      rw [← Real.exp_add, hE]
      refine Real.exp_le_exp.mpr ?_
      rw [hudef]
      have hy1 := (abs_le.mp hy).1
      have hy2 := (abs_le.mp hy).2
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y + 1 / 2) hα]
    rw [hK, kklRA, ← hXe]
    have hN0 : 0 ≤ N := norm_nonneg _
    have hA : 0 ≤ 9 / 2 * (5 / (2 * t) + α + 1) * c * 200 * (6 + X) := by positivity
    calc 9 / 2 * ((5 / (2 * t) + α + 1) * c * (200 * (6 + X)) * (N * E))
        = (9 / 2 * (5 / (2 * t) + α + 1) * c * 200 * (6 + X)) * N * E := by ring
      _ ≤ (9 / 2 * (5 / (2 * t) + α + 1) * c * 200 * (6 + X)) * N *
            (Real.exp (-(t * α ^ 2)) * Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8)) := by
          gcongr
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · refine (hint_bound _ (fun w => mul_nonneg (mul_nonneg (by positivity)
      (gaussDensity_pos ht _).le) (norm_nonneg _)) fun w hw =>
      strip_integrand_le ht hX hy hα hu hw).trans hfinal
  · exact (hint_bound _ (fun w => mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _))
      hpoint2).trans hfinal
  · have h1 : gaussDensity t (9 / 2 - y) * ‖xiLine X (9 / 2)‖ ≤ c * (N * E) :=
      mul_le_mul (gaussDensity_le ht _) (norm_xiLine_nine_halves_le hX hu) (norm_nonneg _) hc0
    have hK0 : 0 ≤ K := hcNE.trans' (by positivity)
    linarith

/-- Half of the Gaussian absorbs `e^{u²/(8t)}`: `g_t(u) e^{u²/(8t)} ≤ 2 g_{2t}(u)`. -/
theorem gaussDensity_mul_exp_le {t : ℝ} (ht : 0 < t) (u : ℝ) :
    gaussDensity t u * Real.exp (u ^ 2 / (8 * t)) ≤ 2 * gaussDensity (2 * t) u := by
  unfold gaussDensity
  have hc : (4 * Real.pi * (2 * t)) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
    rw [show 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
      (show (-1 : ℝ) ≤ -(1 / 2) by norm_num)
    rw [Real.rpow_neg_one] at this
    linarith
  have he : Real.exp (-(u ^ 2 / (4 * t))) * Real.exp (u ^ 2 / (8 * t)) =
      Real.exp (-(u ^ 2 / (4 * (2 * t)))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hc, mul_assoc, he]
  have hpos : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u ^ 2 / (4 * (2 * t)))) := by
    positivity
  nlinarith

/-- **The far integrand.** -/
theorem far_integrand_le {t X y W w : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hX : 200 ≤ X)
    (hy : |y| ≤ 1 / 2) (hα : 0 ≤ (horizontalSlope X).re)
    (hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2))
    (hWu : y + 2 * t * (horizontalSlope X).re ≤ W) (hWX : W ≤ X / 32 - 1 / 2) (hw : W < w) :
    (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖ ≤
      2 * Real.exp 1 * (1 / (2 * t) + (horizontalSlope X).re + 1) *
        (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp ((W - (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8))) *
        (gaussDensity (2 * t) (w - y) *
          Real.exp ((w - y) + (w - W) * ((horizontalSlope X).re + 2))) := by
  set α := (horizontalSlope X).re with hαdef
  set u := y + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hW9 : 9 / 2 ≤ W := hu.1.trans hWu
  have hwy : 0 ≤ w - y := by linarith
  -- `F` at `W` and beyond
  have hFW : ‖xiLine X W‖ ≤ N * Real.exp ((W - u) * (α + 1 / 8)) := by
    have h := norm_xiLine_le_model hX hu ⟨hW9, hWX⟩
    rw [abs_of_nonneg (by linarith), mul_assoc, ← Real.exp_add] at h
    refine h.trans (le_of_eq ?_)
    congr 2; ring
  have hFw := norm_xiLine_le_far hX hW9 hw.le
  rw [← horizontalSlope_re, ← hαdef] at hFw
  have hexpo : (α + 2 + (w + 1 / 2) / (2 * X)) * (w - W) ≤
      (α + 2) * (w - W) + (w - y) ^ 2 / (8 * t) + 1 := by
    have hA : (w + 1 / 2) * (w - W) ≤ 2 * (w - y) ^ 2 + 2 := by
      nlinarith [sq_nonneg (w - y - (y + 1 / 2)), sq_nonneg (y + 1 / 2)]
    have hX0 : 0 < X := by linarith
    have h8 : 8 * t ≤ X := by linarith
    have hq : (w + 1 / 2) / (2 * X) * (w - W) ≤ ((w - y) ^ 2 + 1) / X := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hX0]
      nlinarith
    have hq2 : ((w - y) ^ 2 + 1) / X ≤ (w - y) ^ 2 / (8 * t) + 1 := by
      rw [add_div]
      have : (w - y) ^ 2 / X ≤ (w - y) ^ 2 / (8 * t) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h8
      have : 1 / X ≤ 1 := by rw [div_le_one hX0]; linarith
      linarith
    nlinarith
  have hFw' : ‖xiLine X w‖ ≤ N * Real.exp ((W - u) * (α + 1 / 8)) *
      (Real.exp ((α + 2) * (w - W)) * Real.exp ((w - y) ^ 2 / (8 * t)) * Real.exp 1) := by
    refine hFw.trans ?_
    rw [← Real.exp_add, ← Real.exp_add]
    calc ‖xiLine X W‖ * Real.exp ((α + 2 + (w + 1 / 2) / (2 * X)) * (w - W))
        ≤ N * Real.exp ((W - u) * (α + 1 / 8)) *
            Real.exp ((α + 2) * (w - W) + (w - y) ^ 2 / (8 * t) + 1) := by
          gcongr
    _ = _ := rfl
  -- the weight
  have hweight : |(w - y) / (2 * t)| + ‖horizontalSlope X‖ ≤
      (1 / (2 * t) + α + 1) * Real.exp (w - y) := by
    have he1 : w - y ≤ Real.exp (w - y) := by linarith [Real.add_one_le_exp (w - y)]
    have he2 : 1 ≤ Real.exp (w - y) := Real.one_le_exp hwy
    have ha := norm_horizontalSlope_le hα
    rw [abs_div, abs_of_nonneg hwy, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
    have : (w - y) / (2 * t) ≤ 1 / (2 * t) * Real.exp (w - y) := by
      rw [div_eq_mul_one_div, mul_comm]; gcongr
    nlinarith
  have hGabs := gaussDensity_mul_exp_le ht (w - y)
  have hG0 := (gaussDensity_pos ht (w - y)).le
  have hA0 : 0 ≤ |(w - y) / (2 * t)| + ‖horizontalSlope X‖ := by positivity
  calc (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖
      ≤ ((1 / (2 * t) + α + 1) * Real.exp (w - y)) * gaussDensity t (w - y) *
          (N * Real.exp ((W - u) * (α + 1 / 8)) *
            (Real.exp ((α + 2) * (w - W)) * Real.exp ((w - y) ^ 2 / (8 * t)) * Real.exp 1)) := by
        gcongr
    _ = (1 / (2 * t) + α + 1) * Real.exp 1 * (N * Real.exp ((W - u) * (α + 1 / 8))) *
          (Real.exp (w - y) * Real.exp ((α + 2) * (w - W))) *
          (gaussDensity t (w - y) * Real.exp ((w - y) ^ 2 / (8 * t))) := by ring
    _ ≤ (1 / (2 * t) + α + 1) * Real.exp 1 * (N * Real.exp ((W - u) * (α + 1 / 8))) *
          (Real.exp (w - y) * Real.exp ((α + 2) * (w - W))) *
          (2 * gaussDensity (2 * t) (w - y)) := by
        gcongr
    _ = _ := by
        rw [← Real.exp_add, show w - y + (α + 2) * (w - W) = (w - y) + (w - W) * (α + 2) by ring]
        ring

/-- **The far terms and the boundary value at `W = 2tα + α²`.** -/
theorem far_terms_le {t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2)
    (hα1 : 1 ≤ (horizontalSlope X).re)
    (hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2))
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2) :
    (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRC t (horizontalSlope X).re ∧
    (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRC t (horizontalSlope X).re ∧
    gaussDensity t (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 - y) *
        ‖xiLine X (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRB t (horizontalSlope X).re := by
  have hα : 0 ≤ (horizontalSlope X).re := by linarith
  set α := (horizontalSlope X).re with hαdef
  set u := y + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; nlinarith
  have hN0 : 0 ≤ N := norm_nonneg _
  set C := 2 * Real.exp 1 * (1 / (2 * t) + α + 1) * (N * Real.exp ((W - u) * (α + 1 / 8)))
    with hC
  have hC0 : 0 ≤ C := by positivity
  set m : ℝ → ℝ := fun w => C * (gaussDensity (2 * t) (w - y) *
      Real.exp ((w - y) + (w - W) * (α + 2))) with hm
  have hmsplit : ∀ w, m w = C * Real.exp (-y - W * (α + 2)) *
      (gaussDensity (2 * t) (w - y) * Real.exp (w * (α + 3))) := by
    intro w
    simp only [hm]
    rw [show (w - y) + (w - W) * (α + 2) = (-y - W * (α + 2)) + w * (α + 3) by ring, Real.exp_add]
    ring
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hm_int : Integrable m := by
    refine ((integrable_gaussDensity_sub_mul_rexp h2t y (α + 3)).const_mul
      (C * Real.exp (-y - W * (α + 2)))).congr (Eventually.of_forall fun w => ?_)
    simp only
    rw [hmsplit]
  have hm0 : ∀ w, 0 ≤ m w := fun w => by
    simp only [hm]
    have := (gaussDensity_pos h2t (w - y)).le
    positivity
  have hm_val : ∫ w, m w = C * Real.exp (-y - W * (α + 2)) *
      Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2) := by
    simp_rw [hmsplit]
    rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp h2t]
  have hm_le : ∫ w, m w ≤ N * Real.exp (-(t * α ^ 2)) * kklRC t α := by
    rw [hm_val, hC, kklRC]
    have hexp : Real.exp ((W - u) * (α + 1 / 8)) * Real.exp (-y - W * (α + 2)) *
        Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2) ≤ Real.exp (-(t * α ^ 2)) *
        Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      rw [hWdef, hudef]
      nlinarith
    have hk : 0 ≤ 2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N := by positivity
    calc 2 * Real.exp 1 * (1 / (2 * t) + α + 1) * (N * Real.exp ((W - u) * (α + 1 / 8))) *
          Real.exp (-y - W * (α + 2)) * Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2)
        = (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) *
            (Real.exp ((W - u) * (α + 1 / 8)) * Real.exp (-y - W * (α + 2)) *
              Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2)) := by ring
      _ ≤ (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
          gcongr
      _ ≤ 2 * (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
          have : 0 ≤ (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
            positivity
          linarith
      _ = _ := by ring
  have hpoint : ∀ w ∈ Ioi W, (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) *
      gaussDensity t (w - y) * ‖xiLine X w‖ ≤ m w := fun w hw =>
    far_integrand_le ht ht8 hX hy hα hu hWu hWX hw
  have hone : ∀ w, 1 ≤ |(w - y) / (2 * t)| + ‖horizontalSlope X‖ := by
    intro w
    have := le_norm_horizontalSlope X
    have := abs_nonneg ((w - y) / (2 * t))
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ ((setIntegral_le_integral (s := Ioi W) hm_int
      (Eventually.of_forall hm0)).trans hm_le)
    refine integral_mono_of_nonneg (Eventually.of_forall fun w => ?_) hm_int.integrableOn
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpoint))
    exact mul_nonneg (mul_nonneg (by positivity) (gaussDensity_pos ht _).le) (norm_nonneg _)
  · refine le_trans ?_ ((setIntegral_le_integral (s := Ioi W) hm_int
      (Eventually.of_forall hm0)).trans hm_le)
    refine integral_mono_of_nonneg (Eventually.of_forall fun w =>
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hm_int.integrableOn
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_))
    have hGF : 0 ≤ gaussDensity t (w - y) * ‖xiLine X w‖ :=
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)
    have := hpoint w hw
    have h1 := hone w
    calc gaussDensity t (w - y) * ‖xiLine X w‖
        ≤ (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * (gaussDensity t (w - y) * ‖xiLine X w‖) :=
          le_mul_of_one_le_left hGF h1
      _ = _ := by ring
      _ ≤ m w := this
  · have hW9 : 9 / 2 ≤ W := hu.1.trans hWu
    have hFW : ‖xiLine X W‖ ≤ N * Real.exp ((W - u) * (α + 1 / 8)) := by
      have h := norm_xiLine_le_model hX hu ⟨hW9, hWX⟩
      rw [abs_of_nonneg (by linarith), mul_assoc, ← Real.exp_add] at h
      refine h.trans (le_of_eq ?_)
      congr 2; ring
    have hWy : α ^ 2 - 1 / 2 ≤ W - y := by rw [hWdef]; nlinarith
    have hα2 : 0 ≤ α ^ 2 - 1 / 2 := by nlinarith
    unfold gaussDensity
    rw [kklRB]
    have hc0 : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
    have hexp : Real.exp (-((W - y) ^ 2 / (4 * t))) * Real.exp ((W - u) * (α + 1 / 8)) ≤
        Real.exp (-(t * α ^ 2)) * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) +
          (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hsq : (α ^ 2 - 1 / 2) ^ 2 / (4 * t) ≤ (W - y) ^ 2 / (4 * t) := by
        gcongr
      have hWu' : W - u ≤ α ^ 2 + 1 / 2 := by rw [hWdef, hudef]; linarith
      have : (W - u) * (α + 1 / 8) ≤ (α ^ 2 + 1 / 2) * (α + 1 / 8) := by
        gcongr
      linarith
    calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((W - y) ^ 2 / (4 * t))) * ‖xiLine X W‖
        ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((W - y) ^ 2 / (4 * t))) *
            (N * Real.exp ((W - u) * (α + 1 / 8))) := by gcongr
      _ = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * N * (Real.exp (-((W - y) ^ 2 / (4 * t))) *
            Real.exp ((W - u) * (α + 1 / 8))) := by ring
      _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * N * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) +
              t * α ^ 2)) := by gcongr
      _ = _ := by ring

end

end RHTower.DeBruijn
