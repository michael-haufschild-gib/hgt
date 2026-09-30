import GaloisForLFunctions.RHTower.HalfGaussTransformMonotonicity

/-!
# Window estimates for one-sided Gaussian averages

Let `G(w) = g_t(w − y)`, `Q = ∫_0^∞ G F`, `D = ∫_0^∞ ((w − y)/(2t)) G F`, and fix a window
`[w₁, W] ⊂ [0, ∞)`.

* If `F` follows the exponential model `F(u) e^{(w−u)a}` on the window up to the relative error
  `e^{η|w−u|} − 1`, then `Q` is close to `Main = F(u) e^{−ua} e^{ya + ta²}`, the full-line Gaussian
  average of the model (`norm_halfGaussTransform_sub_main_le`): the error is the model error, the
  two Gaussian tails of the model outside the window, and the parts of `Q` outside the window.
* If `‖F' − aF‖ ≤ η‖F‖` on the window, then integration by parts gives
  `‖D − aQ‖ ≤ ∫_out (|w−y|/(2t) + ‖a‖) G‖F‖ + G(w₁)‖F(w₁)‖ + G(W)‖F(W)‖ + η ∫_{w₁}^{W} G‖F‖`
  (`norm_slope_sub_mul_le`).
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

theorem integral_split_three {f : ℝ → ℂ} {w₁ W : ℝ} (h1 : w₁ ≤ W) (hf : Integrable f) :
    ∫ w, f w = (∫ w in Iic w₁, f w) + (∫ w in Ioc w₁ W, f w) + ∫ w in Ioi W, f w := by
  have hd2 : Disjoint (Ioc w₁ W) (Ioi W) :=
    Set.disjoint_left.mpr fun x hx hx' => (not_lt.mpr hx.2) hx'
  rw [← integral_add_compl (s := Iic w₁) measurableSet_Iic hf, compl_Iic,
    ← Ioc_union_Ioi_eq_Ioi h1, setIntegral_union hd2 measurableSet_Ioi hf.integrableOn
      hf.integrableOn]
  ring

theorem integrable_modelError {t : ℝ} (ht : 0 < t) (y α u η : ℝ) (hη : 0 ≤ η) :
    Integrable (fun w => gaussDensity t (w - y) * Real.exp (w * α) *
      (Real.exp (η * |w - u|) - 1)) := by
  refine ((integrable_gaussDensity_sub_mul_rexp_mul_rexp ht y α η u).add
    (integrable_gaussDensity_sub_mul_rexp_mul_rexp ht y α (-η) u)).mono' ?_
    (Eventually.of_forall fun w => ?_)
  · have := continuous_gaussDensity t
    exact (by fun_prop : Continuous fun w => gaussDensity t (w - y) * Real.exp (w * α) *
      (Real.exp (η * |w - u|) - 1)).aestronglyMeasurable
  · have hG := gaussDensity_sub_mul_rexp_nonneg ht y α w
    have h1 : 1 ≤ Real.exp (η * |w - u|) := Real.one_le_exp (mul_nonneg hη (abs_nonneg _))
    have h2 : Real.exp (η * |w - u|) - 1 ≤ Real.exp (η * (w - u)) + Real.exp (-η * (w - u)) := by
      rcases le_total 0 (w - u) with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-η * (w - u))]
      · rw [abs_of_nonpos h]
        have : η * -(w - u) = -η * (w - u) := by ring
        rw [this]; linarith [Real.exp_pos (η * (w - u))]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hG (by linarith))]
    simp only [Pi.add_apply]
    nlinarith

theorem norm_gauss_mul (t y w : ℝ) (ht : 0 < t) (z : ℂ) :
    ‖(gaussDensity t (w - y) : ℂ) * z‖ = gaussDensity t (w - y) * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht _)]

/-- **The main-term estimate.** -/
theorem norm_halfGaussTransform_sub_main_le {t : ℝ} (ht : 0 < t) {F : ℝ → ℂ} (hF : Continuous F)
    (hint : Integrable (fun w => Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖)) {y w₁ W u η : ℝ} {a : ℂ}
    (hη : 0 ≤ η) (h0 : 0 ≤ w₁) (h1 : w₁ ≤ W)
    (hmodel : ∀ w ∈ Icc w₁ W, ‖F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
      ‖F u‖ * Real.exp ((w - u) * a.re) * (Real.exp (η * |w - u|) - 1)) :
    ‖halfGaussTransform t F y - F u * Complex.exp (-(u * a)) * Complex.exp (y * a + t * a ^ 2)‖ ≤
      ‖F u‖ * Real.exp (-(u * a.re)) *
          ((∫ w in Iic w₁, gaussDensity t (w - y) * Real.exp (w * a.re)) +
            (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * a.re)) +
            ∫ w, gaussDensity t (w - y) * Real.exp (w * a.re) * (Real.exp (η * |w - u|) - 1)) +
        (∫ w in Ioc 0 w₁, gaussDensity t (w - y) * ‖F w‖) +
        ∫ w in Ioi W, gaussDensity t (w - y) * ‖F w‖ := by
  set G : ℝ → ℝ := fun w => gaussDensity t (w - y) with hG
  have hGc : Continuous G := (continuous_gaussDensity t).comp (continuous_id.sub continuous_const)
  have hGF := integrable_gaussDensity_sub_mul ht hF hint y
  have hGe := integrable_gaussDensity_sub_mul_exp ht y a
  set Mn : ℂ := F u * Complex.exp (-(u * a)) * Complex.exp (y * a + t * a ^ 2) with hMn
  set c : ℂ := F u * Complex.exp (-(u * a)) with hc
  have hcn : ‖c‖ = ‖F u‖ * Real.exp (-(u * a.re)) := by
    rw [hc, norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  -- split `Q`
  unfold halfGaussTransform
  rw [setIntegral_Ioi_split h0 h1 hGF.integrableOn]
  -- the window part against the model
  have hmodel_split : ∫ w in Ioc w₁ W, (G w : ℂ) * F w =
      c * (∫ w in Ioc w₁ W, (G w : ℂ) * Complex.exp (w * a)) +
        ∫ w in Ioc w₁ W, (G w : ℂ) * (F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)) := by
    have hcont1 : Continuous fun w : ℝ => (G w : ℂ) * Complex.exp (w * a) := by fun_prop
    have hcont2 : Continuous fun w : ℝ =>
        (G w : ℂ) * (F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)) := by fun_prop
    rw [← integral_const_mul, ← integral_add (hcont1.integrableOn_Ioc.const_mul c)
      hcont2.integrableOn_Ioc]
    congr 1
    funext w
    have he : Complex.exp (((w - u : ℝ) : ℂ) * a) = Complex.exp (-(u * a)) * Complex.exp (w * a) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [hc, he]
    ring
  have hfull : Complex.exp (y * a + t * a ^ 2) =
      (∫ w in Iic w₁, (G w : ℂ) * Complex.exp (w * a)) +
        (∫ w in Ioc w₁ W, (G w : ℂ) * Complex.exp (w * a)) +
        ∫ w in Ioi W, (G w : ℂ) * Complex.exp (w * a) := by
    rw [← integral_gaussDensity_sub_mul_exp ht]
    exact integral_split_three h1 hGe
  -- bounds on the pieces
  have hA : ‖∫ w in Ioc 0 w₁, (G w : ℂ) * F w‖ ≤ ∫ w in Ioc 0 w₁, G w * ‖F w‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext w; exact norm_gauss_mul t y w ht _
  have hC : ‖∫ w in Ioi W, (G w : ℂ) * F w‖ ≤ ∫ w in Ioi W, G w * ‖F w‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext w; exact norm_gauss_mul t y w ht _
  have hnormexp : ∀ w : ℝ, ‖(G w : ℂ) * Complex.exp (w * a)‖ = G w * Real.exp (w * a.re) := by
    intro w
    rw [norm_gauss_mul t y w ht, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  have hT1 : ‖∫ w in Iic w₁, (G w : ℂ) * Complex.exp (w * a)‖ ≤
      ∫ w in Iic w₁, G w * Real.exp (w * a.re) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext w; exact hnormexp w
  have hT2 : ‖∫ w in Ioi W, (G w : ℂ) * Complex.exp (w * a)‖ ≤
      ∫ w in Ioi W, G w * Real.exp (w * a.re) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext w; exact hnormexp w
  have hME : ‖∫ w in Ioc w₁ W, (G w : ℂ) * (F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a))‖ ≤
      ‖F u‖ * Real.exp (-(u * a.re)) *
        ∫ w, G w * Real.exp (w * a.re) * (Real.exp (η * |w - u|) - 1) := by
    have hint_me := integrable_modelError ht y a.re u η hη
    calc ‖∫ w in Ioc w₁ W, (G w : ℂ) * (F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a))‖
        ≤ ∫ w in Ioc w₁ W, ‖F u‖ * Real.exp (-(u * a.re)) *
            (G w * Real.exp (w * a.re) * (Real.exp (η * |w - u|) - 1)) := by
          refine norm_integral_le_of_norm_le ((hint_me.const_mul _).integrableOn) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun w hw => ?_)
          rw [norm_gauss_mul t y w ht]
          have hm := hmodel w (Ioc_subset_Icc_self hw)
          have hsplit : Real.exp ((w - u) * a.re) = Real.exp (-(u * a.re)) * Real.exp (w * a.re) := by
            rw [← Real.exp_add]; ring_nf
          rw [hsplit] at hm
          have hGn : 0 ≤ G w := (gaussDensity_pos ht _).le
          calc G w * ‖F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)‖
              ≤ G w * (‖F u‖ * (Real.exp (-(u * a.re)) * Real.exp (w * a.re)) *
                  (Real.exp (η * |w - u|) - 1)) := by gcongr
            _ = _ := by ring
      _ = ‖F u‖ * Real.exp (-(u * a.re)) *
            ∫ w in Ioc w₁ W, G w * Real.exp (w * a.re) * (Real.exp (η * |w - u|) - 1) := by
          rw [integral_const_mul]
      _ ≤ ‖F u‖ * Real.exp (-(u * a.re)) *
            ∫ w, G w * Real.exp (w * a.re) * (Real.exp (η * |w - u|) - 1) := by
          refine mul_le_mul_of_nonneg_left (setIntegral_le_integral hint_me
            (Eventually.of_forall fun w => ?_)) (by positivity)
          have h1 : 1 ≤ Real.exp (η * |w - u|) := Real.one_le_exp (mul_nonneg hη (abs_nonneg _))
          exact mul_nonneg (gaussDensity_sub_mul_rexp_nonneg ht y _ w) (by linarith)
  -- assemble
  have hkey : (∫ w in Ioc 0 w₁, (G w : ℂ) * F w) + (∫ w in Ioc w₁ W, (G w : ℂ) * F w) +
      (∫ w in Ioi W, (G w : ℂ) * F w) - Mn =
      (∫ w in Ioc 0 w₁, (G w : ℂ) * F w) + (∫ w in Ioi W, (G w : ℂ) * F w) -
        c * ((∫ w in Iic w₁, (G w : ℂ) * Complex.exp (w * a)) +
          ∫ w in Ioi W, (G w : ℂ) * Complex.exp (w * a)) +
        ∫ w in Ioc w₁ W, (G w : ℂ) * (F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a)) := by
    rw [hmodel_split, hMn]
    have : (∫ w in Ioc w₁ W, (G w : ℂ) * Complex.exp (w * a)) =
        Complex.exp (y * a + t * a ^ 2) - (∫ w in Iic w₁, (G w : ℂ) * Complex.exp (w * a)) -
          ∫ w in Ioi W, (G w : ℂ) * Complex.exp (w * a) := by
      rw [hfull]; ring
    rw [this]
    ring
  rw [hkey]
  calc ‖(∫ w in Ioc 0 w₁, (G w : ℂ) * F w) + (∫ w in Ioi W, (G w : ℂ) * F w) -
        c * ((∫ w in Iic w₁, (G w : ℂ) * Complex.exp (w * a)) +
          ∫ w in Ioi W, (G w : ℂ) * Complex.exp (w * a)) +
        ∫ w in Ioc w₁ W, (G w : ℂ) * (F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a))‖
      ≤ ‖∫ w in Ioc 0 w₁, (G w : ℂ) * F w‖ + ‖∫ w in Ioi W, (G w : ℂ) * F w‖ +
          ‖c‖ * (‖∫ w in Iic w₁, (G w : ℂ) * Complex.exp (w * a)‖ +
            ‖∫ w in Ioi W, (G w : ℂ) * Complex.exp (w * a)‖) +
          ‖∫ w in Ioc w₁ W, (G w : ℂ) * (F w - F u * Complex.exp (((w - u : ℝ) : ℂ) * a))‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        · exact norm_add_le _ _
        · rw [norm_mul]; gcongr; exact norm_add_le _ _
    _ ≤ (∫ w in Ioc 0 w₁, G w * ‖F w‖) + (∫ w in Ioi W, G w * ‖F w‖) +
          ‖F u‖ * Real.exp (-(u * a.re)) * ((∫ w in Iic w₁, G w * Real.exp (w * a.re)) +
            ∫ w in Ioi W, G w * Real.exp (w * a.re)) +
          ‖F u‖ * Real.exp (-(u * a.re)) *
            ∫ w, G w * Real.exp (w * a.re) * (Real.exp (η * |w - u|) - 1) := by
        rw [hcn]
        gcongr
    _ = _ := by ring

/-- **The slope estimate.** -/
theorem norm_slope_sub_mul_le {t : ℝ} (ht : 0 < t) {F F' : ℝ → ℂ}
    (hFd : ∀ w, HasDerivAt F (F' w) w) (hF' : Continuous F')
    (hint : Integrable (fun w => Real.exp (-(w ^ 2 / (16 * t))) * ‖F w‖)) {y w₁ W η : ℝ} {a : ℂ}
    (h0 : 0 ≤ w₁) (h1 : w₁ ≤ W)
    (hderiv : ∀ w ∈ Icc w₁ W, ‖F' w - a * F w‖ ≤ η * ‖F w‖) :
    ‖(∫ w in Ioi (0 : ℝ), (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) -
        a * halfGaussTransform t F y‖ ≤
      (∫ w in Ioc 0 w₁, (|(w - y) / (2 * t)| + ‖a‖) * gaussDensity t (w - y) * ‖F w‖) +
        (∫ w in Ioi W, (|(w - y) / (2 * t)| + ‖a‖) * gaussDensity t (w - y) * ‖F w‖) +
        gaussDensity t (w₁ - y) * ‖F w₁‖ + gaussDensity t (W - y) * ‖F W‖ +
        η * ∫ w in Ioc w₁ W, gaussDensity t (w - y) * ‖F w‖ := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun w => (hFd w).continuousAt
  set G : ℝ → ℝ := fun w => gaussDensity t (w - y) with hG
  set sl : ℝ → ℝ := fun w => (w - y) / (2 * t) with hsl
  have hGc : Continuous G := (continuous_gaussDensity t).comp (continuous_id.sub continuous_const)
  have hslc : Continuous sl := by fun_prop
  have hSF := integrable_slope_mul ht hF hint y
  have hGF := integrable_gaussDensity_sub_mul ht hF hint y
  have hnS : ∀ w, ‖(((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w‖ =
      |sl w| * G w * ‖F w‖ := by
    intro w
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussDensity_pos ht _)]
  have hnG : ∀ w, ‖(G w : ℂ) * F w‖ = G w * ‖F w‖ := fun w => norm_gauss_mul t y w ht _
  -- the bracket bound on an outer region
  have hbracket : ∀ s : Set ℝ, MeasurableSet s →
      Integrable (fun w => (|sl w| + ‖a‖) * G w * ‖F w‖) (volume.restrict s) →
      ‖(∫ w in s, (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) -
          a * ∫ w in s, (G w : ℂ) * F w‖ ≤ ∫ w in s, (|sl w| + ‖a‖) * G w * ‖F w‖ := by
    intro s hs hmaj
    rw [← integral_const_mul, ← integral_sub hSF.integrableOn (hGF.integrableOn.const_mul a)]
    refine norm_integral_le_of_norm_le hmaj (Eventually.of_forall fun w => ?_)
    refine (norm_sub_le _ _).trans ?_
    rw [hnS, norm_mul, hnG]
    nlinarith [norm_nonneg a, abs_nonneg (sl w), (gaussDensity_pos ht (w - y)).le, norm_nonneg (F w)]
  have hmajA : Integrable (fun w => (|sl w| + ‖a‖) * G w * ‖F w‖) (volume.restrict (Ioc 0 w₁)) :=
    (by fun_prop : Continuous fun w => (|sl w| + ‖a‖) * G w * ‖F w‖).integrableOn_Ioc
  have hmajC : Integrable (fun w => (|sl w| + ‖a‖) * G w * ‖F w‖) (volume.restrict (Ioi W)) := by
    refine (hSF.norm.add (hGF.norm.const_mul ‖a‖)).integrableOn.congr ?_
    refine Eventually.of_forall fun w => ?_
    simp only [Pi.add_apply]
    rw [hnS, hnG]
    ring
  have hA := hbracket (Ioc 0 w₁) measurableSet_Ioc hmajA
  have hC := hbracket (Ioi W) measurableSet_Ioi hmajC
  -- the window
  have hwin := integral_Ioc_slope_eq (t := t) hFd hF' y h1
  have hmid : ‖(∫ w in Ioc w₁ W, (G w : ℂ) * F' w) - a * ∫ w in Ioc w₁ W, (G w : ℂ) * F w‖ ≤
      η * ∫ w in Ioc w₁ W, G w * ‖F w‖ := by
    have hc1 : Continuous fun w => (G w : ℂ) * F' w := by fun_prop
    have hc2 : Continuous fun w => (G w : ℂ) * F w := by fun_prop
    rw [← integral_const_mul, ← integral_sub hc1.integrableOn_Ioc (hc2.integrableOn_Ioc.const_mul a),
      ← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((by fun_prop : Continuous fun w => η * (G w * ‖F w‖)).integrableOn_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun w hw => ?_))
    have hd := hderiv w (Ioc_subset_Icc_self hw)
    have : (G w : ℂ) * F' w - a * ((G w : ℂ) * F w) = (G w : ℂ) * (F' w - a * F w) := by ring
    rw [this, norm_gauss_mul t y w ht]
    have hGn : 0 ≤ G w := (gaussDensity_pos ht _).le
    calc G w * ‖F' w - a * F w‖ ≤ G w * (η * ‖F w‖) := by gcongr
      _ = η * (G w * ‖F w‖) := by ring
  -- assemble
  unfold halfGaussTransform
  rw [setIntegral_Ioi_split h0 h1 hSF.integrableOn, setIntegral_Ioi_split h0 h1 hGF.integrableOn,
    hwin]
  have hkey : (∫ w in Ioc 0 w₁, (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) +
      ((G w₁ : ℂ) * F w₁ - (G W : ℂ) * F W + ∫ w in Ioc w₁ W, (G w : ℂ) * F' w) +
      (∫ w in Ioi W, (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) -
      a * ((∫ w in Ioc 0 w₁, (G w : ℂ) * F w) + (∫ w in Ioc w₁ W, (G w : ℂ) * F w) +
        ∫ w in Ioi W, (G w : ℂ) * F w) =
      ((∫ w in Ioc 0 w₁, (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) -
          a * ∫ w in Ioc 0 w₁, (G w : ℂ) * F w) +
        ((∫ w in Ioi W, (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * F w) -
          a * ∫ w in Ioi W, (G w : ℂ) * F w) +
        (G w₁ : ℂ) * F w₁ - (G W : ℂ) * F W +
        ((∫ w in Ioc w₁ W, (G w : ℂ) * F' w) - a * ∫ w in Ioc w₁ W, (G w : ℂ) * F w) := by ring
  rw [hkey]
  have h5 : ∀ p q r u v : ℂ, ‖p + q + r - u + v‖ ≤ ‖p‖ + ‖q‖ + ‖r‖ + ‖u‖ + ‖v‖ := by
    intro p q r u v
    calc ‖p + q + r - u + v‖ ≤ ‖p + q + r - u‖ + ‖v‖ := norm_add_le _ _
      _ ≤ ‖p + q + r‖ + ‖u‖ + ‖v‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖p + q‖ + ‖r‖ + ‖u‖ + ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖p‖ + ‖q‖ + ‖r‖ + ‖u‖ + ‖v‖ := by gcongr; exact norm_add_le _ _
  refine (h5 _ _ _ _ _).trans ?_
  rw [hnG, hnG]
  linarith [hA, hC, hmid]

end

end RHTower.DeBruijn
