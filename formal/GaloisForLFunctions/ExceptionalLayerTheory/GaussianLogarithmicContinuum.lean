import GaloisForLFunctions.ExceptionalLayerTheory.GaussianTypeIContinuum

/-!
# Logarithmic Gaussian lattice remainders

Scaling the logarithm before estimating its absolute value retains the
Gaussian power saving. The signed logarithmic continuum term is kept intact.
-/

open Complex MeasureTheory Set Filter Topology Finset

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A logarithmic divisor fibre of the Gaussian Mellin kernel. -/
def gaussianLogMellinWeight (w ε : ℂ) (b x : ℝ) : ℂ :=
  (Real.log (x / b) : ℂ) * gaussianMellinWeight w ε x

/-- An absolute Gaussian moment. -/
def gaussianRealMoment (q α : ℝ) : ℝ :=
  (1 / 2) * (1 / α) ^ ((q + 1) / 2) * Real.Gamma ((q + 1) / 2)

/-- The logarithmic moment budget, normalized at the freely chosen scale `X`. -/
def gaussianLogMomentBudget (q α X b : ℝ) : ℝ :=
  gaussianRealMoment (q + 1) α / X + X * gaussianRealMoment (q - 1) α +
    |Real.log (X / b)| * gaussianRealMoment q α

private theorem abs_log_le_add_inv {x : ℝ} (hx : 0 < x) :
    |Real.log x| ≤ x + x⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h2
  exact abs_le.mpr ⟨by linarith [inv_pos.mpr hx], by linarith [inv_pos.mpr hx]⟩

/-- Normalize before taking absolute values: both powers have the same
Gaussian scaling after integration. -/
theorem abs_log_div_le_scaled {x X b : ℝ} (hx : 0 < x) (hX : 0 < X) (hb : 0 < b) :
    |Real.log (x / b)| ≤ x / X + X / x + |Real.log (X / b)| := by
  have he : x / b = (x / X) * (X / b) := by field_simp
  rw [he, Real.log_mul (div_ne_zero hx.ne' hX.ne') (div_ne_zero hX.ne' hb.ne')]
  have h := abs_log_le_add_inv (div_pos hx hX)
  simp only [inv_div] at h
  linarith [abs_add_le (Real.log (x / X)) (Real.log (X / b))]

private theorem integrable_gaussian_power {q α : ℝ} (hq : -1 < q) (hα : 0 < α) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-α * x ^ (2 : ℕ))) (Ioi 0) := by
  simpa only [Real.rpow_two] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num : (1 : ℝ) ≤ 2) hα)

private theorem integral_gaussian_power {q α : ℝ} (hq : -1 < q) (hα : 0 < α) :
    (∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-α * x ^ 2)) = gaussianRealMoment q α := by
  exact RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi hq hα

private def gaussianLogMajorant (q α X b x : ℝ) : ℝ :=
  X⁻¹ * (x ^ (q + 1) * Real.exp (-α * x ^ 2)) +
    X * (x ^ (q - 1) * Real.exp (-α * x ^ 2)) +
    |Real.log (X / b)| * (x ^ q * Real.exp (-α * x ^ 2))

private theorem log_gaussian_le_majorant {q α X b x : ℝ}
    (hx : 0 < x) (hX : 0 < X) (hb : 0 < b) :
    |Real.log (x / b)| * (x ^ q * Real.exp (-α * x ^ 2)) ≤
      gaussianLogMajorant q α X b x := by
  have h := mul_le_mul_of_nonneg_right (abs_log_div_le_scaled hx hX hb)
    (show 0 ≤ x ^ q * Real.exp (-α * x ^ 2) by positivity)
  have hp : x ^ (q + 1) = x ^ q * x := by rw [Real.rpow_add hx, Real.rpow_one]
  have hm : x ^ (q - 1) = x ^ q / x := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_neg_one, div_eq_mul_inv]
  calc
    _ ≤ (x / X + X / x + |Real.log (X / b)|) *
        (x ^ q * Real.exp (-α * x ^ 2)) := h
    _ = _ := by unfold gaussianLogMajorant; rw [hp, hm]; ring

private theorem integrable_gaussianLogMajorant {q α : ℝ} (hq : 0 < q)
    (hα : 0 < α) (X b : ℝ) :
    IntegrableOn (gaussianLogMajorant q α X b) (Ioi 0) :=
  (((integrable_gaussian_power (by linarith : -1 < q + 1) hα).const_mul _).add
    ((integrable_gaussian_power (by linarith : -1 < q - 1) hα).const_mul _)).add
    ((integrable_gaussian_power (by linarith : -1 < q) hα).const_mul _)

private theorem integral_gaussianLogMajorant {q α : ℝ} (hq : 0 < q)
    (hα : 0 < α) (X b : ℝ) :
    (∫ x in Ioi (0 : ℝ), gaussianLogMajorant q α X b x) =
      gaussianLogMomentBudget q α X b := by
  have hp := (integrable_gaussian_power (by linarith : -1 < q + 1) hα).const_mul X⁻¹
  have hm := (integrable_gaussian_power (by linarith : -1 < q - 1) hα).const_mul X
  have h0 := (integrable_gaussian_power (by linarith : -1 < q) hα).const_mul |Real.log (X / b)|
  have hpm : IntegrableOn (fun x : ℝ =>
      X⁻¹ * (x ^ (q + 1) * Real.exp (-α * x ^ 2)) +
        X * (x ^ (q - 1) * Real.exp (-α * x ^ 2))) (Ioi 0) := hp.add hm
  unfold gaussianLogMajorant
  rw [integral_add hpm h0, integral_add hp hm,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_gaussian_power (by linarith) hα,
    integral_gaussian_power (by linarith) hα,
    integral_gaussian_power (by linarith) hα]
  unfold gaussianLogMomentBudget
  ring

private theorem norm_gaussianMellinWeight {w ε : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖gaussianMellinWeight w ε x‖ = x ^ w.re * Real.exp (-ε.re * x ^ 2) := by
  rw [gaussianMellinWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp]
  congr 2
  simp [pow_two]

private theorem continuousOn_gaussianLogMellinWeight {w : ℂ} (hw : 0 < w.re)
    (ε : ℂ) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (gaussianLogMellinWeight w ε b) (Ioi 0) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_id.div_const b).log fun x hx => ne_of_gt (div_pos hx hb))
  · exact ((Complex.continuous_ofReal_cpow_const hw).mul (by fun_prop)).continuousOn

/-- Absolute convergence of the logarithmic continuous fibre. -/
theorem integrableOn_gaussianLogMellinWeight {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (gaussianLogMellinWeight w ε b) (Ioi 0) := by
  refine (integrable_gaussianLogMajorant hw hε 1 b).mono'
    ((continuousOn_gaussianLogMellinWeight hw ε hb).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_gaussianMellinWeight hx]
  exact log_gaussian_le_majorant hx zero_lt_one hb

/-- A logarithmic moment costs a scale logarithm, with no loss of Gaussian power. -/
theorem integral_norm_gaussianLogMellinWeight_le {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {X b : ℝ} (hX : 0 < X) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianLogMellinWeight w ε b x‖) ≤
      gaussianLogMomentBudget w.re ε.re X b := by
  rw [← integral_gaussianLogMajorant hw hε X b]
  refine integral_mono_ae (integrableOn_gaussianLogMellinWeight hw hε hb).norm
    (integrable_gaussianLogMajorant hw hε X b) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_gaussianMellinWeight hx]
  exact log_gaussian_le_majorant hx hX hb

private def gaussianLogMellinDeriv (w ε : ℂ) (b x : ℝ) : ℂ :=
  gaussianMellinWeight (w - 1) ε x +
    w * gaussianLogMellinWeight (w - 1) ε b x -
    2 * ε * gaussianLogMellinWeight (w + 1) ε b x

/-- Total variation of a logarithmic Gaussian fibre. -/
def gaussianLogMellinVariation (w ε : ℂ) (X b : ℝ) : ℝ :=
  gaussianRealMoment (w.re - 1) ε.re +
    ‖w‖ * gaussianLogMomentBudget (w.re - 1) ε.re X b +
    2 * ‖ε‖ * gaussianLogMomentBudget (w.re + 1) ε.re X b

private theorem integrable_gaussianLogMellinDeriv {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (gaussianLogMellinDeriv w ε b) (Ioi 0) := by
  have hm : 0 < (w - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hp : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  exact ((integrableOn_gaussianMellinWeight hm hε).add
    ((integrableOn_gaussianLogMellinWeight hm hε hb).const_mul w)).sub
      ((integrableOn_gaussianLogMellinWeight hp hε hb).const_mul (2 * ε))

private theorem integral_norm_gaussianMellinWeight {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianMellinWeight w ε x‖) =
      gaussianRealMoment w.re ε.re := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_gaussianMellinWeight hx)]
  exact integral_gaussian_power (by linarith) hε

private theorem integral_norm_gaussianLogMellinDeriv_le {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {X b : ℝ} (hX : 0 < X) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianLogMellinDeriv w ε b x‖) ≤
      gaussianLogMellinVariation w ε X b := by
  have hm : 0 < (w - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hp : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have h0 := (integrableOn_gaussianMellinWeight hm hε).norm
  have h1 := (integrableOn_gaussianLogMellinWeight hm hε hb).norm.const_mul ‖w‖
  have h2 := (integrableOn_gaussianLogMellinWeight hp hε hb).norm.const_mul (2 * ‖ε‖)
  have h01 : IntegrableOn (fun x : ℝ => ‖gaussianMellinWeight (w - 1) ε x‖ +
      ‖w‖ * ‖gaussianLogMellinWeight (w - 1) ε b x‖) (Ioi 0) := h0.add h1
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), ‖gaussianMellinWeight (w - 1) ε x‖ +
        ‖w‖ * ‖gaussianLogMellinWeight (w - 1) ε b x‖ +
        2 * ‖ε‖ * ‖gaussianLogMellinWeight (w + 1) ε b x‖ := by
      apply integral_mono_ae (integrable_gaussianLogMellinDeriv hw hε hb).norm
        ((h0.add h1).add h2)
      exact Filter.Eventually.of_forall fun x => by
        unfold gaussianLogMellinDeriv
        calc
          _ ≤ ‖gaussianMellinWeight (w - 1) ε x +
                w * gaussianLogMellinWeight (w - 1) ε b x‖ +
              ‖2 * ε * gaussianLogMellinWeight (w + 1) ε b x‖ := norm_sub_le _ _
          _ ≤ _ := by
            have hn := norm_add_le (gaussianMellinWeight (w - 1) ε x)
              (w * gaussianLogMellinWeight (w - 1) ε b x)
            simp only [norm_mul] at hn
            simp only [Pi.add_apply, norm_mul, norm_ofNat]
            linarith only [hn]
    _ ≤ _ := by
      rw [integral_add h01 h2, integral_add h0 h1,
        integral_const_mul, integral_const_mul, integral_norm_gaussianMellinWeight hm hε]
      have h1' := integral_norm_gaussianLogMellinWeight_le hm hε hX hb
      have h2' := integral_norm_gaussianLogMellinWeight_le hp hε hX hb
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re] at h1' h2' ⊢
      exact _root_.add_le_add (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left h1' (norm_nonneg w)))
        (mul_le_mul_of_nonneg_left h2' (by positivity))

private theorem continuous_gaussianLogMellinWeight {w : ℂ} (hw : 1 < w.re)
    (ε : ℂ) {b : ℝ} (hb : 0 < b) :
    Continuous (gaussianLogMellinWeight w ε b) := by
  have hm : 0 < (w - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw; linarith
  have hm0 : w - 1 ≠ 0 := fun h => by simp [h] at hm
  have he : gaussianLogMellinWeight w ε b = fun x : ℝ =>
      ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (w - 1) *
        Complex.exp (-(ε * (x : ℂ) ^ 2)) -
      (Real.log b : ℂ) * gaussianMellinWeight w ε x := by
    funext x
    by_cases hx : x = 0
    · simp [hx, gaussianLogMellinWeight, gaussianMellinWeight, Complex.zero_cpow hw0,
        Complex.zero_cpow hm0]
    have hp : (x : ℂ) ^ w = (x : ℂ) ^ (w - 1) * (x : ℂ) := by
      calc
        _ = (x : ℂ) ^ ((w - 1) + 1) := by congr 1; ring
        _ = _ := by rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx), Complex.cpow_one]
    rw [gaussianLogMellinWeight, Real.log_div hx hb.ne', Complex.ofReal_sub]
    unfold gaussianMellinWeight
    rw [hp, Complex.ofReal_mul]
    ring
  rw [he]
  exact (((Complex.continuous_ofReal.comp Real.continuous_mul_log).mul
    (Complex.continuous_ofReal_cpow_const hm)).mul (by fun_prop)).sub
    (continuous_const.mul
      ((Complex.continuous_ofReal_cpow_const (by linarith : 0 < w.re)).mul (by fun_prop)))

private theorem hasDerivAt_gaussianLogMellinWeight {w : ℂ} (hw : 1 < w.re)
    (ε : ℂ) {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (gaussianLogMellinWeight w ε b) (gaussianLogMellinDeriv w ε b x) x := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw; linarith
  have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hw0
  have he := (((Complex.ofRealCLM.hasDerivAt (x := x)).pow 2).const_mul ε).neg.cexp
  have hlog : HasDerivAt (fun y : ℝ => (Real.log (y / b) : ℂ)) (x⁻¹ : ℝ) x := by
    apply ((Real.hasDerivAt_log hx.ne').sub_const (Real.log b)).ofReal_comp.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [Real.log_div hy.ne' hb.ne']
  apply (hlog.mul (hpow.mul he)).congr_deriv
  have hp : (x : ℂ) ^ (w + 1) = (x : ℂ) ^ w * (x : ℂ) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  have hm : (x : ℂ) ^ (w - 1) = (x : ℂ) ^ w * (x : ℂ)⁻¹ := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_neg_one]
  dsimp only [gaussianLogMellinDeriv, gaussianLogMellinWeight, gaussianMellinWeight]
  rw [hp, hm]
  simp only [Pi.neg_apply, Pi.pow_apply, Pi.mul_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, Complex.ofReal_inv]
  ring

private theorem intervalIntegrable_gaussianLogMellinDeriv {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {B a b : ℝ} (hB : 0 < B)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (gaussianLogMellinDeriv w ε B) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (integrable_gaussianLogMellinDeriv hw hε hB).mono_set
    (fun x hx => lt_of_le_of_lt ha hx.1)

private theorem gaussianLogMellin_cell_discrepancy {w ε : ℂ} (hw : 1 < w.re) (hε : 0 < ε.re) {B : ℝ} (hB : 0 < B)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖((b - a : ℝ) : ℂ) * gaussianLogMellinWeight w ε B b -
        ∫ x in a..b, gaussianLogMellinWeight w ε B x‖ ≤
      (b - a) * ∫ x in a..b, ‖gaussianLogMellinDeriv w ε B x‖ := by
  have hc := continuous_gaussianLogMellinWeight hw ε hB
  have hd {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :=
    intervalIntegrable_gaussianLogMellinDeriv hw hε hB ha hab
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => (x : ℂ) - (a : ℂ)) (u' := fun _ => (1 : ℂ))
    (v := gaussianLogMellinWeight w ε B) (v' := gaussianLogMellinDeriv w ε B)
    (a := a) (b := b) (by fun_prop) hc.continuousOn
    (fun x _ => Complex.ofRealCLM.hasDerivAt.sub_const (a : ℂ))
    (fun x hx => hasDerivAt_gaussianLogMellinWeight hw ε hB
      (by rw [min_eq_left hab, max_eq_right hab] at hx; linarith [hx.1]))
    intervalIntegrable_const (hd ha hab)
  simp only [sub_self, zero_mul, sub_zero, one_mul] at hi
  rw [Complex.ofReal_sub] at ⊢
  rw [← hi]
  calc
    _ ≤ ∫ x in a..b, (b - a) * ‖gaussianLogMellinDeriv w ε B x‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall fun x hx => ?_)
        ((hd ha hab).norm.const_mul _)
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      exact mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Every finite lattice sum has a spacing-independent variation bound. -/
theorem norm_sum_gaussianLogMellinWeight_sub_integral_le {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {X B : ℝ} (hX : 0 < X) (hB : 0 < B) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ‖(∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
        (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x‖ ≤
      gaussianLogMellinVariation w ε X B := by
  have hc := continuous_gaussianLogMellinWeight hw ε hB
  have hd {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :=
    intervalIntegrable_gaussianLogMellinDeriv hw hε hB ha hab
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := gaussianLogMellinWeight w ε B)
    (fun _ _ => hc.intervalIntegrable (μ := volume) _ _)
  have hsplit' := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := fun x => ‖gaussianLogMellinDeriv w ε B x‖)
    (fun n _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (hd (by positivity) (by nlinarith [hb] : b * (n : ℝ) ≤ b * (n + 1))).norm)
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsplit hsplit'
  have hcell (n : ℕ) := gaussianLogMellin_cell_discrepancy (ε := ε) hw hε hB
    (show 0 ≤ b * n by positivity)
    (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith [hb])
  have hmain : ‖(b : ℂ) * (∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
      ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x‖ ≤
      b * ∫ x in (0 : ℝ)..(b * N), ‖gaussianLogMellinDeriv w ε B x‖ := by
    rw [mul_sum, ← hsplit, ← sum_sub_distrib, ← hsplit', mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    simpa only [show b * ((n : ℝ) + 1) - b * n = b by ring] using hcell n
  have htotal : (∫ x in (0 : ℝ)..(b * N), ‖gaussianLogMellinDeriv w ε B x‖) ≤
      gaussianLogMellinVariation w ε X B := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine (setIntegral_mono_set (integrable_gaussianLogMellinDeriv hw hε hB).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_).trans
      (integral_norm_gaussianLogMellinDeriv_le hw hε hX hB)
    exact Filter.Eventually.of_forall fun x hx => hx.1
  have he : (b : ℂ) * ((∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
      (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x) =
      (b : ℂ) * (∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
        ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'), one_mul]
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hmain
  exact le_of_mul_le_mul_left (hmain.trans (mul_le_mul_of_nonneg_left htotal hb.le)) hb


/-- Absolute convergence on every positive lattice, including the logarithm. -/
theorem summable_gaussianLogMellinWeight_lattice {w ε : ℂ}
    (hw2 : w.re ≤ 2) (hε : 0 < ε.re) {b B : ℝ} (hb : 0 < b) (hB : 0 < B) :
    Summable (fun n : ℕ => gaussianLogMellinWeight w ε B (b * (n + 1))) := by
  have hs := (summable_nat_add_iff 1).mpr
    (RHTower.summable_pow_mul_exp_neg_nat_sq 3
      (show 0 < ε.re * b ^ 2 by positivity))
  apply (hs.mul_left ((2 + |Real.log (b / B)|) * b ^ w.re)).of_norm_bounded
  intro n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx : 0 < b * ((n : ℝ) + 1) := by positivity
  have hl := abs_log_div_le_scaled hx hb hB
  have hd1 : b * ((n : ℝ) + 1) / b = (n : ℝ) + 1 := by field_simp
  have hd2 : b / (b * ((n : ℝ) + 1)) = ((n : ℝ) + 1)⁻¹ := by field_simp
  rw [hd1, hd2] at hl
  have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ hn0).mpr hn
  have hlog : |Real.log (b * ((n : ℝ) + 1) / B)| ≤
      (2 + |Real.log (b / B)|) * ((n : ℝ) + 1) := by
    nlinarith [abs_nonneg (Real.log (b / B))]
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_gaussianMellinWeight hx, Real.mul_rpow hb.le hn0.le]
  have hp : ((n : ℝ) + 1) ^ w.re ≤ ((n : ℝ) + 1) ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn hw2
  have he : -ε.re * (b * ((n : ℝ) + 1)) ^ 2 =
      -(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2 := by ring
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ((2 + |Real.log (b / B)|) * ((n : ℝ) + 1)) *
        (b ^ w.re * ((n : ℝ) + 1) ^ 2 *
          Real.exp (-(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2)) := by gcongr
    _ = _ := by ring

/-- A complete logarithmic lattice fibre retains its continuous main term,
with an explicit spacing-independent error. -/
theorem norm_tsum_gaussianLogMellinWeight_sub_integral_le {w ε : ℂ}
    (hw : 1 < w.re) (hw2 : w.re ≤ 2) (hε : 0 < ε.re)
    {X B b : ℝ} (hX : 0 < X) (hB : 0 < B) (hb : 0 < b) :
    ‖(∑' n : ℕ, gaussianLogMellinWeight w ε B (b * (n + 1))) -
        (b : ℂ)⁻¹ * ∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε B x‖ ≤
      gaussianLogMellinVariation w ε X B := by
  have hs := (summable_gaussianLogMellinWeight_lattice hw2 hε hb hB).hasSum.tendsto_sum_nat
  have hN : Tendsto (fun n : ℕ => b * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_gaussianLogMellinWeight (by linarith : 0 < w.re) hε hB) hN
  exact le_of_tendsto ((hs.sub (hi.const_mul (b : ℂ)⁻¹)).norm)
    (Filter.Eventually.of_forall fun N =>
      norm_sum_gaussianLogMellinWeight_sub_integral_le hw hε hX hB hb N)

private theorem gaussianRealMoment_nonneg {q α : ℝ} (hq : -1 < q) (hα : 0 < α) :
    0 ≤ gaussianRealMoment q α := by
  have hG := (Real.Gamma_pos_of_pos (show 0 < (q + 1) / 2 by linarith)).le
  unfold gaussianRealMoment
  positivity

private theorem gaussianRealMoment_scale {α X : ℝ} (hα : 0 < α) (hX : 0 < X)
    (hscale : α * X ^ 2 = 2) (q : ℝ) :
    gaussianRealMoment q α = X ^ (q + 1) * gaussianRealMoment q 2 := by
  have hi : 1 / α = (1 / 2 : ℝ) * X ^ 2 := by
    apply (div_eq_iff hα.ne').mpr
    nlinarith only [hscale]
  have hp : (X ^ 2) ^ ((q + 1) / 2) = X ^ (q + 1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hX.le]
    congr 1
    ring
  unfold gaussianRealMoment
  rw [hi, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg X), hp]
  ring

private def gaussianLogScaleBudget (q L : ℝ) : ℝ :=
  gaussianRealMoment (q + 1) 2 + gaussianRealMoment (q - 1) 2 +
    L * gaussianRealMoment q 2

private theorem gaussianLogMomentBudget_scale {α X : ℝ} (hα : 0 < α) (hX : 0 < X)
    (hscale : α * X ^ 2 = 2) (q b : ℝ) :
    gaussianLogMomentBudget q α X b =
      X ^ (q + 1) * gaussianLogScaleBudget q |Real.log (X / b)| := by
  have hp : X ^ (q + 1 + 1) = X ^ (q + 1) * X := by
    rw [Real.rpow_add hX, Real.rpow_one]
  have hm : X * X ^ (q - 1 + 1) = X ^ (q + 1) := by
    rw [show q - 1 + 1 = q by ring, Real.rpow_add hX, Real.rpow_one]
    ring
  unfold gaussianLogMomentBudget
  rw [gaussianRealMoment_scale hα hX hscale, gaussianRealMoment_scale hα hX hscale,
    gaussianRealMoment_scale hα hX hscale, hp]
  have he : X * (X ^ (q - 1 + 1) * gaussianRealMoment (q - 1) 2) =
      X ^ (q + 1) * gaussianRealMoment (q - 1) 2 := by rw [← mul_assoc, hm]
  rw [he]
  unfold gaussianLogScaleBudget
  field_simp
private theorem gaussianLogScaleBudget_nonneg {q L : ℝ} (hq : 0 < q) (hL : 0 ≤ L) :
    0 ≤ gaussianLogScaleBudget q L := by
  have hp := gaussianRealMoment_nonneg (by linarith : -1 < q + 1) (by norm_num : (0 : ℝ) < 2)
  have hm := gaussianRealMoment_nonneg (by linarith : -1 < q - 1) (by norm_num : (0 : ℝ) < 2)
  have h0 := gaussianRealMoment_nonneg (by linarith : -1 < q) (by norm_num : (0 : ℝ) < 2)
  unfold gaussianLogScaleBudget
  positivity

private theorem gaussianLogScaleBudget_le {q L : ℝ} (hq : 0 < q) (hL : 0 ≤ L) :
    gaussianLogScaleBudget q L ≤ gaussianLogScaleBudget q 1 * (1 + L) := by
  have hp := gaussianRealMoment_nonneg (by linarith : -1 < q + 1) (by norm_num : (0 : ℝ) < 2)
  have hm := gaussianRealMoment_nonneg (by linarith : -1 < q - 1) (by norm_num : (0 : ℝ) < 2)
  have h0 := gaussianRealMoment_nonneg (by linarith : -1 < q) (by norm_num : (0 : ℝ) < 2)
  unfold gaussianLogScaleBudget
  nlinarith only [hp, hm, h0, hL, mul_nonneg hp hL, mul_nonneg hm hL]

/-- The explicit constant for logarithmic first-moment lattice errors. -/
def gaussianLogFirstMomentConstant (σ : ℝ) : ℝ :=
  8 * gaussianRealMoment (1 - σ) 2 +
    16 * gaussianLogScaleBudget (1 - σ) 1 +
    128 * gaussianLogScaleBudget (3 - σ) 1

/-- Positivity of the explicit logarithmic error constant throughout the strip. -/
theorem gaussianLogFirstMomentConstant_nonneg {σ : ℝ} (hσ : σ < 1) :
    0 ≤ gaussianLogFirstMomentConstant σ := by
  have h0 := gaussianRealMoment_nonneg (show -1 < 1 - σ by linarith)
    (by norm_num : (0 : ℝ) < 2)
  have h1 := gaussianLogScaleBudget_nonneg (show 0 < 1 - σ by linarith)
    (by norm_num : (0 : ℝ) ≤ 1)
  have h2 := gaussianLogScaleBudget_nonneg (show 0 < 3 - σ by linarith)
    (by norm_num : (0 : ℝ) ≤ 1)
  unfold gaussianLogFirstMomentConstant
  positivity

private theorem norm_mul_gaussianLogMellinVariation_le {w ε : ℂ} {t X b : ℝ}
    (hw : 1 < w.re) (hε : 0 < ε.re) (ht : 1 ≤ t) (hX : 0 < X)
    (hscale : ε.re * X ^ 2 = 2)
    (hwsize : ‖w‖ ≤ 2 * t) (hsector : ‖ε‖ ≤ 4 * ε.re * t) :
    ‖ε / (t : ℂ)‖ * gaussianLogMellinVariation w ε X b ≤
      (8 * gaussianRealMoment (w.re - 1) 2 +
        16 * gaussianLogScaleBudget (w.re - 1) 1 +
        128 * gaussianLogScaleBudget (w.re + 1) 1) *
        t * X ^ (w.re - 2) * (1 + |Real.log (X / b)|) := by
  let L := |Real.log (X / b)|
  let A := gaussianRealMoment (w.re - 1) 2
  let K := gaussianLogScaleBudget (w.re - 1) L
  let J := gaussianLogScaleBudget (w.re + 1) L
  have hA : 0 ≤ A := gaussianRealMoment_nonneg (by linarith) (by norm_num)
  have hK : 0 ≤ K := gaussianLogScaleBudget_nonneg (by linarith) (abs_nonneg _)
  have hJ : 0 ≤ J := gaussianLogScaleBudget_nonneg (by linarith) (abs_nonneg _)
  have ht0 : 0 < t := by linarith
  have hXp : 0 < X ^ w.re := Real.rpow_pos_of_pos hX _
  have hXe : 0 < X ^ (w.re - 2) := Real.rpow_pos_of_pos hX _
  have he : ‖ε / (t : ℂ)‖ ≤ 4 * ε.re := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr hsector
  have hp : X ^ (w.re + 1 + 1) = X ^ w.re * X ^ 2 := by
    rw [show w.re + 1 + 1 = w.re + 2 by ring, Real.rpow_add hX, Real.rpow_two]
  have hV : gaussianLogMellinVariation w ε X b =
      X ^ w.re * (A + ‖w‖ * K + 2 * ‖ε‖ * X ^ 2 * J) := by
    unfold gaussianLogMellinVariation
    rw [gaussianRealMoment_scale hε hX hscale,
      gaussianLogMomentBudget_scale hε hX hscale,
      gaussianLogMomentBudget_scale hε hX hscale, hp,
      show w.re - 1 + 1 = w.re by ring]
    dsimp [A, K, J, L]
    ring
  have hV0 : 0 ≤ gaussianLogMellinVariation w ε X b := by rw [hV]; positivity
  have hJbound : 2 * ‖ε‖ * X ^ 2 * J ≤ 16 * t * J := by
    calc
      _ ≤ 2 * (4 * ε.re * t) * X ^ 2 * J := by gcongr
      _ = _ := by linear_combination 8 * t * J * hscale
  have hVbound : gaussianLogMellinVariation w ε X b ≤
      X ^ w.re * t * (A + 2 * K + 16 * J) := by
    rw [hV]
    have hKbound := mul_le_mul_of_nonneg_right hwsize hK
    have hAbound := mul_le_mul_of_nonneg_right ht hA
    nlinarith only [mul_le_mul_of_nonneg_left
      (show A + ‖w‖ * K + 2 * ‖ε‖ * X ^ 2 * J ≤ t * (A + 2 * K + 16 * J) by
        nlinarith only [hKbound, hAbound, hJbound]) hXp.le]
  have hpower : ε.re * X ^ w.re = 2 * X ^ (w.re - 2) := by
    have hx : X ^ w.re = X ^ (w.re - 2) * X ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add hX]
      congr 1
      ring
    rw [hx]
    linear_combination X ^ (w.re - 2) * hscale
  have hK' := gaussianLogScaleBudget_le (show 0 < w.re - 1 by linarith) (abs_nonneg (Real.log (X / b)))
  have hJ' := gaussianLogScaleBudget_le (show 0 < w.re + 1 by linarith) (abs_nonneg (Real.log (X / b)))
  have hA' : A ≤ A * (1 + L) := by nlinarith [abs_nonneg (Real.log (X / b))]
  calc
    _ ≤ (4 * ε.re) * (X ^ w.re * t * (A + 2 * K + 16 * J)) :=
      mul_le_mul he hVbound hV0 (by positivity)
    _ = 8 * t * X ^ (w.re - 2) * (A + 2 * K + 16 * J) := by
      calc
        _ = 4 * (ε.re * X ^ w.re) * t * (A + 2 * K + 16 * J) := by ring
        _ = _ := by rw [hpower]; ring
    _ ≤ 8 * t * X ^ (w.re - 2) *
        ((A + 2 * gaussianLogScaleBudget (w.re - 1) 1 +
          16 * gaussianLogScaleBudget (w.re + 1) 1) * (1 + L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp [K, J, L] at *
      nlinarith only [hK', hJ', hA']
    _ = _ := by dsimp [A, L]; ring

/-- The logarithmic continuous first moment. -/
def gaussianFirstMomentLogPole (s ε : ℂ) (t : ℝ) : ℂ :=
  (ε / t) * ∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight (2 - s) ε 1 x

private theorem integral_gaussianLogMellinWeight_split {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε b x) =
      (∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε 1 x) -
        (Real.log b : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) *
          ε ^ (-(w + 1) / 2)) := by
  have he : ∀ x ∈ Ioi (0 : ℝ), gaussianLogMellinWeight w ε b x =
      gaussianLogMellinWeight w ε 1 x - (Real.log b : ℂ) * gaussianMellinWeight w ε x := by
    intro x hx
    rw [gaussianLogMellinWeight, gaussianLogMellinWeight, div_one,
      Real.log_div hx.ne' hb.ne', Complex.ofReal_sub, sub_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_sub (integrableOn_gaussianLogMellinWeight hw hε zero_lt_one)
      ((integrableOn_gaussianMellinWeight hw hε).const_mul _),
    integral_const_mul, integral_gaussianMellinWeight hw hε]

/-- Logarithmic first-moment lattice errors gain one Gaussian length, uniformly
in the divisor. The two continuum terms keep their relative sign. -/
theorem norm_tsum_gaussianLogFirstMoment_sub_poles_physical_le {σ t X : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 2 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) * (∑' n : ℕ,
        gaussianLogMellinWeight (2 - ((σ : ℂ) + t * I)) ε b (b * (n + 1))) -
      (b : ℂ)⁻¹ * (gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ε t -
        (Real.log b : ℂ) * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t)‖ ≤
      gaussianLogFirstMomentConstant σ * t * X ^ (-σ) * (1 + |Real.log (X / b)|) := by
  let w : ℂ := 2 - ((σ : ℂ) + t * I)
  have hwre : w.re = 2 - σ := by simp [w]
  have hw : 1 < w.re := by rw [hwre]; linarith
  have hw2 : w.re ≤ 2 := by rw [hwre]; linarith
  have ht0 : 0 < t := by linarith
  have hwsize : ‖w‖ ≤ 2 * t := by
    have he : w = ((2 - σ : ℝ) : ℂ) - (t : ℂ) * I := by dsimp [w]; push_cast; ring
    rw [he]
    calc
      _ ≤ ‖((2 - σ : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_sub_le _ _
      _ = 2 - σ + t := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_pos ht0]
      _ ≤ _ := by linarith
  have hh := mul_le_mul_of_nonneg_left
    (norm_tsum_gaussianLogMellinWeight_sub_integral_le hw hw2 hε hX hb hb)
      (norm_nonneg (ε / (t : ℂ)))
  rw [← norm_mul, integral_gaussianLogMellinWeight_split (by linarith) hε hb] at hh
  have heq : (ε / (t : ℂ)) * ((∑' n : ℕ, gaussianLogMellinWeight w ε b (b * (n + 1))) -
      (b : ℂ)⁻¹ * ((∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε 1 x) -
        (Real.log b : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) *
          ε ^ (-(w + 1) / 2)))) =
      (ε / (t : ℂ)) * (∑' n : ℕ, gaussianLogMellinWeight w ε b (b * (n + 1))) -
        (b : ℂ)⁻¹ * (gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ε t -
          (Real.log b : ℂ) * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t) := by
    have hp : w + 1 = 3 - ((σ : ℂ) + t * I) := by dsimp [w]; ring
    unfold gaussianFirstMomentLogPole gaussianFirstMomentPole
    rw [hp]
    dsimp [w]
    ring
  rw [heq] at hh
  apply hh.trans
  have hv := norm_mul_gaussianLogMellinVariation_le hw hε (by linarith : 1 ≤ t) hX
    hscale hwsize hsector (b := b)
  rw [hwre] at hv
  simpa only [show 2 - σ - 1 = 1 - σ by ring,
    show 2 - σ + 1 = 3 - σ by ring, show 2 - σ - 2 = -σ by ring,
    gaussianLogFirstMomentConstant] using hv

#print axioms integrableOn_gaussianLogMellinWeight
#print axioms integral_norm_gaussianLogMellinWeight_le
#print axioms norm_sum_gaussianLogMellinWeight_sub_integral_le
#print axioms summable_gaussianLogMellinWeight_lattice
#print axioms norm_tsum_gaussianLogMellinWeight_sub_integral_le
#print axioms norm_tsum_gaussianLogFirstMoment_sub_poles_physical_le

end GaloisForLFunctions.ExceptionalLayerTheory
