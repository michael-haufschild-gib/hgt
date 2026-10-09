import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality
import GaloisForLFunctions.RHTower.SuzukiScrewWeilIdentity
import GaloisForLFunctions.RHTower.CCMEvenGroundXiStripConvergenceRH

/-!
# The Poisson majorant of a Paley–Wiener transform

Let `f` be integrable and vanish outside `[-a, a]`, and let `F(z) = ∫ f(t) e^{izt} dt`. For every
`x ∈ ℝ` and `y > 0` with `F(x + iy) ≠ 0`, the function `u ↦ log |F(u)| / ((u - x)² + y²)` is
integrable and

`log |F(x + iy)| ≤ a y + (y/π) ∫ log |F(u)| / ((u - x)² + y²) du`.

So the growth of `F` off the real line is bounded by its exponential type plus the Poisson mean of
`log |F|` on the real line. For transforms without non-real zeros this is an equality (no Blaschke
factors), so for real-rooted transforms the strip growth is a functional of the real-line modulus.

**Proof.** `H(ζ) = F(x + 2yζ) e^{2iyaζ}` is bounded by `‖f‖₁` on the closed upper half-plane.
Transport it to the unit disc by `w ↦ ζ = i(1/(1 - w) - 1/2)`, which sends `0` to `i/2` and the
unit circle to the real line. The boundary Jensen inequality for functions bounded on the disc
(singular only at `w = 1`) gives `log |H(i/2)| ≤` the circle average of `log |H|`. On the real
line `|H| = |F|`, and the circle average becomes the Poisson integral.
-/

open Complex MeasureTheory Set Filter Topology Real

namespace RHTower

noncomputable section

/-- The transform `z ↦ ∫ f(t) e^{izt} dt` of an integrable function supported in `[-a, a]` is
entire. -/
theorem differentiable_suzukiEntireFourier {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : GaloisForLFunctions.HTGeometry.FourierZeroFlip.SupportedIn a f) :
    Differentiable ℂ (suzukiEntireFourier f) := by
  have hdiff := CCMXiStrip.differentiable_unitaryLaplace ha hf hs
  have heq : suzukiEntireFourier f = fun z =>
      GaloisForLFunctions.HTGeometry.FourierLaplaceDivision.unitaryLaplace f
        (-z / (2 * Real.pi)) := by
    funext z
    rw [suzukiEntireFourier, GaloisForLFunctions.HTGeometry.FourierLaplaceDivision.unitaryLaplace]
    congr 1
    funext t
    rw [mul_comm]
    congr 1
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    field_simp
  rw [heq]
  exact hdiff.comp (by fun_prop)

/-- Above the real line the transform grows at most like `e^{a Im z}`. -/
theorem norm_suzukiEntireFourier_le {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ t, f t ≠ 0 → |t| ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖suzukiEntireFourier f z‖ ≤ (∫ t : ℝ, ‖f t‖) * Real.exp (a * z.im) := by
  rw [suzukiEntireFourier, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun t => norm_nonneg _) (hf.norm.mul_const _)
    (Eventually.of_forall fun t => ?_))
  · show ‖f t * cexp (I * z * (t : ℂ))‖ ≤ ‖f t‖ * Real.exp (a * z.im)
    rw [norm_mul, Complex.norm_exp]
    by_cases ht : f t = 0
    · rw [ht, norm_zero, zero_mul, zero_mul]
    · gcongr
      have hre : (I * z * (t : ℂ)).re = -(z.im * t) := by simp [mul_re, mul_im]
      rw [hre]
      have hta := hs t ht
      calc -(z.im * t) ≤ |z.im * t| := neg_le_abs _
        _ = z.im * |t| := by rw [abs_mul, abs_of_nonneg hz]
        _ ≤ z.im * a := mul_le_mul_of_nonneg_left hta hz
        _ = a * z.im := mul_comm _ _

/-! ## The disc model of the upper half-plane -/

/-- The map `w ↦ i(1/(1 - w) - 1/2)` from the unit disc onto the upper half-plane. -/
def discToUpper (w : ℂ) : ℂ := I * (halfPlaneOfDisc w - 1 / 2)

theorem discToUpper_zero : discToUpper 0 = I / 2 := by
  simp only [discToUpper, halfPlaneOfDisc, sub_zero, inv_one]
  ring

theorem im_discToUpper (w : ℂ) : (discToUpper w).im = (halfPlaneOfDisc w).re - 1 / 2 := by
  simp [discToUpper]

theorem discToUpper_circleMap (t : ℝ) :
    discToUpper (circleMap 0 1 (criticalLineAngle t)) = -(t : ℂ) := by
  rw [discToUpper, halfPlaneOfDisc_circleMap_criticalLineAngle]
  ring_nf
  rw [I_sq]
  ring

/-- **The Poisson majorant of a Paley–Wiener transform.** -/
theorem log_norm_le_poissonMajorant {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ t, f t ≠ 0 → |t| ≤ a) (x : ℝ) {y : ℝ} (hy : 0 < y)
    (hF : suzukiEntireFourier f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    Integrable (fun u : ℝ => Real.log ‖suzukiEntireFourier f u‖ / ((u - x) ^ 2 + y ^ 2)) ∧
      Real.log ‖suzukiEntireFourier f ((x : ℂ) + (y : ℂ) * I)‖ ≤
        a * y + y / π * ∫ u : ℝ, Real.log ‖suzukiEntireFourier f u‖ / ((u - x) ^ 2 + y ^ 2) := by
  set F : ℂ → ℂ := suzukiEntireFourier f with hFdef
  set M : ℝ := ∫ t : ℝ, ‖f t‖ with hM
  have hsupp : GaloisForLFunctions.HTGeometry.FourierZeroFlip.SupportedIn a f := by
    intro t ht
    by_contra hne
    exact ht (abs_le.mp (hs t hne))
  have hFdiff : Differentiable ℂ F := differentiable_suzukiEntireFourier ha hf hsupp
  set H : ℂ → ℂ := fun ζ => F ((x : ℂ) + 2 * (y : ℂ) * ζ) * cexp (I * (2 * y * a : ℝ) * ζ)
    with hHdef
  have hHdiff : Differentiable ℂ H := by
    intro ζ
    exact ((hFdiff _).comp ζ (by fun_prop)).mul (by fun_prop)
  have hHbound : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖H ζ‖ ≤ M := by
    intro ζ hζ
    have him : ((x : ℂ) + 2 * (y : ℂ) * ζ).im = 2 * y * ζ.im := by simp
    have h1 := norm_suzukiEntireFourier_le hf hs (z := (x : ℂ) + 2 * (y : ℂ) * ζ)
      (by rw [him]; positivity)
    rw [him] at h1
    have h2 : ‖cexp (I * (2 * y * a : ℝ) * ζ)‖ = Real.exp (-(2 * y * a * ζ.im)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [mul_re, mul_im]
    rw [hHdef, norm_mul, h2]
    calc ‖F ((x : ℂ) + 2 * (y : ℂ) * ζ)‖ * Real.exp (-(2 * y * a * ζ.im))
        ≤ M * Real.exp (a * (2 * y * ζ.im)) * Real.exp (-(2 * y * a * ζ.im)) := by gcongr
      _ = M := by
        rw [mul_assoc, ← Real.exp_add]
        rw [show a * (2 * y * ζ.im) + -(2 * y * a * ζ.im) = 0 by ring, Real.exp_zero, mul_one]
  set Φ : ℂ → ℂ := fun w => H (discToUpper w) with hΦdef
  have hΦdiff : DifferentiableOn ℂ Φ {1}ᶜ := by
    intro w hw
    have hw1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    have hd : DifferentiableAt ℂ discToUpper w := by
      unfold discToUpper halfPlaneOfDisc
      exact ((differentiableAt_const _).sub differentiableAt_id |>.inv hw1 |>.sub_const _
        |>.const_mul _)
    exact ((hHdiff _).comp w hd).differentiableWithinAt
  have hΦmeas : Measurable Φ := by
    have hd : Measurable discToUpper := by
      unfold discToUpper halfPlaneOfDisc
      exact measurable_const.mul ((measurable_const.sub measurable_id).inv.sub_const _)
    exact hHdiff.continuous.measurable.comp hd
  have hΦ0eq : Φ 0 = F ((x : ℂ) + (y : ℂ) * I) * cexp (-((y * a : ℝ) : ℂ)) := by
    simp only [hΦdef, hHdef, discToUpper_zero]
    congr 1
    · congr 1; ring
    · congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
  have hΦ0 : Φ 0 ≠ 0 := by
    rw [hΦ0eq]
    exact mul_ne_zero hF (Complex.exp_ne_zero _)
  have hgrowth : ∃ A : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 →
      Real.log ‖Φ w‖ ≤ A - 2 * Real.log ‖1 - w‖ := by
    refine ⟨max 0 (Real.log M) + 2 * Real.log 2, fun w hw hw1 => ?_⟩
    have hre := re_halfPlaneOfDisc_ge hw hw1
    have hb : ‖Φ w‖ ≤ M := hHbound _ (by rw [im_discToUpper]; linarith)
    have hlog1 : Real.log ‖Φ w‖ ≤ max 0 (Real.log M) := by
      rcases eq_or_lt_of_le (norm_nonneg (Φ w)) with h0 | hpos
      · rw [← h0, Real.log_zero]; exact le_max_left _ _
      · exact (Real.log_le_log hpos hb).trans (le_max_right _ _)
    have hpos1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw1))
    have hle2 : ‖1 - w‖ ≤ 2 := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hlog2 : Real.log ‖1 - w‖ ≤ Real.log 2 := Real.log_le_log hpos1 hle2
    linarith
  obtain ⟨hci, hineq⟩ := circleIntegrable_and_sum_log_add_le_circleAverage hΦdiff hΦmeas hΦ0
    hgrowth (U := ∅) (by simp)
  simp only [Finset.sum_empty, zero_add] at hineq
  -- the boundary values
  have hbdry : ∀ t : ℝ, Real.log ‖Φ (circleMap 0 1 (criticalLineAngle t))‖ =
      Real.log ‖F ((x - 2 * y * t : ℝ) : ℂ)‖ := by
    intro t
    simp only [hΦdef, hHdef, discToUpper_circleMap]
    rw [norm_mul]
    have h1 : ‖cexp (I * (2 * y * a : ℝ) * -(t : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp [mul_re, mul_im]
    rw [h1, mul_one]
    congr 2
    push_cast
    ring_nf
  set g : ℝ → ℝ := fun u => Real.log ‖F u‖ / ((u - x) ^ 2 + y ^ 2) with hg
  have hline : ∀ t : ℝ, Real.log ‖Φ (circleMap 0 1 (criticalLineAngle t))‖ / (1 / 4 + t ^ 2) =
      4 * y ^ 2 * g (x + (-(2 * y)) * t) := by
    intro t
    rw [hbdry, hg]
    simp only
    have hden : ((x + -(2 * y) * t) - x) ^ 2 + y ^ 2 = 4 * y ^ 2 * (1 / 4 + t ^ 2) := by ring
    rw [hden, show x - 2 * y * t = x + -(2 * y) * t by ring]
    have hpos : 0 < 1 / 4 + t ^ 2 := by positivity
    field_simp
  have hc2y : (-(2 * y)) ≠ 0 := by linarith
  -- integrability
  have hint_t := (circleIntegrable_iff_integrable_criticalLine _).mp hci
  have hint_t' : Integrable fun t : ℝ => g (x + (-(2 * y)) * t) := by
    have := hint_t.const_mul ((4 * y ^ 2)⁻¹)
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only [hline]
    field_simp
  have hint_u : Integrable g := by
    have h1 : Integrable (fun t : ℝ => (fun s : ℝ => g (x + s)) (-(2 * y) * t)) := hint_t'
    have h2 := (integrable_comp_mul_left_iff (fun s : ℝ => g (x + s)) hc2y).mp h1
    have h3 := h2.comp_add_left (-x)
    refine h3.congr (ae_of_all _ fun u => ?_)
    simp
  refine ⟨hint_u, ?_⟩
  -- the inequality
  rw [circleAverage_eq_integral_criticalLine] at hineq
  simp only [hline] at hineq
  rw [integral_const_mul] at hineq
  have hsub : (∫ t : ℝ, g (x + (-(2 * y)) * t)) = (2 * y)⁻¹ * ∫ u : ℝ, g u := by
    have h1 := Measure.integral_comp_mul_left (fun s : ℝ => g (x + s)) (-(2 * y))
    rw [h1, integral_add_left_eq_self, smul_eq_mul]
    congr 1
    rw [abs_inv, abs_neg, abs_of_pos (by linarith)]
  rw [hsub] at hineq
  rw [hΦ0eq, norm_mul, Complex.norm_exp] at hineq
  simp only [neg_re, ofReal_re] at hineq
  rw [Real.log_mul (norm_ne_zero_iff.mpr hF) (Real.exp_pos _).ne', Real.log_exp] at hineq
  have hpi : 0 < π := Real.pi_pos
  have hfinal : (2 * π)⁻¹ * (4 * y ^ 2 * ((2 * y)⁻¹ * ∫ u : ℝ, g u)) =
      y / π * ∫ u : ℝ, g u := by
    field_simp
    ring
  rw [hfinal] at hineq
  simp only [hg] at hineq ⊢
  linarith

theorem suzukiEntireFourier_comp_neg (f : ℝ → ℂ) (z : ℂ) :
    suzukiEntireFourier (fun t => f (-t)) z = suzukiEntireFourier f (-z) := by
  rw [suzukiEntireFourier, suzukiEntireFourier,
    ← integral_neg_eq_self (fun t : ℝ => f t * cexp (I * -z * (t : ℂ)))]
  congr 1
  funext t
  push_cast
  ring_nf

/-- **The Poisson majorant below the real line.** -/
theorem log_norm_le_poissonMajorant_lower {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ t, f t ≠ 0 → |t| ≤ a) (x : ℝ) {y : ℝ} (hy : 0 < y)
    (hF : suzukiEntireFourier f ((x : ℂ) - (y : ℂ) * I) ≠ 0) :
    Integrable (fun u : ℝ => Real.log ‖suzukiEntireFourier f u‖ / ((u - x) ^ 2 + y ^ 2)) ∧
      Real.log ‖suzukiEntireFourier f ((x : ℂ) - (y : ℂ) * I)‖ ≤
        a * y + y / π * ∫ u : ℝ, Real.log ‖suzukiEntireFourier f u‖ / ((u - x) ^ 2 + y ^ 2) := by
  set g : ℝ → ℂ := fun t => f (-t) with hgdef
  have hg : Integrable g := hf.comp_neg
  have hgs : ∀ t, g t ≠ 0 → |t| ≤ a := fun t ht => by
    have := hs (-t) ht
    rwa [abs_neg] at this
  have hpt : suzukiEntireFourier f ((x : ℂ) - (y : ℂ) * I) =
      suzukiEntireFourier g (((-x : ℝ) : ℂ) + (y : ℂ) * I) := by
    rw [hgdef, suzukiEntireFourier_comp_neg]
    congr 1
    push_cast
    ring
  have hline : ∀ u : ℝ, Real.log ‖suzukiEntireFourier g u‖ / ((u - -x) ^ 2 + y ^ 2) =
      (fun v : ℝ => Real.log ‖suzukiEntireFourier f v‖ / ((v - x) ^ 2 + y ^ 2)) (-u) := by
    intro u
    rw [hgdef, suzukiEntireFourier_comp_neg]
    simp only [ofReal_neg]
    congr 1
    ring
  obtain ⟨hint, hle⟩ := log_norm_le_poissonMajorant ha hg hgs (-x) hy (by rwa [← hpt])
  simp only [hline] at hint hle
  refine ⟨?_, ?_⟩
  · simpa using hint.comp_neg
  · rw [hpt]
    rwa [integral_neg_eq_self (fun v : ℝ => Real.log ‖suzukiEntireFourier f v‖ /
      ((v - x) ^ 2 + y ^ 2))] at hle

/-- **The Poisson majorant in both half-planes**, in exponential form. -/
theorem norm_suzukiEntireFourier_le_exp_poisson {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : Integrable f) (hs : ∀ t, f t ≠ 0 → |t| ≤ a) {z : ℂ} (hz : z.im ≠ 0) :
    ‖suzukiEntireFourier f z‖ ≤ Real.exp (a * |z.im| + |z.im| / π *
      ∫ u : ℝ, Real.log ‖suzukiEntireFourier f u‖ / ((u - z.re) ^ 2 + z.im ^ 2)) := by
  by_cases h0 : suzukiEntireFourier f z = 0
  · rw [h0, norm_zero]; exact (Real.exp_pos _).le
  have hpos : 0 < ‖suzukiEntireFourier f z‖ := norm_pos_iff.mpr h0
  rw [← Real.log_le_iff_le_exp hpos]
  rcases lt_or_gt_of_ne hz with hneg | hpos'
  · have hy : 0 < -z.im := neg_pos.mpr hneg
    have hzeq : z = (z.re : ℂ) - ((-z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hzeq] at h0
    have h := (log_norm_le_poissonMajorant_lower ha hf hs z.re hy h0).2
    rw [← hzeq, neg_sq] at h
    rwa [abs_of_neg hneg]
  · have hzeq : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    rw [hzeq] at h0
    have h := (log_norm_le_poissonMajorant ha hf hs z.re hpos' h0).2
    rw [← hzeq] at h
    rwa [abs_of_pos hpos']

end

end RHTower
