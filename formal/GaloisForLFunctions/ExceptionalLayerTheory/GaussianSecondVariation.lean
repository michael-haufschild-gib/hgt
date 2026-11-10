import GaloisForLFunctions.ExceptionalLayerTheory.GaussianTypeIContinuum
import GaloisForLFunctions.HTGeometry.EulerMaclaurinSecondOrder

/-!
# Second-order cancellation on Gaussian divisor lattices

The first Gaussian moment and its first derivative vanish at the origin.
The integrable second derivative therefore controls the complete lattice
error, gaining an additional lattice-spacing factor over total variation.
-/

open Complex MeasureTheory Set Filter Topology Finset

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def gaussianFirstDeriv (w ε : ℂ) (x : ℝ) : ℂ :=
  w * gaussianMellinWeight (w - 1) ε x - 2 * ε * gaussianMellinWeight (w + 1) ε x

private def gaussianSecondDeriv (w ε : ℂ) (x : ℝ) : ℂ :=
  w * (w - 1) * gaussianMellinWeight (w - 2) ε x -
    2 * ε * (2 * w + 1) * gaussianMellinWeight w ε x +
    4 * ε ^ 2 * gaussianMellinWeight (w + 2) ε x

private theorem continuous_gaussianMellinWeight {w : ℂ} (hw : 0 < w.re) (ε : ℂ) :
    Continuous (gaussianMellinWeight w ε) :=
  (Complex.continuous_ofReal_cpow_const hw).mul (by fun_prop)

private theorem continuous_gaussianFirstDeriv {w : ℂ} (hw : 1 < w.re) (ε : ℂ) :
    Continuous (gaussianFirstDeriv w ε) := by
  have hm : 0 < (w - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hp : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  exact (continuous_const.mul (continuous_gaussianMellinWeight hm ε)).sub
    (continuous_const.mul (continuous_gaussianMellinWeight hp ε))

private theorem hasDerivAt_gaussianMellinWeight {w : ℂ} (hw : 0 < w.re)
    (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianMellinWeight w ε) (gaussianFirstDeriv w ε x) x := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hw0
  have he := (((Complex.ofRealCLM.hasDerivAt (x := x)).pow 2).const_mul ε).neg.cexp
  apply (hpow.mul he).congr_deriv
  have hp : (x : ℂ) ^ (w + 1) = (x : ℂ) ^ w * (x : ℂ) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  dsimp only [gaussianFirstDeriv, gaussianMellinWeight]
  rw [hp]
  simp only [Pi.neg_apply, Pi.pow_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

private theorem hasDerivAt_gaussianFirstDeriv {w : ℂ} (hw : 1 < w.re)
    (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianFirstDeriv w ε) (gaussianSecondDeriv w ε x) x := by
  have hm : 0 < (w - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hp : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  apply (((hasDerivAt_gaussianMellinWeight hm ε hx).const_mul w).sub
    ((hasDerivAt_gaussianMellinWeight hp ε hx).const_mul (2 * ε))).congr_deriv
  dsimp only [gaussianFirstDeriv, gaussianSecondDeriv]
  rw [show w - 1 - 1 = w - 2 by ring, sub_add_cancel, add_sub_cancel_right,
    show w + 1 + 1 = w + 2 by ring]
  ring

private theorem norm_gaussianMellinWeight {w ε : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖gaussianMellinWeight w ε x‖ = x ^ w.re * Real.exp (-ε.re * x ^ 2) := by
  rw [gaussianMellinWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp]
  congr 2
  simp [pow_two]

private theorem integrable_gaussian_power {q α : ℝ} (hq : -1 < q) (hα : 0 < α) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-α * x ^ (2 : ℕ))) (Ioi 0) := by
  simpa only [Real.rpow_two] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num : (1 : ℝ) ≤ 2) hα)

private theorem integrable_gaussianMellinWeight {w ε : ℂ}
    (hw : -1 < w.re) (hε : 0 < ε.re) :
    IntegrableOn (gaussianMellinWeight w ε) (Ioi 0) := by
  have hc : ContinuousOn (gaussianMellinWeight w ε) (Ioi 0) := by
    intro x hx
    exact ((Complex.continuousAt_ofReal_cpow_const x w (Or.inr hx.ne')).mul
      (by fun_prop)).continuousWithinAt
  refine (integrable_gaussian_power hw hε).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (norm_gaussianMellinWeight hx).le

private theorem integral_norm_gaussianMellinWeight {w ε : ℂ}
    (hw : -1 < w.re) (hε : 0 < ε.re) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianMellinWeight w ε x‖) =
      (1 / 2) * (1 / ε.re) ^ ((w.re + 1) / 2) * Real.Gamma ((w.re + 1) / 2) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_gaussianMellinWeight hx)]
  exact RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi hw hε

private theorem integrable_gaussianSecondDeriv {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) :
    IntegrableOn (gaussianSecondDeriv w ε) (Ioi 0) := by
  have hm : -1 < (w - 2).re := by simp only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  have hp : -1 < (w + 2).re := by simp only [Complex.add_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  exact (((integrable_gaussianMellinWeight hm hε).const_mul (w * (w - 1))).sub
    ((integrable_gaussianMellinWeight (by linarith) hε).const_mul (2 * ε * (2 * w + 1)))).add
    ((integrable_gaussianMellinWeight hp hε).const_mul (4 * ε ^ 2))

/-- An explicit integral bound for the second derivative of the Mellin Gaussian. -/
def gaussianSecondVariation (w ε : ℂ) : ℝ :=
  (‖w‖ * ‖w - 1‖ / 2) * (1 / ε.re) ^ ((w.re - 1) / 2) * Real.Gamma ((w.re - 1) / 2) +
    (‖ε‖ * ‖2 * w + 1‖) * (1 / ε.re) ^ ((w.re + 1) / 2) * Real.Gamma ((w.re + 1) / 2) +
    (2 * ‖ε‖ ^ 2) * (1 / ε.re) ^ ((w.re + 3) / 2) * Real.Gamma ((w.re + 3) / 2)

private theorem integral_norm_gaussianSecondDeriv_le {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianSecondDeriv w ε x‖) ≤ gaussianSecondVariation w ε := by
  have hm : -1 < (w - 2).re := by simp only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  have hp : -1 < (w + 2).re := by simp only [Complex.add_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  have hi0 := (integrable_gaussianMellinWeight hm hε).norm.const_mul (‖w‖ * ‖w - 1‖)
  have hi1 := (integrable_gaussianMellinWeight (show -1 < w.re by linarith) hε).norm.const_mul
    (2 * ‖ε‖ * ‖2 * w + 1‖)
  have hi2 := (integrable_gaussianMellinWeight hp hε).norm.const_mul (4 * ‖ε‖ ^ 2)
  have hi01 : IntegrableOn (fun x : ℝ => ‖w‖ * ‖w - 1‖ * ‖gaussianMellinWeight (w - 2) ε x‖ +
      2 * ‖ε‖ * ‖2 * w + 1‖ * ‖gaussianMellinWeight w ε x‖) (Ioi 0) := hi0.add hi1
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ),
        ‖w‖ * ‖w - 1‖ * ‖gaussianMellinWeight (w - 2) ε x‖ +
        2 * ‖ε‖ * ‖2 * w + 1‖ * ‖gaussianMellinWeight w ε x‖ +
        4 * ‖ε‖ ^ 2 * ‖gaussianMellinWeight (w + 2) ε x‖ := by
      apply integral_mono_ae (integrable_gaussianSecondDeriv hw hε).norm (hi01.add hi2)
      exact Filter.Eventually.of_forall fun x => by
        unfold gaussianSecondDeriv
        calc
          _ ≤ ‖w * (w - 1) * gaussianMellinWeight (w - 2) ε x -
                2 * ε * (2 * w + 1) * gaussianMellinWeight w ε x‖ +
              ‖4 * ε ^ 2 * gaussianMellinWeight (w + 2) ε x‖ := norm_add_le _ _
          _ ≤ _ := by
            have hn := norm_sub_le (w * (w - 1) * gaussianMellinWeight (w - 2) ε x)
              (2 * ε * (2 * w + 1) * gaussianMellinWeight w ε x)
            simp only [norm_mul, norm_ofNat] at hn
            simp only [Pi.add_apply, norm_mul, norm_ofNat, norm_pow]
            linarith only [hn]
    _ = _ := by
      rw [integral_add hi01 hi2, integral_add hi0 hi1,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_norm_gaussianMellinWeight hm hε,
        integral_norm_gaussianMellinWeight (by linarith) hε,
        integral_norm_gaussianMellinWeight hp hε]
      simp only [Complex.sub_re, Complex.add_re, show (2 : ℂ).re = 2 by norm_num]
      rw [show w.re - 2 + 1 = w.re - 1 by ring, show w.re + 2 + 1 = w.re + 3 by ring]
      unfold gaussianSecondVariation
      ring

private theorem intervalIntegrable_gaussianSecondDeriv {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (gaussianSecondDeriv w ε) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (integrable_gaussianSecondDeriv hw hε).mono_set
    (fun x hx => lt_of_le_of_lt ha hx.1)

private theorem gaussian_trapezoid_cell {w ε : ℂ} (hw : 1 < w.re) (hε : 0 < ε.re)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖((b - a : ℝ) : ℂ) * (gaussianMellinWeight w ε b + gaussianMellinWeight w ε a) / 2 -
        ∫ x in a..b, gaussianMellinWeight w ε x‖ ≤
      (b - a) ^ 2 / 8 * ∫ x in a..b, ‖gaussianSecondDeriv w ε x‖ := by
  let R := fun x : ℝ => ((x - (a + b) / 2 : ℝ) : ℂ)
  let K := fun x : ℝ => (((x - a) * (x - b) / 2 : ℝ) : ℂ)
  have hc := continuous_gaussianMellinWeight (show 0 < w.re by linarith) ε
  have hd := continuous_gaussianFirstDeriv hw ε
  have hD := intervalIntegrable_gaussianSecondDeriv hw hε ha hab
  have hxpos (x : ℝ) (hx : x ∈ Ioo (min a b) (max a b)) : 0 < x := by
    rw [min_eq_left hab, max_eq_right hab] at hx
    linarith [hx.1]
  have hR (x : ℝ) : HasDerivAt R 1 x := by
    simpa [R] using ((hasDerivAt_id x).sub_const ((a + b) / 2)).ofReal_comp
  have hK (x : ℝ) : HasDerivAt K (R x) x := by
    apply ((((hasDerivAt_id x).sub_const a).mul
      ((hasDerivAt_id x).sub_const b)).div_const 2).ofReal_comp.congr_deriv
    dsimp [R]
    push_cast
    ring
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := R) (u' := fun _ => (1 : ℂ))
    (v := gaussianMellinWeight w ε) (v' := gaussianFirstDeriv w ε)
    (a := a) (b := b) (by dsimp [R]; fun_prop) hc.continuousOn
    (fun x _ => hR x)
    (fun x hx => hasDerivAt_gaussianMellinWeight (by linarith) ε (hxpos x hx))
    intervalIntegrable_const (hd.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := K) (u' := R) (v := gaussianFirstDeriv w ε) (v' := gaussianSecondDeriv w ε)
    (a := a) (b := b) (by dsimp [K]; fun_prop) hd.continuousOn
    (fun x _ => hK x) (fun x hx => hasDerivAt_gaussianFirstDeriv hw ε (hxpos x hx))
    (by apply Continuous.intervalIntegrable; dsimp [R]; fun_prop) hD
  have hKa : K a = 0 := by simp [K]
  have hKb : K b = 0 := by simp [K]
  rw [hKa, hKb, zero_mul, zero_mul, sub_self, zero_sub] at h2
  simp only [one_mul] at h1
  have he : ((b - a : ℝ) : ℂ) * (gaussianMellinWeight w ε b + gaussianMellinWeight w ε a) / 2 -
      ∫ x in a..b, gaussianMellinWeight w ε x =
        -(∫ x in a..b, K x * gaussianSecondDeriv w ε x) := by
    rw [h2, neg_neg, h1]
    dsimp [R]
    push_cast
    ring
  rw [he, norm_neg]
  calc
    _ ≤ ∫ x in a..b, ((b - a) ^ 2 / 8) * ‖gaussianSecondDeriv w ε x‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall fun x hx => ?_) (hD.norm.const_mul _)
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hKsign : (x - a) * (x - b) / 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) (by linarith [hx.2])) (by norm_num)
      change ‖(((x - a) * (x - b) / 2 : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hKsign]
      nlinarith [sq_nonneg (2 * x - a - b)]
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The finite trapezoidal error uses the integrable second derivative;
no second derivative at the singular origin is required. -/
theorem norm_sum_gaussianMellinWeight_sub_trapezoid_integral_le {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ‖(∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
        gaussianMellinWeight w ε (b * N) / 2 -
        (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x‖ ≤
      b / 8 * gaussianSecondVariation w ε := by
  have hc := continuous_gaussianMellinWeight (show 0 < w.re by linarith) ε
  have hzero : gaussianMellinWeight w ε 0 = 0 := by
    have hw0 : w ≠ 0 := fun h => by simp [h] at hw; linarith
    simp [gaussianMellinWeight, Complex.zero_cpow hw0]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := gaussianMellinWeight w ε)
    (fun _ _ => hc.intervalIntegrable (μ := volume) _ _)
  have hsplit' := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := fun x => ‖gaussianSecondDeriv w ε x‖)
    (fun n _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (intervalIntegrable_gaussianSecondDeriv hw hε (by positivity)
          (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith [hb])).norm)
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsplit hsplit'
  have htrap := GaloisForLFunctions.HTGeometry.sum_trapezoid_complex
    (fun x => gaussianMellinWeight w ε (b * x)) N
  rw [sum_range_succ'] at htrap
  simp only [Nat.cast_zero, mul_zero, hzero, add_zero, zero_add,
    Nat.cast_add, Nat.cast_one] at htrap
  have hmain : ‖(b : ℂ) * ((∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
      gaussianMellinWeight w ε (b * N) / 2) -
      ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x‖ ≤
      b ^ 2 / 8 * ∫ x in (0 : ℝ)..(b * N), ‖gaussianSecondDeriv w ε x‖ := by
    rw [← htrap, mul_sum, ← hsplit, ← sum_sub_distrib, ← hsplit', mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    have hh := gaussian_trapezoid_cell hw hε
      (show 0 ≤ b * n by positivity)
      (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith [hb])
    simpa only [show b * ((n : ℝ) + 1) - b * n = b by ring, mul_div_assoc] using hh
  have htotal : (∫ x in (0 : ℝ)..(b * N), ‖gaussianSecondDeriv w ε x‖) ≤
      gaussianSecondVariation w ε := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine (setIntegral_mono_set (integrable_gaussianSecondDeriv hw hε).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_).trans
      (integral_norm_gaussianSecondDeriv_le hw hε)
    exact Filter.Eventually.of_forall fun x hx => hx.1
  have he : (b : ℂ) * (((∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
      gaussianMellinWeight w ε (b * N) / 2) -
      (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x) =
      (b : ℂ) * ((∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
      gaussianMellinWeight w ε (b * N) / 2) -
        ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'), one_mul]
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hmain
  have hh := hmain.trans (mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ b ^ 2 / 8))
  apply le_of_mul_le_mul_left (a := b) _ hb
  convert hh using 1; ring

/-- The complete Gaussian lattice has a second-order remainder. The endpoint
correction disappears by absolute convergence of the lattice series. -/
theorem norm_tsum_gaussianMellinWeight_sub_main_second_le {w ε : ℂ}
    (hw : 1 < w.re) (hw2 : w.re ≤ 2) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    ‖(∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) *
        ε ^ (-(w + 1) / 2))‖ ≤ b / 8 * gaussianSecondVariation w ε := by
  have hs := summable_gaussianMellinWeight_lattice hw2 hε hb
  have hs0 : Summable (fun n : ℕ => gaussianMellinWeight w ε (b * n)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hz := hs0.tendsto_atTop_zero.div_const (2 : ℂ)
  have hN : Tendsto (fun n : ℕ => b * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_gaussianMellinWeight (by linarith : 0 < w.re) hε) hN
  rw [integral_gaussianMellinWeight (by linarith) hε] at hi
  have hh := le_of_tendsto
    (((hs.hasSum.tendsto_sum_nat.sub hz).sub (hi.const_mul (b : ℂ)⁻¹)).norm)
    (Filter.Eventually.of_forall fun N =>
      norm_sum_gaussianMellinWeight_sub_trapezoid_integral_le hw hε hb N)
  simpa only [zero_div, sub_zero] using hh

/-- The dimensionless constant for the second-order first-moment remainder. -/
def gaussianSecondMomentLatticeConstant (σ : ℝ) : ℝ :=
  Real.Gamma ((1 - σ) / 2) + 10 * Real.Gamma ((3 - σ) / 2) +
    16 * Real.Gamma ((5 - σ) / 2)

private theorem damping_rpow_cancel {α : ℝ} (hα : 0 < α) (q : ℝ) :
    α * (1 / α) ^ q = α ^ (1 - q) := by
  rw [one_div, Real.inv_rpow hα.le, ← Real.rpow_neg hα.le]
  nth_rw 1 [← Real.rpow_one α]
  rw [← Real.rpow_add hα]
  congr 1

private theorem norm_mul_gaussianSecondVariation_le {w ε : ℂ} {t : ℝ}
    (hw : 1 < w.re) (hε : 0 < ε.re) (ht : 0 < t)
    (hwsize : ‖w‖ ≤ 2 * t) (hwminus : ‖w - 1‖ ≤ 2 * t)
    (hwtwice : ‖2 * w + 1‖ ≤ 5 * t) (hsector : ‖ε‖ ≤ 4 * ε.re * t) :
    ‖ε / (t : ℂ)‖ * gaussianSecondVariation w ε ≤
      8 * (Real.Gamma ((w.re - 1) / 2) + 10 * Real.Gamma ((w.re + 1) / 2) +
        16 * Real.Gamma ((w.re + 3) / 2)) * t ^ 2 * ε.re ^ ((3 - w.re) / 2) := by
  have hg0 : 0 ≤ Real.Gamma ((w.re - 1) / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hg1 : 0 ≤ Real.Gamma ((w.re + 1) / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hg2 : 0 ≤ Real.Gamma ((w.re + 3) / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hv : 0 ≤ gaussianSecondVariation w ε := by
    unfold gaussianSecondVariation
    positivity
  have he : ‖ε / (t : ℂ)‖ ≤ 4 * ε.re := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact (div_le_iff₀ ht).mpr hsector
  have hc0 : ‖w‖ * ‖w - 1‖ / 2 ≤ 2 * t ^ 2 := by
    have hh := mul_le_mul hwsize hwminus (norm_nonneg _) (by positivity : 0 ≤ 2 * t)
    nlinarith only [hh]
  have hc1 : ‖ε‖ * ‖2 * w + 1‖ ≤ 20 * ε.re * t ^ 2 := by
    have hh := mul_le_mul hsector hwtwice (norm_nonneg _) (by positivity : 0 ≤ 4 * ε.re * t)
    nlinarith only [hh]
  have hc2 : 2 * ‖ε‖ ^ 2 ≤ 32 * ε.re ^ 2 * t ^ 2 := by
    have hh := mul_le_mul hsector hsector (norm_nonneg _) (by positivity : 0 ≤ 4 * ε.re * t)
    nlinarith only [hh]
  have hV : gaussianSecondVariation w ε ≤
      (2 * t ^ 2) * (1 / ε.re) ^ ((w.re - 1) / 2) * Real.Gamma ((w.re - 1) / 2) +
      (20 * ε.re * t ^ 2) * (1 / ε.re) ^ ((w.re + 1) / 2) * Real.Gamma ((w.re + 1) / 2) +
      (32 * ε.re ^ 2 * t ^ 2) * (1 / ε.re) ^ ((w.re + 3) / 2) * Real.Gamma ((w.re + 3) / 2) := by
    unfold gaussianSecondVariation
    exact _root_.add_le_add (_root_.add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0 (by positivity)) hg0)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 (by positivity)) hg1))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (by positivity)) hg2)
  have hpow0 : ε.re * (1 / ε.re) ^ ((w.re - 1) / 2) = ε.re ^ ((3 - w.re) / 2) := by
    rw [damping_rpow_cancel hε]
    congr 1
    ring
  have hpow1 : ε.re ^ 2 * (1 / ε.re) ^ ((w.re + 1) / 2) = ε.re ^ ((3 - w.re) / 2) := by
    calc
      _ = ε.re * (ε.re * (1 / ε.re) ^ ((w.re + 1) / 2)) := by ring
      _ = ε.re * ε.re ^ (1 - (w.re + 1) / 2) := by rw [damping_rpow_cancel hε]
      _ = _ := by
        nth_rw 1 [← Real.rpow_one ε.re]
        rw [← Real.rpow_add hε]
        congr 1
        ring
  have hpow2 : ε.re ^ 3 * (1 / ε.re) ^ ((w.re + 3) / 2) = ε.re ^ ((3 - w.re) / 2) := by
    calc
      _ = ε.re ^ 2 * (ε.re * (1 / ε.re) ^ ((w.re + 3) / 2)) := by ring
      _ = ε.re ^ 2 * ε.re ^ (1 - (w.re + 3) / 2) := by rw [damping_rpow_cancel hε]
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_add hε]
        congr 1
        ring
  calc
    _ ≤ (4 * ε.re) * _ := mul_le_mul he hV hv (by positivity)
    _ = 8 * t ^ 2 * Real.Gamma ((w.re - 1) / 2) *
          (ε.re * (1 / ε.re) ^ ((w.re - 1) / 2)) +
        80 * t ^ 2 * Real.Gamma ((w.re + 1) / 2) *
          (ε.re ^ 2 * (1 / ε.re) ^ ((w.re + 1) / 2)) +
        128 * t ^ 2 * Real.Gamma ((w.re + 3) / 2) *
          (ε.re ^ 3 * (1 / ε.re) ^ ((w.re + 3) / 2)) := by ring
    _ = _ := by rw [hpow0, hpow1, hpow2]; ring

/-- Positivity of the second-order constant throughout the open strip. -/
theorem gaussianSecondMomentLatticeConstant_nonneg {σ : ℝ} (hσ : σ < 1) :
    0 ≤ gaussianSecondMomentLatticeConstant σ := by
  have h0 := Real.Gamma_pos_of_pos (show 0 < (1 - σ) / 2 by linarith)
  have h1 := Real.Gamma_pos_of_pos (show 0 < (3 - σ) / 2 by linarith)
  have h2 := Real.Gamma_pos_of_pos (show 0 < (5 - σ) / 2 by linarith)
  unfold gaussianSecondMomentLatticeConstant
  positivity

/-- After subtracting the exact continuum pole, the first moment gains a
second power of the Gaussian length through trapezoidal cancellation. -/
theorem norm_tsum_gaussianFirstMoment_sub_pole_second_le {σ t : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 2 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) * (∑' n : ℕ,
        gaussianMellinWeight (2 - ((σ : ℂ) + t * I)) ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t‖ ≤
      gaussianSecondMomentLatticeConstant σ * b * t ^ 2 * ε.re ^ ((1 + σ) / 2) := by
  let w : ℂ := 2 - ((σ : ℂ) + t * I)
  have hwre : w.re = 2 - σ := by simp [w]
  have hw : 1 < w.re := by rw [hwre]; linarith
  have hw2 : w.re ≤ 2 := by rw [hwre]; linarith
  have ht0 : 0 < t := by linarith
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ) - (t : ℂ) * I‖ ≤ r + t := by
    calc
      _ ≤ ‖(r : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_sub_le _ _
      _ = _ := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_pos ht0]
  have hwsize : ‖w‖ ≤ 2 * t := by
    have he : w = ((2 - σ : ℝ) : ℂ) - (t : ℂ) * I := by dsimp [w]; push_cast; ring
    rw [he]
    exact (hnorm (2 - σ) (by linarith)).trans (by linarith)
  have hwminus : ‖w - 1‖ ≤ 2 * t := by
    have he : w - 1 = ((1 - σ : ℝ) : ℂ) - (t : ℂ) * I := by dsimp [w]; push_cast; ring
    rw [he]
    exact (hnorm (1 - σ) (by linarith)).trans (by linarith)
  have hwtwice : ‖2 * w + 1‖ ≤ 5 * t := by
    have hh := norm_add_le (2 * w) 1
    simp only [norm_mul, norm_ofNat, norm_one] at hh
    linarith only [hh, hwsize, ht]
  have hh := mul_le_mul_of_nonneg_left
    (norm_tsum_gaussianMellinWeight_sub_main_second_le hw hw2 hε hb) (norm_nonneg (ε / (t : ℂ)))
  rw [← norm_mul] at hh
  have hm : (w + 1) / 2 = (3 - ((σ : ℂ) + t * I)) / 2 := by dsimp [w]; ring
  have hn : -(w + 1) / 2 = -(3 - ((σ : ℂ) + t * I)) / 2 := by dsimp [w]; ring
  have heq : (ε / (t : ℂ)) * ((∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) * ε ^ (-(w + 1) / 2))) =
      (ε / (t : ℂ)) * (∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
        (b : ℂ)⁻¹ * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t := by
    rw [hm, hn]
    unfold gaussianFirstMomentPole
    ring
  rw [heq] at hh
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_left
    (norm_mul_gaussianSecondVariation_le hw hε ht0 hwsize hwminus hwtwice hsector)
    (by positivity : 0 ≤ b / 8)
  rw [hwre] at hs
  simp only [show 2 - σ - 1 = 1 - σ by ring,
    show 2 - σ + 1 = 3 - σ by ring, show 2 - σ + 3 = 5 - σ by ring,
    show 3 - (2 - σ) = 1 + σ by ring] at hs
  unfold gaussianSecondMomentLatticeConstant
  convert hs using 1 <;> ring

private theorem damping_power_le_physical_scale {σ α X : ℝ}
    (hσ1 : σ < 1) (hX : 0 < X) (hscale : α * X ^ 2 = 2) :
    α ^ ((1 + σ) / 2) ≤ 2 * X ^ (-1 - σ) := by
  have ha : α = 2 / X ^ 2 := (eq_div_iff (pow_ne_zero 2 hX.ne')).mpr hscale
  have hp : (X ^ 2) ^ ((1 + σ) / 2) = X ^ (1 + σ) := by
    rw [← Real.rpow_two X, ← Real.rpow_mul hX.le]
    congr 1
    ring
  have htwo : (2 : ℝ) ^ ((1 + σ) / 2) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : (1 + σ) / 2 ≤ 1)
  calc
    _ = (2 : ℝ) ^ ((1 + σ) / 2) / X ^ (1 + σ) := by
      rw [ha, Real.div_rpow (by norm_num) (sq_nonneg X), hp]
    _ ≤ 2 / X ^ (1 + σ) := div_le_div_of_nonneg_right htwo (Real.rpow_nonneg hX.le _)
    _ = _ := by
      rw [show -1 - σ = -(1 + σ) by ring, Real.rpow_neg hX.le, div_eq_mul_inv]

/-- At the physical scale, the complete fibre error is `Oσ(bt²X⁻¹⁻σ)`. -/
theorem norm_tsum_gaussianFirstMoment_sub_pole_second_physical_le {σ t X : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 2 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) * (∑' n : ℕ,
        gaussianMellinWeight (2 - ((σ : ℂ) + t * I)) ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t‖ ≤
      2 * gaussianSecondMomentLatticeConstant σ * b * t ^ 2 * X ^ (-1 - σ) := by
  have hC := gaussianSecondMomentLatticeConstant_nonneg hσ1
  apply (norm_tsum_gaussianFirstMoment_sub_pole_second_le hσ hσ1 ht hε hsector hb).trans
  calc
    _ ≤ gaussianSecondMomentLatticeConstant σ * b * t ^ 2 * (2 * X ^ (-1 - σ)) :=
      mul_le_mul_of_nonneg_left (damping_power_le_physical_scale hσ1 hX hscale) (by positivity)
    _ = _ := by ring

#print axioms norm_sum_gaussianMellinWeight_sub_trapezoid_integral_le
#print axioms norm_tsum_gaussianMellinWeight_sub_main_second_le
#print axioms norm_tsum_gaussianFirstMoment_sub_pole_second_le
#print axioms norm_tsum_gaussianFirstMoment_sub_pole_second_physical_le

end GaloisForLFunctions.ExceptionalLayerTheory
