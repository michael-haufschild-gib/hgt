import GaloisForLFunctions.HTGeometry.ComplexRateGammaIntegral
import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeSource
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Continuous main terms of Gaussian type-I sums

The lattice discrepancy is controlled by the total variation of the
Gaussian Mellin weight. Its bound is independent of lattice spacing.
The continuous main term is evaluated at a complex damping rate.
-/

open Complex MeasureTheory Set Filter Topology Finset

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The continuous Gaussian Mellin weight, including its value at zero. -/
def gaussianMellinWeight (w ε : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ w * Complex.exp (-(ε * (x : ℂ) ^ 2))

private def gaussianMellinDeriv (w ε : ℂ) (x : ℝ) : ℂ :=
  w * (x : ℂ) ^ (w - 1) * Complex.exp (-(ε * (x : ℂ) ^ 2)) -
    2 * ε * (x : ℂ) ^ (w + 1) * Complex.exp (-(ε * (x : ℂ) ^ 2))

private theorem continuous_gaussianMellinWeight {w : ℂ} (hw : 0 < w.re) (ε : ℂ) :
    Continuous (gaussianMellinWeight w ε) :=
  (Complex.continuous_ofReal_cpow_const hw).mul (by fun_prop)

private theorem continuous_gaussianMellinDeriv {w : ℂ} (hw : 1 < w.re) (ε : ℂ) :
    Continuous (gaussianMellinDeriv w ε) := by
  have hm : Continuous (fun x : ℝ => (x : ℂ) ^ (w - 1)) :=
    Complex.continuous_ofReal_cpow_const (by simpa using sub_pos.mpr hw)
  have hp : Continuous (fun x : ℝ => (x : ℂ) ^ (w + 1)) :=
    Complex.continuous_ofReal_cpow_const (by simp only [Complex.add_re, Complex.one_re]; linarith)
  unfold gaussianMellinDeriv
  exact ((continuous_const.mul hm).mul (by fun_prop)).sub
    ((continuous_const.mul hp).mul (by fun_prop))

private theorem hasDerivAt_gaussianMellinWeight {w : ℂ} (hw : 0 < w.re)
    (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianMellinWeight w ε) (gaussianMellinDeriv w ε x) x := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hw0
  have he := (((Complex.ofRealCLM.hasDerivAt (x := x)).pow 2).const_mul ε).neg.cexp
  apply (hpow.mul he).congr_deriv
  dsimp only [gaussianMellinDeriv, Complex.ofRealCLM_apply, map_one]
  have hp : (x : ℂ) ^ (w + 1) = (x : ℂ) ^ w * (x : ℂ) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  rw [hp]
  simp only [Pi.neg_apply, Pi.pow_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
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

/-- Absolute convergence of the continuous Gaussian Mellin weight. -/
theorem integrableOn_gaussianMellinWeight {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) :
    IntegrableOn (gaussianMellinWeight w ε) (Ioi 0) := by
  refine (integrable_gaussian_power (by linarith : -1 < w.re) hε).mono' ?_ ?_
  · exact (continuous_gaussianMellinWeight hw ε).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (norm_gaussianMellinWeight hx).le

private theorem norm_gaussianMellinDeriv_le {w ε : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖gaussianMellinDeriv w ε x‖ ≤
      ‖w‖ * (x ^ (w.re - 1) * Real.exp (-ε.re * x ^ 2)) +
        2 * ‖ε‖ * (x ^ (w.re + 1) * Real.exp (-ε.re * x ^ 2)) := by
  have hm := norm_gaussianMellinWeight (w := w - 1) (ε := ε) hx
  have hp := norm_gaussianMellinWeight (w := w + 1) (ε := ε) hx
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re] at hm hp
  have he : gaussianMellinDeriv w ε x =
      w * gaussianMellinWeight (w - 1) ε x - 2 * ε * gaussianMellinWeight (w + 1) ε x := by
    unfold gaussianMellinDeriv gaussianMellinWeight
    ring
  rw [he]
  simpa only [norm_mul, norm_ofNat, hm, hp] using
    norm_sub_le (w * gaussianMellinWeight (w - 1) ε x)
      (2 * ε * gaussianMellinWeight (w + 1) ε x)

/-- Explicit total-variation budget for a complex Gaussian Mellin weight. -/
def gaussianMellinVariation (w ε : ℂ) : ℝ :=
  ‖w‖ / 2 * (1 / ε.re) ^ (w.re / 2) * Real.Gamma (w.re / 2) +
    ‖ε‖ * (1 / ε.re) ^ ((w.re + 2) / 2) * Real.Gamma ((w.re + 2) / 2)

private theorem integrable_gaussianMellinDeriv {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) :
    IntegrableOn (gaussianMellinDeriv w ε) (Ioi 0) := by
  refine ((integrable_gaussian_power (by linarith : -1 < w.re - 1) hε).const_mul ‖w‖ |>.add
    ((integrable_gaussian_power (by linarith : -1 < w.re + 1) hε).const_mul (2 * ‖ε‖))).mono'
      (continuous_gaussianMellinDeriv hw ε).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_gaussianMellinDeriv_le hx

private theorem integral_norm_gaussianMellinDeriv_le {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianMellinDeriv w ε x‖) ≤ gaussianMellinVariation w ε := by
  have hm := integrable_gaussian_power (by linarith : -1 < w.re - 1) hε
  have hp := integrable_gaussian_power (by linarith : -1 < w.re + 1) hε
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ),
        ‖w‖ * (x ^ (w.re - 1) * Real.exp (-ε.re * x ^ 2)) +
          2 * ‖ε‖ * (x ^ (w.re + 1) * Real.exp (-ε.re * x ^ 2)) := by
      apply integral_mono_ae (integrable_gaussianMellinDeriv hw hε).norm
        ((hm.const_mul _).add (hp.const_mul _))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_gaussianMellinDeriv_le hx
    _ = _ := by
      rw [integral_add (hm.const_mul _) (hp.const_mul _), integral_const_mul,
        integral_const_mul, RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi (by linarith) hε,
        RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi (by linarith) hε]
      simp only [sub_add_cancel, add_assoc, one_add_one_eq_two]
      unfold gaussianMellinVariation
      ring

private theorem gaussianMellin_cell_discrepancy {w ε : ℂ} (hw : 1 < w.re)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖((b - a : ℝ) : ℂ) * gaussianMellinWeight w ε b -
        ∫ x in a..b, gaussianMellinWeight w ε x‖ ≤
      (b - a) * ∫ x in a..b, ‖gaussianMellinDeriv w ε x‖ := by
  have hc := continuous_gaussianMellinWeight (by linarith : 0 < w.re) ε
  have hd := continuous_gaussianMellinDeriv hw ε
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => (x : ℂ) - (a : ℂ)) (u' := fun _ => (1 : ℂ))
    (v := gaussianMellinWeight w ε) (v' := gaussianMellinDeriv w ε)
    (a := a) (b := b) (by fun_prop) hc.continuousOn
    (fun x _ => Complex.ofRealCLM.hasDerivAt.sub_const (a : ℂ))
    (fun x hx => hasDerivAt_gaussianMellinWeight (by linarith) ε
      (by rw [min_eq_left hab, max_eq_right hab] at hx; linarith [hx.1]))
    intervalIntegrable_const (hd.intervalIntegrable _ _)
  simp only [sub_self, zero_mul, sub_zero, one_mul] at hi
  rw [Complex.ofReal_sub] at ⊢
  rw [← hi]
  calc
    _ ≤ ∫ x in a..b, (b - a) * ‖gaussianMellinDeriv w ε x‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall fun x hx => ?_)
        ((continuous_const.mul hd.norm).intervalIntegrable _ _)
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      exact mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Every finite lattice sum has a spacing-independent variation bound. -/
theorem norm_sum_gaussianMellinWeight_sub_integral_le {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ‖(∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
        (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x‖ ≤
      gaussianMellinVariation w ε := by
  have hc := continuous_gaussianMellinWeight (by linarith : 0 < w.re) ε
  have hd := continuous_gaussianMellinDeriv hw ε
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := gaussianMellinWeight w ε)
    (fun _ _ => hc.intervalIntegrable (μ := volume) _ _)
  have hsplit' := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := fun x => ‖gaussianMellinDeriv w ε x‖)
    (fun _ _ => hd.norm.intervalIntegrable (μ := volume) _ _)
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsplit hsplit'
  have hcell (n : ℕ) := gaussianMellin_cell_discrepancy (ε := ε) hw
    (show 0 ≤ b * n by positivity)
    (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith [hb])
  have hmain : ‖(b : ℂ) * (∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
      ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x‖ ≤
      b * ∫ x in (0 : ℝ)..(b * N), ‖gaussianMellinDeriv w ε x‖ := by
    rw [mul_sum, ← hsplit, ← sum_sub_distrib, ← hsplit', mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    simpa only [show b * ((n : ℝ) + 1) - b * n = b by ring] using hcell n
  have htotal : (∫ x in (0 : ℝ)..(b * N), ‖gaussianMellinDeriv w ε x‖) ≤
      gaussianMellinVariation w ε := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine (setIntegral_mono_set (integrable_gaussianMellinDeriv hw hε).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_).trans
      (integral_norm_gaussianMellinDeriv_le hw hε)
    exact Filter.Eventually.of_forall fun x hx => hx.1
  have he : (b : ℂ) * ((∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x) =
      (b : ℂ) * (∑ n ∈ range N, gaussianMellinWeight w ε (b * (n + 1))) -
        ∫ x in (0 : ℝ)..(b * N), gaussianMellinWeight w ε x := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'), one_mul]
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hmain
  exact le_of_mul_le_mul_left (hmain.trans (mul_le_mul_of_nonneg_left htotal hb.le)) hb

/-- The continuous main term at a complex damping rate. -/
theorem integral_gaussianMellinWeight {w ε : ℂ} (hw : 0 < w.re) (hε : 0 < ε.re) :
    (∫ x in Ioi (0 : ℝ), gaussianMellinWeight w ε x) =
      (1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) * ε ^ (-(w + 1) / 2) := by
  let a : ℂ := (w + 1) / 2
  have ha : 0 < a.re := by
    dsimp [a]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    positivity
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ => (y : ℂ) ^ (a - 1) * Complex.exp (-(ε * y)))
    (p := 2) (by norm_num)
  rw [_root_.HTGeometry.integral_cpow_mul_cexp_neg_mul_complex ha hε] at hsub
  have he : (∫ x in Ioi (0 : ℝ), (2 * x ^ ((2 : ℝ) - 1)) •
        ((↑(x ^ (2 : ℝ)) : ℂ) ^ (a - 1) * Complex.exp (-(ε * ↑(x ^ (2 : ℝ)))))) =
      2 * ∫ x in Ioi (0 : ℝ), gaussianMellinWeight w ε x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [Real.rpow_two, RHTower.cpow_sq_ofReal hx]
    have hp : 2 * (a - 1) = w - 1 := by dsimp [a]; ring
    rw [hp]
    have hxpow : (x : ℂ) * (x : ℂ) ^ (w - 1) = (x : ℂ) ^ w := by
      nth_rewrite 1 [← Complex.cpow_one (x : ℂ)]
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
      congr 1
      ring
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
    unfold gaussianMellinWeight
    calc
      _ = 2 * ((x : ℂ) * (x : ℂ) ^ (w - 1)) * Complex.exp (-(ε * (x : ℂ) ^ 2)) := by ring
      _ = _ := by rw [hxpow]; ring
  rw [he] at hsub
  dsimp only [a] at hsub
  have hneg : -((w + 1) / 2) = -(w + 1) / 2 := by ring
  rw [hneg] at hsub
  linear_combination hsub / 2

/-- Absolute convergence of every positive lattice of first-moment exponents. -/
theorem summable_gaussianMellinWeight_lattice {w ε : ℂ}
    (hw2 : w.re ≤ 2) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => gaussianMellinWeight w ε (b * (n + 1))) := by
  have hs := (summable_nat_add_iff 1).mpr
    (RHTower.summable_pow_mul_exp_neg_nat_sq 2
      (show 0 < ε.re * b ^ 2 by positivity))
  apply (hs.mul_left (b ^ w.re)).of_norm_bounded
  intro n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hx : 0 < b * ((n : ℝ) + 1) := by positivity
  rw [norm_gaussianMellinWeight hx, Real.mul_rpow hb.le (by positivity)]
  have hp : ((n : ℝ) + 1) ^ w.re ≤ ((n : ℝ) + 1) ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn hw2
  have he : -ε.re * (b * ((n : ℝ) + 1)) ^ 2 =
      -(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2 := by ring
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ b ^ w.re * ((n : ℝ) + 1) ^ (2 : ℕ) *
        Real.exp (-(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hb.le w.re)) (Real.exp_pos _).le
    _ = _ := by ring

/-- The complete lattice sum equals its explicit continuous main term up to
a remainder bounded independently of lattice spacing. -/
theorem norm_tsum_gaussianMellinWeight_sub_main_le {w ε : ℂ}
    (hw : 1 < w.re) (hw2 : w.re ≤ 2) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    ‖(∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) *
        ε ^ (-(w + 1) / 2))‖ ≤ gaussianMellinVariation w ε := by
  have hs := (summable_gaussianMellinWeight_lattice hw2 hε hb).hasSum.tendsto_sum_nat
  have hN : Tendsto (fun n : ℕ => b * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_gaussianMellinWeight (by linarith : 0 < w.re) hε) hN
  rw [integral_gaussianMellinWeight (by linarith) hε] at hi
  exact le_of_tendsto ((hs.sub (hi.const_mul (b : ℂ)⁻¹)).norm)
    (Filter.Eventually.of_forall fun N => norm_sum_gaussianMellinWeight_sub_integral_le hw hε hb N)

private theorem damping_rpow_cancel {α : ℝ} (hα : 0 < α) (q : ℝ) :
    α * (1 / α) ^ q = α ^ (1 - q) := by
  rw [one_div, Real.inv_rpow hα.le, ← Real.rpow_neg hα.le]
  nth_rw 1 [← Real.rpow_one α]
  rw [← Real.rpow_add hα]
  congr 1

private theorem norm_mul_gaussianMellinVariation_le {w ε : ℂ} {t : ℝ}
    (hw : 1 < w.re) (hε : 0 < ε.re) (ht : 0 < t)
    (hwsize : ‖w‖ ≤ 2 * t) (hsector : ‖ε‖ ≤ 4 * ε.re * t) :
    ‖ε / (t : ℂ)‖ * gaussianMellinVariation w ε ≤
      (4 * Real.Gamma (w.re / 2) + 16 * Real.Gamma ((w.re + 2) / 2)) *
        t * ε.re ^ (1 - w.re / 2) := by
  have hg1 : 0 ≤ Real.Gamma (w.re / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hg2 : 0 ≤ Real.Gamma ((w.re + 2) / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hv : 0 ≤ gaussianMellinVariation w ε := by
    unfold gaussianMellinVariation
    positivity
  have he : ‖ε / (t : ℂ)‖ ≤ 4 * ε.re := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact (div_le_iff₀ ht).mpr hsector
  have hV : gaussianMellinVariation w ε ≤
      t * (1 / ε.re) ^ (w.re / 2) * Real.Gamma (w.re / 2) +
        (4 * ε.re * t) * (1 / ε.re) ^ ((w.re + 2) / 2) *
          Real.Gamma ((w.re + 2) / 2) := by
    unfold gaussianMellinVariation
    exact _root_.add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : ‖w‖ / 2 ≤ t) (by positivity)) hg1)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsector (by positivity)) hg2)
  have hpow1 := damping_rpow_cancel hε (w.re / 2)
  have hpow2 : ε.re ^ 2 * (1 / ε.re) ^ ((w.re + 2) / 2) =
      ε.re ^ (1 - w.re / 2) := by
    calc
      _ = ε.re * (ε.re * (1 / ε.re) ^ ((w.re + 2) / 2)) := by ring
      _ = ε.re * ε.re ^ (1 - (w.re + 2) / 2) := by rw [damping_rpow_cancel hε]
      _ = ε.re ^ (1 - w.re / 2) := by
        nth_rw 1 [← Real.rpow_one ε.re]
        rw [← Real.rpow_add hε]
        congr 1
        ring
  calc
    _ ≤ (4 * ε.re) *
        (t * (1 / ε.re) ^ (w.re / 2) * Real.Gamma (w.re / 2) +
          (4 * ε.re * t) * (1 / ε.re) ^ ((w.re + 2) / 2) *
            Real.Gamma ((w.re + 2) / 2)) := mul_le_mul he hV hv (by positivity)
    _ = 4 * t * Real.Gamma (w.re / 2) * (ε.re * (1 / ε.re) ^ (w.re / 2)) +
        16 * t * Real.Gamma ((w.re + 2) / 2) *
          (ε.re ^ 2 * (1 / ε.re) ^ ((w.re + 2) / 2)) := by ring
    _ = _ := by rw [hpow1, hpow2]; ring

/-- The first-moment continuum term, evaluated without any zero-location input. -/
def gaussianFirstMomentPole (s ε : ℂ) (t : ℝ) : ℂ :=
  (ε / t) * ((1 / 2 : ℂ) * Complex.Gamma ((3 - s) / 2) * ε ^ (-(3 - s) / 2))

/-- The lattice remainder gains one full power of the Gaussian length.
The bound is uniform in every positive real lattice spacing. -/
theorem norm_tsum_gaussianFirstMoment_sub_pole_le {σ t : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 2 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) * (∑' n : ℕ,
        gaussianMellinWeight (2 - ((σ : ℂ) + t * I)) ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t‖ ≤
      (4 * Real.Gamma (1 - σ / 2) + 16 * Real.Gamma (2 - σ / 2)) *
        t * ε.re ^ (σ / 2) := by
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
    (norm_tsum_gaussianMellinWeight_sub_main_le hw hw2 hε hb) (norm_nonneg (ε / (t : ℂ)))
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
  have hs := norm_mul_gaussianMellinVariation_le hw hε ht0 hwsize hsector
  rw [hwre] at hs
  simpa only [show (2 - σ) / 2 = 1 - σ / 2 by ring,
    show (2 - σ + 2) / 2 = 2 - σ / 2 by ring,
    show 1 - (1 - σ / 2) = σ / 2 by ring] using hs

#print axioms integrableOn_gaussianMellinWeight
#print axioms norm_sum_gaussianMellinWeight_sub_integral_le
#print axioms integral_gaussianMellinWeight
#print axioms summable_gaussianMellinWeight_lattice
#print axioms norm_tsum_gaussianMellinWeight_sub_main_le
#print axioms norm_tsum_gaussianFirstMoment_sub_pole_le

end GaloisForLFunctions.ExceptionalLayerTheory
