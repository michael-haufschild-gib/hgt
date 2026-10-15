import Mathlib.NumberTheory.LSeries.Dirichlet
import GaloisForLFunctions.RHTower.SoninExtendedFunctionalEquation
import GaloisForLFunctions.RHTower.SoninMellinFunctional
import GaloisForLFunctions.RHTower.SoninPrimePolarSignedEnergy
import GaloisForLFunctions.RHTower.MellinHeadChart
import GaloisForLFunctions.RHTower.CCMHardyCriticalMellinNonextension

/-!
# The actual damped prime–polar current on the physical Sonin carrier

Both normalized dilation directions, all von Mangoldt prime powers and the
literal polar density are retained. In the absolute-convergence half-plane,
the continuous head Mellin probe identifies the complete physical current
with two translated regularized critical Mellin defects. Changing the lower
polar endpoint contributes its exact finite physical integral.

The Hardy-zero obstruction excludes an L² representative of the continued
weak row at negative damping. This is a statement about the differentiated
current, not critical admission of the original logarithmic primitive, and
it does not prove the Riemann hypothesis.
-/

noncomputable section
open MeasureTheory Set Complex Filter Topology
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry
namespace RHTower

def soninHeadMellin (f : SoninL2) (w : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (w - 1) * f x

private theorem head_power_memLp {w : ℂ} (hw : 1 / 2 < w.re) :
    MemLp ((Ioo (0 : ℝ) 1).indicator (fun x : ℝ => (x : ℂ) ^ (-(starRingEnd ℂ) (1 - w))))
      2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Ioo).mpr
  apply memLp_two_cpow_Ioo (by norm_num : (0 : ℝ) < 1)
  change 1 - w.re < 1 / 2
  linarith

def soninHeadMellinCLM (w : ℂ) (hw : 1 / 2 < w.re) : SoninL2 →L[ℂ] ℂ :=
  innerSL ℂ ((head_power_memLp hw).toLp _)

theorem soninHeadMellinCLM_apply (w : ℂ) (hw : 1 / 2 < w.re) (f : SoninL2) :
    soninHeadMellinCLM w hw f = soninHeadMellin f w := by
  change ⟪(head_power_memLp hw).toLp _, f⟫_ℂ = _
  rw [MeasureTheory.L2.inner_def, soninHeadMellin,
    ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [(head_power_memLp hw).coeFn_toLp] with x hx
  rw [RCLike.inner_apply, hx]
  by_cases hxin : x ∈ Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hxin, Set.indicator_of_mem hxin,
      conj_ofReal_cpow_neg hxin.1 (1 - w)]
    rw [show -(1 - w) = w - 1 by ring]
    exact mul_comm _ _
  · simp only [Set.indicator_of_notMem hxin, map_zero, mul_zero]

theorem soninHeadMellin_eq_laplace (f : SoninL2) (w : ℂ) :
    soninHeadMellin f w = laplaceRay (logChartHead 1 f) (w - 1 / 2) := by
  have h := mellinHead_eq_laplaceRay (by norm_num : (0 : ℝ) < 1) f (1 - w)
  simpa only [show -(1 - w) = w - 1 by ring,
    show (1 : ℂ) / 2 - (1 - w) = w - 1 / 2 by ring,
    Complex.ofReal_one, Complex.one_cpow, one_mul, soninHeadMellin] using h

theorem analyticOnNhd_soninHeadMellin (f : SoninL2) :
    AnalyticOnNhd ℂ (soninHeadMellin f) {w : ℂ | 1 / 2 < w.re} := by
  have hphi := memLp_two_logChartHead (by norm_num : (0 : ℝ) < 1)
    ((Lp.memLp f).restrict (Ioo (0 : ℝ) 1))
  have hd : DifferentiableOn ℂ (soninHeadMellin f) {w : ℂ | 1 / 2 < w.re} := by
    intro w hw
    change 1 / 2 < w.re at hw
    have hshift : 0 < (w - 1 / 2).re := by simp only [Complex.sub_re]; norm_num; linarith
    have hlap := (differentiableOn_laplaceRay hphi).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hshift)
    have heq : soninHeadMellin f = fun z => laplaceRay (logChartHead 1 f) (z - 1 / 2) :=
      funext (soninHeadMellin_eq_laplace f)
    rw [heq]
    exact (hlap.comp w (differentiableAt_id.sub_const _)).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem soninHeadMellin_bandIndicator {r : ℝ} (hr : 0 < r)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    soninHeadMellin (bandIndicator r) w = (min 1 r : ℝ) ^ w / w := by
  have ha : 0 < min (1 : ℝ) r := lt_min zero_lt_one hr
  have hne : w ≠ 0 := by intro h; subst w; norm_num at hw
  have hint : Ioc (0 : ℝ) 1 ∩ centralInterval r = Ioc (0 : ℝ) (min 1 r) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, centralInterval, Set.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨hx, hx1⟩, _, hxr⟩
      exact ⟨hx, hx1, hxr⟩
    · rintro ⟨hx, hx1, hxr⟩
      exact ⟨⟨hx, hx1⟩, by linarith, hxr⟩
  have heq : soninHeadMellin (bandIndicator r) w =
      ∫ x in Ioc (0 : ℝ) 1,
        (centralInterval r).indicator (fun x : ℝ => (x : ℂ) ^ (w - 1)) x := by
    rw [soninHeadMellin, ← integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [(bandIndicator_coeFn r).restrict] with x hx
    rw [hx]
    by_cases hxr : x ∈ centralInterval r
    · simp only [Set.indicator_of_mem hxr, mul_one]
    · simp only [Set.indicator_of_notMem hxr, mul_zero]
  rw [heq, setIntegral_indicator (measurableSet_centralInterval r), hint,
    ← intervalIntegral.integral_of_le ha.le,
    integral_cpow (Or.inl (show (-1 : ℝ) < (w - 1).re by
      simp only [Complex.sub_re, Complex.one_re]; linarith)),
    show w - 1 + 1 = w by ring, Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero]

/-- No physical L2 vector realizes the complete weak current row below
critical damping, even with an arbitrary expanding-leg constant. -/
theorem not_exists_soninHeadMellin_current_negative
    {z : ℂ} (hzlo : -(1 / 2 : ℝ) < z.re) (hzhi : z.re < 0) (c : ℂ) :
    ¬ ∃ f : SoninL2, ∀ w : ℂ, 1 < (z + w).re →
      w * soninHeadMellin f w = -regularizedCriticalMellinDefect (z + w - 1) + c := by
  rintro ⟨f, hf⟩
  let A : ℂ → ℂ := fun u =>
    -((u + 1 - z) * soninHeadMellin f (u + 1 - z)) + c
  have hA : AnalyticOnNhd ℂ A {u : ℂ | z.re - 1 / 2 < u.re} := by
    intro u hu
    have hw : 1 / 2 < (u + 1 - z).re := by
      change z.re - 1 / 2 < u.re at hu
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith
    have hshift : AnalyticAt ℂ (fun v : ℂ => v + 1 - z) u := by fun_prop
    have hm : AnalyticAt ℂ (fun v => soninHeadMellin f (v + 1 - z)) u :=
      AnalyticAt.comp (f := fun v : ℂ => v + 1 - z)
        (analyticOnNhd_soninHeadMellin f (u + 1 - z) hw) hshift
    exact (hshift.mul hm).neg.add analyticAt_const
  have heq : ∀ u : ℂ, 0 < u.re → A u = regularizedCriticalMellinDefect u := by
    intro u hu
    have hw : 1 < (z + (u + 1 - z)).re := by
      rw [show z + (u + 1 - z) = u + 1 by ring, Complex.add_re, Complex.one_re]
      linarith
    have h := hf (u + 1 - z) hw
    rw [show z + (u + 1 - z) - 1 = u by ring] at h
    dsimp only [A]
    linear_combination -h
  exact no_analytic_extension_regularizedCriticalMellinDefect_pastHardy
    (c := z.re - 1 / 2) (by linarith) (by linarith) A hA heq


private theorem dilation_bandIndicator_one {r : ℝ} (hr : 0 < r) :
    rayDilate r (bandIndicator 1) = (Real.sqrt r : ℂ) • bandIndicator r⁻¹ := by
  rw [rayDilate_of_pos hr]
  apply Lp.ext
  have hcomp := (bandIndicator_coeFn 1).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [dilation_ae r hr (bandIndicator 1), hcomp,
    Lp.coeFn_smul (Real.sqrt r : ℂ) (bandIndicator r⁻¹),
    bandIndicator_coeFn r⁻¹] with x hd hc hs hb
  simp only [Function.comp_apply] at hc
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hd, hc, hs, hb]
  have hmem : r * x ∈ centralInterval 1 ↔ x ∈ centralInterval r⁻¹ := by
    simp only [centralInterval, Set.mem_Icc]
    have hi := mul_inv_cancel₀ hr.ne'
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor <;> nlinarith
    · rintro ⟨hlo, hhi⟩
      constructor <;> nlinarith
  by_cases hx : x ∈ centralInterval r⁻¹
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
  · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mp hx)]

private theorem sqrt_exp (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
  rw [Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Both literal physical dilation legs, with their original critical weight. -/
def soninDampedCurrentOrbit (z : ℂ) (u : ℝ) : SoninL2 :=
  Complex.exp (-(z + 1 / 2) * u) •
    (rayDilate (Real.exp u) (bandIndicator 1) +
      rayDilate (Real.exp (-u)) (bandIndicator 1))

/-- Exact head Mellin transform of the physical dilation of the unit interval. -/
theorem soninHeadMellin_dilated_bandIndicator (u : ℝ) {w : ℂ} (hw : 1 / 2 < w.re) :
    soninHeadMellin (rayDilate (Real.exp u) (bandIndicator 1)) w =
      (Real.exp (u / 2) : ℂ) * (min 1 (Real.exp (-u)) : ℝ) ^ w / w := by
  rw [dilation_bandIndicator_one (Real.exp_pos _),
    ← soninHeadMellinCLM_apply w hw, map_smul,
    soninHeadMellinCLM_apply, soninHeadMellin_bandIndicator (inv_pos.mpr (Real.exp_pos _)) hw,
    sqrt_exp, ← Real.exp_neg]
  simp only [smul_eq_mul, mul_div_assoc]

theorem soninHeadMellin_dampedCurrentOrbit {z w : ℂ} {u : ℝ}
    (hu : 0 ≤ u) (hw : 1 / 2 < w.re) :
    w * soninHeadMellin (soninDampedCurrentOrbit z u) w =
      Complex.exp (-(z + w) * u) + Complex.exp (-(z + 1) * u) := by
  have hw0 : w ≠ 0 := by intro h; subst w; norm_num at hw
  have h1 : Real.exp (-u) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have h2 : 1 ≤ Real.exp u := Real.one_le_exp hu
  rw [soninDampedCurrentOrbit, ← soninHeadMellinCLM_apply w hw,
    map_smul, map_add, soninHeadMellinCLM_apply, soninHeadMellinCLM_apply,
    soninHeadMellin_dilated_bandIndicator u hw, soninHeadMellin_dilated_bandIndicator (-u) hw,
    neg_neg, min_eq_right h1, min_eq_left h2, Complex.ofReal_one, Complex.one_cpow]
  rw [GaloisForLFunctions.cpow_ofReal_exp]
  simp only [smul_eq_mul, Complex.ofReal_exp]
  push_cast
  field_simp
  rw [mul_add]
  simp only [← Complex.exp_add]
  congr 1 <;> congr 1 <;> ring


private def pairedGroundOrbit (u : ℝ) : SoninL2 :=
  rayDilate (Real.exp u) (bandIndicator 1) +
    rayDilate (Real.exp (-u)) (bandIndicator 1)

private theorem continuous_pairedGroundOrbit : Continuous pairedGroundOrbit :=
  (continuous_dilationOrbit (bandIndicator 1)).add
    ((continuous_dilationOrbit (bandIndicator 1)).comp continuous_neg)

private theorem norm_pairedGroundOrbit_le (u : ℝ) :
    ‖pairedGroundOrbit u‖ ≤ 2 * ‖bandIndicator 1‖ := by
  calc
    _ ≤ ‖rayDilate (Real.exp u) (bandIndicator 1)‖ +
        ‖rayDilate (Real.exp (-u)) (bandIndicator 1)‖ := norm_add_le _ _
    _ = _ := by rw [norm_rayDilate (Real.exp_pos _), norm_rayDilate (Real.exp_pos _)]; ring

private theorem integrable_weighted_pairedGroundOrbit {μ : Measure ℝ} {g : ℝ → ℂ}
    (hg : Integrable g μ) : Integrable (fun u => g u • pairedGroundOrbit u) μ := by
  apply Integrable.mono' (hg.norm.mul_const (2 * ‖bandIndicator 1‖))
    (hg.aestronglyMeasurable.smul continuous_pairedGroundOrbit.aestronglyMeasurable)
  filter_upwards [] with u
  change ‖g u • pairedGroundOrbit u‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_pairedGroundOrbit_le u) (norm_nonneg _)

/-- Literal all-prime-power current, both physical dilation directions. -/
def soninDampedPrimeCurrent (z : ℂ) : SoninL2 :=
  ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z + 1/2) n •
    pairedGroundOrbit (Real.log n)

/-- The original polar current density, split into its two exponential terms. -/
def soninDampedPolarCurrent (z : ℂ) : SoninL2 :=
  ∫ u in Ioi (0 : ℝ),
    (Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u)) • pairedGroundOrbit u

def soninDampedPrimePolarCurrent (z : ℂ) : SoninL2 :=
  soninDampedPrimeCurrent z - soninDampedPolarCurrent z

private theorem summable_primeCurrent {z : ℂ} (hz : 1/2 < z.re) :
    Summable (fun n : ℕ =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z + 1/2) n •
        pairedGroundOrbit (Real.log n)) := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := z + 1/2) (by simp only [Complex.add_re]; norm_num; linarith)
  apply (hs.norm.mul_right (2 * ‖bandIndicator 1‖)).of_norm_bounded
  intro n
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_pairedGroundOrbit_le _) (norm_nonneg _)

private theorem integrable_polarCurrent {z : ℂ} (hz : 1/2 < z.re) :
    IntegrableOn (fun u : ℝ =>
      (Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u)) • pairedGroundOrbit u)
      (Ioi 0) := by
  apply integrable_weighted_pairedGroundOrbit
  apply Integrable.add
  · exact integrableOn_exp_mul_complex_Ioi (by simp only [Complex.neg_re, Complex.sub_re]; norm_num; linarith) 0
  · exact integrableOn_exp_mul_complex_Ioi (by simp only [Complex.neg_re, Complex.add_re]; norm_num; linarith) 0


private theorem lseries_term_exp (f : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term f s n = f n * Complex.exp (-s * (Real.log n : ℂ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : (n : ℂ) ^ s = Complex.exp ((Real.log n : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnR.le]
  rw [LSeries.term_of_ne_zero hn, hpow, div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  ring

private theorem head_primeCurrent_term {z w : ℂ} (hw : 1/2 < w.re) (n : ℕ) :
    w * soninHeadMellin
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z+1/2) n •
        pairedGroundOrbit (Real.log n)) w =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z+w) n +
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z+1) n := by
  by_cases hn : n = 0
  · subst n
    rw [LSeries.term_zero, zero_smul, ← soninHeadMellinCLM_apply w hw, map_zero]
    simp
  · rw [lseries_term_exp _ _ hn, mul_smul]
    change w * soninHeadMellin
      ((ArithmeticFunction.vonMangoldt n : ℂ) • soninDampedCurrentOrbit z (Real.log n)) w = _
    rw [← soninHeadMellinCLM_apply w hw, map_smul, soninHeadMellinCLM_apply]
    simp only [smul_eq_mul]
    rw [mul_left_comm w, soninHeadMellin_dampedCurrentOrbit
      (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)) hw,
      lseries_term_exp _ _ hn, lseries_term_exp _ _ hn, mul_add]

theorem soninHeadMellin_dampedPrimeCurrent {z w : ℂ}
    (hz : 1/2 < z.re) (hw : 1/2 < w.re) :
    w * soninHeadMellin (soninDampedPrimeCurrent z) w =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z+w) +
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z+1) := by
  have hs1 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := z+w) (by simp only [Complex.add_re]; linarith)
  have hs2 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := z+1) (by simp only [Complex.add_re, Complex.one_re]; linarith)
  rw [soninDampedPrimeCurrent, ← soninHeadMellinCLM_apply w hw,
    (soninHeadMellinCLM w hw).map_tsum (summable_primeCurrent hz), ← tsum_mul_left]
  simp_rw [soninHeadMellinCLM_apply, head_primeCurrent_term hw]
  exact hs1.tsum_add hs2

private theorem polar_weight_eq (z : ℂ) (u : ℝ) :
    Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u) =
      ((Real.exp u : ℂ) + 1) * Complex.exp (-(z+1/2) * u) := by
  rw [add_mul, one_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  ring

private theorem head_polarCurrent_integrand {z w : ℂ} {u : ℝ}
    (hu : 0 ≤ u) (hw : 1/2 < w.re) :
    w * soninHeadMellin
      ((Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u)) • pairedGroundOrbit u) w =
      (Complex.exp (-(z+w-1) * u) + Complex.exp (-(z+w) * u)) +
        (Complex.exp (-z * u) + Complex.exp (-(z+1) * u)) := by
  rw [polar_weight_eq, mul_smul]
  change w * soninHeadMellin (((Real.exp u : ℂ) + 1) • soninDampedCurrentOrbit z u) w = _
  rw [← soninHeadMellinCLM_apply w hw, map_smul, soninHeadMellinCLM_apply]
  simp only [smul_eq_mul]
  rw [mul_left_comm w, soninHeadMellin_dampedCurrentOrbit hu hw, Complex.ofReal_exp]
  simp only [add_mul, mul_add, one_mul, ← Complex.exp_add]
  have h1 : (u : ℂ) + -(z+w) * u = -(z+w-1)*u := by ring
  have h2 : (u : ℂ) + -(z+1) * u = -z*u := by ring
  rw [h1, h2]

theorem soninHeadMellin_dampedPolarCurrent {z w : ℂ}
    (hz : 1/2 < z.re) (hw : 1/2 < w.re) :
    w * soninHeadMellin (soninDampedPolarCurrent z) w =
      (1 / (z+w-1) + 1 / (z+w)) + (1 / z + 1 / (z+1)) := by
  have hn1 : (-(z+w-1)).re < 0 := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.one_re]; linarith
  have hn2 : (-(z+w)).re < 0 := by simp only [Complex.neg_re, Complex.add_re]; linarith
  have hn3 : (-z).re < 0 := by simp only [Complex.neg_re]; linarith
  have hn4 : (-(z+1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith
  have h1 := integrableOn_exp_mul_complex_Ioi hn1 0
  have h2 := integrableOn_exp_mul_complex_Ioi hn2 0
  have h3 := integrableOn_exp_mul_complex_Ioi hn3 0
  have h4 := integrableOn_exp_mul_complex_Ioi hn4 0
  rw [soninDampedPolarCurrent, ← soninHeadMellinCLM_apply w hw,
    ← (soninHeadMellinCLM w hw).integral_comp_comm (integrable_polarCurrent hz),
    ← integral_const_mul]
  simp_rw [soninHeadMellinCLM_apply]
  trans ∫ u in Ioi (0 : ℝ),
      (Complex.exp (-(z+w-1) * u) + Complex.exp (-(z+w) * u)) +
        (Complex.exp (-z * u) + Complex.exp (-(z+1) * u))
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact head_polarCurrent_integrand hu.le hw
  · have h12 : IntegrableOn (fun u : ℝ =>
        Complex.exp (-(z+w-1) * u) + Complex.exp (-(z+w) * u)) (Ioi 0) := h1.add h2
    have h34 : IntegrableOn (fun u : ℝ =>
        Complex.exp (-z * u) + Complex.exp (-(z+1) * u)) (Ioi 0) := h3.add h4
    rw [integral_add h12 h34, integral_add h1 h2, integral_add h3 h4,
      integral_exp_mul_complex_Ioi hn1 0, integral_exp_mul_complex_Ioi hn2 0,
      integral_exp_mul_complex_Ioi hn3 0, integral_exp_mul_complex_Ioi hn4 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]

theorem soninHeadMellin_dampedPrimePolarCurrent {z w : ℂ}
    (hz : 1/2 < z.re) (hw : 1/2 < w.re) :
    w * soninHeadMellin (soninDampedPrimePolarCurrent z) w =
      -regularizedCriticalMellinDefect (z+w-1) - regularizedCriticalMellinDefect z := by
  have hz0 : 0 < z.re := by linarith
  have hzw : 0 < (z+w-1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; linarith
  rw [soninDampedPrimePolarCurrent, ← soninHeadMellinCLM_apply w hw,
    map_sub, soninHeadMellinCLM_apply, soninHeadMellinCLM_apply, mul_sub,
    soninHeadMellin_dampedPrimeCurrent hz hw, soninHeadMellin_dampedPolarCurrent hz hw,
    regularizedCriticalMellinDefect_eq_continued hzw,
    regularizedCriticalMellinDefect_eq_continued hz0,
    ← criticalMellinDefectLaplaceChannelComplex_eq_continued hzw,
    ← criticalMellinDefectLaplaceChannelComplex_eq_continued hz0,
    criticalMellinDefectLaplaceChannelComplex, criticalMellinDefectLaplaceChannelComplex,
    continuousPolarLaplaceChannelComplex_eq hzw, continuousPolarLaplaceChannelComplex_eq hz0]
  simp only [vonMangoldtPrimeLaplaceChannelComplex, show z+w-1+1 = z+w by ring]
  ring


/-- Literal finite polar segment, retaining both normalized physical dilation legs. -/
def soninDampedFinitePolarCurrent (b : ℝ) (z : ℂ) : SoninL2 :=
  ∫ u in (0 : ℝ)..b,
    (Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u)) • pairedGroundOrbit u

/-- The actual current with the original positive lower polar endpoint. -/
def soninDampedPrimePolarCurrentFrom (b : ℝ) (z : ℂ) : SoninL2 :=
  soninDampedPrimeCurrent z - ∫ u in Ioi b,
    (Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u)) • pairedGroundOrbit u

theorem soninDampedPrimePolarCurrentFrom_eq {b : ℝ} (hb : 0 ≤ b)
    {z : ℂ} (hz : 1/2 < z.re) :
    soninDampedPrimePolarCurrentFrom b z =
      soninDampedPrimePolarCurrent z + soninDampedFinitePolarCurrent b z := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrable_polarCurrent hz) hb
  unfold soninDampedPrimePolarCurrentFrom soninDampedPrimePolarCurrent
    soninDampedPolarCurrent soninDampedFinitePolarCurrent
  rw [← hi]
  abel

theorem soninHeadMellin_dampedPrimePolarCurrentFrom {b : ℝ} (hb : 0 ≤ b)
    {z w : ℂ} (hz : 1/2 < z.re) (hw : 1/2 < w.re) :
    w * soninHeadMellin (soninDampedPrimePolarCurrentFrom b z) w =
      -regularizedCriticalMellinDefect (z+w-1) - regularizedCriticalMellinDefect z +
        w * soninHeadMellin (soninDampedFinitePolarCurrent b z) w := by
  rw [soninDampedPrimePolarCurrentFrom_eq hb hz, ← soninHeadMellinCLM_apply w hw,
    map_add, soninHeadMellinCLM_apply, soninHeadMellinCLM_apply, mul_add,
    soninHeadMellin_dampedPrimePolarCurrent hz hw]

/-- Finite physical polar subtraction cannot repair the negative-damping carrier obstruction. -/
theorem not_exists_soninDampedPrimePolarCurrentFrom_negative
    (b : ℝ) {z : ℂ} (hzlo : -(1/2 : ℝ) < z.re) (hzhi : z.re < 0) :
    ¬ ∃ f : SoninL2, ∀ w : ℂ, 1 < (z+w).re →
      w * soninHeadMellin f w =
        -regularizedCriticalMellinDefect (z+w-1) - regularizedCriticalMellinDefect z +
          w * soninHeadMellin (soninDampedFinitePolarCurrent b z) w := by
  rintro ⟨f, hf⟩
  apply not_exists_soninHeadMellin_current_negative hzlo hzhi
    (-regularizedCriticalMellinDefect z)
  refine ⟨f - soninDampedFinitePolarCurrent b z, ?_⟩
  intro w hw
  have hw' : 1/2 < w.re := by
    rw [Complex.add_re] at hw
    linarith
  rw [← soninHeadMellinCLM_apply w hw', map_sub,
    soninHeadMellinCLM_apply, soninHeadMellinCLM_apply, mul_sub, hf w hw]
  ring

theorem polarCurrent_weight_native (z : ℂ) (u : ℝ) :
    Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u) =
      Complex.exp (-z*u) * (2 * Real.cosh (u/2) : ℝ) := by
  rw [Real.cosh_eq]
  push_cast
  ring_nf
  rw [← Complex.exp_add, ← Complex.exp_add]

theorem intervalIntegrable_soninDampedFinitePolarCurrent (b : ℝ) (z : ℂ) :
    IntervalIntegrable (fun u : ℝ =>
      (Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u)) • pairedGroundOrbit u)
      volume 0 b := by
  have hc : Continuous (fun u : ℝ =>
      Complex.exp (-(z-1/2) * u) + Complex.exp (-(z+1/2) * u)) := by fun_prop
  exact (hc.smul continuous_pairedGroundOrbit).intervalIntegrable 0 b

end RHTower
