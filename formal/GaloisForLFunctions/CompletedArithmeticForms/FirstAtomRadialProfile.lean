import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomFourierTail
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralJets
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Analytic radial profiles of the first theta atom

The complex radial source has a product exponential envelope on a fixed
strip. Cauchy estimates control every derivative under its radial tail.
-/

open Complex Filter Set MeasureTheory
open scoped Topology SchwartzMap FourierTransform
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

/-- Complex continuation of the first-atom radial tail integrand. -/
def firstAtomRadialKernel (u : ℝ) (z : ℂ) : ℂ :=
  (u ^ (3 / 2 : ℝ) : ℝ) *
    (4 * (u : ℂ) ^ 2 + 9 - 12 * (u : ℂ) * Complex.cosh (2 * z)) *
      Complex.exp (-2 * (u : ℂ) * Complex.cosh (2 * z))

theorem firstAtomRadialKernel_entire (u : ℝ) :
    Differentiable ℂ (firstAtomRadialKernel u) := by
  unfold firstAtomRadialKernel
  fun_prop

/-- The complex radial integrand restricts to the literal signed radial source. -/
theorem firstAtomRadialKernel_ofReal {u : ℝ} (hu : 0 < u) (t : ℝ) :
    4 * firstAtomRadialKernel u (t : ℂ) =
      ((u ^ (-(1 / 2 : ℝ)) * thetaCuspWignerRadialProfile (2 * u) t : ℝ) : ℂ) := by
  have h2 : u ^ (-(1 / 2 : ℝ)) * u ^ 2 = u ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hu]
    congr 1
    norm_num
  have h3 : u ^ (-(1 / 2 : ℝ)) * u ^ 3 = u ^ (3 / 2 : ℝ) * u := by
    calc
      _ = (u ^ (-(1 / 2 : ℝ)) * u ^ 2) * u := by ring
      _ = _ := by rw [h2]
  have h4 : u ^ (-(1 / 2 : ℝ)) * u ^ 4 = u ^ (3 / 2 : ℝ) * u ^ 2 := by
    calc
      _ = (u ^ (-(1 / 2 : ℝ)) * u ^ 2) * u ^ 2 := by ring
      _ = _ := by rw [h2]
  unfold firstAtomRadialKernel thetaCuspWignerRadialProfile
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_cosh, ← Complex.ofReal_exp,
    ← Complex.ofReal_pow, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_neg]
  congr 1
  rw [show -2 * u = -(2 * u) by ring]
  linear_combination
    -16 * Real.exp (-(2 * u) * Real.cosh (2 * t)) * h4 +
    48 * Real.cosh (2 * t) * Real.exp (-(2 * u) * Real.cosh (2 * t)) * h3 -
    36 * Real.exp (-(2 * u) * Real.cosh (2 * t)) * h2

private theorem norm_cosh_le_real_cosh (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, Real.cosh_eq, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have h := norm_add_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

private theorem abs_le_real_cosh (x : ℝ) : |x| ≤ Real.cosh x := by
  have hs := Real.self_le_sinh_iff.mpr (abs_nonneg x)
  have hc := Real.cosh_pos |x|
  have hs0 := Real.sinh_nonneg_iff.mpr (abs_nonneg x)
  have hid := Real.cosh_sq |x|
  rw [Real.cosh_abs] at hc hid
  nlinarith only [hs, hc, hs0, hid, sq_nonneg (Real.sinh |x| - |x|), abs_nonneg x]

private theorem cos_im_lower {z : ℂ} (hz : |z.im| ≤ Real.pi / 6) :
    (1 / 2 : ℝ) ≤ Real.cos (2 * z.im) := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (2 * z.im))
    (show Real.pi / 3 ≤ Real.pi by linarith only [Real.pi_pos])
    (show |2 * z.im| ≤ Real.pi / 3 by rw [abs_mul]; norm_num; linarith only [hz])
  simpa only [Real.cos_abs, Real.cos_pi_div_three] using h

private theorem re_cosh_two_mul (z : ℂ) :
    (Complex.cosh (2 * z)).re = Real.cosh (2 * z.re) * Real.cos (2 * z.im) := by
  have he : 2 * z = ((2 * z.re : ℝ) : ℂ) + ((2 * z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [he, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- Product exponential domination of the literal complex source on a fixed strip. -/
theorem norm_firstAtomRadialKernel_le {u : ℝ} (hu : 2 ≤ u) {z : ℂ}
    (hz : |z.im| ≤ Real.pi / 6) :
    ‖firstAtomRadialKernel u z‖ ≤
      9600 * Real.exp (-u / 4) * Real.exp (-|z.re|) := by
  let c := Real.cosh (2 * z.re)
  let v := u * c
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hc1 : 1 ≤ c := Real.one_le_cosh _
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have huv : u ≤ v := by dsimp only [v]; nlinarith only [mul_nonneg hu0 (sub_nonneg.mpr hc1)]
  have hv1 : 1 ≤ v := by linarith only [hu, huv]
  have hv0 : 0 ≤ v := zero_le_one.trans hv1
  have hcx : 2 * |z.re| ≤ c := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      abs_le_real_cosh (2 * z.re)
  have hvx : u / 2 + 2 * |z.re| ≤ v := by
    have h := mul_nonneg (show 0 ≤ u - 1 by linarith only [hu])
      (show 0 ≤ c - 1 by linarith only [hc1])
    dsimp only [v]
    nlinarith only [h, hu, hcx]
  have hnormc : ‖Complex.cosh (2 * z)‖ ≤ c := by
    simpa only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero] using norm_cosh_le_real_cosh (2 * z)
  have hnormp : ‖4 * (u : ℂ) ^ 2 + 9 - 12 * (u : ℂ) * Complex.cosh (2 * z)‖ ≤
      25 * v ^ 2 := by
    have h1 := norm_sub_le (4 * (u : ℂ) ^ 2 + 9) (12 * (u : ℂ) * Complex.cosh (2 * z))
    have h2 := norm_add_le (4 * (u : ℂ) ^ 2) 9
    have h3 : ‖12 * (u : ℂ) * Complex.cosh (2 * z)‖ ≤ 12 * u * c := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      norm_num only [norm_ofNat]
      exact mul_le_mul_of_nonneg_left hnormc (by positivity)
    norm_num only [norm_mul, norm_pow, norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hu0] at h2
    have huv2 : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu0 huv 2
    have hv2 : v ≤ v ^ 2 := by nlinarith only [mul_nonneg hv0 (sub_nonneg.mpr hv1)]
    have hv22 : 1 ≤ v ^ 2 := one_le_pow₀ hv1
    change ‖_‖ ≤ _
    have h3' : ‖12 * (u : ℂ) * Complex.cosh (2 * z)‖ ≤ 12 * v := by
      simpa only [v, mul_assoc] using h3
    linarith only [h1, h2, h3', huv2, hv2, hv22]
  have hp : u ^ (3 / 2 : ℝ) ≤ v ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ u by linarith only [hu])
      (show (3 / 2 : ℝ) ≤ 2 by norm_num)
    rw [Real.rpow_two] at h
    exact h.trans (pow_le_pow_left₀ hu0 huv 2)
  have he : ‖Complex.exp (-2 * (u : ℂ) * Complex.cosh (2 * z))‖ ≤ Real.exp (-v) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hcos := cos_im_lower hz
    rw [Complex.mul_re, Complex.mul_re]
    simp only [Complex.mul_im, Complex.neg_re, Complex.re_ofNat, Complex.ofReal_re,
      Complex.neg_im, Complex.im_ofNat, Complex.ofReal_im, mul_zero,
      sub_zero, re_cosh_two_mul]
    have h := mul_le_mul_of_nonneg_left hcos (mul_nonneg hu0 hc0)
    dsimp only [v, c] at *
    linarith only [h]
  have hraw : ‖firstAtomRadialKernel u z‖ ≤ 25 * v ^ 4 * Real.exp (-v) := by
    unfold firstAtomRadialKernel
    rw [norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hu0 _)]
    calc
      _ ≤ (v ^ 2 * (25 * v ^ 2)) * Real.exp (-v) :=
        mul_le_mul (mul_le_mul hp hnormp (norm_nonneg _) (sq_nonneg _)) he
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hfac := Real.pow_div_factorial_le_exp (v / 2) (by positivity) 4
  norm_num only [Nat.factorial] at hfac
  have hepos : 0 ≤ Real.exp (-v / 2) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hfac hepos
  have hexp : Real.exp (v / 2) * Real.exp (-v / 2) = 1 := by
    rw [← Real.exp_add, show v / 2 + -v / 2 = 0 by ring, Real.exp_zero]
  rw [hexp] at hmul
  have hpay : v ^ 4 * Real.exp (-v / 2) ≤ 384 := by nlinarith only [hmul]
  have hsplit : Real.exp (-v) = Real.exp (-v / 2) * Real.exp (-v / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdec : Real.exp (-v / 2) ≤ Real.exp (-u / 4) * Real.exp (-|z.re|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hvx])
  calc
    _ ≤ 25 * v ^ 4 * Real.exp (-v) := hraw
    _ = 25 * (v ^ 4 * Real.exp (-v / 2)) * Real.exp (-v / 2) := by rw [hsplit]; ring
    _ ≤ 9600 * Real.exp (-v / 2) := by nlinarith only [mul_le_mul_of_nonneg_right hpay hepos]
    _ ≤ _ := by nlinarith only [hdec]

/-- Literal radial integral of the first-atom complex source. -/
def firstAtomRadialTail (q : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi q, firstAtomRadialKernel u z

/-- Integrable radial envelope, extended by zero below the cutoff. -/
def firstAtomRadialEnvelope (q u : ℝ) : ℝ :=
  (Ioi q).indicator (fun v : ℝ => 9600 * Real.exp (-v / 4)) u

private def cutoffRadialKernel (q u : ℝ) (z : ℂ) : ℂ :=
  (Ioi q).indicator (fun v : ℝ => firstAtomRadialKernel v z) u

private theorem cutoffRadialKernel_entire (q u : ℝ) :
    Differentiable ℂ (cutoffRadialKernel q u) := by
  by_cases h : u ∈ Ioi q
  · have he : cutoffRadialKernel q u = firstAtomRadialKernel u := by
      funext z
      exact Set.indicator_of_mem h _
    rw [he]
    exact firstAtomRadialKernel_entire u
  · have he : cutoffRadialKernel q u = fun _ : ℂ => 0 := by
      funext z
      exact Set.indicator_of_notMem h _
    rw [he]
    exact differentiable_const _

private theorem cutoffRadialKernel_measurable (q : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun u => cutoffRadialKernel q u z) volume := by
  have hc : Continuous (fun u : ℝ => firstAtomRadialKernel u z) := by
    unfold firstAtomRadialKernel
    fun_prop (disch := norm_num)
  exact hc.aestronglyMeasurable.indicator measurableSet_Ioi

private theorem firstAtomRadialEnvelope_nonneg (q u : ℝ) :
    0 ≤ firstAtomRadialEnvelope q u := by
  exact Set.indicator_nonneg (fun v _ => by positivity) u

private theorem integrable_firstAtomRadialEnvelope (q : ℝ) :
    Integrable (firstAtomRadialEnvelope q) := by
  have he : IntegrableOn (fun u : ℝ => 9600 * Real.exp (-u / 4)) (Ioi q) := by
    have h : IntegrableOn (fun u : ℝ => 9600 * Real.exp (-(1 / 4 : ℝ) * u)) (Ioi q) :=
      (integrableOn_exp_mul_Ioi (a := -(1 / 4 : ℝ)) (by norm_num) q).const_mul 9600
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    dsimp only
    congr 2
    ring
  exact (integrable_indicator_iff measurableSet_Ioi).mpr he

private theorem cutoffRadialKernel_bound {q : ℝ} (hq : 2 ≤ q) (u : ℝ) {z : ℂ}
    (hz : |z.im| ≤ Real.pi / 6) :
    ‖cutoffRadialKernel q u z‖ ≤ firstAtomRadialEnvelope q u * Real.exp (-|z.re|) := by
  by_cases hu : u ∈ Ioi q
  · simp only [cutoffRadialKernel, firstAtomRadialEnvelope, Set.indicator_of_mem hu]
    exact norm_firstAtomRadialKernel_le (hq.trans hu.le) hz
  · simp only [cutoffRadialKernel, firstAtomRadialEnvelope, Set.indicator_of_notMem hu,
      norm_zero, zero_mul, le_refl]

private theorem cutoffRadialKernel_bound_uniform {q : ℝ} (hq : 2 ≤ q) (u : ℝ) {z : ℂ}
    (hz : |z.im| ≤ Real.pi / 6) :
    ‖cutoffRadialKernel q u z‖ ≤ firstAtomRadialEnvelope q u := by
  have he : Real.exp (-|z.re|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  exact (cutoffRadialKernel_bound hq u hz).trans
    ((mul_le_mul_of_nonneg_left he (firstAtomRadialEnvelope_nonneg q u)).trans_eq (mul_one _))

private theorem integral_cutoffRadialKernel (q : ℝ) (z : ℂ) :
    (∫ u : ℝ, cutoffRadialKernel q u z) = firstAtomRadialTail q z := by
  exact integral_indicator measurableSet_Ioi

/-- Holomorphy of the actual radial tail follows from its explicit source envelope. -/
theorem differentiableAt_firstAtomRadialTail {q : ℝ} (hq : 2 ≤ q) {z : ℂ}
    (hz : |z.im| < Real.pi / 6) : DifferentiableAt ℂ (firstAtomRadialTail q) z := by
  have h := hasDerivAt_integral_iteratedDeriv_of_strip_bound
    (cutoffRadialKernel_entire q) (cutoffRadialKernel_measurable q)
    (integrable_firstAtomRadialEnvelope q)
    (fun u w hw => cutoffRadialKernel_bound_uniform hq u hw) 0 hz
  simp only [iteratedDeriv_zero, integral_cutoffRadialKernel] at h
  exact h.differentiableAt

/-- Exponential decay of the actual tail throughout the closed source strip. -/
theorem norm_firstAtomRadialTail_le {q : ℝ} (hq : 2 ≤ q) {z : ℂ}
    (hz : |z.im| ≤ Real.pi / 6) :
    ‖firstAtomRadialTail q z‖ ≤
      (∫ u : ℝ, firstAtomRadialEnvelope q u) * Real.exp (-|z.re|) := by
  have he := (integrable_firstAtomRadialEnvelope q).mul_const (Real.exp (-|z.re|))
  have hi : Integrable (fun u => cutoffRadialKernel q u z) :=
    he.mono' (cutoffRadialKernel_measurable q z)
      (Eventually.of_forall fun u => cutoffRadialKernel_bound hq u hz)
  rw [← integral_cutoffRadialKernel]
  calc
    _ ≤ ∫ u : ℝ, ‖cutoffRadialKernel q u z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, firstAtomRadialEnvelope q u * Real.exp (-|z.re|) :=
      integral_mono_ae hi.norm he (Eventually.of_forall fun u => cutoffRadialKernel_bound hq u hz)
    _ = _ := integral_mul_const _ _

/-- The integrated first-atom profile is an actual Schwartz function. -/
def firstAtomRadialTailSchwartz (q : ℝ) (hq : 2 ≤ q) : SchwartzMap ℝ ℂ :=
  schwartzOfStripDecay (firstAtomRadialTail q)
    (δ := Real.pi / 12) (by positivity)
    (integral_nonneg (firstAtomRadialEnvelope_nonneg q))
    (fun z hz => differentiableAt_firstAtomRadialTail hq (by linarith only [hz]))
    (fun z hz => norm_firstAtomRadialTail_le hq (by linarith only [hz, Real.pi_pos]))

@[simp] theorem firstAtomRadialTailSchwartz_apply (q : ℝ) (hq : 2 ≤ q) (t : ℝ) :
    firstAtomRadialTailSchwartz q hq t = firstAtomRadialTail q (t : ℂ) := rfl

private theorem iteratedDeriv_cutoffRadialKernel (q u : ℝ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (cutoffRadialKernel q u) z =
      (Ioi q).indicator (fun v => iteratedDeriv n (firstAtomRadialKernel v) z) u := by
  by_cases hu : u ∈ Ioi q
  · have he : cutoffRadialKernel q u = firstAtomRadialKernel u := by
      funext w
      exact Set.indicator_of_mem hu _
    rw [he, Set.indicator_of_mem hu]
  · have he : cutoffRadialKernel q u = fun _ : ℂ => 0 := by
      funext w
      exact Set.indicator_of_notMem hu _
    rw [he, Set.indicator_of_notMem hu]
    simp

/-- All literal radial source jets are absolutely integrable on their tail. -/
theorem integrableOn_iteratedDeriv_firstAtomRadialKernel {q : ℝ} (hq : 2 ≤ q)
    (n : ℕ) {z : ℂ} (hz : |z.im| < Real.pi / 6) :
    IntegrableOn (fun u => iteratedDeriv n (firstAtomRadialKernel u) z) (Ioi q) := by
  have hi := integrable_iteratedDeriv_of_strip_bound
    (cutoffRadialKernel_entire q) (cutoffRadialKernel_measurable q)
    (integrable_firstAtomRadialEnvelope q)
    (fun u w hw => cutoffRadialKernel_bound_uniform hq u hw) n hz
  simp only [iteratedDeriv_cutoffRadialKernel] at hi
  exact (integrable_indicator_iff measurableSet_Ioi).mp hi

/-- Every complex jet of the actual tail is its admitted radial integral. -/
theorem iteratedDeriv_firstAtomRadialTail {q : ℝ} (hq : 2 ≤ q) (n : ℕ) {z : ℂ}
    (hz : |z.im| < Real.pi / 6) :
    iteratedDeriv n (firstAtomRadialTail q) z =
      ∫ u in Ioi q, iteratedDeriv n (firstAtomRadialKernel u) z := by
  have h := iteratedDeriv_integral_of_strip_bound
    (cutoffRadialKernel_entire q) (cutoffRadialKernel_measurable q)
    (integrable_firstAtomRadialEnvelope q)
    (fun u w hw => cutoffRadialKernel_bound_uniform hq u hw) n hz
  simp only [integral_cutoffRadialKernel] at h
  simp only [h, iteratedDeriv_cutoffRadialKernel, integral_indicator measurableSet_Ioi]

end
end GaloisForLFunctions.CompletedArithmeticForms
