import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomRadialProfile
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Aperture-weighted radial theta profiles

A polynomial envelope absorbs the exact logarithmic aperture primitive.
Dominated holomorphic integration gives a Schwartz profile, all-order jet
identities, and its literal Fourier integral.
-/

set_option autoImplicit false

open Complex Filter Set MeasureTheory
open scoped Topology SchwartzMap FourierTransform
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section


/-- The aperture primitive after multiplicative radial substitution. -/
def apertureRadialWeight (a q u : ℝ) : ℝ :=
  Real.log (u / q) * Real.sinh (a * Real.log (u / q))

theorem apertureRadialWeight_bounds {a q u : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) (hu : q ≤ u) :
    0 ≤ apertureRadialWeight a q u ∧ apertureRadialWeight a q u ≤ u ^ 2 := by
  have hq0 : 0 < q := by linarith only [hq]
  have hu0 : 0 < u := hq0.trans_le hu
  have hr1 : 1 ≤ u / q := (le_div_iff₀ hq0).mpr (by simpa using hu)
  have hr0 : 0 < u / q := by positivity
  have hru : u / q ≤ u := div_le_self hu0.le (by linarith only [hq])
  have hl0 : 0 ≤ Real.log (u / q) := Real.log_nonneg hr1
  have hlu : Real.log (u / q) ≤ u :=
    (Real.log_le_sub_one_of_pos hr0).trans (by linarith only [hru])
  have hs0 : 0 ≤ Real.sinh (a * Real.log (u / q)) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hl0)
  have hse : Real.sinh (a * Real.log (u / q)) ≤ Real.exp (a * Real.log (u / q)) := by
    rw [Real.sinh_eq]
    linarith only [Real.exp_pos (a * Real.log (u / q)), Real.exp_pos (-(a * Real.log (u / q)))]
  have hsu : Real.sinh (a * Real.log (u / q)) ≤ u := by
    calc
      _ ≤ Real.exp (a * Real.log (u / q)) := hse
      _ ≤ Real.exp (Real.log (u / q)) :=
        Real.exp_le_exp.mpr (mul_le_of_le_one_left hl0 ha1)
      _ = u / q := Real.exp_log hr0
      _ ≤ u := hru
  refine ⟨mul_nonneg hl0 hs0, ?_⟩
  dsimp only [apertureRadialWeight]
  simpa only [pow_two] using mul_le_mul hlu hsu hs0 hu0.le

private theorem square_mul_exp_quarter_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-u / 4) ≤ 128 * Real.exp (-u / 8) := by
  have hp := Real.pow_div_factorial_le_exp (u / 8) (by positivity) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at hp
  have hp' : u ^ 2 ≤ 128 * Real.exp (u / 8) := by nlinarith only [hp]
  have hm := mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-u / 4)).le
  rw [mul_assoc, ← Real.exp_add, show u / 8 + -u / 4 = -u / 8 by ring] at hm
  exact hm

private def cutoffApertureKernel (a q u : ℝ) (z : ℂ) : ℂ :=
  (Ioi q).indicator (fun v => (apertureRadialWeight a q v : ℂ) * firstAtomRadialKernel v z) u

private def apertureRadialEnvelope (q u : ℝ) : ℝ :=
  (Ioi q).indicator (fun v : ℝ => (128 * 9600) * Real.exp (-v / 8)) u

private theorem cutoffApertureKernel_entire (a q u : ℝ) :
    Differentiable ℂ (cutoffApertureKernel a q u) := by
  by_cases hu : u ∈ Ioi q
  · have he : cutoffApertureKernel a q u =
        fun z => (apertureRadialWeight a q u : ℂ) * firstAtomRadialKernel u z := by
      funext z
      exact Set.indicator_of_mem hu _
    rw [he]
    exact (differentiable_const _).mul (firstAtomRadialKernel_entire u)
  · have he : cutoffApertureKernel a q u = fun _ : ℂ => 0 := by
      funext z
      exact Set.indicator_of_notMem hu _
    rw [he]
    exact differentiable_const _

private theorem cutoffApertureKernel_measurable (a q : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun u => cutoffApertureKernel a q u z) volume := by
  have hw : Measurable (fun u : ℝ => (apertureRadialWeight a q u : ℂ)) := by
    unfold apertureRadialWeight
    fun_prop
  have hK : Continuous (fun u : ℝ => firstAtomRadialKernel u z) := by
    unfold firstAtomRadialKernel
    fun_prop (disch := norm_num)
  exact (hw.aestronglyMeasurable.mul hK.aestronglyMeasurable).indicator measurableSet_Ioi

private theorem apertureRadialEnvelope_nonneg (q u : ℝ) : 0 ≤ apertureRadialEnvelope q u :=
  Set.indicator_nonneg (fun _ _ => by positivity) u

private theorem integrable_apertureRadialEnvelope (q : ℝ) :
    Integrable (apertureRadialEnvelope q) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  have hi := (integrableOn_exp_mul_Ioi (a := -(1 / 8 : ℝ)) (by norm_num) q).const_mul (128 * 9600)
  refine hi.congr (Eventually.of_forall fun u => ?_)
  change 128 * 9600 * Real.exp (-(1 / 8 : ℝ) * u) = 128 * 9600 * Real.exp (-u / 8)
  rw [show -(1 / 8 : ℝ) * u = -u / 8 by ring]

private theorem cutoffApertureKernel_bound {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) (u : ℝ) {z : ℂ} (hz : |z.im| ≤ Real.pi / 6) :
    ‖cutoffApertureKernel a q u z‖ ≤ apertureRadialEnvelope q u * Real.exp (-|z.re|) := by
  by_cases hu : u ∈ Ioi q
  · simp only [cutoffApertureKernel, apertureRadialEnvelope, Set.indicator_of_mem hu,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨hw0, hwu⟩ := apertureRadialWeight_bounds ha0 ha1 hq hu.le
    rw [abs_of_nonneg hw0]
    have hu0 : 0 ≤ u := (by linarith only [hq] : 0 ≤ q).trans hu.le
    calc
      _ ≤ u ^ 2 * (9600 * Real.exp (-u / 4) * Real.exp (-|z.re|)) :=
        mul_le_mul hwu (norm_firstAtomRadialKernel_le (hq.trans hu.le) hz) (norm_nonneg _) (sq_nonneg _)
      _ = 9600 * (u ^ 2 * Real.exp (-u / 4)) * Real.exp (-|z.re|) := by ring
      _ ≤ 9600 * (128 * Real.exp (-u / 8)) * Real.exp (-|z.re|) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (square_mul_exp_quarter_le hu0) (by norm_num)) (Real.exp_pos _).le
      _ = _ := by ring
  · simp only [cutoffApertureKernel, apertureRadialEnvelope, Set.indicator_of_notMem hu,
      norm_zero, zero_mul, le_refl]

private theorem cutoffApertureKernel_bound_uniform {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) (u : ℝ) {z : ℂ} (hz : |z.im| ≤ Real.pi / 6) :
    ‖cutoffApertureKernel a q u z‖ ≤ apertureRadialEnvelope q u := by
  have he : Real.exp (-|z.re|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  exact (cutoffApertureKernel_bound ha0 ha1 hq u hz).trans
    ((mul_le_mul_of_nonneg_left he (apertureRadialEnvelope_nonneg q u)).trans_eq (mul_one _))

/-- Radial theta profile retaining the exact aperture primitive. -/
def apertureRadialProfile (a q : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi q, (apertureRadialWeight a q u : ℂ) * firstAtomRadialKernel u z

private theorem integral_cutoffApertureKernel (a q : ℝ) (z : ℂ) :
    (∫ u : ℝ, cutoffApertureKernel a q u z) = apertureRadialProfile a q z :=
  integral_indicator measurableSet_Ioi

theorem differentiableAt_apertureRadialProfile {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) {z : ℂ} (hz : |z.im| < Real.pi / 6) :
    DifferentiableAt ℂ (apertureRadialProfile a q) z := by
  have h := hasDerivAt_integral_iteratedDeriv_of_strip_bound
    (cutoffApertureKernel_entire a q) (cutoffApertureKernel_measurable a q)
    (integrable_apertureRadialEnvelope q)
    (fun u w hw => cutoffApertureKernel_bound_uniform ha0 ha1 hq u hw) 0 hz
  simp only [iteratedDeriv_zero, integral_cutoffApertureKernel] at h
  exact h.differentiableAt

theorem norm_apertureRadialProfile_le {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) {z : ℂ} (hz : |z.im| ≤ Real.pi / 6) :
    ‖apertureRadialProfile a q z‖ ≤
      (∫ u : ℝ, apertureRadialEnvelope q u) * Real.exp (-|z.re|) := by
  have he := (integrable_apertureRadialEnvelope q).mul_const (Real.exp (-|z.re|))
  have hi : Integrable (fun u => cutoffApertureKernel a q u z) :=
    he.mono' (cutoffApertureKernel_measurable a q z)
      (Eventually.of_forall fun u => cutoffApertureKernel_bound ha0 ha1 hq u hz)
  rw [← integral_cutoffApertureKernel]
  calc
    _ ≤ ∫ u : ℝ, ‖cutoffApertureKernel a q u z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, apertureRadialEnvelope q u * Real.exp (-|z.re|) :=
      integral_mono_ae hi.norm he (Eventually.of_forall fun u => cutoffApertureKernel_bound ha0 ha1 hq u hz)
    _ = _ := integral_mul_const _ _

def apertureRadialSchwartz (a q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) : SchwartzMap ℝ ℂ :=
  schwartzOfStripDecay (apertureRadialProfile a q)
    (δ := Real.pi / 12) (by positivity)
    (integral_nonneg (apertureRadialEnvelope_nonneg q))
    (fun z hz => differentiableAt_apertureRadialProfile ha0 ha1 hq (by linarith only [hz]))
    (fun z hz => norm_apertureRadialProfile_le ha0 ha1 hq (by linarith only [hz, Real.pi_pos]))

private theorem iteratedDeriv_cutoffApertureKernel (a q u : ℝ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (cutoffApertureKernel a q u) z =
      (Ioi q).indicator (fun v => (apertureRadialWeight a q v : ℂ) *
        iteratedDeriv n (firstAtomRadialKernel v) z) u := by
  by_cases hu : u ∈ Ioi q
  · have he : cutoffApertureKernel a q u =
        fun w => (apertureRadialWeight a q u : ℂ) * firstAtomRadialKernel u w := by
      funext w
      exact Set.indicator_of_mem hu _
    rw [he, Set.indicator_of_mem hu, iteratedDeriv_const_mul_field]
  · have he : cutoffApertureKernel a q u = fun _ : ℂ => 0 := by
      funext w
      exact Set.indicator_of_notMem hu _
    rw [he, Set.indicator_of_notMem hu]
    simp

/-- Every radial source jet remains integrable with the exact aperture weight. -/
theorem integrableOn_apertureRadialWeight_mul_jet {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) (n : ℕ) {z : ℂ} (hz : |z.im| < Real.pi / 6) :
    IntegrableOn (fun u => (apertureRadialWeight a q u : ℂ) *
      iteratedDeriv n (firstAtomRadialKernel u) z) (Ioi q) := by
  have hi := integrable_iteratedDeriv_of_strip_bound
    (cutoffApertureKernel_entire a q) (cutoffApertureKernel_measurable a q)
    (integrable_apertureRadialEnvelope q)
    (fun u w hw => cutoffApertureKernel_bound_uniform ha0 ha1 hq u hw) n hz
  simp only [iteratedDeriv_cutoffApertureKernel] at hi
  exact (integrable_indicator_iff measurableSet_Ioi).mp hi

/-- All profile jets are the literal aperture-weighted radial integrals. -/
theorem iteratedDeriv_apertureRadialProfile {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) (n : ℕ) {z : ℂ} (hz : |z.im| < Real.pi / 6) :
    iteratedDeriv n (apertureRadialProfile a q) z =
      ∫ u in Ioi q, (apertureRadialWeight a q u : ℂ) *
        iteratedDeriv n (firstAtomRadialKernel u) z := by
  have h := iteratedDeriv_integral_of_strip_bound
    (cutoffApertureKernel_entire a q) (cutoffApertureKernel_measurable a q)
    (integrable_apertureRadialEnvelope q)
    (fun u w hw => cutoffApertureKernel_bound_uniform ha0 ha1 hq u hw) n hz
  simp only [integral_cutoffApertureKernel] at h
  simp only [h, iteratedDeriv_cutoffApertureKernel, integral_indicator measurableSet_Ioi]

private def apertureFourierKernel (a q b : ℝ) (p : ℝ × ℝ) : ℂ :=
  cutoffApertureKernel a q p.1 (p.2 : ℂ) * thetaWignerDifferencePhase b p.2

private theorem integrable_apertureFourierKernel {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) (b : ℝ) :
    Integrable (apertureFourierKernel a q b) ((volume : Measure ℝ).prod volume) := by
  have ht : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
    simpa only [pow_zero, one_mul, neg_one_mul] using
      _root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (by norm_num : 0 < (1 : ℝ))
  have he := (integrable_apertureRadialEnvelope q).mul_prod ht
  have hm : AEStronglyMeasurable (apertureFourierKernel a q b)
      ((volume : Measure ℝ).prod volume) := by
    let S : Set (ℝ × ℝ) := Ioi q ×ˢ univ
    have hs : MeasurableSet S := measurableSet_Ioi.prod MeasurableSet.univ
    have hw : Measurable (fun p : ℝ × ℝ => (apertureRadialWeight a q p.1 : ℂ)) := by
      unfold apertureRadialWeight
      fun_prop
    have hc : Continuous (fun p : ℝ × ℝ => firstAtomRadialKernel p.1 (p.2 : ℂ) *
        thetaWignerDifferencePhase b p.2) := by
      unfold firstAtomRadialKernel thetaWignerDifferencePhase
      fun_prop (disch := norm_num)
    have hid : apertureFourierKernel a q b = S.indicator
        (fun p : ℝ × ℝ => (apertureRadialWeight a q p.1 : ℂ) *
          (firstAtomRadialKernel p.1 (p.2 : ℂ) * thetaWignerDifferencePhase b p.2)) := by
      funext p
      by_cases hp : p.1 ∈ Ioi q
      · simp only [apertureFourierKernel, cutoffApertureKernel, Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p ∈ S from ⟨hp, mem_univ _⟩), mul_assoc]
      · have hn : p ∉ S := fun h => hp h.1
        simp only [apertureFourierKernel, cutoffApertureKernel, Set.indicator_of_notMem hp,
          Set.indicator_of_notMem hn, zero_mul]
    rw [hid]
    exact (hw.aestronglyMeasurable.mul hc.aestronglyMeasurable).indicator hs
  refine he.mono' hm ?_
  filter_upwards with p
  have hphase : ‖thetaWignerDifferencePhase b p.2‖ = 1 := by
    simp [thetaWignerDifferencePhase, Complex.norm_exp]
  simp only [apertureFourierKernel, norm_mul, hphase, mul_one]
  exact cutoffApertureKernel_bound ha0 ha1 hq p.1 (by simp; positivity)

private theorem integral_apertureFourierKernel_left (a q b t : ℝ) :
    (∫ u : ℝ, apertureFourierKernel a q b (u, t)) =
      apertureRadialProfile a q (t : ℂ) * thetaWignerDifferencePhase b t := by
  simp only [apertureFourierKernel]
  rw [integral_mul_const, integral_cutoffApertureKernel]

private theorem integral_apertureFourierKernel_right (a q b u : ℝ) :
    (∫ t : ℝ, apertureFourierKernel a q b (u, t)) =
      (Ioi q).indicator (fun v : ℝ => (apertureRadialWeight a q v : ℂ) *
        ∫ t : ℝ, firstAtomRadialKernel v (t : ℂ) * thetaWignerDifferencePhase b t) u := by
  by_cases hu : u ∈ Ioi q
  · simp only [apertureFourierKernel, cutoffApertureKernel, Set.indicator_of_mem hu,
      mul_assoc, integral_const_mul]
  · simp only [apertureFourierKernel, cutoffApertureKernel, Set.indicator_of_notMem hu,
      zero_mul, integral_zero]

/-- Absolute radial integrability of the aperture-weighted Fourier slices. -/
theorem integrableOn_apertureRadialWeight_mul_fourier {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : 2 ≤ q) (b : ℝ) :
    IntegrableOn (fun u => (apertureRadialWeight a q u : ℂ) *
      ∫ t : ℝ, firstAtomRadialKernel u (t : ℂ) * thetaWignerDifferencePhase b t) (Ioi q) := by
  have h := (integrable_apertureFourierKernel ha0 ha1 hq b).integral_prod_left
  simp only [integral_apertureFourierKernel_right] at h
  exact (integrable_indicator_iff measurableSet_Ioi).mp h

/-- Exact normalization of the radial kernel's Fourier slice. -/
theorem integral_apertureRadialKernel_phase {u : ℝ} (hu : 0 < u) (b : ℝ) :
    (∫ t : ℝ, firstAtomRadialKernel u (t : ℂ) * thetaWignerDifferencePhase b t) =
      (1 / 4 : ℂ) * (u ^ (-(1 / 2 : ℝ)) : ℝ) * thetaCuspWignerRadialTransform (2 * u) b := by
  have he (t : ℝ) : firstAtomRadialKernel u (t : ℂ) * thetaWignerDifferencePhase b t =
      ((1 / 4 : ℂ) * (u ^ (-(1 / 2 : ℝ)) : ℝ)) *
        ((thetaCuspWignerRadialProfile (2 * u) t : ℂ) * thetaWignerDifferencePhase b t) := by
    have h := firstAtomRadialKernel_ofReal hu t
    push_cast at h
    linear_combination (thetaWignerDifferencePhase b t / 4) * h
  simp_rw [he]
  rw [integral_const_mul]
  rfl

/-- Fubini retains the aperture primitive in the literal radial Fourier transform. -/
theorem fourier_apertureRadialSchwartz_eq_integral {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 2 ≤ q) (ξ : ℝ) :
    𝓕 (apertureRadialSchwartz a q ha0 ha1 hq : ℝ → ℂ) ξ =
      ∫ u in Ioi q, (apertureRadialWeight a q u : ℂ) *
        ∫ t : ℝ, firstAtomRadialKernel u (t : ℂ) * thetaWignerDifferencePhase (-Real.pi * ξ) t := by
  have hF := integrable_apertureFourierKernel ha0 ha1 hq (-Real.pi * ξ)
  rw [Real.fourier_eq]
  change (∫ t : ℝ, (Real.fourierChar (-(inner ℝ t ξ)) : ℂ) *
    apertureRadialProfile a q (t : ℂ)) = _
  have he := integral_integral_swap (f := fun u t : ℝ =>
    apertureFourierKernel a q (-Real.pi * ξ) (u, t)) hF
  simp only [integral_apertureFourierKernel_left, integral_apertureFourierKernel_right,
    integral_indicator measurableSet_Ioi] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with t
  have hphase : (Real.fourierChar (-(inner ℝ t ξ)) : ℂ) =
      thetaWignerDifferencePhase (-Real.pi * ξ) t := by
    simp only [Real.fourierChar_apply, thetaWignerDifferencePhase, RCLike.inner_apply, conj_trivial]
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

/-- The unshifted aperture profile has a real Fourier transform. -/
theorem fourier_apertureRadialSchwartz_im_zero {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : 2 ≤ q) (ξ : ℝ) :
    (𝓕 (apertureRadialSchwartz a q ha0 ha1 hq : ℝ → ℂ) ξ).im = 0 := by
  rw [fourier_apertureRadialSchwartz_eq_integral ha0 ha1 hq]
  have hi := integrableOn_apertureRadialWeight_mul_fourier ha0 ha1 hq (-Real.pi * ξ)
  have he := Complex.imCLM.integral_comp_comm hi
  simp only [Complex.imCLM_apply] at he
  rw [← he]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hq.trans hu.le)
  rw [integral_apertureRadialKernel_phase hu0]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.div_im, Complex.div_re, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat,
    thetaCuspWignerRadialTransform_im_zero, mul_zero, zero_mul, add_zero, sub_zero,
    zero_div, Pi.zero_apply]

/-- Real Fourier inversion data is the literal weighted radial Fourier integral. -/
theorem fourier_apertureRadialSchwartz_re {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : 2 ≤ q) (ξ : ℝ) :
    (𝓕 (apertureRadialSchwartz a q ha0 ha1 hq : ℝ → ℂ) ξ).re =
      ∫ u in Ioi q, apertureRadialWeight a q u *
        (∫ t : ℝ, firstAtomRadialKernel u (t : ℂ) *
          thetaWignerDifferencePhase (-Real.pi * ξ) t).re := by
  rw [fourier_apertureRadialSchwartz_eq_integral ha0 ha1 hq]
  have hi := integrableOn_apertureRadialWeight_mul_fourier ha0 ha1 hq (-Real.pi * ξ)
  have he := Complex.reCLM.integral_comp_comm hi
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at he
  exact he.symm

#print axioms differentiableAt_apertureRadialProfile
#print axioms apertureRadialSchwartz
#print axioms iteratedDeriv_apertureRadialProfile
#print axioms fourier_apertureRadialSchwartz_eq_integral

end
end GaloisForLFunctions.CompletedArithmeticForms
