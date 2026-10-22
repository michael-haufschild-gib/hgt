import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemmaAd2C1
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemmaAd1
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Suzuki's canonical Hankel differential system

This module formalizes Suzuki (2012), equations (406)--(413), from the literal arithmetic-cusp
kernel and the proved Fredholm solution.  Equation (406) is first established as a strong `L¹`
identity; the spatial Euler identities below use a genuine weak derivative and prove its agreement
with the pointwise derivative on the exact regular locus.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace
attribute [local instance 2000] NormedAddCommGroup.toAddCommGroup

/-- Integration by parts for continuous complex functions differentiable away from countable
sets.  Unlike mathlib's basic interval lemma, this version admits Suzuki's arithmetic cusp loci.
Integrability is required only for the two products occurring in the identity, not for the raw
derivative fields separately. -/
theorem intervalIntegral_integral_mul_deriv_eq_deriv_mul_off_countable
    {u v u' v' : ℝ → ℂ} {a b : ℝ} {s t : Set ℝ}
    (hs : s.Countable) (ht : t.Countable)
    (hu : ContinuousOn u (uIcc a b)) (hv : ContinuousOn v (uIcc a b))
    (hdu : ∀ x ∈ Ioo (min a b) (max a b) \ s, HasDerivAt u (u' x) x)
    (hdv : ∀ x ∈ Ioo (min a b) (max a b) \ t, HasDerivAt v (v' x) x)
    (hintUV : IntervalIntegrable (fun x => u' x * v x) volume a b)
    (hintVU : IntervalIntegrable (fun x => u x * v' x) volume a b) :
    (∫ x in a..b, u x * v' x) =
      u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  have hprod : ContinuousOn (fun x => u x * v x) (uIcc a b) := hu.mul hv
  have hderiv : ∀ x ∈ Ioo (min a b) (max a b) \ (s ∪ t),
      HasDerivAt (fun y => u y * v y) (u' x * v x + u x * v' x) x := by
    intro x hx
    exact (hdu x ⟨hx.1, fun hxs => hx.2 (Or.inl hxs)⟩).mul
      (hdv x ⟨hx.1, fun hxt => hx.2 (Or.inr hxt)⟩)
  have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable
    (fun x => u x * v x) (fun x => u' x * v x + u x * v' x)
    (hs.union ht) hprod hderiv (hintUV.add hintVU)
  rw [intervalIntegral.integral_add hintUV hintVU] at hFTC
  apply eq_sub_of_add_eq
  rw [add_comm]
  exact hFTC

/-- A literal finite Hankel output vanishes throughout the lower support gap. -/
theorem suzukiSourceHIntervalIntegral_eq_zero_of_le_reciprocal
    {omega a x : ℝ} (ha : 0 < a) (hx : x ≤ 1 / a)
    (phi : C(ClosedInterval 0 a, ℂ)) :
    suzukiSourceHIntervalIntegral omega a phi x = 0 := by
  rw [suzukiSourceHIntervalIntegral]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  have hxy : x * (y : ℝ) ≤ 1 := by
    calc
      x * (y : ℝ) ≤ (1 / a) * a :=
        mul_le_mul hx y.property.2 y.property.1 (one_div_nonneg.mpr ha.le)
      _ = 1 := by field_simp
  simp [suzukiSourceHFinite, not_lt_of_ge hxy]

theorem hasDerivAt_suzukiSourceHIntervalIntegral_zero_of_lt_reciprocal
    {omega a x : ℝ} (ha : 0 < a) (hx : x < 1 / a)
    (phi : C(ClosedInterval 0 a, ℂ)) :
    HasDerivAt (suzukiSourceHIntervalIntegral omega a phi) 0 x := by
  have hev : suzukiSourceHIntervalIntegral omega a phi =ᶠ[nhds x]
      fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with z hz
    exact suzukiSourceHIntervalIntegral_eq_zero_of_le_reciprocal ha hz.le phi
  exact (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hev

theorem contDiffOn_one_suzukiSourceHIntervalIntegral_Ioi
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a)
    (phi : C(ClosedInterval 0 a, ℂ)) :
    ContDiffOn ℝ 1 (suzukiSourceHIntervalIntegral omega a phi) (Ioi 0) := by
  intro x hx
  exact (contDiffAt_one_suzukiSourceHIntervalIntegral homega ha hx phi).contDiffWithinAt

/-- The genuine spatial Euler derivative of a Hankel output is interval integrable.  Smoothing
makes it continuous on `(0,∞)`; the exact support gap makes it zero near the origin. -/
theorem intervalIntegrable_suzukiSourceHIntervalEuler
    {omega a b : ℝ} (homega : 1 < omega) (ha : 0 < a) (hb : 0 ≤ b)
    (phi : C(ClosedInterval 0 a, ℂ)) :
    IntervalIntegrable (fun x : ℝ =>
      (x : ℂ) * deriv (suzukiSourceHIntervalIntegral omega a phi) x)
      volume 0 b := by
  let F := suzukiSourceHIntervalIntegral omega a phi
  let E : ℝ → ℂ := fun x => (x : ℂ) * deriv F x
  have hE0 : ContinuousAt E 0 := by
    have hrecip : 0 < 1 / a := one_div_pos.mpr ha
    have hev : E =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hrecip] with x hx
      have hd := hasDerivAt_suzukiSourceHIntervalIntegral_zero_of_lt_reciprocal
        (omega := omega) ha hx phi
      dsimp only [E, F]
      rw [hd.deriv, mul_zero]
    exact continuousAt_const.congr_of_eventuallyEq hev
  have hE : ContinuousOn E (Icc 0 b) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hxpos
    · exact hE0.continuousWithinAt
    · have hdcontOn : ContinuousOn (deriv F) (Ioi 0) :=
        ContDiffOn.continuousOn_deriv_of_isOpen
          (contDiffOn_one_suzukiSourceHIntervalIntegral_Ioi homega ha phi)
          isOpen_Ioi (by norm_num)
      have hdcont : ContinuousAt (deriv F) x :=
        (hdcontOn x hxpos).continuousAt (Ioi_mem_nhds hxpos)
      have hreal : ContinuousAt (fun z : ℝ => (z : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt
      exact (hreal.mul hdcont).continuousWithinAt
  have hEu : ContinuousOn E (uIcc 0 b) := by
    simpa only [uIcc_of_le hb] using hE
  simpa only [E, F] using hEu.intervalIntegrable

/-- Exact logarithmic `W^{1,1}` representative of the weighted spatial derivative
`x ∂ₓ h_omega(cx)`, below a chosen smooth-extension horizon. -/
def suzukiScaledSourceEulerExtension
    (omega R c x : ℝ) : ℂ :=
  suzukiSourceHLogSmoothExtensionDerivative omega R
    (Real.log c + Real.log x)

theorem integrable_suzukiScaledSourceEulerExtension_subtype
    {omega R c b : ℝ} (homega : 1 < omega) (hb : 0 < b) :
    Integrable (fun x : ClosedInterval 0 b =>
      suzukiScaledSourceEulerExtension omega R c (x : ℝ)) := by
  have hshift : Integrable (fun r : ℝ =>
      suzukiSourceHLogSmoothExtensionDerivative omega R (Real.log c + r)) :=
    (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R).comp_add_left _
  exact integrable_suzukiLogPullback hb _ hshift

/-- Chain rule for the literal arithmetic source away from its exact scaled integer cusp set. -/
theorem hasDerivAt_suzukiScaledSource_of_regular
    {omega R c x : ℝ} (homega : 1 < omega) (hR : 0 ≤ R)
    (hc : 0 < c) (hx : 0 < x) (hrR : Real.log c + Real.log x < R)
    (hregular : ∀ n : ℕ, c * x ≠ (n : ℝ)) :
    HasDerivAt (fun y : ℝ => suzukiSourceHFinite omega (c * y))
      ((x⁻¹ : ℝ) • suzukiScaledSourceEulerExtension omega R c x) x := by
  have hrnot : Real.log c + Real.log x ∉ Set.range (fun n : ℕ => Real.log n) := by
    rintro ⟨n, hn⟩
    have hexp := congrArg Real.exp hn
    rw [Real.exp_add, Real.exp_log hc, Real.exp_log hx] at hexp
    cases n with
    | zero =>
        simp only [Nat.cast_zero, Real.log_zero, Real.exp_zero] at hexp
        exact hregular 1 (by simpa only [Nat.cast_one] using hexp.symm)
    | succ n =>
        have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        rw [Real.exp_log hnpos] at hexp
        exact hregular (n + 1)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hexp.symm)
  have hext := hasDerivAt_suzukiSourceHLogSmoothExtension_of_not_mem_log_nat
    (B := R) homega hrnot
  have harg : HasDerivAt (fun y : ℝ => Real.log c + Real.log y) x⁻¹ x :=
    (Real.hasDerivAt_log hx.ne').const_add (Real.log c)
  have hcomp := hext.scomp x harg
  have hev : (fun y : ℝ => suzukiSourceHLogSmoothExtension omega R
      (Real.log c + Real.log y)) =ᶠ[nhds x]
      fun y => suzukiSourceHFinite omega (c * y) := by
    have hpos : ∀ᶠ y : ℝ in nhds x, 0 < y := Ioi_mem_nhds hx
    have hhor : ∀ᶠ y : ℝ in nhds x, Real.log c + Real.log y < R :=
      (continuousAt_const.add (Real.continuousAt_log hx.ne')).eventually
        (Iio_mem_nhds hrR)
    filter_upwards [hpos, hhor] with y hy hyr
    rw [suzukiSourceHLogSmoothExtension_eq_sourceHFinite_exp omega hR hyr.le,
      Real.exp_add, Real.exp_log hc, Real.exp_log hy]
  exact hcomp.congr_of_eventuallyEq hev.symm

theorem suzukiScaledSourceEuler_eq_deriv_of_regular
    {omega R c x : ℝ} (homega : 1 < omega) (hR : 0 ≤ R)
    (hc : 0 < c) (hx : 0 < x) (hrR : Real.log c + Real.log x < R)
    (hregular : ∀ n : ℕ, c * x ≠ (n : ℝ)) :
    (x : ℂ) * deriv (fun y : ℝ => suzukiSourceHFinite omega (c * y)) x =
      suzukiScaledSourceEulerExtension omega R c x := by
  have hd := hasDerivAt_suzukiScaledSource_of_regular
    homega hR hc hx hrR hregular
  rw [hd.deriv]
  simp only [Complex.real_smul]
  have hcancel : (x : ℂ) * ((x⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast hx.ne')
  rw [← mul_assoc, hcancel, one_mul]

/-- The weighted derivative of the unsmoothed arithmetic source is integrable across every cusp.
This is the exact physical-variable consequence of the logarithmic `W^{1,1}` theorem. -/
theorem intervalIntegrable_suzukiScaledSourceEuler
    {omega c b : ℝ} (homega : 1 < omega) (hc : 0 < c) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ =>
      (x : ℂ) * deriv (fun y : ℝ => suzukiSourceHFinite omega (c * y)) x)
      volume 0 b := by
  let R := suzukiSourceLogExtensionHorizon b (Real.log c)
  have hR : 0 ≤ R := suzukiSourceLogExtensionHorizon_nonneg b (Real.log c)
  have hhor : Real.log c + Real.log b < R :=
    lt_suzukiSourceLogExtensionHorizon b (Real.log c)
  have hsmooth : Integrable (fun x : ClosedInterval 0 b =>
      suzukiScaledSourceEulerExtension omega R c (x : ℝ)) :=
    integrable_suzukiScaledSourceEulerExtension_subtype homega hb
  have hbad : (Set.range fun n : ℕ => (n : ℝ) / c).Countable :=
    Set.countable_range _
  have hcuspAe : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.range (fun n : ℕ => (n : ℝ) / c) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      hbad.measure_zero (volume : Measure ℝ)
  have haeReal : ∀ᵐ x : ℝ ∂volume,
      x ≠ 0 ∧ x ∉ Set.range (fun n : ℕ => (n : ℝ) / c) := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0, hcuspAe] with x hx0 hxcusp
    exact ⟨hx0, hxcusp⟩
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 b → ℝ)
      (volume : Measure (ClosedInterval 0 b))
      ((volume : Measure ℝ).restrict (Icc 0 b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have haeSub := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae haeReal)
  have heq : (fun x : ClosedInterval 0 b =>
      ((x : ℝ) : ℂ) * deriv
        (fun y : ℝ => suzukiSourceHFinite omega (c * y)) (x : ℝ)) =ᵐ[volume]
      fun x => suzukiScaledSourceEulerExtension omega R c (x : ℝ) := by
    filter_upwards [haeSub] with x hxgood
    have hxpos : 0 < (x : ℝ) :=
      lt_of_le_of_ne x.property.1 (Ne.symm hxgood.1)
    have hxlog : Real.log (x : ℝ) ≤ Real.log b :=
      Real.strictMonoOn_log.monotoneOn hxpos hb x.property.2
    apply suzukiScaledSourceEuler_eq_deriv_of_regular homega hR hc hxpos (by linarith)
    intro n hcn
    apply hxgood.2
    refine ⟨n, ?_⟩
    calc
      (n : ℝ) / c = (c * (x : ℝ)) / c := by rw [hcn]
      _ = (x : ℝ) := by field_simp
  have hsub : Integrable (fun x : ClosedInterval 0 b =>
      ((x : ℝ) : ℂ) * deriv
        (fun y : ℝ => suzukiSourceHFinite omega (c * y)) (x : ℝ)) :=
    hsmooth.congr heq.symm
  have hsub' : Integrable
      ((fun x : ℝ => (x : ℂ) * deriv
        (fun y : ℝ => suzukiSourceHFinite omega (c * y)) x) ∘
        ((↑) : ClosedInterval 0 b → ℝ)) := by
    exact hsub
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb.le]
  apply (hmp.integrable_comp_emb
    (show MeasurableEmbedding ((↑) : ClosedInterval 0 b → ℝ) from
      MeasurableEmbedding.subtype_coe measurableSet_Icc)).mp
  exact hsub'

/-- The spatial derivative of the global Fredholm solution is the derivative of its literal
source-minus-Hankel-output formula on the exact regular locus. -/
theorem hasDerivAt_suzukiHankelPhiGlobal_spatial_formula
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx : x ∈ SuzukiHankelRegularX a) :
    HasDerivAt (suzukiHankelPhiGlobal epsilon omega a homega ha)
      (deriv (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x -
        epsilon.coeff * deriv
          (suzukiSourceHIntervalIntegral omega a
            (suzukiHankelPhiContinuous epsilon omega a homega ha)) x) x := by
  let phi := suzukiHankelPhiContinuous epsilon omega a homega ha
  have hs : HasDerivAt (fun z : ℝ => suzukiSourceHFinite omega (a * z))
      (deriv (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x) x :=
    ((contDiffAt_one_suzukiHankelBoundaryGlobal homega ha hx).differentiableAt
      (by norm_num)).hasDerivAt
  have hH : HasDerivAt (suzukiSourceHIntervalIntegral omega a phi)
      (deriv (suzukiSourceHIntervalIntegral omega a phi) x) x :=
    ((contDiffAt_one_suzukiSourceHIntervalIntegral homega (by linarith) hx.1 phi).differentiableAt
      (by norm_num)).hasDerivAt
  have hformula := hs.sub ((hasDerivAt_const x epsilon.coeff).mul hH)
  have hphiAe := suzukiHankelPhiContinuous_ae (omega := omega) epsilon (by linarith) ha
  have hev : suzukiHankelPhiGlobal epsilon omega a homega ha =ᶠ[nhds x]
      fun z : ℝ => suzukiSourceHFinite omega (a * z) -
        epsilon.coeff * suzukiSourceHIntervalIntegral omega a phi z := by
    apply Eventually.of_forall
    intro z
    rw [suzukiHankelPhiGlobal]
    congr 2
    rw [suzukiSourceHIntervalIntegral]
    apply integral_congr_ae
    filter_upwards [hphiAe] with y hy
    change suzukiSourceHFinite omega (z * (y : ℝ)) *
        suzukiHankelPhi epsilon omega a (by linarith) ha y =
      suzukiSourceHFinite omega (z * (y : ℝ)) *
        suzukiHankelPhiContinuous epsilon omega a homega ha y
    rw [← hy]
  simpa only [zero_mul, zero_add] using hformula.congr_of_eventuallyEq hev

/-- Genuine spatial Euler field `delta_x phi = x phi' + phi/2`.  It is defined from Lean's
pointwise derivative, not from the differential equation to be proved. -/
def suzukiHankelEulerPhi
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 1 < a) (x : ℝ) : ℂ :=
  (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) x +
    (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha x

theorem intervalIntegrable_suzukiHankelPhiGlobal_deriv_mul_add
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    IntervalIntegrable (fun x : ℝ =>
      (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) x +
        suzukiHankelPhiGlobal epsilon omega a homega ha x) volume 0 a := by
  let phi := suzukiHankelPhiContinuous epsilon omega a homega ha
  let H := suzukiSourceHIntervalIntegral omega a phi
  have hs := intervalIntegrable_suzukiScaledSourceEuler homega (by linarith : 0 < a)
    (by linarith : 0 < a)
  have hH := intervalIntegrable_suzukiSourceHIntervalEuler
    homega (by linarith : 0 < a) (by linarith : 0 ≤ a) phi
  have hphi : IntervalIntegrable
      (suzukiHankelPhiGlobal epsilon omega a homega ha) volume 0 a := by
    have hc : ContinuousOn (suzukiHankelPhiGlobal epsilon omega a homega ha) (uIcc 0 a) := by
      rw [uIcc_of_le (by linarith : 0 ≤ a)]
      exact (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha).mono
        (fun x hx => hx.1)
    exact hc.intervalIntegrable
  have hexplicit : IntervalIntegrable (fun x : ℝ =>
      (x : ℂ) * deriv (fun y : ℝ => suzukiSourceHFinite omega (a * y)) x -
        epsilon.coeff * ((x : ℂ) * deriv H x) +
        suzukiHankelPhiGlobal epsilon omega a homega ha x) volume 0 a :=
    (hs.sub (hH.const_mul epsilon.coeff)).add hphi
  have hbad : (Set.range fun n : ℕ => (n : ℝ) / a).Countable := Set.countable_range _
  have hcuspAe : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.range (fun n : ℕ => (n : ℝ) / a) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      hbad.measure_zero (volume : Measure ℝ)
  have heq : ∀ᵐ x : ℝ ∂(volume.restrict (uIoc 0 a)),
      (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) x +
          suzukiHankelPhiGlobal epsilon omega a homega ha x =
        (x : ℂ) * deriv (fun y : ℝ => suzukiSourceHFinite omega (a * y)) x -
          epsilon.coeff * ((x : ℂ) * deriv H x) +
          suzukiHankelPhiGlobal epsilon omega a homega ha x := by
    filter_upwards [ae_restrict_of_ae hcuspAe,
      ae_restrict_mem measurableSet_uIoc] with x hxcusp hxmem
    have hxmem' : x ∈ Ioc 0 a := by
      simpa only [uIoc_of_le (by linarith : 0 ≤ a)] using hxmem
    have hxreg : x ∈ SuzukiHankelRegularX a := by
      refine ⟨hxmem'.1, ?_⟩
      intro n hxn
      apply hxcusp
      exact ⟨n, hxn.symm⟩
    have hd := hasDerivAt_suzukiHankelPhiGlobal_spatial_formula
      epsilon homega ha hxreg
    rw [hd.deriv]
    ring
  have heqFun : (fun x : ℝ =>
      (x : ℂ) * deriv (fun y : ℝ => suzukiSourceHFinite omega (a * y)) x -
        epsilon.coeff * ((x : ℂ) * deriv H x) +
        suzukiHankelPhiGlobal epsilon omega a homega ha x) =ᵐ[
        volume.restrict (uIoc 0 a)] fun x =>
      (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) x +
        suzukiHankelPhiGlobal epsilon omega a homega ha x := by
    filter_upwards [heq] with x hx
    exact hx.symm
  exact hexplicit.congr_ae heqFun

/-- The literal Euler field is integrable on Suzuki's Fredholm interval, including across all
arithmetic cusps. -/
theorem intervalIntegrable_suzukiHankelEulerPhi
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    IntervalIntegrable (suzukiHankelEulerPhi epsilon omega a homega ha) volume 0 a := by
  have hmain := intervalIntegrable_suzukiHankelPhiGlobal_deriv_mul_add epsilon homega ha
  have hphi : IntervalIntegrable
      (suzukiHankelPhiGlobal epsilon omega a homega ha) volume 0 a := by
    have hc : ContinuousOn (suzukiHankelPhiGlobal epsilon omega a homega ha) (uIcc 0 a) := by
      rw [uIcc_of_le (by linarith : 0 ≤ a)]
      exact (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha).mono
        (fun x hx => hx.1)
    exact hc.intervalIntegrable
  change IntervalIntegrable (fun x : ℝ =>
    (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) x +
      (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha x) volume 0 a
  have hrewrite : (fun x : ℝ =>
      (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) x +
        (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha x) =
      (fun x : ℝ =>
        ((x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) x +
          suzukiHankelPhiGlobal epsilon omega a homega ha x) -
        (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha x) := by
    funext x
    ring
  rw [hrewrite]
  exact hmain.sub (hphi.const_mul (1 / 2 : ℂ))

/-- Opposite sign in Suzuki's coupled positive/negative system. -/
def SuzukiHankelSign.opposite : SuzukiHankelSign → SuzukiHankelSign
  | .positive => .negative
  | .negative => .positive

@[simp] theorem SuzukiHankelSign.opposite_positive :
    SuzukiHankelSign.positive.opposite = .negative := rfl

@[simp] theorem SuzukiHankelSign.opposite_negative :
    SuzukiHankelSign.negative.opposite = .positive := rfl

@[simp] theorem SuzukiHankelSign.opposite_opposite (epsilon : SuzukiHankelSign) :
    epsilon.opposite.opposite = epsilon := by cases epsilon <;> rfl

@[simp] theorem SuzukiHankelSign.coeff_opposite (epsilon : SuzukiHankelSign) :
    epsilon.opposite.coeff = -epsilon.coeff := by cases epsilon <;> simp

/-- Suzuki (2012), equation (406), as an exact strong `L¹` identity on a fixed window.  Its
left side is `(1 + epsilon H_a)(a ∂ₐ phi_a^epsilon)`; its right side is the literal scaled source
derivative minus the moving-endpoint rank-one row. -/
theorem suzuki_equation_406_L1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
        ((a : ℂ) • suzukiFixedWindowPhiDerivativeL1
          epsilon omega B homega hB a ha0 haB) =
      (a : ℂ) • suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a -
        (a : ℂ) • suzukiFixedWindowSignedSectionDerivativeAtPhiL1
          epsilon omega B homega hB a ha0 haB := by
  have hbase :
      suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
          (suzukiFixedWindowPhiDerivativeL1
            epsilon omega B homega hB a ha0 haB) =
        suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a -
          suzukiFixedWindowSignedSectionDerivativeAtPhiL1
            epsilon omega B homega hB a ha0 haB := by
    rw [suzukiFixedWindowPhiDerivativeL1]
    exact suzukiFixedWindowResolventOperatorL1_apply_inverse
      epsilon omega B homega hB a _
  rw [map_smul, hbase, smul_sub]

/-- The derivative of Suzuki's physical Hankel integral, obtained from the literal logarithmic
`W^{1,1}` source extension.  This is the analytic bridge from aperture differentiation to the
spatial Euler identity; no differentiability of the cusp kernel is assumed at the exceptional
points. -/
theorem hasDerivAt_suzukiSourceHIntervalIntegral_explicit
    {omega a x : ℝ} (homega : 1 < omega) (ha : 0 < a) (hx : 0 < x)
    (phi : C(ClosedInterval 0 a, ℂ)) :
    let R := max 0 (Real.log x + Real.log a) + 1
    let W := suzukiReflectedLogProfile a ha.le phi
    let D := suzukiSourceHLogSmoothExtensionDerivative omega R
    HasDerivAt (suzukiSourceHIntervalIntegral omega a phi)
      ((x⁻¹ : ℝ) • suzukiLogConvolution W D (Real.log x)) x := by
  dsimp only
  let R : ℝ := max 0 (Real.log x + Real.log a) + 1
  let W : ℝ → ℂ := suzukiReflectedLogProfile a ha.le phi
  let H : ℝ → ℂ := suzukiSourceHLogSmoothExtension omega R
  let D : ℝ → ℂ := suzukiSourceHLogSmoothExtensionDerivative omega R
  have hR : 0 ≤ R := by
    dsimp only [R]
    linarith [le_max_left 0 (Real.log x + Real.log a)]
  have hxR : Real.log x + Real.log a < R := by
    dsimp only [R]
    linarith [le_max_right 0 (Real.log x + Real.log a)]
  have hW : Integrable W := integrable_suzukiReflectedLogProfile ha phi
  have hD : Integrable D := integrable_suzukiSourceHLogSmoothExtensionDerivative homega R
  have hH : Integrable H := integrable_suzukiSourceHLogSmoothExtension homega R
  have hWmeas : Measurable W := measurable_suzukiReflectedLogProfile ha.le phi
  have hWH : ∀ s, Integrable (fun t => W t * H (s - t)) := by
    intro s
    exact (hH.comp_sub_left s).bdd_mul hWmeas.aestronglyMeasurable
      (Eventually.of_forall fun t => norm_suzukiReflectedLogProfile_le ha phi t)
  have hWzero : ∀ t, t < -Real.log a → W t = 0 := by
    intro t ht
    exact suzukiReflectedLogProfile_eq_zero_of_lt_neg_log ha phi ht
  have hFTC : ∀ u v, u < R → v < R →
      (∫ r in u..v, D r) = H v - H u := by
    intro u v _ _
    exact integral_suzukiSourceHLogSmoothExtensionDerivative_eq_sub homega R u v
  have hJ : Continuous (suzukiLogConvolution W D) :=
    continuous_suzukiLogConvolution_of_integrable_right hD hWmeas
      (fun t => norm_suzukiReflectedLogProfile_le ha phi t)
      (fun t ht => continuousAt_suzukiReflectedLogProfile_of_ne_neg_log ha phi ht)
  have hlog : HasDerivAt (suzukiLogConvolution W H)
      (suzukiLogConvolution W D (Real.log x)) (Real.log x) :=
    hasDerivAt_suzukiLogConvolution hW hD hWH hWzero hFTC hJ hxR
  have hcomp := hlog.scomp x (Real.hasDerivAt_log hx.ne')
  have hev : (fun z : ℝ => suzukiLogConvolution W H (Real.log z)) =ᶠ[nhds x]
      suzukiSourceHIntervalIntegral omega a phi := by
    have hpos : ∀ᶠ z : ℝ in nhds x, 0 < z := Ioi_mem_nhds hx
    have hhor : ∀ᶠ z : ℝ in nhds x, Real.log z + Real.log a < R :=
      (Real.continuousAt_log hx.ne').add continuousAt_const |>.eventually
        (Iio_mem_nhds hxR)
    filter_upwards [hpos, hhor] with z hz hzR
    rw [suzukiLogConvolution_reflectedProfile_eq_interval ha phi]
    rw [suzukiSourceHIntervalIntegral]
    apply integral_congr_ae
    let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
        (volume : Measure (ClosedInterval 0 a))
        ((volume : Measure ℝ).restrict (Icc 0 a)) :=
      measurePreserving_subtype_coe measurableSet_Icc
    have hne := hmp.quasiMeasurePreserving.ae
      (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0))
    filter_upwards [hne] with y hy0
    have hy : 0 < (y : ℝ) :=
      lt_of_le_of_ne y.property.1 (Ne.symm hy0)
    have hylog : Real.log (y : ℝ) ≤ Real.log a :=
      Real.strictMonoOn_log.monotoneOn hy ha y.property.2
    change suzukiSourceHLogSmoothExtension omega R
        (Real.log z + Real.log (y : ℝ)) * phi y = _
    rw [suzukiSourceHLogSmoothExtension_eq_sourceHFinite_exp omega hR (by linarith),
      Real.exp_add, Real.exp_log hz, Real.exp_log hy]
  exact hcomp.congr_of_eventuallyEq hev.symm

/-- Exact Euler transport identity for Suzuki's Hankel integral.  The equality holds despite the
countable arithmetic cusp set because both sides are represented by the same logarithmic
`W^{1,1}` derivative. -/
theorem suzukiSourceHIntervalEuler_eq_integral_deriv
    {omega a x : ℝ} (homega : 1 < omega) (ha : 0 < a) (hx : 0 < x)
    (phi : C(ClosedInterval 0 a, ℂ)) :
    (x : ℂ) * deriv (suzukiSourceHIntervalIntegral omega a phi) x =
      ∫ y : ClosedInterval 0 a,
        ((y : ℝ) : ℂ) * deriv
          (fun z : ℝ => suzukiSourceHFinite omega (x * z)) (y : ℝ) * phi y := by
  let R : ℝ := max 0 (Real.log x + Real.log a) + 1
  let W : ℝ → ℂ := suzukiReflectedLogProfile a ha.le phi
  let D : ℝ → ℂ := suzukiSourceHLogSmoothExtensionDerivative omega R
  have hR : 0 ≤ R := by
    dsimp only [R]
    linarith [le_max_left 0 (Real.log x + Real.log a)]
  have hxR : Real.log x + Real.log a < R := by
    dsimp only [R]
    linarith [le_max_right 0 (Real.log x + Real.log a)]
  have hd := hasDerivAt_suzukiSourceHIntervalIntegral_explicit homega ha hx phi
  change HasDerivAt (suzukiSourceHIntervalIntegral omega a phi)
    ((x⁻¹ : ℝ) • suzukiLogConvolution W D (Real.log x)) x at hd
  have hcancel : (x : ℂ) * ((x⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast hx.ne')
  rw [hd.deriv, Complex.real_smul, ← mul_assoc, hcancel, one_mul,
    suzukiLogConvolution_reflectedProfile_eq_interval ha phi]
  apply integral_congr_ae
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hbad : (Set.range fun n : ℕ => (n : ℝ) / x).Countable := Set.countable_range _
  have hcuspAe : ∀ᵐ y : ℝ ∂volume,
      y ∉ Set.range (fun n : ℕ => (n : ℝ) / x) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      hbad.measure_zero (volume : Measure ℝ)
  have hgood := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0 |>.and hcuspAe))
  filter_upwards [hgood] with y hygood
  have hy : 0 < (y : ℝ) :=
    lt_of_le_of_ne y.property.1 (Ne.symm hygood.1)
  have hylog : Real.log (y : ℝ) ≤ Real.log a :=
    Real.strictMonoOn_log.monotoneOn hy ha y.property.2
  have hreg : ∀ n : ℕ, x * (y : ℝ) ≠ (n : ℝ) := by
    intro n hxy
    apply hygood.2
    refine ⟨n, ?_⟩
    calc
      (n : ℝ) / x = (x * (y : ℝ)) / x := by rw [hxy]
      _ = (y : ℝ) := by field_simp
  have heuler := suzukiScaledSourceEuler_eq_deriv_of_regular
    homega hR hx hy (by linarith) hreg
  change suzukiScaledSourceEulerExtension omega R x (y : ℝ) * phi y = _
  rw [← heuler]

/-- Subtype integration on a closed real interval agrees with interval integration. -/
theorem integral_subtype_closedInterval_eq_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b) (F : ℝ → E) :
    (∫ y : ClosedInterval a b, F (y : ℝ) ∂volume) = ∫ y in a..b, F y := by
  calc
    (∫ y : ClosedInterval a b, F (y : ℝ) ∂volume) =
        ∫ y in Icc a b, F y :=
      MeasureTheory.integral_subtype measurableSet_Icc F
    _ = ∫ y in Ioc a b, F y := MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ y in a..b, F y := by
      rw [intervalIntegral.integral_of_le hab]

/-- The exact spatial integration-by-parts step used in Suzuki (2012), equation (407).  Kernel
cusps `n/x` and Fredholm-solution cusps `n/a` are treated as two independent countable exceptional
sets.  Both weighted derivative products are proved interval-integrable across those cusps. -/
theorem suzuki_spatial_integration_by_parts
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx : 0 < x) :
    (∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega (x * y) *
          ((y : ℂ) * deriv
              (suzukiHankelPhiGlobal epsilon omega a homega ha) y +
            suzukiHankelPhiGlobal epsilon omega a homega ha y)) =
      suzukiSourceHFinite omega (x * a) *
          ((a : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha a) -
        ∫ y in (0 : ℝ)..a,
          deriv (fun z : ℝ => suzukiSourceHFinite omega (x * z)) y *
            ((y : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha y) := by
  let P : ℝ → ℂ := suzukiHankelPhiGlobal epsilon omega a homega ha
  let u : ℝ → ℂ := fun y => suzukiSourceHFinite omega (x * y)
  let v : ℝ → ℂ := fun y => y • P y
  let u' : ℝ → ℂ := fun y => deriv u y
  let v' : ℝ → ℂ := fun y => y • deriv P y + P y
  let s : Set ℝ := Set.range fun n : ℕ => (n : ℝ) / x
  let t : Set ℝ := Set.range fun n : ℕ => (n : ℝ) / a
  have h0a : 0 ≤ a := by linarith
  have hu : ContinuousOn u (uIcc 0 a) := by
    rw [uIcc_of_le h0a]
    intro y hy
    rcases eq_or_lt_of_le hy.1 with rfl | hypos
    · have hrecip : 0 < 1 / x := one_div_pos.mpr hx
      have hev : u =ᶠ[nhds 0] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hrecip] with z hz
        dsimp only [u]
        rw [suzukiSourceHFinite, if_neg]
        exact not_lt_of_ge (calc
          x * z ≤ x * (1 / x) := mul_le_mul_of_nonneg_left hz.le hx.le
          _ = 1 := by field_simp)
      exact (continuousAt_const.congr_of_eventuallyEq hev).continuousWithinAt
    · exact ((continuousAt_suzukiSourceHFinite homega (mul_pos hx hypos)).comp
        (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  have hP : ContinuousOn P (uIcc 0 a) := by
    rw [uIcc_of_le h0a]
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha).mono
      (fun _ hy => hy.1)
  have hv : ContinuousOn v (uIcc 0 a) := by
    exact continuous_id.continuousOn.smul hP
  have hs : s.Countable := Set.countable_range _
  have ht : t.Countable := Set.countable_range _
  have hdu : ∀ y ∈ Ioo (min 0 a) (max 0 a) \ s, HasDerivAt u (u' y) y := by
    intro y hy
    have hy' : y ∈ Ioo 0 a := by simpa [min_eq_left h0a, max_eq_right h0a] using hy.1
    have hnat : ∀ n : ℕ, x * y ≠ (n : ℝ) := by
      intro n hxy
      apply hy.2
      refine ⟨n, ?_⟩
      calc
        (n : ℝ) / x = (x * y) / x := by rw [hxy]
        _ = y := by field_simp
    have hd : DifferentiableAt ℝ u y := by
      exact ((contDiffAt_one_suzukiSourceHFinite_of_not_nat homega
        (mul_pos hx hy'.1) hnat).comp y
          (contDiffAt_const.mul contDiffAt_id)).differentiableAt (by norm_num)
    exact hd.hasDerivAt
  have hdv : ∀ y ∈ Ioo (min 0 a) (max 0 a) \ t, HasDerivAt v (v' y) y := by
    intro y hy
    have hy' : y ∈ Ioo 0 a := by simpa [min_eq_left h0a, max_eq_right h0a] using hy.1
    have hyreg : y ∈ SuzukiHankelRegularX a := by
      refine ⟨hy'.1, ?_⟩
      intro n hyn
      apply hy.2
      exact ⟨n, hyn.symm⟩
    have hphi : HasDerivAt P (deriv P y) y :=
      ((contDiffAt_one_suzukiHankelPhiGlobal_of_regular epsilon homega ha hyreg).differentiableAt
        (by norm_num)).hasDerivAt
    have hsmul := (hasDerivAt_id y).smul hphi
    have hev : v =ᶠ[nhds y] ((id : ℝ → ℝ) • P) := by
      apply Eventually.of_forall
      intro z
      change z • P z = z • P z
      rfl
    simpa only [v', id_eq, one_smul] using hsmul.congr_of_eventuallyEq hev
  have huEuler : IntervalIntegrable (fun y : ℝ =>
      (y : ℂ) * deriv u y) volume 0 a := by
    simpa only [u] using intervalIntegrable_suzukiScaledSourceEuler
      homega hx (by linarith : 0 < a)
  have hintUV : IntervalIntegrable (fun y => u' y * v y) volume 0 a := by
    have h := huEuler.mul_continuousOn hP
    apply h.congr
    intro y _
    dsimp only [u', v, P]
    rw [Complex.real_smul]
    ring
  have hvPrime : IntervalIntegrable v' volume 0 a := by
    simpa only [v', P, Complex.real_smul] using
      intervalIntegrable_suzukiHankelPhiGlobal_deriv_mul_add epsilon homega ha
  have hintVU : IntervalIntegrable (fun y => u y * v' y) volume 0 a := by
    exact hvPrime.continuousOn_mul hu
  have hibp := intervalIntegral_integral_mul_deriv_eq_deriv_mul_off_countable
    hs ht hu hv hdu hdv hintUV hintVU
  simpa only [u, v, u', v', P, Complex.real_smul, zero_mul, mul_zero, sub_zero,
    Complex.ofReal_zero] using hibp

end RHTower
