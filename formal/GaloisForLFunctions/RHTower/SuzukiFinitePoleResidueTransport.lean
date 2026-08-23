import GaloisForLFunctions.RHTower.SuzukiContourLineIntegrability
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Suzuki finite-pole residue transport

The pointwise shifted-Xi quotient is replaced internally by mathlib's canonical meromorphic normal
form, which fills common-zero removabilities without changing punctured germs. Exact endpoint
integrability, Xi-good selected vertical sides, and arbitrary-order rectangle residues then yield
the card's normalized finite-pole contour identity for the original pointwise quotient.
-/

namespace RHTower

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped BigOperators Interval

noncomputable section

/-- Canonical normal-form representative of Suzuki's shifted-Xi quotient. It fills removable
common-zero values and retains value `0` at genuine poles, without changing any punctured germ. -/
def suzukiCanonicalThetaNF (omega : ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn (suzukiCanonicalTheta omega) Set.univ

theorem meromorphicNFOn_suzukiCanonicalThetaNF (omega : ℝ) :
    MeromorphicNFOn (suzukiCanonicalThetaNF omega) Set.univ := by
  exact meromorphicNFOn_toMeromorphicNFOn _ _

theorem meromorphicOn_suzukiCanonicalThetaNF (omega : ℝ) :
    MeromorphicOn (suzukiCanonicalThetaNF omega) Set.univ :=
  (meromorphicNFOn_suzukiCanonicalThetaNF omega).meromorphicOn

theorem suzukiCanonicalThetaNF_eq_of_E_ne_zero
    (omega : ℝ) {z : ℂ} (hE : suzukiCanonicalE omega z ≠ 0) :
    suzukiCanonicalThetaNF omega z = suzukiCanonicalTheta omega z := by
  have htheta := meromorphicOn_suzukiCanonicalTheta omega
  rw [suzukiCanonicalThetaNF,
    toMeromorphicNFOn_eq_toMeromorphicNFAt htheta (Set.mem_univ z)]
  rw [toMeromorphicNFAt_eq_self.2]
  have han : AnalyticAt ℂ (suzukiCanonicalTheta omega) z := by
    rw [show suzukiCanonicalTheta omega = fun w : ℂ =>
        suzukiCanonicalESharp omega w / suzukiCanonicalE omega w by
      funext w
      exact suzukiCanonicalTheta_eq_ESharp_div_E omega w]
    exact ((differentiable_suzukiCanonicalESharp omega).analyticAt z).div
      ((differentiable_suzukiCanonicalE omega).analyticAt z) hE
  exact han.meromorphicNFAt

private theorem countable_suzukiCanonicalE_zeroSet (omega : ℝ) :
    {z : ℂ | suzukiCanonicalE omega z = 0}.Countable := by
  apply HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd
  · exact (differentiable_suzukiCanonicalE omega).differentiableOn.analyticOnNhd isOpen_univ
  · exact ⟨0, suzukiCanonicalE_zero_ne_zero omega⟩

theorem suzukiCanonicalThetaNF_horizontal_ae_eq
    (omega sigma : ℝ) :
    (fun x : ℝ => suzukiCanonicalThetaNF omega
      ((x : ℂ) + (sigma : ℂ) * Complex.I)) =ᵐ[volume]
    fun x : ℝ => suzukiCanonicalTheta omega
      ((x : ℂ) + (sigma : ℂ) * Complex.I) := by
  have hinj : Function.Injective fun x : ℝ =>
      (x : ℂ) + (sigma : ℂ) * Complex.I := by
    intro x y hxy
    apply_fun Complex.re at hxy
    simpa using hxy
  have hpre : {x : ℝ | suzukiCanonicalE omega
      ((x : ℂ) + (sigma : ℂ) * Complex.I) = 0}.Countable :=
    (countable_suzukiCanonicalE_zeroSet omega).preimage hinj
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (hpre.measure_zero volume)] with x hx
  apply suzukiCanonicalThetaNF_eq_of_E_ne_zero
  simpa using hx

theorem suzukiCanonicalThetaNF_vertical_ae_eq
    (omega x : ℝ) :
    (fun y : ℝ => suzukiCanonicalThetaNF omega
      ((x : ℂ) + (y : ℂ) * Complex.I)) =ᵐ[volume]
    fun y : ℝ => suzukiCanonicalTheta omega
      ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have hinj : Function.Injective fun y : ℝ =>
      (x : ℂ) + (y : ℂ) * Complex.I := by
    intro y₁ y₂ hy
    apply_fun Complex.im at hy
    simpa using hy
  have hpre : {y : ℝ | suzukiCanonicalE omega
      ((x : ℂ) + (y : ℂ) * Complex.I) = 0}.Countable :=
    (countable_suzukiCanonicalE_zeroSet omega).preimage hinj
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (hpre.measure_zero volume)] with y hy
  apply suzukiCanonicalThetaNF_eq_of_E_ne_zero
  simpa using hy

/-- Exact test integrand formed from the common-divisor-canceled shifted-Xi quotient. -/
def suzukiCanonicalHankelContourIntegrandNF
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) (z : ℂ) : ℂ :=
  suzukiCanonicalThetaNF omega z *
    deningerMeyerStrongLogMellin g (-Complex.I * z) *
    Complex.exp (-Complex.I * z * (r : ℂ))

theorem suzukiCanonicalHankelContourIntegrandNF_horizontal_ae_eq
    (omega sigma : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    (fun x : ℝ => suzukiCanonicalHankelContourIntegrandNF omega g r
      ((x : ℂ) + (sigma : ℂ) * Complex.I)) =ᵐ[volume]
    fun x : ℝ => suzukiCanonicalHankelContourIntegrand omega g r
      ((x : ℂ) + (sigma : ℂ) * Complex.I) := by
  filter_upwards [suzukiCanonicalThetaNF_horizontal_ae_eq omega sigma] with x hx
  rw [suzukiCanonicalHankelContourIntegrandNF,
    suzukiCanonicalHankelContourIntegrand, hx]

theorem suzukiCanonicalHankelContourIntegrandNF_vertical_ae_eq
    (omega x : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    (fun y : ℝ => suzukiCanonicalHankelContourIntegrandNF omega g r
      ((x : ℂ) + (y : ℂ) * Complex.I)) =ᵐ[volume]
    fun y : ℝ => suzukiCanonicalHankelContourIntegrand omega g r
      ((x : ℂ) + (y : ℂ) * Complex.I) := by
  filter_upwards [suzukiCanonicalThetaNF_vertical_ae_eq omega x] with y hy
  rw [suzukiCanonicalHankelContourIntegrandNF,
    suzukiCanonicalHankelContourIntegrand, hy]

theorem meromorphicAt_suzukiCanonicalHankelContourIntegrandNF
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) (z : ℂ) :
    MeromorphicAt (suzukiCanonicalHankelContourIntegrandNF omega g r) z := by
  rw [show suzukiCanonicalHankelContourIntegrandNF omega g r = fun w : ℂ =>
      suzukiCanonicalThetaNF omega w *
        deningerMeyerStrongLogMellin g (-Complex.I * w) *
        Complex.exp (-Complex.I * w * (r : ℂ)) by rfl]
  have htheta := meromorphicOn_suzukiCanonicalThetaNF omega z (Set.mem_univ z)
  have hM : AnalyticAt ℂ
      (fun w : ℂ => deningerMeyerStrongLogMellin g (-Complex.I * w)) z :=
    ((differentiable_deningerMeyerStrongLogMellin g.property).analyticAt
      (-Complex.I * z)).comp (by fun_prop)
  have hexp : AnalyticAt ℂ
      (fun w : ℂ => Complex.exp (-Complex.I * w * (r : ℂ))) z := by fun_prop
  exact (htheta.mul hM.meromorphicAt).mul hexp.meromorphicAt

theorem meromorphicAt_suzukiCanonicalHankelContourIntegrand
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) (z : ℂ) :
    MeromorphicAt (suzukiCanonicalHankelContourIntegrand omega g r) z := by
  rw [show suzukiCanonicalHankelContourIntegrand omega g r = fun w : ℂ =>
      suzukiCanonicalTheta omega w *
        deningerMeyerStrongLogMellin g (-Complex.I * w) *
        Complex.exp (-Complex.I * w * (r : ℂ)) by rfl]
  have htheta := meromorphicOn_suzukiCanonicalTheta omega z (Set.mem_univ z)
  have hM : AnalyticAt ℂ
      (fun w : ℂ => deningerMeyerStrongLogMellin g (-Complex.I * w)) z :=
    ((differentiable_deningerMeyerStrongLogMellin g.property).analyticAt
      (-Complex.I * z)).comp (by fun_prop)
  have hexp : AnalyticAt ℂ
      (fun w : ℂ => Complex.exp (-Complex.I * w * (r : ℂ))) z := by fun_prop
  exact (htheta.mul hM.meromorphicAt).mul hexp.meromorphicAt

theorem suzukiCanonicalHankelContourIntegrandNF_eventuallyEq_nhdsNE
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) (z : ℂ) :
    suzukiCanonicalHankelContourIntegrandNF omega g r =ᶠ[𝓝[≠] z]
      suzukiCanonicalHankelContourIntegrand omega g r := by
  have htheta := (meromorphicOn_suzukiCanonicalTheta omega).toMeromorphicNFOn_eq_self_on_nhdsNE
    (Set.mem_univ z)
  filter_upwards [htheta] with w hw
  rw [suzukiCanonicalHankelContourIntegrandNF,
    suzukiCanonicalHankelContourIntegrand, suzukiCanonicalThetaNF, hw]

theorem laurentCoeff_suzukiCanonicalHankelContourIntegrandNF_eq
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) (z : ℂ) (ell : ℤ) :
    GaloisForLFunctions.HTGeometry.laurentCoeff
        (suzukiCanonicalHankelContourIntegrandNF omega g r) z ell =
      GaloisForLFunctions.HTGeometry.laurentCoeff
        (suzukiCanonicalHankelContourIntegrand omega g r) z ell := by
  exact GaloisForLFunctions.HTGeometry.laurentCoeff_congr
    (meromorphicAt_suzukiCanonicalHankelContourIntegrandNF omega g r z)
    (suzukiCanonicalHankelContourIntegrandNF_eventuallyEq_nhdsNE omega g r z) ell

theorem analyticAt_suzukiCanonicalHankelContourIntegrandNF_of_theta
    {omega : ℝ} (g : DeningerMeyerStrongLogTarget) (r : ℝ) {z : ℂ}
    (htheta : AnalyticAt ℂ (suzukiCanonicalThetaNF omega) z) :
    AnalyticAt ℂ (suzukiCanonicalHankelContourIntegrandNF omega g r) z := by
  rw [show suzukiCanonicalHankelContourIntegrandNF omega g r = fun w : ℂ =>
      suzukiCanonicalThetaNF omega w *
        deningerMeyerStrongLogMellin g (-Complex.I * w) *
        Complex.exp (-Complex.I * w * (r : ℂ)) by rfl]
  have hM : AnalyticAt ℂ
      (fun w : ℂ => deningerMeyerStrongLogMellin g (-Complex.I * w)) z :=
    ((differentiable_deningerMeyerStrongLogMellin g.property).analyticAt
      (-Complex.I * z)).comp (by fun_prop)
  exact (htheta.mul hM).mul (by fun_prop)

/-- Source-faithful meaning of “finitely many uncancelled upper-half-plane poles” in the
nontrivial range `0 < omega < 1/2`: `P` is exactly a finite pole set in `0 < Im z < 1`, and the
canonical canceled quotient is analytic everywhere else in the closed transport strip. -/
def SuzukiCanonicalFiniteUpperPoleDivisor (omega : ℝ) (P : Finset ℂ) : Prop :=
  (∀ p ∈ P, 0 < p.im ∧ p.im < 1 ∧
    meromorphicOrderAt (suzukiCanonicalThetaNF omega) p < 0) ∧
  ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → z ∉ P →
    AnalyticAt ℂ (suzukiCanonicalThetaNF omega) z

theorem integrable_suzukiCanonicalHankelContourIntegrandNF_real
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    Integrable fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrandNF omega g r (x : ℂ) := by
  have hae : (fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrandNF omega g r (x : ℂ)) =ᵐ[volume]
      fun x : ℝ => suzukiCanonicalHankelContourIntegrand omega g r (x : ℂ) := by
    simpa using
      suzukiCanonicalHankelContourIntegrandNF_horizontal_ae_eq omega 0 g r
  exact (integrable_suzukiCanonicalHankelContourIntegrand_real omega g r).congr hae.symm

theorem integrable_suzukiCanonicalHankelContourIntegrandNF_horizontal_one
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2)
    (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    Integrable fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrandNF omega g r
        ((x : ℂ) + Complex.I) := by
  have hae : (fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrandNF omega g r
        ((x : ℂ) + Complex.I)) =ᵐ[volume]
      fun x : ℝ => suzukiCanonicalHankelContourIntegrand omega g r
        ((x : ℂ) + Complex.I) := by
    simpa using
      suzukiCanonicalHankelContourIntegrandNF_horizontal_ae_eq omega 1 g r
  exact (integrable_suzukiCanonicalHankelContourIntegrand_horizontal_one
    homega0 homegaHalf g r).congr hae.symm

theorem vIntegral_suzukiCanonicalHankelContourIntegrandNF_eq
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r x c d : ℝ) :
    VIntegral (suzukiCanonicalHankelContourIntegrandNF omega g r) x c d =
      VIntegral (suzukiCanonicalHankelContourIntegrand omega g r) x c d := by
  rw [VIntegral]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [suzukiCanonicalHankelContourIntegrandNF_vertical_ae_eq
    omega x g r] with y hy _
  exact hy

/-- Complete finite-pole transport for Suzuki's exact shifted-Xi test pairing. The theorem is
closed and unconditional: its sole implication antecedent is exactly the card's finite
uncancelled-pole condition, encoded by `SuzukiCanonicalFiniteUpperPoleDivisor`; no growth,
innerness, RH, simplicity, or extra contour premise occurs. -/
theorem horizontalIntegral_normalized_sub_eq_I_mul_sum_laurentCoeff_suzukiCanonical_of_finite
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2) :
    ∀ P : Finset ℂ, SuzukiCanonicalFiniteUpperPoleDivisor omega P →
      ∀ (g : DeningerMeyerStrongLogTarget) (r : ℝ),
      (1 / (2 * (Real.pi : ℂ))) *
          (∫ x : ℝ, suzukiCanonicalHankelContourIntegrand omega g r (x : ℂ)) -
        (1 / (2 * (Real.pi : ℂ))) *
          (∫ x : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
            ((x : ℂ) + Complex.I)) =
        Complex.I * ∑ p ∈ P,
          GaloisForLFunctions.HTGeometry.laurentCoeff
            (suzukiCanonicalHankelContourIntegrand omega g r) p (-1) := by
  intro P hP g r
  let f := suzukiCanonicalHankelContourIntegrandNF omega g r
  have hPim : ∀ p ∈ P, (0 : ℝ) < p.im ∧ p.im < 1 := by
    intro p hp
    exact ⟨(hP.1 p hp).1, (hP.1 p hp).2.1⟩
  have hmero : ∀ p ∈ P, MeromorphicAt f p := by
    intro p _
    exact meromorphicAt_suzukiCanonicalHankelContourIntegrandNF omega g r p
  have hoff : ∀ z : ℂ, (0 : ℝ) ≤ z.im → z.im ≤ 1 → z ∉ P →
      AnalyticAt ℂ f z := by
    intro z hz0 hz1 hzP
    exact analyticAt_suzukiCanonicalHankelContourIntegrandNF_of_theta g r
      (hP.2 z hz0 hz1 hzP)
  have hc : Integrable fun x : ℝ => f ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by
    simpa [f] using integrable_suzukiCanonicalHankelContourIntegrandNF_real omega g r
  have hd : Integrable fun x : ℝ => f ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) := by
    simpa [f] using
      integrable_suzukiCanonicalHankelContourIntegrandNF_horizontal_one
        homega0 homegaHalf g r
  obtain ⟨T, hT, hrightRaw, hleftRaw⟩ :=
    exists_suzukiCanonicalHankelContour_vertical_tendsto_zero homega0 homegaHalf g r
  have hright : Tendsto (fun n => VIntegral f (T n) 0 1) atTop (nhds 0) := by
    apply hrightRaw.congr'
    filter_upwards with n
    exact (vIntegral_suzukiCanonicalHankelContourIntegrandNF_eq
      omega g r (T n) 0 1).symm
  have hleft : Tendsto (fun n => VIntegral f (-(T n)) 0 1) atTop (nhds 0) := by
    apply hleftRaw.congr'
    filter_upwards with n
    exact (vIntegral_suzukiCanonicalHankelContourIntegrandNF_eq
      omega g r (-(T n)) 0 1).symm
  have htransport :=
    GaloisForLFunctions.HTGeometry.horizontalIntegral_normalized_sub_eq_I_mul_sum_laurentCoeff_of_vertical_tendsto_seq
        (f := f) (c := 0) (d := 1) (by norm_num) hPim hmero hoff hc hd hT hright hleft
  have hbot :
      (∫ x : ℝ, f ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ, suzukiCanonicalHankelContourIntegrand omega g r (x : ℂ) := by
    apply MeasureTheory.integral_congr_ae
    simpa [f] using
      suzukiCanonicalHankelContourIntegrandNF_horizontal_ae_eq omega 0 g r
  have htop :
      (∫ x : ℝ, f ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
          ((x : ℂ) + Complex.I) := by
    apply MeasureTheory.integral_congr_ae
    simpa [f] using
      suzukiCanonicalHankelContourIntegrandNF_horizontal_ae_eq omega 1 g r
  have hres : (∑ p ∈ P,
      GaloisForLFunctions.HTGeometry.laurentCoeff f p (-1)) =
      ∑ p ∈ P, GaloisForLFunctions.HTGeometry.laurentCoeff
        (suzukiCanonicalHankelContourIntegrand omega g r) p (-1) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact laurentCoeff_suzukiCanonicalHankelContourIntegrandNF_eq omega g r p (-1)
  rw [hbot, htop, hres] at htransport
  exact htransport

end

end RHTower
