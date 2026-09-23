import GaloisForLFunctions.RHTower.XiMassFourierBesselIdentity
import GaloisForLFunctions.HTGeometry.MassBesselDeepTimeCarrier

/-!
# The mass Fourier--Bessel identity on the full right half-plane

For a positive real part of the vertical spectral parameter, the propagation argument
`τ² + h²` either has positive real part (on the real-time slice) or nonzero imaginary part.
Thus it never reaches the square-root cut.  The principal root and the Bessel side are
holomorphic on the whole right half-plane, so the real-time Fourier--Bessel identity extends
there by the identity theorem.  This attaches the previously abstract deep-time Bessel carrier
to the literal mass Fourier transform.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The full holomorphy domain for the mass Fourier--Bessel transform. -/
def xiMassBesselRightHalfPlane : Set ℂ := {τ : ℂ | 0 < τ.re}

theorem convex_xiMassBesselRightHalfPlane : Convex ℝ xiMassBesselRightHalfPlane :=
  convex_halfSpace_re_gt 0

theorem isOpen_xiMassBesselRightHalfPlane : IsOpen xiMassBesselRightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem xiMassPropagation_im (h : ℝ) (τ : ℂ) :
    (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)).im = 2 * τ.re * τ.im := by
  simp [pow_two, Complex.add_im, Complex.mul_im]
  ring

/-- A right-half-plane spectral parameter never maps to the square-root cut. -/
theorem xiMassPropagation_re_pos_or_im_ne_zero {h : ℝ} {τ : ℂ}
    (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    0 < (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)).re ∨ (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)).im ≠ 0 := by
  by_cases him : τ.im = 0
  · left
    have hval : (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)).re = τ.re ^ (2 : ℕ) - τ.im ^ (2 : ℕ) + h ^ (2 : ℕ) := by
      simp [pow_two, Complex.add_re, Complex.mul_re]
    rw [hval, him]
    change 0 < τ.re at hτ
    nlinarith [sq_pos_of_pos hτ]
  · right
    rw [xiMassPropagation_im]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hτ)) him

theorem xiMassPropagationRoot_re_pos {h : ℝ} {τ : ℂ}
    (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    0 < (HTGeometry.csqrt (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))).re := by
  rcases xiMassPropagation_re_pos_or_im_ne_zero hτ with hre | him
  · rw [HTGeometry.csqrt_re]
    exact HTGeometry.csqrtRe_pos hre
  · exact HTGeometry.csqrt_re_pos_of_im_ne_zero him

theorem xiMassPropagationRoot_ne_zero {h : ℝ} {τ : ℂ}
    (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    HTGeometry.csqrt (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)) ≠ 0 := by
  intro hzero
  have hre := xiMassPropagationRoot_re_pos (h := h) hτ
  rw [hzero] at hre
  simp at hre

theorem differentiableAt_xiMassPropagationRoot {h : ℝ} {τ : ℂ}
    (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    DifferentiableAt ℂ (fun z : ℂ => HTGeometry.csqrt (z ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))) τ := by
  have hpoly : DifferentiableAt ℂ (fun z : ℂ => z ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)) τ := by fun_prop
  rcases xiMassPropagation_re_pos_or_im_ne_zero (h := h) hτ with hre | him
  · exact (HTGeometry.differentiableAt_csqrt hre).comp τ hpoly
  · exact (HTGeometry.differentiableAt_csqrt_of_im_ne_zero him).comp τ hpoly

theorem re_mul_xiMassPropagationRoot_pos {a h : ℝ} {τ : ℂ} (ha : 0 < a)
    (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    0 < ((a : ℂ) * HTGeometry.csqrt (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))).re :=
  HTGeometry.re_ofReal_mul_pos ha (xiMassPropagationRoot_re_pos hτ)

theorem differentiableAt_xiMassBesselSide_rightHalfPlane {a h : ℝ} {τ : ℂ} (ha : 0 < a)
    (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    DifferentiableAt ℂ (xiMassBesselSide a h) τ := by
  have hroot := differentiableAt_xiMassPropagationRoot (h := h) hτ
  have hrootne := xiMassPropagationRoot_ne_zero (h := h) hτ
  have hnum : DifferentiableAt ℂ (fun z : ℂ => 2 * (a : ℂ) * z) τ := by fun_prop
  have hinner : DifferentiableAt ℂ
      (fun z : ℂ => (a : ℂ) * HTGeometry.csqrt (z ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))) τ :=
    hroot.const_mul _
  have hbes : DifferentiableAt ℂ
      (fun z : ℂ => HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt
        (z ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ)))) τ := by
    have hcomp : DifferentiableAt ℂ
        (HTGeometry.besselK1C ∘ fun z : ℂ => (a : ℂ) * HTGeometry.csqrt
          (z ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))) τ :=
      (HTGeometry.differentiableAt_besselK1C
        (re_mul_xiMassPropagationRoot_pos (h := h) ha hτ)).comp τ hinner
    exact hcomp
  exact (hnum.div hroot hrootne).mul hbes

/-- The real-time Fourier--Bessel formula analytically continues across every timelike ray. -/
theorem xiMassProfileC_eq_besselSide_rightHalfPlane {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    Set.EqOn (xiMassProfileC a h) (xiMassBesselSide a h) xiMassBesselRightHalfPlane := by
  have hopen : IsOpen xiMassBesselRightHalfPlane := isOpen_xiMassBesselRightHalfPlane
  have hconn : IsPreconnected xiMassBesselRightHalfPlane :=
    convex_xiMassBesselRightHalfPlane.isPreconnected
  have hone : (1 : ℂ) ∈ xiMassBesselRightHalfPlane := by norm_num [xiMassBesselRightHalfPlane]
  have hL : DifferentiableOn ℂ (xiMassProfileC a h) xiMassBesselRightHalfPlane := by
    intro z hz
    exact (hasDerivAt_xiMassProfileC ha hz).differentiableAt.differentiableWithinAt
  have hR : DifferentiableOn ℂ (xiMassBesselSide a h) xiMassBesselRightHalfPlane := by
    intro z hz
    exact (differentiableAt_xiMassBesselSide_rightHalfPlane ha hz).differentiableWithinAt
  have hLa : AnalyticOnNhd ℂ (xiMassProfileC a h) xiMassBesselRightHalfPlane :=
    DifferentiableOn.analyticOnNhd hL hopen
  have hRa : AnalyticOnNhd ℂ (xiMassBesselSide a h) xiMassBesselRightHalfPlane :=
    DifferentiableOn.analyticOnNhd hR hopen
  have htendR : Filter.Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) Filter.atTop
      (nhds 1) := by
    have hzero : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using Filter.Tendsto.const_add (1 : ℝ) hzero
  have htend : Filter.Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      Filter.atTop (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhds (1 : ℝ)) (nhds ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt
      have hcomp := hcont.comp htendR
      simp only [Function.comp_def, Complex.ofReal_one] at hcomp
      exact hcomp
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      have hreal : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by
        exact_mod_cast congrArg Complex.re hcontra
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreqAt : ∀ n : ℕ,
      xiMassProfileC a h ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
        = xiMassBesselSide a h ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
    intro n
    refine xiMassProfileC_eq_besselSide_real ha hh.le ?_
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
      xiMassProfileC a h z = xiMassBesselSide a h z :=
    htend.frequently ((Filter.Eventually.of_forall hfreqAt).frequently)
  exact hLa.eqOn_of_preconnected_of_frequently_eq hRa hconn hone hfreq

theorem stripFourier_xiMass_eq_bessel_rightHalfPlane {a h : ℝ} {τ : ℂ} (ha : 0 < a)
    (hh : 0 < h) (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    stripFourier (xiMassAnalyticTest a τ) (h : ℂ) =
      2 * (a : ℂ) * τ / HTGeometry.csqrt (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))
        * HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (τ ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ))) := by
  rw [← xiMassProfileC_eq_stripFourier ha hτ]
  exact xiMassProfileC_eq_besselSide_rightHalfPlane ha hh hτ

/-- The literal Fourier transform equals the deep-time mass-Bessel carrier. -/
theorem stripFourier_xiMass_eq_massBesselCarrier {a h : ℝ} {τ : ℂ} (ha : 0 < a)
    (hh : 0 < h) (hτ : τ ∈ xiMassBesselRightHalfPlane) :
    stripFourier (xiMassAnalyticTest a τ) (h : ℂ) = HTGeometry.massBesselCarrier a τ h := by
  rw [stripFourier_xiMass_eq_bessel_rightHalfPlane ha hh hτ,
    HTGeometry.massBesselCarrier, HTGeometry.massBesselRoot]
  ring

end

end RHTower
