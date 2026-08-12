import GaloisForLFunctions.RHTower.CCMArchimedeanPhaseTraceFormula
import GaloisForLFunctions.RHTower.CCMArchimedeanWeilDistribution
import GaloisForLFunctions.RHTower.CCMArchimedeanMellinTransport
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries
import GaloisForLFunctions.HTGeometry.SchwartzPolynomialDifferentialFrame
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Exact CCM archimedean phase--Weil bridge

This module proves the normalization-sensitive Gamma/digamma transform omitted in the
formal diagonal argument of Connes--Consani Proposition 7(iv). Finite Gauss sums are paired
with exact Fourier resolvents before taking limits, preserving the zero-germ cancellation at
the singular point. The resulting time kernel differs from the explicit Weil finite part by
the integrable logistic correction of mass `2 * log 2`, producing the exact `log (4 * pi)`
constant. Spectral and geometric operator traces are then identified with that distribution.

All endpoint theorems are unconditional on the intrinsic compact-Schwartz test space.
-/


open Complex Filter MeasureTheory Set
open scoped BigOperators FourierTransform SchwartzMap

noncomputable section
namespace RHTower

theorem ccm_fourierInv_fourier_apply (H : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ ξ : ℝ,
      Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) *
        (𝓕 (H : ℝ → ℂ)) ξ) = H x := by
  have hFourier : Integrable (𝓕 (H : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable)
  have hinv :
      𝓕⁻ (𝓕 (H : ℝ → ℂ)) x = H x :=
    H.integrable.fourierInv_fourier_eq hFourier H.continuous.continuousAt
  rw [Real.fourierInv_eq'] at hinv
  simpa only [RCLike.inner_apply, conj_trivial, ofReal_mul,
    Complex.real_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hinv

theorem ccm_integral_fourier_mul_verticalResolvent
    (H : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) :
    (∫ ξ : ℝ,
        (𝓕 (H : ℝ → ℂ)) ξ *
          (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) =
      ∫ t : ℝ in Ioi 0,
        Complex.exp (-(c : ℂ) * (t : ℂ)) * H (t / 2) := by
  let F : ℝ → ℂ := fun ξ => (𝓕 (H : ℝ → ℂ)) ξ
  let e : ℝ → ℂ := (Ioi (0 : ℝ)).indicator
    (fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ)))
  let K : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (((Real.pi * p.2 * p.1 : ℝ) : ℂ) * I) *
      (e p.1 * F p.2)
  have he : Integrable e := by
    dsimp only [e]
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_exp_mul_complex_Ioi
      (a := -(c : ℂ)) (by simp only [Complex.neg_re, Complex.ofReal_re]; linarith) 0
  have hF : Integrable F := by
    dsimp only [F]
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable)
  have hbase : Integrable (fun p : ℝ × ℝ => e p.1 * F p.2) :=
    he.mul_prod hF
  have hK : Integrable K := by
    dsimp only [K]
    refine hbase.norm.mono' ?_ ?_
    · exact
        (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
          hbase.aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul, Complex.norm_exp]
      have hre : ((((Real.pi * p.2 * p.1 : ℝ) : ℂ) * I)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero, one_mul]
  have hresolvent : ∀ ξ : ℝ,
      (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ =
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-(c : ℂ) * (t : ℂ)) *
            Complex.exp (((Real.pi * ξ * t : ℝ) : ℂ) * I) := by
    intro ξ
    let q : ℂ := -(((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)
    have hq : q.re < 0 := by
      dsimp only [q]
      simp [Complex.mul_re]
      exact hc
    have hfun : (fun t : ℝ =>
        Complex.exp (-(c : ℂ) * (t : ℂ)) *
          Complex.exp (((Real.pi * ξ * t : ℝ) : ℂ) * I)) =
        fun t : ℝ => Complex.exp (q * (t : ℂ)) := by
      funext t
      rw [← Complex.exp_add]
      congr 1
      dsimp only [q]
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex_Ioi hq 0]
    simp only [ofReal_zero, mul_zero, exp_zero]
    dsimp only [q]
    rw [show -(((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I) =
        -1 * (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I) by ring]
    field_simp
  change (∫ ξ : ℝ, F ξ *
      (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) = _
  simp_rw [hresolvent]
  calc
    (∫ ξ : ℝ, F ξ *
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-(c : ℂ) * (t : ℂ)) *
            Complex.exp (((Real.pi * ξ * t : ℝ) : ℂ) * I)) =
        ∫ ξ : ℝ, ∫ t : ℝ, K (t, ξ) := by
      congr with ξ
      rw [← integral_indicator measurableSet_Ioi]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp only [K, e, Set.indicator_of_mem ht]
        ring
      · simp [K, e, ht]
    _ = ∫ t : ℝ, ∫ ξ : ℝ, K (t, ξ) := by
      apply integral_integral_swap
      change Integrable (K ∘ Prod.swap) (volume.prod volume)
      exact hK.swap
    _ = ∫ t : ℝ in Ioi 0,
        Complex.exp (-(c : ℂ) * (t : ℂ)) * H (t / 2) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem ht]
        rw [show (fun ξ : ℝ => K (t, ξ)) = fun ξ : ℝ =>
            Complex.exp (-(c : ℂ) * (t : ℂ)) *
              (Complex.exp ((((2 * Real.pi * ξ * (t / 2) : ℝ) : ℂ)) * I) *
                (𝓕 (H : ℝ → ℂ)) ξ) by
          funext ξ
          dsimp only [K, F]
          rw [show e t = Complex.exp (-(c : ℂ) * (t : ℂ)) by
            simp [e, ht]]
          push_cast
          ring]
        rw [integral_const_mul, ccm_fourierInv_fourier_apply H (t / 2)]
      · rw [Set.indicator_of_notMem ht]
        have he0 : e t = 0 := Set.indicator_of_notMem ht _
        simp [K, he0]

theorem ccm_fourier_reflectedSchwartz
    (H : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (SchwartzMap.reflectedSchwartz H : ℝ → ℂ)) ξ =
      (𝓕 (H : ℝ → ℂ)) (-ξ) := by
  change 𝓕 (SchwartzMap.reflectedSchwartz H) ξ = 𝓕 H (-ξ)
  exact Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) H ξ

theorem ccm_integral_fourier_mul_negativeVerticalResolvent
    (H : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) :
    (∫ ξ : ℝ,
        (𝓕 (H : ℝ → ℂ)) ξ *
          (((c : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) =
      ∫ t : ℝ in Ioi 0,
        Complex.exp (-(c : ℂ) * (t : ℂ)) * H (-(t / 2)) := by
  have h := ccm_integral_fourier_mul_verticalResolvent
    (SchwartzMap.reflectedSchwartz H) hc
  have hleft :
      (∫ ξ : ℝ,
          (𝓕 (H : ℝ → ℂ)) ξ *
            (((c : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) =
        ∫ ξ : ℝ,
          (𝓕 (SchwartzMap.reflectedSchwartz H : ℝ → ℂ)) ξ *
            (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ := by
    rw [← MeasureTheory.integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [ccm_fourier_reflectedSchwartz]
    congr 2
    push_cast
    ring
  rw [hleft, h]
  apply integral_congr_ae
  filter_upwards with t
  rw [SchwartzMap.reflectedSchwartz_apply]

theorem ccm_integrable_fourier_mul_verticalResolvent
    (H : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ *
        (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) := by
  let F : ℝ → ℂ := fun ξ => (𝓕 (H : ℝ → ℂ)) ξ
  let d : ℝ → ℂ := fun ξ =>
    ((c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹
  have hF : Integrable F := by
    dsimp only [F]
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable)
  have hdenne : ∀ ξ : ℝ,
      (c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I ≠ 0 := by
    intro ξ h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re] at hre
    linarith
  have hdcont : Continuous d := by
    dsimp only [d]
    exact (by fun_prop : Continuous (fun ξ : ℝ =>
      (c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)).inv₀ hdenne
  have hdbound : ∀ ξ : ℝ, ‖d ξ‖ ≤ 1 / c := by
    intro ξ
    have hre : c ≤ ‖(c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I‖ := by
      have h := Complex.re_le_norm
        ((c : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)
      simpa [Complex.mul_re] using h
    dsimp only [d]
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hc hre
  simpa only [F, d] using
    hF.mul_bdd hdcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdbound)

theorem ccm_integrable_fourier_mul_negativeVerticalResolvent
    (H : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ *
        (((c : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) := by
  let d : ℝ → ℂ := fun ξ =>
    ((c : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹
  have hF : Integrable (fun ξ : ℝ => (𝓕 (H : ℝ → ℂ)) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable)
  have hdenne : ∀ ξ : ℝ,
      (c : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I ≠ 0 := by
    intro ξ h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re] at hre
    linarith
  have hdcont : Continuous d := by
    dsimp only [d]
    exact (by fun_prop : Continuous (fun ξ : ℝ =>
      (c : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)).inv₀ hdenne
  have hdbound : ∀ ξ : ℝ, ‖d ξ‖ ≤ 1 / c := by
    intro ξ
    have hre : c ≤ ‖(c : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I‖ := by
      have h := Complex.re_le_norm
        ((c : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)
      simpa [Complex.mul_re] using h
    dsimp only [d]
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hc hre
  simpa only [d] using
    hF.mul_bdd hdcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdbound)

def ccmQuarterPiDigammaPoint (ξ : ℝ) : ℂ :=
  ((1 / 4 : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I

@[simp] theorem ccmQuarterPiDigammaPoint_re (ξ : ℝ) :
    (ccmQuarterPiDigammaPoint ξ).re = 1 / 4 := by
  simp [ccmQuarterPiDigammaPoint, Complex.mul_re]

theorem ccm_re_gaussDigammaSeriesTerm_eq_resolvent_pair
    (ξ : ℝ) (n : ℕ) :
    ((gaussDigammaSeriesTerm (ccmQuarterPiDigammaPoint ξ) n).re : ℂ) =
      1 / ((n : ℂ) + 1) -
        (1 / 2 : ℂ) *
          ((((n : ℝ) + 1 / 4 : ℝ) : ℂ) +
              ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ -
        (1 / 2 : ℂ) *
          ((((n : ℝ) + 1 / 4 : ℝ) : ℂ) -
              ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ := by
  let z := gaussDigammaSeriesTerm (ccmQuarterPiDigammaPoint ξ) n
  calc
    ((z.re : ℝ) : ℂ) = (z + (starRingEnd ℂ) z) / 2 := by
      apply Complex.ext <;> simp
    _ = _ := by
      dsimp only [z]
      unfold gaussDigammaSeriesTerm ccmQuarterPiDigammaPoint
      simp only [map_sub, map_div₀, map_one, map_add, map_natCast,
        map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring

theorem ccm_integral_fourier_mul_re_gaussDigammaSeriesTerm
    (H : 𝓢(ℝ, ℂ)) (n : ℕ) :
    (∫ ξ : ℝ,
        (𝓕 (H : ℝ → ℂ)) ξ *
          ((gaussDigammaSeriesTerm
            (ccmQuarterPiDigammaPoint ξ) n).re : ℂ)) =
      H 0 / ((n : ℂ) + 1) -
        ∫ h : ℝ in Ioi 0,
          Complex.exp
              (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) *
            (H h + H (-h)) := by
  let c : ℝ := (n : ℝ) + 1 / 4
  have hc : 0 < c := by dsimp only [c]; positivity
  have hF : Integrable (fun ξ : ℝ => (𝓕 (H : ℝ → ℂ)) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable)
  have hplus := ccm_integrable_fourier_mul_negativeVerticalResolvent H hc
  have hminus := ccm_integrable_fourier_mul_verticalResolvent H hc
  have hconst : Integrable (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ * (1 / ((n : ℂ) + 1))) := hF.mul_const _
  simp_rw [ccm_re_gaussDigammaSeriesTerm_eq_resolvent_pair]
  have hfun : (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ *
        (1 / ((n : ℂ) + 1) -
          (1 / 2 : ℂ) *
            ((((n : ℝ) + 1 / 4 : ℝ) : ℂ) +
              ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹ -
          (1 / 2 : ℂ) *
            ((((n : ℝ) + 1 / 4 : ℝ) : ℂ) -
              ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹)) =
      fun ξ : ℝ =>
        (𝓕 (H : ℝ → ℂ)) ξ * (1 / ((n : ℂ) + 1)) -
          (1 / 2 : ℂ) *
            ((𝓕 (H : ℝ → ℂ)) ξ *
              (((c : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) -
          (1 / 2 : ℂ) *
            ((𝓕 (H : ℝ → ℂ)) ξ *
              (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹) := by
    funext ξ
    dsimp only [c]
    ring
  rw [hfun]
  let A : ℝ → ℂ := fun ξ =>
    (𝓕 (H : ℝ → ℂ)) ξ * (1 / ((n : ℂ) + 1))
  let B : ℝ → ℂ := fun ξ => (1 / 2 : ℂ) *
    ((𝓕 (H : ℝ → ℂ)) ξ *
      (((c : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹)
  let C : ℝ → ℂ := fun ξ => (1 / 2 : ℂ) *
    ((𝓕 (H : ℝ → ℂ)) ξ *
      (((c : ℝ) : ℂ) - ((Real.pi * ξ : ℝ) : ℂ) * I)⁻¹)
  change (∫ ξ : ℝ, (A - B - C) ξ) = _
  have hA : Integrable A := by simpa only [A] using hconst
  have hB : Integrable B := by simpa only [B] using hplus.const_mul (1 / 2 : ℂ)
  have hC : Integrable C := by simpa only [C] using hminus.const_mul (1 / 2 : ℂ)
  have hzero : (∫ ξ : ℝ, (𝓕 (H : ℝ → ℂ)) ξ) = H 0 := by
    simpa only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
      zero_div] using ccm_fourierInv_fourier_apply H 0
  simp only [Pi.sub_apply]
  rw [integral_sub (f := fun ξ => A ξ - B ξ) (g := C) (hA.sub hB) hC,
    integral_sub (f := A) (g := B) hA hB]
  dsimp only [A, B, C]
  rw [integral_mul_const, integral_const_mul, integral_const_mul,
    hzero,
    ccm_integral_fourier_mul_negativeVerticalResolvent H hc,
    ccm_integral_fourier_mul_verticalResolvent H hc]
  let Qplus : ℝ → ℂ := fun h =>
    Complex.exp (-((2 * c : ℝ) : ℂ) * (h : ℂ)) * H h
  let Qminus : ℝ → ℂ := fun h =>
    Complex.exp (-((2 * c : ℝ) : ℂ) * (h : ℂ)) * H (-h)
  have hscalePlus := MeasureTheory.integral_comp_mul_left_Ioi
    Qplus 0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hscaleMinus := MeasureTheory.integral_comp_mul_left_Ioi
    Qminus 0 (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num at hscalePlus hscaleMinus
  have hQplusComp : (fun t : ℝ => Qplus (1 / 2 * t)) =
      fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ)) * H (t / 2) := by
    funext t
    dsimp only [Qplus]
    congr 2 <;> push_cast <;> ring
  have hQminusComp : (fun t : ℝ => Qminus (1 / 2 * t)) =
      fun t : ℝ => Complex.exp (-(c : ℂ) * (t : ℂ)) * H (-(t / 2)) := by
    funext t
    dsimp only [Qminus]
    congr 2
    · push_cast
      ring
    · congr 1
      ring
  have hplusScale :
      (∫ t : ℝ in Ioi 0,
          Complex.exp (-(c : ℂ) * (t : ℂ)) * H (t / 2)) =
        2 * ∫ h : ℝ in Ioi 0, Qplus h := by
    rw [← hQplusComp]
    exact hscalePlus
  have hminusScale :
      (∫ t : ℝ in Ioi 0,
          Complex.exp (-(c : ℂ) * (t : ℂ)) * H (-(t / 2))) =
        2 * ∫ h : ℝ in Ioi 0, Qminus h := by
    rw [← hQminusComp]
    exact hscaleMinus
  rw [hplusScale, hminusScale]
  have hQplus : IntegrableOn Qplus (Ioi 0) := by
    have hbounded : ∀ᵐ h : ℝ ∂volume.restrict (Ioi 0),
        ‖Complex.exp (-((2 * c : ℝ) : ℂ) * (h : ℂ))‖ ≤ 1 := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      have hpos : 0 < 2 * c * h := mul_pos (mul_pos (by norm_num) hc) hh
      linarith
    have hraw := H.integrable.integrableOn.mul_bdd
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.restrict hbounded
    exact hraw.congr (Filter.Eventually.of_forall fun h => by
      dsimp only [Qplus, Function.comp_apply]
      ring)
  have hQminus : IntegrableOn Qminus (Ioi 0) := by
    have hreflect : Integrable (fun h : ℝ => H (-h)) := H.integrable.comp_neg
    have hbounded : ∀ᵐ h : ℝ ∂volume.restrict (Ioi 0),
        ‖Complex.exp (-((2 * c : ℝ) : ℂ) * (h : ℂ))‖ ≤ 1 := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      have hpos : 0 < 2 * c * h := mul_pos (mul_pos (by norm_num) hc) hh
      linarith
    have hraw := hreflect.integrableOn.mul_bdd
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.restrict hbounded
    exact hraw.congr (Filter.Eventually.of_forall fun h => by
      dsimp only [Qminus, Function.comp_apply]
      ring)
  have htarget :
      (∫ h : ℝ in Ioi 0,
          Complex.exp
              (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) *
            (H h + H (-h))) =
        (∫ h : ℝ in Ioi 0, Qminus h) +
          ∫ h : ℝ in Ioi 0, Qplus h := by
    rw [← integral_add hQminus hQplus]
    apply integral_congr_ae
    filter_upwards with h
    dsimp only [Qplus, Qminus, c]
    ring
  rw [htarget]
  ring

theorem ccm_integrable_fourier_mul_re_gaussDigammaSeriesTerm
    (H : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Integrable (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ *
        ((gaussDigammaSeriesTerm
          (ccmQuarterPiDigammaPoint ξ) n).re : ℂ)) := by
  let c : ℝ := (n : ℝ) + 1 / 4
  have hc : 0 < c := by dsimp only [c]; positivity
  have hF : Integrable (fun ξ : ℝ => (𝓕 (H : ℝ → ℂ)) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable)
  have hconst : Integrable (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ * (1 / ((n : ℂ) + 1))) := hF.mul_const _
  have hplus :=
    (ccm_integrable_fourier_mul_negativeVerticalResolvent H hc).const_mul
      (1 / 2 : ℂ)
  have hminus :=
    (ccm_integrable_fourier_mul_verticalResolvent H hc).const_mul
      (1 / 2 : ℂ)
  apply ((hconst.sub hplus).sub hminus).congr
  filter_upwards with ξ
  simp only [Pi.sub_apply]
  rw [ccm_re_gaussDigammaSeriesTerm_eq_resolvent_pair]
  dsimp only [c]
  ring

def ccmQuarterGaussPartialIntegrand
    (H : 𝓢(ℝ, ℂ)) (N : ℕ) (ξ : ℝ) : ℂ :=
  (𝓕 (H : ℝ → ℂ)) ξ *
    ((∑ n ∈ Finset.range N,
      gaussDigammaSeriesTerm (ccmQuarterPiDigammaPoint ξ) n).re : ℂ)

def ccmQuarterGaussLimitIntegrand
    (H : 𝓢(ℝ, ℂ)) (ξ : ℝ) : ℂ :=
  (𝓕 (H : ℝ → ℂ)) ξ *
    ((Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re +
      Real.eulerMascheroniConstant : ℝ)

def ccmQuarterDigammaMul (H : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun ξ : ℝ => Complex.digamma (ccmQuarterPiDigammaPoint ξ))
    ((SchwartzMap.fourierTransformCLM ℂ) H)

@[simp] theorem ccmQuarterDigammaMul_apply
    (H : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ccmQuarterDigammaMul H ξ =
      Complex.digamma (ccmQuarterPiDigammaPoint ξ) *
        (𝓕 (H : ℝ → ℂ)) ξ := by
  rw [ccmQuarterDigammaMul,
    SchwartzMap.smulLeftCLM_apply_apply]
  · rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
    exact smul_eq_mul _ _
  · simpa only [ccmQuarterPiDigammaPoint] using
      digamma_oneQuarter_piLine_hasTemperateGrowth

def ccmQuarterGaussMajorant
    (H : 𝓢(ℝ, ℂ)) (ξ : ℝ) : ℝ :=
  ‖ccmQuarterDigammaMul H ξ‖ +
    (|Real.eulerMascheroniConstant| + 1) *
      ‖(𝓕 (H : ℝ → ℂ)) ξ‖ +
    5 * (3 + 2 * Real.pi) *
      ((1 + |ξ|) * ‖(𝓕 (H : ℝ → ℂ)) ξ‖)

theorem norm_ccmQuarterPiDigammaPoint_sub_one_le (ξ : ℝ) :
    ‖ccmQuarterPiDigammaPoint ξ - 1‖ ≤
      3 / 4 + Real.pi * |ξ| := by
  have h := Complex.norm_le_abs_re_add_abs_im
    (ccmQuarterPiDigammaPoint ξ - 1)
  have hre : (ccmQuarterPiDigammaPoint ξ - 1).re = -3 / 4 := by
    rw [Complex.sub_re, ccmQuarterPiDigammaPoint_re]
    norm_num
  have him : (ccmQuarterPiDigammaPoint ξ - 1).im = Real.pi * ξ := by
    simp [ccmQuarterPiDigammaPoint, Complex.mul_im]
  rw [hre, him] at h
  norm_num [abs_mul, abs_of_pos Real.pi_pos] at h ⊢
  exact h

theorem ccmQuarterGaussLogWeight_le (ξ : ℝ) :
    1 + Real.log
        (1 + 2 * ‖ccmQuarterPiDigammaPoint ξ - 1‖) ≤
      (3 + 2 * Real.pi) * (1 + |ξ|) := by
  have hnorm := norm_ccmQuarterPiDigammaPoint_sub_one_le ξ
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 1 + 2 * ‖ccmQuarterPiDigammaPoint ξ - 1‖ by positivity)
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs : 0 ≤ |ξ| := abs_nonneg ξ
  nlinarith

theorem integrable_ccmQuarterGaussMajorant
    (H : 𝓢(ℝ, ℂ)) :
    Integrable (ccmQuarterGaussMajorant H) := by
  have hD : Integrable (fun ξ : ℝ => ‖ccmQuarterDigammaMul H ξ‖) :=
    (ccmQuarterDigammaMul H).integrable.norm
  have hF : Integrable (fun ξ : ℝ => ‖(𝓕 (H : ℝ → ℂ)) ξ‖) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable.norm)
  have hpolyRaw :=
    ((𝓕 H : SchwartzMap ℝ ℂ).integrable_pow_mul
      (volume : Measure ℝ) 1)
  have hpoly : Integrable (fun ξ : ℝ =>
      (1 + |ξ|) * ‖(𝓕 (H : ℝ → ℂ)) ξ‖) := by
    have hsum := hF.add hpolyRaw
    apply hsum.congr
    filter_upwards with ξ
    simp only [Pi.add_apply, pow_one, Real.norm_eq_abs,
      SchwartzMap.fourier_coe]
    ring
  have hmain := (hD.add (hF.const_mul
      (|Real.eulerMascheroniConstant| + 1))).add
        (hpoly.const_mul (5 * (3 + 2 * Real.pi)))
  apply hmain.congr
  filter_upwards with ξ
  unfold ccmQuarterGaussMajorant
  simp only [Pi.add_apply]

theorem norm_ccmQuarterGaussPartialIntegrand_le_majorant
    (H : 𝓢(ℝ, ℂ)) (N : ℕ) (ξ : ℝ) :
    ‖ccmQuarterGaussPartialIntegrand H N ξ‖ ≤
      ccmQuarterGaussMajorant H ξ := by
  have hsum := norm_sum_gaussDigammaSeriesTerm_oneQuarter_le
    (ccmQuarterPiDigammaPoint_re ξ) N
  have hreNorm :
      ‖((∑ n ∈ Finset.range N,
        gaussDigammaSeriesTerm (ccmQuarterPiDigammaPoint ξ) n).re : ℂ)‖ ≤
        ‖∑ n ∈ Finset.range N,
          gaussDigammaSeriesTerm (ccmQuarterPiDigammaPoint ξ) n‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_re_le_norm _
  have hlog := ccmQuarterGaussLogWeight_le ξ
  rw [ccmQuarterGaussPartialIntegrand, norm_mul]
  refine (mul_le_mul_of_nonneg_left (hreNorm.trans hsum) (norm_nonneg _)).trans ?_
  rw [ccmQuarterGaussMajorant, ccmQuarterDigammaMul_apply, norm_mul]
  have hF0 : 0 ≤ ‖(𝓕 (H : ℝ → ℂ)) ξ‖ := norm_nonneg _
  have hgamma : 0 ≤ |Real.eulerMascheroniConstant| + 1 := by positivity
  have hC : 0 ≤ 5 * (3 + 2 * Real.pi) := by positivity
  calc
    ‖(𝓕 (H : ℝ → ℂ)) ξ‖ *
        (‖Complex.digamma (ccmQuarterPiDigammaPoint ξ)‖ +
          |Real.eulerMascheroniConstant| + 1 +
            5 * (1 + Real.log
              (1 + 2 * ‖ccmQuarterPiDigammaPoint ξ - 1‖))) ≤
      ‖(𝓕 (H : ℝ → ℂ)) ξ‖ *
        (‖Complex.digamma (ccmQuarterPiDigammaPoint ξ)‖ +
          |Real.eulerMascheroniConstant| + 1 +
            5 * ((3 + 2 * Real.pi) * (1 + |ξ|))) := by
        gcongr
    _ = _ := by ring

theorem integrable_ccmQuarterGaussPartialIntegrand
    (H : 𝓢(ℝ, ℂ)) (N : ℕ) :
    Integrable (ccmQuarterGaussPartialIntegrand H N) := by
  rw [show ccmQuarterGaussPartialIntegrand H N = fun ξ : ℝ =>
      ∑ n ∈ Finset.range N,
        (𝓕 (H : ℝ → ℂ)) ξ *
          ((gaussDigammaSeriesTerm
            (ccmQuarterPiDigammaPoint ξ) n).re : ℂ) by
    funext ξ
    rw [ccmQuarterGaussPartialIntegrand]
    have hReSum :
        ((∑ n ∈ Finset.range N,
          gaussDigammaSeriesTerm (ccmQuarterPiDigammaPoint ξ) n).re : ℂ) =
          ∑ n ∈ Finset.range N,
            ((gaussDigammaSeriesTerm
              (ccmQuarterPiDigammaPoint ξ) n).re : ℂ) := by
      rw [← Complex.reCLM_apply, map_sum]
      push_cast
      simp only [Complex.reCLM_apply]
    rw [hReSum]
    rw [Finset.mul_sum]]
  exact MeasureTheory.integrable_finsetSum _ fun n _ =>
    ccm_integrable_fourier_mul_re_gaussDigammaSeriesTerm H n

theorem tendsto_integral_ccmQuarterGaussPartialIntegrand
    (H : 𝓢(ℝ, ℂ)) :
    Tendsto
      (fun N : ℕ => ∫ ξ : ℝ,
        ccmQuarterGaussPartialIntegrand H N ξ)
      atTop
      (nhds (∫ ξ : ℝ, ccmQuarterGaussLimitIntegrand H ξ)) := by
  apply tendsto_integral_of_dominated_convergence
    (ccmQuarterGaussMajorant H)
  · intro N
    exact (integrable_ccmQuarterGaussPartialIntegrand H N).aestronglyMeasurable
  · exact integrable_ccmQuarterGaussMajorant H
  · intro N
    exact Filter.Eventually.of_forall fun ξ =>
      norm_ccmQuarterGaussPartialIntegrand_le_majorant H N ξ
  · exact Filter.Eventually.of_forall fun ξ => by
      have hs : 0 < (ccmQuarterPiDigammaPoint ξ).re := by
        rw [ccmQuarterPiDigammaPoint_re]
        norm_num
      have hseries :=
        (summable_gaussDigammaSeriesTerm hs).hasSum.tendsto_sum_nat
      have hvalue :
          ∑' n : ℕ, gaussDigammaSeriesTerm
              (ccmQuarterPiDigammaPoint ξ) n =
            Complex.digamma (ccmQuarterPiDigammaPoint ξ) +
              (Real.eulerMascheroniConstant : ℂ) := by
        rw [digamma_eq_neg_euler_add_tsum_gauss hs]
        ring
      rw [hvalue] at hseries
      have hre := Complex.continuous_re.continuousAt.tendsto.comp hseries
      have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
      unfold ccmQuarterGaussPartialIntegrand ccmQuarterGaussLimitIntegrand
      convert tendsto_const_nhds.mul hcomplex using 1
      · funext N
        rfl
      · simp

/-! ## Time-side Gauss cancellation -/

def ccmCompactSchwartzLogEvenization
    (H : CCMCompactSchwartzLogTest) : CCMCompactSchwartzLogTest where
  toSchwartzMap := H.toSchwartzMap +
    SchwartzMap.reflectedSchwartz H.toSchwartzMap
  radius := H.radius
  one_lt_radius := H.one_lt_radius
  eq_zero_of_radius_le_abs x hx := by
    have hxpos := H.eq_zero_of_radius_le_abs x hx
    have hxneg := H.eq_zero_of_radius_le_abs (-x) (by simpa using hx)
    simp [hxpos, hxneg]

@[simp] theorem ccmCompactSchwartzLogEvenization_apply
    (H : CCMCompactSchwartzLogTest) (h : ℝ) :
    ccmCompactSchwartzLogEvenization H h = H h + H (-h) := by
  simp [ccmCompactSchwartzLogEvenization]

def ccmArchimedeanGaussCorrection
    (H : CCMCompactSchwartzLogTest) (h : ℝ) : ℂ :=
  2 * H 0 *
    ((Real.exp (-h) / (1 + Real.exp (-h)) : ℝ) : ℂ)

theorem integrableOn_ccmArchimedeanGaussCorrection
    (H : CCMCompactSchwartzLogTest) :
    IntegrableOn (ccmArchimedeanGaussCorrection H) (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn
      (fun h : ℝ => 2 * ‖H 0‖ * Real.exp (-h)) (Ioi (0 : ℝ)) := by
    change Integrable (fun h : ℝ => 2 * ‖H 0‖ * Real.exp (-h))
      (volume.restrict (Ioi (0 : ℝ)))
    exact (integrableOn_exp_neg_Ioi 0).const_mul (2 * ‖H 0‖)
  have hcont : Continuous (ccmArchimedeanGaussCorrection H) := by
    unfold ccmArchimedeanGaussCorrection
    exact continuous_const.mul
      (Complex.continuous_ofReal.comp
        ((Real.continuous_exp.comp continuous_neg).div₀
          (continuous_const.add (Real.continuous_exp.comp continuous_neg))
          (fun h => by positivity)))
  refine hdom.mono' hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [ccmArchimedeanGaussCorrection, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ Real.exp (-h) / (1 + Real.exp (-h)) := by positivity
  rw [abs_of_nonneg hnonneg, norm_ofNat]
  have hfrac : Real.exp (-h) / (1 + Real.exp (-h)) ≤ Real.exp (-h) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-h)]
  nlinarith [norm_nonneg (H 0)]

def ccmArchimedeanGaussCancellationKernel
    (H : CCMCompactSchwartzLogTest) (h : ℝ) : ℂ :=
  ccmArchimedeanWeilSharpIntegrand (ccmCompactSchwartzLogEvenization H) h +
    ccmArchimedeanGaussCorrection H h

theorem integrableOn_ccmArchimedeanGaussCancellationKernel
    (H : CCMCompactSchwartzLogTest) :
    IntegrableOn (ccmArchimedeanGaussCancellationKernel H) (Ioi (0 : ℝ)) :=
  (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi
      (ccmCompactSchwartzLogEvenization H)).add
    (integrableOn_ccmArchimedeanGaussCorrection H)

theorem ccmArchimedeanGaussCancellationKernel_eq
    (H : CCMCompactSchwartzLogTest) {h : ℝ} (hh : 0 < h) :
    ccmArchimedeanGaussCancellationKernel H h =
      (((Real.exp (-h / 2) : ℝ) : ℂ) * (H h + H (-h)) -
          2 * ((Real.exp (-2 * h) : ℝ) : ℂ) * H 0) /
        ((1 - Real.exp (-2 * h) : ℝ) : ℂ) := by
  have hden : (1 - Real.exp (-2 * h) : ℝ) ≠ 0 := by
    have : Real.exp (-2 * h) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hplus : (1 + Real.exp (-h) : ℝ) ≠ 0 := by positivity
  rw [ccmArchimedeanGaussCancellationKernel,
    ccmArchimedeanWeilSharpIntegrand,
    ccmArchimedeanWeilSharpNumerator,
    ccmCompactSchwartzLogEvenization_apply,
    ccmArchimedeanGaussCorrection]
  rw [show (ccmCompactSchwartzLogEvenization H) 0 = 2 * H 0 by
    simp [ccmCompactSchwartzLogEvenization_apply, two_mul]]
  have hexp : Real.exp h - Real.exp (-h) =
      Real.exp h * (1 - Real.exp (-2 * h)) := by
    have hneg : Real.exp (-h) = Real.exp h * Real.exp (-2 * h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hneg]
    ring
  have hhalf : Real.exp (h / 2) * Real.exp (-h) = Real.exp (-h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : Real.exp (-2 * h) = Real.exp (-h) * Real.exp (-h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heh : ((Real.exp h : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero h
  have hdenC : (((1 - Real.exp (-2 * h) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hden
  have hplusC : (((1 + Real.exp (-h) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hplus
  rw [hexp]
  simp only [ofReal_mul, ofReal_sub, ofReal_add, ofReal_one, ofReal_div]
  simp only [ofReal_sub, ofReal_add, ofReal_one] at hdenC hplusC
  have hdenC' : 1 - (((Real.exp (-(h * 2)) : ℝ) : ℂ)) ≠ 0 := by
    rw [show -(h * 2) = -2 * h by ring]
    exact hdenC
  have hbc : ((Real.exp (-h) : ℝ) : ℂ) * ((Real.exp h : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← Complex.exp_add]
    simp
  have hce : ((Real.exp h : ℝ) : ℂ) *
      ((Real.exp (-(h / 2)) : ℝ) : ℂ) =
        ((Real.exp (h / 2) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  have hcd : ((Real.exp h : ℝ) : ℂ) *
      ((Real.exp (-(h * 2)) : ℝ) : ℂ) =
        ((Real.exp (-h) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  field_simp [heh, hdenC, hdenC', hplusC]
  linear_combination
    (-(H h + H (-h)) *
      (1 + ((Real.exp (-h) : ℝ) : ℂ))) * hce +
    (2 * H 0) * hbc +
    (2 * H 0) * hcd

def ccmQuarterGaussTimeTerm
    (H : CCMCompactSchwartzLogTest) (n : ℕ) (h : ℝ) : ℂ :=
  2 * H 0 * (((Real.exp (-2 * h) : ℝ) : ℂ) ^ (n + 1)) -
    ((Real.exp (-h / 2) : ℝ) : ℂ) * (H h + H (-h)) *
      (((Real.exp (-2 * h) : ℝ) : ℂ) ^ n)

theorem ccmQuarterGaussTimeTerm_eq_exp
    (H : CCMCompactSchwartzLogTest) (n : ℕ) (h : ℝ) :
    ccmQuarterGaussTimeTerm H n h =
      2 * Complex.exp
          (-((2 * ((n : ℝ) + 1) : ℝ) : ℂ) * (h : ℂ)) * H 0 -
        Complex.exp
          (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) *
            (H h + H (-h)) := by
  rw [ccmQuarterGaussTimeTerm]
  have hq : (((Real.exp (-2 * h) : ℝ) : ℂ) ^ n) =
      Complex.exp (-(((2 * (n : ℝ) * h : ℝ)) : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hq1 : (((Real.exp (-2 * h) : ℝ) : ℂ) ^ (n + 1)) =
      Complex.exp (-(((2 * ((n : ℝ) + 1) * h : ℝ)) : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hq, hq1]
  have heq1 : Complex.exp (-(((2 * ((n : ℝ) + 1) * h : ℝ)) : ℂ)) =
      Complex.exp (-((2 * ((n : ℝ) + 1) : ℝ) : ℂ) * (h : ℂ)) := by
    congr 1
    push_cast
    ring
  have heq2 : Complex.exp (((-h / 2 : ℝ) : ℂ) -
        (((2 * (n : ℝ) * h : ℝ)) : ℂ)) =
      Complex.exp (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) := by
    congr 1
    push_cast
    ring
  have hprod : ((Real.exp (-h / 2) : ℝ) : ℂ) *
      Complex.exp (-(((2 * (n : ℝ) * h : ℝ)) : ℂ)) =
      Complex.exp (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    exact heq2
  rw [heq1]
  have hsecond : ((Real.exp (-h / 2) : ℝ) : ℂ) *
        (H h + H (-h)) *
        Complex.exp (-(((2 * (n : ℝ) * h : ℝ)) : ℂ)) =
      Complex.exp (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) *
        (H h + H (-h)) := by
    calc
      ((Real.exp (-h / 2) : ℝ) : ℂ) * (H h + H (-h)) *
          Complex.exp (-(((2 * (n : ℝ) * h : ℝ)) : ℂ)) =
        (((Real.exp (-h / 2) : ℝ) : ℂ) *
          Complex.exp (-(((2 * (n : ℝ) * h : ℝ)) : ℂ))) *
            (H h + H (-h)) := by ring
      _ = _ := by rw [hprod]
  rw [hsecond]
  ring

theorem integrableOn_ccmQuarterGaussTimeTerm
    (H : CCMCompactSchwartzLogTest) (n : ℕ) :
    IntegrableOn (ccmQuarterGaussTimeTerm H n) (Ioi (0 : ℝ)) := by
  let a : ℂ := -((2 * ((n : ℝ) + 1) : ℝ) : ℂ)
  let b : ℂ := -((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ)
  have ha : a.re < 0 := by dsimp only [a]; simp; positivity
  have hb : b.re < 0 := by dsimp only [b]; simp; positivity
  have hfirst : IntegrableOn
      (fun h : ℝ => 2 * Complex.exp (a * (h : ℂ)) * H 0)
      (Ioi (0 : ℝ)) := by
    change Integrable (fun h : ℝ => 2 * Complex.exp (a * (h : ℂ)) * H 0)
      (volume.restrict (Ioi (0 : ℝ)))
    exact ((integrableOn_exp_mul_complex_Ioi ha 0).const_mul (2 : ℂ)).mul_const (H 0)
  have hpair : Integrable (fun h : ℝ => H h + H (-h)) :=
    H.toSchwartzMap.integrable.add H.toSchwartzMap.integrable.comp_neg
  have hbound : ∀ᵐ h : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      ‖Complex.exp (b * (h : ℂ))‖ ≤ 1 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
    have hh' : 0 < h := hh
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    dsimp only [b]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    have : 0 < 2 * ((n : ℝ) + 1 / 4) * h := by positivity
    linarith
  have hsecond : IntegrableOn
      (fun h : ℝ => Complex.exp (b * (h : ℂ)) * (H h + H (-h)))
      (Ioi (0 : ℝ)) := by
    have hraw := hpair.integrableOn.mul_bdd
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.restrict
      hbound
    apply hraw.congr
    filter_upwards with h
    dsimp only [Function.comp_apply]
    ring
  rw [show ccmQuarterGaussTimeTerm H n = fun h : ℝ =>
      2 * Complex.exp (a * (h : ℂ)) * H 0 -
        Complex.exp (b * (h : ℂ)) * (H h + H (-h)) by
    funext h
    rw [ccmQuarterGaussTimeTerm_eq_exp]]
  exact hfirst.sub hsecond

theorem sum_ccmQuarterGaussTimeTerm_eq
    (H : CCMCompactSchwartzLogTest) (N : ℕ) {h : ℝ} (hh : 0 < h) :
    (∑ n ∈ Finset.range N, ccmQuarterGaussTimeTerm H n h) =
      -ccmArchimedeanGaussCancellationKernel H h *
        (1 - (((Real.exp (-2 * h) : ℝ) : ℂ) ^ N)) := by
  let q : ℂ := ((Real.exp (-2 * h) : ℝ) : ℂ)
  let A : ℂ := ((Real.exp (-h / 2) : ℝ) : ℂ) * (H h + H (-h))
  have hqne : q ≠ 1 := by
    intro hcontra
    have hre := congrArg Complex.re hcontra
    dsimp only [q] at hre
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    have hlt : Real.exp (-2 * h) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hsum : (∑ n ∈ Finset.range N, ccmQuarterGaussTimeTerm H n h) =
      (2 * H 0 * q - A) * ∑ n ∈ Finset.range N, q ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [ccmQuarterGaussTimeTerm, q, A]
    rw [pow_succ']
    ring
  rw [hsum, geom_sum_eq hqne,
    ccmArchimedeanGaussCancellationKernel_eq H hh]
  simp only [ofReal_sub, ofReal_one]
  change (2 * H 0 * q - A) * ((q ^ N - 1) / (q - 1)) =
    -((A - 2 * q * H 0) / (1 - q)) * (1 - q ^ N)
  field_simp [hqne]
  ring

theorem integral_ccmQuarterGaussConstantTerm
    (H : CCMCompactSchwartzLogTest) (n : ℕ) :
    (∫ h : ℝ in Ioi 0,
        2 * Complex.exp
          (-((2 * ((n : ℝ) + 1) : ℝ) : ℂ) * (h : ℂ)) * H 0) =
      H 0 / ((n : ℂ) + 1) := by
  let a : ℂ := -((2 * ((n : ℝ) + 1) : ℝ) : ℂ)
  have ha : a.re < 0 := by dsimp only [a]; simp; positivity
  rw [show (fun h : ℝ =>
      2 * Complex.exp
          (-((2 * ((n : ℝ) + 1) : ℝ) : ℂ) * (h : ℂ)) * H 0) =
      fun h : ℝ => (2 * H 0) * Complex.exp (a * (h : ℂ)) by
    funext h
    dsimp only [a]
    ring]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi ha 0]
  dsimp only [a]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hne : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < (n : ℝ) + 1).ne'
  field_simp
  push_cast
  ring

theorem integral_ccmQuarterGaussTimeTerm
    (H : CCMCompactSchwartzLogTest) (n : ℕ) :
    (∫ h : ℝ in Ioi 0, ccmQuarterGaussTimeTerm H n h) =
      H 0 / ((n : ℂ) + 1) -
        ∫ h : ℝ in Ioi 0,
          Complex.exp
              (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) *
            (H h + H (-h)) := by
  let A : ℝ → ℂ := fun h =>
    2 * Complex.exp
      (-((2 * ((n : ℝ) + 1) : ℝ) : ℂ) * (h : ℂ)) * H 0
  let B : ℝ → ℂ := fun h =>
    Complex.exp
      (-((2 * ((n : ℝ) + 1 / 4) : ℝ) : ℂ) * (h : ℂ)) *
        (H h + H (-h))
  have hA : IntegrableOn A (Ioi (0 : ℝ)) := by
    let a : ℂ := -((2 * ((n : ℝ) + 1) : ℝ) : ℂ)
    have ha : a.re < 0 := by dsimp only [a]; simp; positivity
    change Integrable A (volume.restrict (Ioi (0 : ℝ)))
    simpa only [A, a] using
      ((integrableOn_exp_mul_complex_Ioi ha 0).const_mul (2 : ℂ)).mul_const (H 0)
  have hT := integrableOn_ccmQuarterGaussTimeTerm H n
  have hB : IntegrableOn B (Ioi (0 : ℝ)) := by
    have hraw := hA.sub hT
    apply hraw.congr
    filter_upwards with h
    dsimp only [A, B, Pi.sub_apply]
    rw [ccmQuarterGaussTimeTerm_eq_exp]
    ring
  rw [show ccmQuarterGaussTimeTerm H n = A - B by
    funext h
    dsimp only [A, B, Pi.sub_apply]
    rw [ccmQuarterGaussTimeTerm_eq_exp]]
  change (∫ h : ℝ in Ioi 0, A h - B h) = _
  rw [integral_sub hA hB, integral_ccmQuarterGaussConstantTerm]

theorem integral_ccmQuarterGaussPartialIntegrand_eq_time
    (H : CCMCompactSchwartzLogTest) (N : ℕ) :
    (∫ ξ : ℝ,
        ccmQuarterGaussPartialIntegrand H.toSchwartzMap N ξ) =
      ∫ h : ℝ in Ioi 0,
        ∑ n ∈ Finset.range N, ccmQuarterGaussTimeTerm H n h := by
  rw [show ccmQuarterGaussPartialIntegrand H.toSchwartzMap N = fun ξ : ℝ =>
      ∑ n ∈ Finset.range N,
        (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
          ((gaussDigammaSeriesTerm
            (ccmQuarterPiDigammaPoint ξ) n).re : ℂ) by
    funext ξ
    rw [ccmQuarterGaussPartialIntegrand]
    rw [← Finset.mul_sum]
    congr 1
    rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply]
    exact_mod_cast rfl]
  calc
    (∫ ξ : ℝ, ∑ n ∈ Finset.range N,
        (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
          ((gaussDigammaSeriesTerm
            (ccmQuarterPiDigammaPoint ξ) n).re : ℂ)) =
        ∑ n ∈ Finset.range N, ∫ ξ : ℝ,
          (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
            ((gaussDigammaSeriesTerm
              (ccmQuarterPiDigammaPoint ξ) n).re : ℂ) := by
      rw [MeasureTheory.integral_finsetSum]
      intro n hn
      exact ccm_integrable_fourier_mul_re_gaussDigammaSeriesTerm
        H.toSchwartzMap n
    _ = ∑ n ∈ Finset.range N,
        ∫ h : ℝ in Ioi 0, ccmQuarterGaussTimeTerm H n h := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ccm_integral_fourier_mul_re_gaussDigammaSeriesTerm,
        integral_ccmQuarterGaussTimeTerm]
    _ = ∫ h : ℝ in Ioi 0,
        ∑ n ∈ Finset.range N, ccmQuarterGaussTimeTerm H n h := by
      rw [MeasureTheory.integral_finsetSum]
      intro n hn
      exact integrableOn_ccmQuarterGaussTimeTerm H n

def ccmArchimedeanGaussCancellationPartialKernel
    (H : CCMCompactSchwartzLogTest) (N : ℕ) (h : ℝ) : ℂ :=
  ccmArchimedeanGaussCancellationKernel H h *
    (1 - (((Real.exp (-2 * h) : ℝ) : ℂ) ^ N))

theorem tendsto_integral_ccmArchimedeanGaussCancellationPartialKernel
    (H : CCMCompactSchwartzLogTest) :
    Tendsto
      (fun N : ℕ => ∫ h : ℝ in Ioi 0,
        ccmArchimedeanGaussCancellationPartialKernel H N h)
      atTop
      (nhds (∫ h : ℝ in Ioi 0,
        ccmArchimedeanGaussCancellationKernel H h)) := by
  apply tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi 0))
    (fun h : ℝ => ‖ccmArchimedeanGaussCancellationKernel H h‖)
  · intro N
    exact (integrableOn_ccmArchimedeanGaussCancellationKernel H).aestronglyMeasurable.mul
      ((by fun_prop : Continuous (fun h : ℝ =>
        (1 - (((Real.exp (-2 * h) : ℝ) : ℂ) ^ N)))).aestronglyMeasurable)
  · exact (integrableOn_ccmArchimedeanGaussCancellationKernel H).norm
  · intro N
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
    let q : ℝ := Real.exp (-2 * h)
    have hq0 : 0 ≤ q := by dsimp only [q]; positivity
    have hq1 : q < 1 := by
      dsimp only [q]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by have hh' : 0 < h := hh; linarith)
    have hpow0 : 0 ≤ q ^ N := pow_nonneg hq0 N
    have hpow1 : q ^ N ≤ 1 := (pow_le_one₀ hq0 hq1.le)
    rw [ccmArchimedeanGaussCancellationPartialKernel, norm_mul]
    have hfac : ‖(1 - (((q : ℝ) : ℂ) ^ N))‖ = 1 - q ^ N := by
      rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpow1)]
    rw [show ((Real.exp (-2 * h) : ℝ) : ℂ) = (q : ℂ) by rfl, hfac]
    exact mul_le_of_le_one_right (norm_nonneg _) (by linarith)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
    let q : ℝ := Real.exp (-2 * h)
    have hq0 : 0 ≤ q := by dsimp only [q]; positivity
    have hq1 : q < 1 := by
      dsimp only [q]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by have hh' : 0 < h := hh; linarith)
    have hpow : Tendsto (fun N : ℕ => q ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hpowComplex : Tendsto (fun N : ℕ => ((q ^ N : ℝ) : ℂ)) atTop (nhds 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hpow
    have hK : Tendsto (fun _ : ℕ => ccmArchimedeanGaussCancellationKernel H h) atTop
        (nhds (ccmArchimedeanGaussCancellationKernel H h)) := tendsto_const_nhds
    have hOne : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1) := tendsto_const_nhds
    simpa only [ccmArchimedeanGaussCancellationPartialKernel, sub_zero, mul_one,
      ← ofReal_pow, q] using hK.mul (hOne.sub hpowComplex)

theorem integral_ccmQuarterGaussPartialIntegrand_eq_partialKernel
    (H : CCMCompactSchwartzLogTest) (N : ℕ) :
    (∫ ξ : ℝ,
        ccmQuarterGaussPartialIntegrand H.toSchwartzMap N ξ) =
      -∫ h : ℝ in Ioi 0,
        ccmArchimedeanGaussCancellationPartialKernel H N h := by
  rw [integral_ccmQuarterGaussPartialIntegrand_eq_time]
  calc
    (∫ h : ℝ in Ioi 0,
        ∑ n ∈ Finset.range N, ccmQuarterGaussTimeTerm H n h) =
        ∫ h : ℝ in Ioi 0,
          -ccmArchimedeanGaussCancellationPartialKernel H N h := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
      rw [sum_ccmQuarterGaussTimeTerm_eq H N hh]
      simp only [ccmArchimedeanGaussCancellationPartialKernel, neg_mul]
    _ = -∫ h : ℝ in Ioi 0,
        ccmArchimedeanGaussCancellationPartialKernel H N h := by
      exact integral_neg _

theorem integral_fourier_mul_quarterDigamma_add_euler_eq_cancellation
    (H : CCMCompactSchwartzLogTest) :
    (∫ ξ : ℝ,
        ccmQuarterGaussLimitIntegrand H.toSchwartzMap ξ) =
      -∫ h : ℝ in Ioi 0,
        ccmArchimedeanGaussCancellationKernel H h := by
  have hfreq := tendsto_integral_ccmQuarterGaussPartialIntegrand
    H.toSchwartzMap
  have htime :=
    (tendsto_integral_ccmArchimedeanGaussCancellationPartialKernel H).neg
  have heq : (fun N : ℕ => ∫ ξ : ℝ,
      ccmQuarterGaussPartialIntegrand H.toSchwartzMap N ξ) =
      fun N : ℕ => -∫ h : ℝ in Ioi 0,
        ccmArchimedeanGaussCancellationPartialKernel H N h := by
    funext N
    exact integral_ccmQuarterGaussPartialIntegrand_eq_partialKernel H N
  rw [heq] at hfreq
  exact tendsto_nhds_unique hfreq htime

theorem integrableOn_ccmLogisticCorrection :
    IntegrableOn
      (fun h : ℝ => Real.exp (-h) / (1 + Real.exp (-h)))
      (Ioi (0 : ℝ)) := by
  have hcont : Continuous (fun h : ℝ =>
      Real.exp (-h) / (1 + Real.exp (-h))) := by
    exact (Real.continuous_exp.comp continuous_neg).div₀
      (continuous_const.add (Real.continuous_exp.comp continuous_neg))
      (fun h => by positivity)
  refine (integrableOn_exp_neg_Ioi 0).mono'
    hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  change |Real.exp (-h) / (1 + Real.exp (-h))| ≤ Real.exp (-h)
  rw [abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.exp_pos (-h)]

theorem integral_ccmLogisticCorrection_eq_log_two :
    (∫ h : ℝ in Ioi 0,
        Real.exp (-h) / (1 + Real.exp (-h))) = Real.log 2 := by
  let P : ℝ → ℝ := fun h => -Real.log (1 + Real.exp (-h))
  let f : ℝ → ℝ := fun h => Real.exp (-h) / (1 + Real.exp (-h))
  have hP : ∀ h : ℝ, HasDerivAt P (f h) h := by
    intro h
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x))
        (-Real.exp (-h)) h := by
      simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using
        (Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_id h).neg
    have hlog := (hexp.const_add 1).log (by positivity : 1 + Real.exp (-h) ≠ 0)
    dsimp only [P, f]
    have hneg := hlog.neg
    change HasDerivAt (fun y : ℝ => -Real.log (1 + Real.exp (-y)))
      (-(-Real.exp (-h) / (1 + Real.exp (-h)))) h at hneg
    convert hneg using 1
    ring
  have hfinite : ∀ T : ℝ,
      (∫ h : ℝ in (0 : ℝ)..T, f h) = P T - P 0 := by
    intro T
    have hderiv : deriv P = f := by
      funext h
      exact (hP h).deriv
    have hfcont : Continuous f := by
      dsimp only [f]
      exact (Real.continuous_exp.comp continuous_neg).div₀
        (continuous_const.add (Real.continuous_exp.comp continuous_neg))
        (fun h => by positivity)
    rw [← hderiv]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun h hh => (hP h).differentiableAt)
      (by rw [hderiv]; exact hfcont.intervalIntegrable 0 T)
  have himproper := intervalIntegral_tendsto_integral_Ioi 0
    (by simpa only [f] using integrableOn_ccmLogisticCorrection) tendsto_id
  have hexpZero : Tendsto (fun T : ℝ => Real.exp (-T)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hinside : Tendsto (fun T : ℝ => 1 + Real.exp (-T)) atTop (nhds 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hexpZero
  have hlogZero : Tendsto (fun T : ℝ => Real.log (1 + Real.exp (-T)))
      atTop (nhds 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hinside
  have hPZero : Tendsto P atTop (nhds 0) := by
    simpa only [P, neg_zero] using hlogZero.neg
  have hP0 : P 0 = -Real.log 2 := by norm_num [P]
  have hright : Tendsto (fun T : ℝ => P T - P 0) atTop (nhds (Real.log 2)) := by
    rw [hP0]
    simpa only [sub_neg_eq_add, zero_add] using hPZero.add_const (Real.log 2)
  have hfiniteTendsto : Tendsto (fun T : ℝ => ∫ h : ℝ in (0 : ℝ)..T, f h)
      atTop (nhds (Real.log 2)) := by
    exact hright.congr' (Filter.Eventually.of_forall fun T => (hfinite T).symm)
  exact tendsto_nhds_unique himproper hfiniteTendsto

theorem integral_ccmArchimedeanGaussCorrection
    (H : CCMCompactSchwartzLogTest) :
    (∫ h : ℝ in Ioi 0, ccmArchimedeanGaussCorrection H h) =
      2 * H 0 * (Real.log 2 : ℂ) := by
  rw [show ccmArchimedeanGaussCorrection H = fun h : ℝ =>
      (2 * H 0) *
        ((Real.exp (-h) / (1 + Real.exp (-h)) : ℝ) : ℂ) by rfl]
  rw [integral_const_mul]
  have hcomplex :
      (∫ h : ℝ in Ioi 0,
          ((Real.exp (-h) / (1 + Real.exp (-h)) : ℝ) : ℂ)) =
        (Real.log 2 : ℂ) := by
    have hreal := congrArg (fun x : ℝ => (x : ℂ))
      integral_ccmLogisticCorrection_eq_log_two
    calc
      (∫ h : ℝ in Ioi 0,
          ((Real.exp (-h) / (1 + Real.exp (-h)) : ℝ) : ℂ)) =
        (((∫ h : ℝ in Ioi 0,
          Real.exp (-h) / (1 + Real.exp (-h)) : ℝ)) : ℂ) :=
          _root_.integral_ofReal
      _ = (Real.log 2 : ℂ) := hreal
  rw [hcomplex]

def ccmArchimedeanWeilDistribution
    (H : CCMCompactSchwartzLogTest) : ℂ :=
  ccmArchimedeanWeilSharpDistribution (ccmCompactSchwartzLogEvenization H)

theorem real_log_four_mul_pi :
    Real.log (4 * Real.pi) = Real.log Real.pi + 2 * Real.log 2 := by
  rw [show (4 : ℝ) * Real.pi = (2 : ℝ) ^ 2 * Real.pi by ring,
    Real.log_mul (pow_ne_zero 2 (by norm_num)) Real.pi_ne_zero,
    Real.log_pow]
  norm_num
  ring

theorem ccmGaussCancellation_constant_eq_weilDistribution
    (H : CCMCompactSchwartzLogTest) :
    ((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) * H 0 +
        ∫ h : ℝ in Ioi 0, ccmArchimedeanGaussCancellationKernel H h =
      ccmArchimedeanWeilDistribution H := by
  have hsplit :
      (∫ h : ℝ in Ioi 0, ccmArchimedeanGaussCancellationKernel H h) =
        (∫ h : ℝ in Ioi 0,
          ccmArchimedeanWeilSharpIntegrand (ccmCompactSchwartzLogEvenization H) h) +
        ∫ h : ℝ in Ioi 0, ccmArchimedeanGaussCorrection H h := by
    rw [show ccmArchimedeanGaussCancellationKernel H = fun h : ℝ =>
        ccmArchimedeanWeilSharpIntegrand (ccmCompactSchwartzLogEvenization H) h +
          ccmArchimedeanGaussCorrection H h by rfl]
    exact integral_add
      (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi
        (ccmCompactSchwartzLogEvenization H))
      (integrableOn_ccmArchimedeanGaussCorrection H)
  rw [hsplit, integral_ccmArchimedeanGaussCorrection,
    ccmArchimedeanWeilDistribution,
    ccmArchimedeanWeilSharpDistribution,
    ccmCompactSchwartzLogEvenization_apply, neg_zero, real_log_four_mul_pi]
  push_cast
  ring

theorem integrable_ccmQuarterGaussLimitIntegrand
    (H : 𝓢(ℝ, ℂ)) :
    Integrable (ccmQuarterGaussLimitIntegrand H) := by
  have hD : Integrable (fun ξ : ℝ =>
      Complex.digamma (ccmQuarterPiDigammaPoint ξ) *
        (𝓕 (H : ℝ → ℂ)) ξ) := by
    have hraw : Integrable (ccmQuarterDigammaMul H) :=
      (ccmQuarterDigammaMul H).integrable
    apply hraw.congr
    filter_upwards with ξ
    rw [ccmQuarterDigammaMul_apply]
  have hDre : Integrable (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ *
        ((Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re : ℂ)) := by
    have hDnorm : Integrable (fun ξ : ℝ =>
        ‖Complex.digamma (ccmQuarterPiDigammaPoint ξ) *
          (𝓕 (H : ℝ → ℂ)) ξ‖) := hD.norm
    refine hDnorm.mono' ?_ ?_
    · have hdigamma : Continuous (fun ξ : ℝ =>
          Complex.digamma (ccmQuarterPiDigammaPoint ξ)) := by
        simpa only [ccmQuarterPiDigammaPoint] using
          digamma_oneQuarter_piLine_hasTemperateGrowth.1.continuous
      exact ((𝓕 H : SchwartzMap ℝ ℂ).continuous.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp
          (Complex.continuous_re.comp hdigamma)).aestronglyMeasurable)
    filter_upwards with ξ
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖(𝓕 (H : ℝ → ℂ)) ξ‖ *
          |(Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re| ≤
        ‖(𝓕 (H : ℝ → ℂ)) ξ‖ *
          ‖Complex.digamma (ccmQuarterPiDigammaPoint ξ)‖ :=
        mul_le_mul_of_nonneg_left
          (Complex.abs_re_le_norm
            (Complex.digamma (ccmQuarterPiDigammaPoint ξ)))
          (norm_nonneg ((𝓕 (H : ℝ → ℂ)) ξ))
      _ = _ := mul_comm _ _
  have hF : Integrable (fun ξ : ℝ =>
      (𝓕 (H : ℝ → ℂ)) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H : SchwartzMap ℝ ℂ).integrable)
  unfold ccmQuarterGaussLimitIntegrand
  apply (hDre.add (hF.const_mul (Real.eulerMascheroniConstant : ℂ))).congr
  filter_upwards with ξ
  simp only [Pi.add_apply]
  push_cast
  ring

theorem integral_fourier_mul_logPi_sub_re_quarterDigamma_eq_weilDistribution
    (H : CCMCompactSchwartzLogTest) :
    (∫ ξ : ℝ,
        (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
          ((Real.log Real.pi -
            (Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re : ℝ) : ℂ)) =
      ccmArchimedeanWeilDistribution H := by
  have hF : Integrable (fun ξ : ℝ =>
      (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 H.toSchwartzMap : SchwartzMap ℝ ℂ).integrable)
  have hlimit := integrable_ccmQuarterGaussLimitIntegrand H.toSchwartzMap
  have hF0 : (∫ ξ : ℝ,
      (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ) = H 0 := by
    simpa only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
      zero_div] using ccm_fourierInv_fourier_apply H.toSchwartzMap 0
  calc
    (∫ ξ : ℝ,
        (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
          ((Real.log Real.pi -
            (Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re : ℝ) : ℂ)) =
      ∫ ξ : ℝ,
        ((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) *
            (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ -
          ccmQuarterGaussLimitIntegrand H.toSchwartzMap ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      unfold ccmQuarterGaussLimitIntegrand
      push_cast
      ring
    _ = ((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) * H 0 +
        ∫ h : ℝ in Ioi 0, ccmArchimedeanGaussCancellationKernel H h := by
      rw [integral_sub (hF.const_mul _) hlimit, integral_const_mul, hF0,
        integral_fourier_mul_quarterDigamma_add_euler_eq_cancellation H]
      ring
    _ = ccmArchimedeanWeilDistribution H :=
      ccmGaussCancellation_constant_eq_weilDistribution H

theorem gammaHardyPhaseRate_pairing_ccmSchwartzMellinSymbol_eq_weilDistribution
    (H : CCMCompactSchwartzLogTest) :
    (-1 / (Real.pi : ℂ)) *
        ∫ t : ℝ, (gammaHardyPhaseRate t : ℂ) *
          ccmSchwartzMellinSymbol H.toSchwartzMap t =
      ccmArchimedeanWeilDistribution H := by
  let G : ℝ → ℂ := fun t => (gammaHardyPhaseRate t : ℂ) *
    ccmSchwartzMellinSymbol H.toSchwartzMap t
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G (2 * Real.pi)
  have habs : |((2 * Real.pi)⁻¹)| = (2 * Real.pi)⁻¹ := by
    rw [abs_of_pos]
    positivity
  rw [habs, Complex.real_smul] at hscale
  have hscaled :
      (-1 / (Real.pi : ℂ)) * (∫ t : ℝ, G t) =
        (-2 : ℂ) * ∫ ξ : ℝ, G ((2 * Real.pi) * ξ) := by
    rw [hscale]
    push_cast
    field_simp [Real.pi_ne_zero]
  change (-1 / (Real.pi : ℂ)) * (∫ t : ℝ, G t) = _
  rw [hscaled]
  calc
    (-2 : ℂ) * ∫ ξ : ℝ, G ((2 * Real.pi) * ξ) =
        ∫ ξ : ℝ,
          (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
            ((Real.log Real.pi -
              (Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      have hpoint : linePt ((2 * Real.pi) * ξ) / 2 =
          ccmQuarterPiDigammaPoint ξ := by
        unfold linePt ccmQuarterPiDigammaPoint
        push_cast
        ring
      unfold G gammaHardyPhaseRate
      rw [hpoint, ccmSchwartzMellinSymbol_apply]
      have harg : 2 * Real.pi * ξ / (2 * Real.pi) = ξ := by
        field_simp [Real.pi_ne_zero]
      rw [harg]
      push_cast
      ring
    _ = ccmArchimedeanWeilDistribution H :=
      integral_fourier_mul_logPi_sub_re_quarterDigamma_eq_weilDistribution H

/-- Exact spectral form of Connes--Consani Proposition 7(iv), including identification with the
explicit archimedean Weil distribution rather than only the phase-rate integral. -/
theorem opTrace_ccmSchwartzMellinMultiplier_mul_scatteringLogDifferential_eq_weilDistribution
    (H : CCMCompactSchwartzLogTest) :
    ContinuousLinearMap.opTrace
        (ccmSchwartzMultiplier (ccmSchwartzMellinSymbol H.toSchwartzMap) *
          ccmArchimedeanScatteringLogDifferential) =
      ccmArchimedeanWeilDistribution H := by
  rw [opTrace_ccmSchwartzMultiplier_mul_scatteringLogDifferential_eq_phaseRate]
  exact gammaHardyPhaseRate_pairing_ccmSchwartzMellinSymbol_eq_weilDistribution H

theorem opTrace_unitaryConjugate_of_isTraceClass
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (U : H ≃ₗᵢ[ℂ] K) (T : K →L[ℂ] K)
    (hT : T.IsTraceClass) :
    ContinuousLinearMap.opTrace
        (U.symm.toLinearIsometry.toContinuousLinearMap ∘L
          (T ∘L U.toLinearIsometry.toContinuousLinearMap)) =
      ContinuousLinearMap.opTrace T := by
  rcases hT with ⟨S, V, hS, hV, hfactor⟩
  rw [hfactor]
  let A : K →L[ℂ] H :=
    U.symm.toLinearIsometry.toContinuousLinearMap ∘L S
  let B : H →L[ℂ] K :=
    V ∘L U.toLinearIsometry.toContinuousLinearMap
  have hA : A.IsHilbertSchmidt :=
    hS.comp_left U.symm.toLinearIsometry.toContinuousLinearMap
  have hB : B.IsHilbertSchmidt :=
    hV.comp_right U.toLinearIsometry.toContinuousLinearMap
  calc
    ContinuousLinearMap.opTrace
        (U.symm.toLinearIsometry.toContinuousLinearMap ∘L
          ((S ∘L V) ∘L U.toLinearIsometry.toContinuousLinearMap)) =
      ContinuousLinearMap.opTrace (A ∘L B) := by
        congr 1
    _ = ContinuousLinearMap.opTrace (B ∘L A) :=
      ContinuousLinearMap.opTrace_comp_comm hA hB
    _ = ContinuousLinearMap.opTrace (V ∘L S) := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      change V (U (U.symm (S x))) = V (S x)
      rw [U.apply_symm_apply]
    _ = ContinuousLinearMap.opTrace (S ∘L V) :=
      ContinuousLinearMap.opTrace_comp_comm hV hS

/-- Literal geometric-space Connes--Consani Proposition 7(iv): the tested integrated scaling
operator times the geometric scattering logarithmic differential is trace class and has trace the
explicit archimedean Weil distribution. -/
theorem opTrace_ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_weilDistribution
    (H : CCMCompactSchwartzLogTest) :
    ContinuousLinearMap.opTrace
        (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) ∘L
          ccmArchimedeanGeometricScatteringLogDifferential) =
      ccmArchimedeanWeilDistribution H := by
  rw [ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_mellinConjugate]
  change ContinuousLinearMap.opTrace
      (archimedeanMellinUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
        ((ccmSchwartzMultiplier (ccmSchwartzMellinSymbol H.toSchwartzMap) *
          ccmArchimedeanScatteringLogDifferential) ∘L
            archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap)) = _
  rw [opTrace_unitaryConjugate_of_isTraceClass archimedeanMellinUnitary]
  · exact
      opTrace_ccmSchwartzMellinMultiplier_mul_scatteringLogDifferential_eq_weilDistribution H
  · exact ccmSchwartzMultiplier_mul_scatteringLogDifferential_isTraceClass
      (ccmSchwartzMellinSymbol H.toSchwartzMap)

end RHTower

