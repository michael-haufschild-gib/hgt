import GaloisForLFunctions.RHTower.HedenmalmThetaEsscherResolventFrame
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay

/-!
# Exact source pseudomodes outside the Xi divisor strip

The literal compact theta inverse has exponentially accurate, source-selected left pseudomodes
at reciprocal exterior parameters. At the same parameters every true spectral point remains at
least an explicit inverse-quadratic distance away. Both conclusions are unconditional.

The mechanism combines the Esscher source-resolvent row, its frequency-independent Gram norm,
completed-theta horizontal decay, and the exact reciprocal Xi divisor. The vectors do not use
zero enumeration. This is a quantitative bridge between existing source results, not a proof of
RH or a claim that arbitrary perturbations preserve prime coefficients. General pseudospectral
interpretations are standard (Krejčiřík--Siegl--Tater--Viola, J. Math. Phys. 56 (2015), 103513).
-/

open Complex MeasureTheory Set

namespace RHTower.HedenmalmThetaSource

noncomputable section
open HedenmalmQuantile HedenmalmClosedWeightedDerivative
private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

theorem norm_thetaEsscherFourierFamily_eq (h tau : ℝ) :
    ‖thetaEsscherFourierFamily h tau‖ = ‖thetaEsscherFourierFamily h 0‖ := by
  have hi : inner ℂ (thetaEsscherFourierFamily h tau) (thetaEsscherFourierFamily h tau) =
      inner ℂ (thetaEsscherFourierFamily h 0) (thetaEsscherFourierFamily h 0) := by
    simp only [inner_thetaEsscherFourierFamily, sub_self]
  have hs : ‖thetaEsscherFourierFamily h tau‖ ^ 2 =
      ‖thetaEsscherFourierFamily h 0‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re hi
  nlinarith [norm_nonneg (thetaEsscherFourierFamily h tau),
    norm_nonneg (thetaEsscherFourierFamily h 0)]

theorem thetaEsscherFourierFamily_ne_zero_of_half_le_abs
    {h : ℝ} (hh : 1 / 2 ≤ |h|) (tau : ℝ) : thetaEsscherFourierFamily h tau ≠ 0 := by
  intro hzero
  have hi := inner_thetaEsscherFourierFamily_eq_complexResolventMoment h tau pinnedOne
  rw [hzero, inner_zero_left, thetaComplexResolventMoment_pinnedOne] at hi
  exact rootA_one_ne_zero_of_sourcePencil_isUnit
    (isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hh tau) hi.symm

theorem adjoint_thetaSourcePencil_esscher
    {h : ℝ} (hh : 1 / 2 ≤ |h|) (tau : ℝ) :
    (thetaSourcePencil (thetaEsscherResolventParameter h tau)).adjoint
        (thetaEsscherFourierFamily h tau) =
      (starRingEnd ℂ) (rootA thetaSource (thetaEsscherResolventParameter h tau) 1) •
        pinnedOne := by
  let z := thetaEsscherResolventParameter h tau
  have hz := isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hh tau
  have hA : (starRingEnd ℂ) (rootA thetaSource z 1) ≠ 0 := by
    simpa using rootA_one_ne_zero_of_sourcePencil_isUnit hz
  have hE : thetaEsscherFourierFamily h tau =
      (starRingEnd ℂ) (rootA thetaSource z 1) •
        (thetaComplexResolvent z).adjoint pinnedOne := by
    rw [adjoint_thetaComplexResolvent_pinnedOne_eq_esscher hz,
      smul_inv_smul₀ hA]
  have hinv : (thetaSourcePencil z).adjoint ∘L (thetaComplexResolvent z).adjoint = 1 := by
    rw [← ContinuousLinearMap.adjoint_comp]
    have hmul : thetaComplexResolvent z ∘L thetaSourcePencil z = 1 :=
      Ring.inverse_mul_cancel _ hz
    rw [hmul, ContinuousLinearMap.adjoint_one]
  rw [hE, map_smul]
  exact congrArg (fun T : ThetaH →L[ℂ] ThetaH =>
    (starRingEnd ℂ) (rootA thetaSource z 1) • T pinnedOne) hinv

/-- Unit source-selected vector; no Xi zeros occur in its definition. -/
def thetaExteriorPseudomode (h tau : ℝ) : ThetaH :=
  ((‖thetaEsscherFourierFamily h 0‖ : ℝ) : ℂ)⁻¹ • thetaEsscherFourierFamily h tau

theorem norm_thetaExteriorPseudomode {h : ℝ} (hh : 1 / 2 ≤ |h|) (tau : ℝ) :
    ‖thetaExteriorPseudomode h tau‖ = 1 := by
  have hN := norm_ne_zero_iff.mpr (thetaEsscherFourierFamily_ne_zero_of_half_le_abs hh 0)
  simp only [thetaExteriorPseudomode, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_norm, norm_thetaEsscherFourierFamily_eq]
  exact inv_mul_cancel₀ hN

theorem norm_adjoint_thetaSourcePencil_pseudomode
    {h : ℝ} (hh : 1 / 2 ≤ |h|) (tau : ℝ) :
    ‖(thetaSourcePencil (thetaEsscherResolventParameter h tau)).adjoint
        (thetaExteriorPseudomode h tau)‖ =
      ‖XiC (thetaEsscherResolventParameter h tau)‖ * ‖pinnedOne‖ /
        (thetaSource.mass * ‖thetaEsscherFourierFamily h 0‖) := by
  rw [thetaExteriorPseudomode, map_smul, adjoint_thetaSourcePencil_esscher hh,
    norm_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    Complex.norm_conj, rootA_one, xiC_thetaSource_all, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos thetaSource.mass_pos]
  ring

theorem exists_norm_XiC_esscher_le {h δ : ℝ}
    (hh : |h| < 1) (hδ : 0 ≤ δ) (hδpi : δ < Real.pi / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau : ℝ,
      ‖XiC (thetaEsscherResolventParameter h tau)‖ ≤ C * Real.exp (-δ * |tau|) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_XiC_horizontal_le hh hδ (by linarith)
  refine ⟨C, hC, fun tau => ?_⟩
  have hb := hbound (-tau) (-h) (by rw [abs_neg])
  simpa [thetaEsscherResolventParameter, sub_eq_add_neg, neg_mul] using hb

theorem exists_exponential_thetaExteriorPencil_residual
    {h δ : ℝ} (hh0 : 1 / 2 ≤ |h|) (hh1 : |h| < 1)
    (hδ : 0 < δ) (hδpi : δ < Real.pi / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ tau : ℝ,
      ‖(thetaSourcePencil (thetaEsscherResolventParameter h tau)).adjoint
        (thetaExteriorPseudomode h tau)‖ ≤ C * Real.exp (-δ * |tau|) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_XiC_esscher_le hh1 hδ.le hδpi
  let D := ‖pinnedOne‖ / (thetaSource.mass * ‖thetaEsscherFourierFamily h 0‖)
  have hD : 0 < D := div_pos (norm_pos_iff.mpr pinnedOne_ne_zero)
    (mul_pos thetaSource.mass_pos
      (norm_pos_iff.mpr (thetaEsscherFourierFamily_ne_zero_of_half_le_abs hh0 0)))
  refine ⟨(C + 1) * D, mul_pos (by linarith) hD, fun tau => ?_⟩
  rw [norm_adjoint_thetaSourcePencil_pseudomode hh0]
  calc
    _ = ‖XiC (thetaEsscherResolventParameter h tau)‖ * D := by dsimp [D]; ring
    _ ≤ (C * Real.exp (-δ * |tau|)) * D := mul_le_mul_of_nonneg_right (hb tau) hD.le
    _ ≤ ((C + 1) * D) * Real.exp (-δ * |tau|) := by
      nlinarith [mul_pos hD (Real.exp_pos (-δ * |tau|))]

theorem thetaEsscherResolventParameter_ne_zero {h : ℝ}
    (hh : 1 / 2 ≤ |h|) (tau : ℝ) : thetaEsscherResolventParameter h tau ≠ 0 := by
  intro heq
  have hi := congrArg Complex.im heq
  simp only [thetaEsscherResolventParameter_im, Complex.zero_im, neg_eq_zero] at hi
  subst h
  norm_num at hh

theorem norm_thetaExteriorPseudomode_residual {h : ℝ}
    (hh : 1 / 2 ≤ |h|) (tau : ℝ) :
    ‖thetaKernelOperator.adjoint (thetaExteriorPseudomode h tau) -
        (starRingEnd ℂ) (-(thetaEsscherResolventParameter h tau)⁻¹) •
          thetaExteriorPseudomode h tau‖ =
      ‖(thetaSourcePencil (thetaEsscherResolventParameter h tau)).adjoint
          (thetaExteriorPseudomode h tau)‖ / ‖thetaEsscherResolventParameter h tau‖ := by
  let z := thetaEsscherResolventParameter h tau
  let v := thetaExteriorPseudomode h tau
  have hz : (starRingEnd ℂ) z ≠ 0 := by
    simpa using thetaEsscherResolventParameter_ne_zero hh tau
  have heq : thetaKernelOperator.adjoint v - (starRingEnd ℂ) (-z⁻¹) • v =
      ((starRingEnd ℂ) z)⁻¹ • (thetaSourcePencil z).adjoint v := by
    simp only [thetaSourcePencil, map_add, map_smulₛₗ,
      ContinuousLinearMap.adjoint_one, add_apply,
      one_apply_eq_self, smul_apply,
      map_neg, map_inv₀, smul_add, smul_smul, inv_mul_cancel₀ hz,
      one_smul, neg_smul, sub_neg_eq_add]
    module
  change ‖thetaKernelOperator.adjoint v - (starRingEnd ℂ) (-z⁻¹) • v‖ = _
  rw [heq, norm_smul, norm_inv, Complex.norm_conj]
  ring

private theorem norm_sub_neg_inv_eq {z a : ℂ} (hz : z ≠ 0) (ha : a ≠ 0) :
    ‖-z⁻¹ - -a⁻¹‖ = ‖a - z‖ / (‖z‖ * ‖a‖) := by
  have heq : -z⁻¹ - -a⁻¹ = (z - a) / (z * a) := by field_simp; ring
  rw [heq, norm_div, norm_mul, norm_sub_rev]

theorem thetaExterior_spectral_separation {h : ℝ} (hh : 1 / 2 < |h|)
    (tau : ℝ) {mu : ℂ} (hmu : mu ∈ spectrum ℂ thetaKernelOperator) :
    (|h| - 1 / 2) /
        (‖thetaEsscherResolventParameter h tau‖ *
          (‖thetaEsscherResolventParameter h tau‖ + (|h| - 1 / 2))) ≤
      ‖-(thetaEsscherResolventParameter h tau)⁻¹ - mu‖ := by
  let z := thetaEsscherResolventParameter h tau
  let d := |h| - 1 / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hz : z ≠ 0 := thetaEsscherResolventParameter_ne_zero hh.le tau
  have hZ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  change d / (‖z‖ * (‖z‖ + d)) ≤ ‖-z⁻¹ - mu‖
  by_cases hm0 : mu = 0
  · subst mu
    rw [sub_zero, norm_neg, norm_inv]
    apply (div_le_iff₀ (mul_pos hZ (add_pos hZ hd))).2
    field_simp
    linarith
  obtain ⟨a, ha, rfl⟩ :=
    (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero hm0).1 hmu
  have ha0 : a ≠ 0 := fun h => XiC_zero_ne (h ▸ ha)
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have haim : |a.im| < 1 / 2 := abs_lt.mpr (by
    simpa only [neg_div] using xiC_zero_im_mem_openHalf ha)
  have hsep : d ≤ ‖a - z‖ := by
    have htri := abs_add_le (a.im - z.im) (-a.im)
    have him := Complex.abs_im_le_norm (a - z)
    have hzIm : |z.im| = |h| := by simp [z]
    rw [Complex.sub_im] at him
    rw [show a.im - z.im + -a.im = -z.im by ring, abs_neg, abs_neg, hzIm] at htri
    dsimp [d]
    linarith
  have htri : ‖a‖ ≤ ‖a - z‖ + ‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a - z) z
  rw [norm_sub_neg_inv_eq hz ha0]
  apply (div_le_div_iff₀ (mul_pos hZ (add_pos hZ hd)) (mul_pos hZ hA)).2
  have hprod : d * ‖a‖ ≤ ‖a - z‖ * (‖z‖ + d) := by
    nlinarith [mul_le_mul_of_nonneg_left htri hd.le,
      mul_le_mul_of_nonneg_right hsep hZ.le]
  nlinarith [mul_le_mul_of_nonneg_left hprod hZ.le]

/-- Exponentially accurate source pseudomodes with inverse-quadratic separation from every
true spectral point. All constants are independent of frequency; RH is not assumed. -/
theorem thetaExterior_pseudospectral_separation
    {h δ : ℝ} (hh0 : 1 / 2 < |h|) (hh1 : |h| < 1)
    (hδ : 0 < δ) (hδpi : δ < Real.pi / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ tau : ℝ,
      ‖thetaExteriorPseudomode h tau‖ = 1 ∧
      ‖thetaKernelOperator.adjoint (thetaExteriorPseudomode h tau) -
          (starRingEnd ℂ) (-(thetaEsscherResolventParameter h tau)⁻¹) •
            thetaExteriorPseudomode h tau‖ ≤
        C * Real.exp (-δ * |tau|) / ‖thetaEsscherResolventParameter h tau‖ ∧
      ∀ mu ∈ spectrum ℂ thetaKernelOperator,
        (|h| - 1 / 2) /
            (‖thetaEsscherResolventParameter h tau‖ *
              (‖thetaEsscherResolventParameter h tau‖ + (|h| - 1 / 2))) ≤
          ‖-(thetaEsscherResolventParameter h tau)⁻¹ - mu‖ := by
  obtain ⟨C, hC, hb⟩ := exists_exponential_thetaExteriorPencil_residual hh0.le hh1 hδ hδpi
  refine ⟨C, hC, fun tau => ⟨norm_thetaExteriorPseudomode hh0.le tau, ?_, ?_⟩⟩
  · rw [norm_thetaExteriorPseudomode_residual hh0.le]
    exact div_le_div_of_nonneg_right (hb tau) (norm_nonneg _)
  · exact fun _ hmu => thetaExterior_spectral_separation hh0 tau hmu

/-- Exterior source resolvents grow exponentially despite the entire line being zero-free. -/
theorem exists_exponential_thetaComplexResolvent_lower
    {h δ : ℝ} (hh0 : 1 / 2 ≤ |h|) (hh1 : |h| < 1)
    (hδ : 0 < δ) (hδpi : δ < Real.pi / 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ tau : ℝ,
      c * Real.exp (δ * |tau|) ≤
        ‖thetaComplexResolvent (thetaEsscherResolventParameter h tau)‖ := by
  obtain ⟨C, hC, hb⟩ := exists_exponential_thetaExteriorPencil_residual hh0 hh1 hδ hδpi
  refine ⟨C⁻¹, inv_pos.mpr hC, fun tau => ?_⟩
  let z := thetaEsscherResolventParameter h tau
  let v := thetaExteriorPseudomode h tau
  have hz := isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hh0 tau
  have hinv : (thetaComplexResolvent z).adjoint ∘L (thetaSourcePencil z).adjoint = 1 := by
    rw [← ContinuousLinearMap.adjoint_comp]
    have hmul : thetaSourcePencil z ∘L thetaComplexResolvent z = 1 :=
      Ring.mul_inverse_cancel _ hz
    rw [hmul, ContinuousLinearMap.adjoint_one]
  have hnorm := (thetaComplexResolvent z).adjoint.le_opNorm ((thetaSourcePencil z).adjoint v)
  have heval : (thetaComplexResolvent z).adjoint ((thetaSourcePencil z).adjoint v) = v :=
    congrArg (fun T : ThetaH →L[ℂ] ThetaH => T v) hinv
  rw [heval, show ‖v‖ = 1 from norm_thetaExteriorPseudomode hh0 tau,
    ContinuousLinearMap.adjoint.norm_map] at hnorm
  have hineq : 1 ≤ ‖thetaComplexResolvent z‖ * (C * Real.exp (-δ * |tau|)) :=
    hnorm.trans (mul_le_mul_of_nonneg_left (hb tau) (norm_nonneg _))
  have hm := mul_le_mul_of_nonneg_right hineq (Real.exp_pos (δ * |tau|)).le
  have hexp : Real.exp (-δ * |tau|) * Real.exp (δ * |tau|) = 1 := by
    rw [← Real.exp_add, show -δ * |tau| + δ * |tau| = 0 by ring, Real.exp_zero]
  have hfinal : Real.exp (δ * |tau|) ≤ ‖thetaComplexResolvent z‖ * C := by
    simpa only [one_mul, mul_assoc, hexp, mul_one] using hm
  change C⁻¹ * Real.exp (δ * |tau|) ≤ ‖thetaComplexResolvent z‖
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ hC).2 hfinal

end
end RHTower.HedenmalmThetaSource

