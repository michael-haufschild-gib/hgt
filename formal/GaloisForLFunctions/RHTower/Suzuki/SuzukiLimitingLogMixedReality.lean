import GaloisForLFunctions.RHTower.Suzuki.SuzukiLimitingLogOperator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedScrewWeilBridge

/-!
# Mixed reality of Suzuki's limiting logarithmic form

This module proves the exact complexification mechanism for Suzuki's limiting form. It rewrites
the mixed closed form as the restricted Weil form plus the finite-prime, scalar, and origin-kernel
corrections, then proves each correction is real on pairs of literal real source-core vectors.

The proof is coefficient-level: translated real representatives, every finite-prime summand, and
the real integral kernel are checked directly. No conjugation-invariance premise is introduced.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem inner_suzukiLimitingLogClosedForm_eq_weil_add_corrections
    (u v : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiLimitingLogClosedForm u v =
      suzukiWeilIntervalForm suzukiLimitingUnitAperture u v +
      inner ℂ
        (suzukiLimitingIntervalPrimeOperator
          (suzukiLimitingLogFormEmbedding u))
        (suzukiLimitingLogFormEmbedding v) +
      (((2 * suzukiWeilArchimedeanConstant + 1 : ℝ) : ℂ) *
        inner ℂ (suzukiLimitingLogFormEmbedding u)
          (suzukiLimitingLogFormEmbedding v)) +
      inner ℂ
        (suzukiLimitingOriginKernelOperator
          (suzukiLimitingLogFormEmbedding u))
        (suzukiLimitingLogFormEmbedding v) := by
  let f := suzukiLimitingLogFormEmbedding u
  let g := suzukiLimitingLogFormEmbedding v
  let e : SuzukiApertureIntervalL2 1 ≃ₗᵢ[ℂ]
      suzukiApertureHilbert suzukiLimitingUnitAperture :=
    suzukiApertureL2Equiv suzukiLimitingUnitAperture
  have htransport (T : suzukiApertureHilbert suzukiLimitingUnitAperture →L[ℂ]
      suzukiApertureHilbert suzukiLimitingUnitAperture) :
      inner ℂ (e.symm (T (e f))) g = inner ℂ (T (e f)) (e g) := by
    calc
      inner ℂ (e.symm (T (e f))) g =
          inner ℂ (e.symm (T (e f))) (e.symm (e g)) := by
        rw [e.symm_apply_apply]
      _ = inner ℂ (T (e f)) (e g) := e.symm.inner_map_map _ _
  unfold suzukiLimitingLogClosedForm suzukiWeilIntervalForm
  change inner ℂ u v +
      inner ℂ
        (((suzukiLimitingScalar •
            (1 : SuzukiApertureIntervalL2 1 →L[ℂ]
              SuzukiApertureIntervalL2 1)) f +
          e.symm (ccmPolarOperator suzukiLimitingUnitAperture (e f))) +
          suzukiLimitingOriginKernelOperator f) g =
      (inner ℂ u v +
        inner ℂ
          (e.symm (ccmRestrictedWeilBoundedRemainder
            suzukiLimitingUnitAperture (e f))) g) +
        inner ℂ
          (e.symm (ccmFinitePrimeOperator
            suzukiLimitingUnitAperture (e f))) g +
        ((2 * suzukiWeilArchimedeanConstant + 1 : ℝ) : ℂ) *
          inner ℂ f g +
        inner ℂ (suzukiLimitingOriginKernelOperator f) g
  rw [inner_add_left, inner_add_left, smul_apply, one_apply_eq_self,
    inner_smul_left, star_suzukiLimitingScalar,
    htransport (ccmPolarOperator suzukiLimitingUnitAperture),
    htransport (ccmRestrictedWeilBoundedRemainder suzukiLimitingUnitAperture),
    htransport (ccmFinitePrimeOperator suzukiLimitingUnitAperture)]
  unfold ccmRestrictedWeilBoundedRemainder suzukiLimitingScalar
  rw [sub_apply, add_apply, smul_apply, one_apply_eq_self,
    inner_sub_left, inner_add_left, inner_smul_left,
    star_ccmArchimedeanRemainderScalar]
  rw [e.inner_map_map]
  ring

theorem inner_suzukiLimitingCoreIntervalVector_mixed_eq_ofReal
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    inner ℂ (suzukiLimitingCoreIntervalVector u)
        (suzukiLimitingCoreIntervalVector v) =
      ((∫ x : SuzukiApertureInterval 1,
        u (x : ℝ) * v (x : ℝ) : ℝ) : ℂ) := by
  let f := suzukiLimitingCoreIntervalVector u
  let g := suzukiLimitingCoreIntervalVector v
  have hf : (f : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (u (x : ℝ) : ℂ) := suzukiLimitingCoreIntervalVector_coeFn u
  have hg : (g : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (v (x : ℝ) : ℂ) := suzukiLimitingCoreIntervalVector_coeFn v
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval 1, inner ℂ (f x) (g x)) =
        ∫ x : SuzukiApertureInterval 1,
          ((u (x : ℝ) * v (x : ℝ) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hfx hgx
      rw [hfx, hgx]
      simp [RCLike.inner_apply]
      ring
    _ = _ := integral_ofReal

theorem inner_suzukiLimitingCoreIntervalVector_mixed_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (inner ℂ (suzukiLimitingCoreIntervalVector u)
      (suzukiLimitingCoreIntervalVector v)).im = 0 := by
  rw [inner_suzukiLimitingCoreIntervalVector_mixed_eq_ofReal]
  simp

theorem inner_logTranslationCLM_suzukiRestrictedWeilCoreCCMFormVector_mixed_eq_ofReal
    (a : SuzukiPositiveAperture)
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) (h : ℝ) :
    inner ℂ
        (logTranslationCLM h
          (ccmArchimedeanFormToAperture a
            (suzukiRestrictedWeilCoreCCMFormVector a u)).1)
        (ccmArchimedeanFormToAperture a
          (suzukiRestrictedWeilCoreCCMFormVector a v)).1 =
      ((∫ x : ℝ, u (x + h) * v x : ℝ) : ℂ) := by
  let f : SoninL2 := (ccmArchimedeanFormToAperture a
    (suzukiRestrictedWeilCoreCCMFormVector a u)).1
  let g : SoninL2 := (ccmArchimedeanFormToAperture a
    (suzukiRestrictedWeilCoreCCMFormVector a v)).1
  have hf : (f : ℝ → ℂ) =ᵐ[volume] fun x => (u x : ℂ) :=
    ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u
  have hg : (g : ℝ → ℂ) =ᵐ[volume] fun x => (v x : ℂ) :=
    ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a v
  have hfshift := hf.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htrans := Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : ℝ, inner ℂ ((logTranslationCLM h f) x) (g x)) =
        ∫ x : ℝ, ((u (x + h) * v x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [htrans, hfshift, hg] with x htx hux hvx
      change inner ℂ
        (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
          (MellinL2.realTranslation_measurePreserving h) f x) (g x) = _
      rw [htx, hux, hvx]
      simp [RCLike.inner_apply, MellinL2.realTranslationEquiv]
      ring
    _ = _ := integral_ofReal

theorem inner_ccmPrimeTransportOperator_realCore_mixed_im_eq_zero
    (a : SuzukiPositiveAperture) (n : ℕ)
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    (inner ℂ
      (ccmPrimeTransportOperator a n
        (ccmArchimedeanFormToAperture a
          (suzukiRestrictedWeilCoreCCMFormVector a u)))
      (ccmArchimedeanFormToAperture a
        (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0 := by
  rw [inner_ccmPrimeTransportOperator]
  rw [inner_logTranslationCLM_suzukiRestrictedWeilCoreCCMFormVector_mixed_eq_ofReal,
    inner_logTranslationCLM_suzukiRestrictedWeilCoreCCMFormVector_mixed_eq_ofReal]
  simp

theorem inner_suzukiLimitingIntervalPrimeOperator_realCore_mixed_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiLimitingIntervalPrimeOperator
        (suzukiLimitingCoreIntervalVector u))
      (suzukiLimitingCoreIntervalVector v)).im = 0 := by
  classical
  let a := suzukiLimitingUnitAperture
  let qu := suzukiRestrictedWeilCoreCCMFormVector a u
  let qv := suzukiRestrictedWeilCoreCCMFormVector a v
  let f := ccmArchimedeanFormToAperture a qu
  let g := ccmArchimedeanFormToAperture a qv
  let e := suzukiApertureL2Equiv a
  have hfu : suzukiLimitingCoreIntervalVector u = e.symm f :=
    suzukiLimitingCoreIntervalVector_eq_formEmbedding u
  have hfv : suzukiLimitingCoreIntervalVector v = e.symm g :=
    suzukiLimitingCoreIntervalVector_eq_formEmbedding v
  rw [hfu, hfv]
  change (inner ℂ (e.symm (ccmFinitePrimeOperator a (e (e.symm f))))
    (e.symm g)).im = 0
  rw [e.apply_symm_apply, e.symm.inner_map_map]
  unfold ccmFinitePrimeOperator
  generalize Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn, add_apply, inner_add_left, Complex.add_im, ih]
      rw [smul_apply, inner_smul_left]
      have hterm := inner_ccmPrimeTransportOperator_realCore_mixed_im_eq_zero
        a n u v
      change (inner ℂ (ccmPrimeTransportOperator a n f) g).im = 0 at hterm
      rw [show (starRingEnd ℂ)
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) =
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) by
            exact Complex.conj_ofReal _]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, hterm, mul_zero, zero_add]

theorem inner_suzukiLimitingOriginKernelOperatorRaw_realCore_mixed_eq_ofReal
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    inner ℂ
        (suzukiLimitingOriginKernelOperatorRaw
          (suzukiLimitingCoreIntervalVector u))
        (suzukiLimitingCoreIntervalVector v) =
      ((∫ x : SuzukiApertureInterval 1,
        (∫ y : SuzukiApertureInterval 1,
          suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) * u (y : ℝ)) *
            v (x : ℝ) : ℝ) : ℂ) := by
  let f := suzukiLimitingCoreIntervalVector u
  let g := suzukiLimitingCoreIntervalVector v
  have hf : (f : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (u (x : ℝ) : ℂ) := suzukiLimitingCoreIntervalVector_coeFn u
  have hg : (g : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (v (x : ℝ) : ℂ) := suzukiLimitingCoreIntervalVector_coeFn v
  have hop := suzukiLimitingOriginKernelOperatorRaw_coeFn f
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval 1,
        inner ℂ (suzukiLimitingOriginKernelOperatorRaw f x) (g x)) =
        ∫ x : SuzukiApertureInterval 1,
          (((∫ y : SuzukiApertureInterval 1,
              suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) *
                u (y : ℝ)) * v (x : ℝ) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hop, hg] with x hx hgx
      rw [hx, hgx]
      have hinner :
          (∫ y : SuzukiApertureInterval 1,
              (suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) : ℂ) * f y) =
            ((∫ y : SuzukiApertureInterval 1,
              suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) *
                u (y : ℝ) : ℝ) : ℂ) := by
        calc
          _ = ∫ y : SuzukiApertureInterval 1,
              ((suzukiOriginRemainderCurvature ((x : ℝ) - (y : ℝ)) *
                u (y : ℝ) : ℝ) : ℂ) := by
            apply integral_congr_ae
            filter_upwards [hf] with y hfy
            rw [hfy]
            push_cast
            rfl
          _ = _ := integral_ofReal
      rw [hinner]
      simp [RCLike.inner_apply]
      ring
    _ = _ := integral_ofReal

theorem inner_suzukiLimitingOriginKernelOperatorRaw_realCore_mixed_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiLimitingOriginKernelOperatorRaw
        (suzukiLimitingCoreIntervalVector u))
      (suzukiLimitingCoreIntervalVector v)).im = 0 := by
  rw [inner_suzukiLimitingOriginKernelOperatorRaw_realCore_mixed_eq_ofReal]
  simp

theorem inner_suzukiLimitingOriginKernelOperator_realCore_mixed_im_eq_zero
    (u v : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiLimitingOriginKernelOperator
        (suzukiLimitingCoreIntervalVector u))
      (suzukiLimitingCoreIntervalVector v)).im = 0 := by
  let f := suzukiLimitingCoreIntervalVector u
  let g := suzukiLimitingCoreIntervalVector v
  have huv := inner_suzukiLimitingOriginKernelOperatorRaw_realCore_mixed_im_eq_zero u v
  have hvu := inner_suzukiLimitingOriginKernelOperatorRaw_realCore_mixed_im_eq_zero v u
  have hadj : inner ℂ
      (ContinuousLinearMap.adjoint suzukiLimitingOriginKernelOperatorRaw f) g =
      inner ℂ f (suzukiLimitingOriginKernelOperatorRaw g) := by
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  have hconj : inner ℂ f (suzukiLimitingOriginKernelOperatorRaw g) =
      star (inner ℂ (suzukiLimitingOriginKernelOperatorRaw g) f) := by
    exact (inner_conj_symm f (suzukiLimitingOriginKernelOperatorRaw g)).symm
  have hreverse :
      (inner ℂ f (suzukiLimitingOriginKernelOperatorRaw g)).im = 0 := by
    rw [hconj]
    change -(inner ℂ (suzukiLimitingOriginKernelOperatorRaw g) f).im = 0
    dsimp only [f, g] at hvu ⊢
    rw [hvu, neg_zero]
  unfold suzukiLimitingOriginKernelOperator
  rw [smul_apply, add_apply, inner_smul_left, inner_add_left, hadj, hconj]
  dsimp only [f, g] at huv hvu ⊢
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    apply Complex.ext <;> norm_num]
  dsimp only [f, g] at hreverse
  norm_num [Complex.mul_im, Complex.add_im, huv, hreverse]

end RHTower

