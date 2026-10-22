import GaloisForLFunctions.RHTower.CCM.CCMOnePrimeCayleyTransport
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicAffineProjection

open Complex MeasureTheory
open scoped ENNReal InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- Fourier-index involution implementing `Jf(z)=z⁻¹f(z⁻¹)`. -/
def ccmHardyFlipIndexEquiv : ℤ ≃ ℤ where
  toFun n := -n - 1
  invFun n := -n - 1
  left_inv n := by dsimp; ring
  right_inv n := by dsimp; ring

@[simp] theorem ccmHardyFlipIndexEquiv_apply (n : ℤ) :
    ccmHardyFlipIndexEquiv n = -n - 1 := rfl

@[simp] theorem ccmHardyFlipIndexEquiv_symm_apply (n : ℤ) :
    ccmHardyFlipIndexEquiv.symm n = -n - 1 := rfl

/-- Circle Hardy flip `e_n ↦ e_{-n-1}` in exact Fourier coordinates. -/
def ccmHardyFlipUnitary : CCMCircleL2 ≃ₗᵢ[ℂ] CCMCircleL2 :=
  (fourierBasis (T := (1 : ℝ))).repr |>.trans
    (lpReindexEquiv ccmHardyFlipIndexEquiv) |>.trans
      (fourierBasis (T := (1 : ℝ))).repr.symm

private theorem lpReindexEquiv_ccmHardyFlip_single (n : ℤ) :
    lpReindexEquiv ccmHardyFlipIndexEquiv (lp.single 2 n 1) =
      lp.single 2 (-n - 1) 1 := by
  apply lp.ext
  funext k
  rw [lpReindexEquiv_apply]
  by_cases hk : k = -n - 1
  · subst k
    simp
  · have hpre : -k - 1 ≠ n := by
      intro h
      apply hk
      omega
    simp [lp.single_apply, hpre, hk]

@[simp] theorem ccmHardyFlipUnitary_fourierLp (n : ℤ) :
    ccmHardyFlipUnitary (fourierLp 2 n : CCMCircleL2) =
      (fourierLp 2 (-n - 1) : CCMCircleL2) := by
  change (fourierBasis (T := (1 : ℝ))).repr.symm
      (lpReindexEquiv ccmHardyFlipIndexEquiv
        ((fourierBasis (T := (1 : ℝ))).repr
          (fourierLp 2 n : CCMCircleL2))) = _
  rw [show (fourierLp 2 n : CCMCircleL2) =
      (fourierBasis (T := (1 : ℝ))) n by rw [coe_fourierBasis],
    HilbertBasis.repr_self, lpReindexEquiv_ccmHardyFlip_single,
    HilbertBasis.repr_symm_single, coe_fourierBasis]

private theorem dense_span_ccmPaperCircleFourierBasis :
    Dense ((Submodule.span ℂ (Set.range
      (fourierBasis (T := (1 : ℝ))))) : Set CCMCircleL2) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    (fourierBasis (T := (1 : ℝ))).dense_span]
  rfl

/-- The Hardy flip exchanges the nonnegative and strictly negative circle projections. -/
theorem ccmCircleHardyProjection_ccmHardyFlipUnitary :
    ccmCircleHardyProjection.comp
        ccmHardyFlipUnitary.toLinearIsometry.toContinuousLinearMap =
      ccmHardyFlipUnitary.toLinearIsometry.toContinuousLinearMap.comp
        (1 - ccmCircleHardyProjection) := by
  apply ContinuousLinearMap.ext_on dense_span_ccmPaperCircleFourierBasis
  rintro _ ⟨n, rfl⟩
  rw [coe_fourierBasis]
  change ccmCircleHardyProjection
      (ccmHardyFlipUnitary (fourierLp 2 n : CCMCircleL2)) =
    ccmHardyFlipUnitary
      ((1 - ccmCircleHardyProjection) (fourierLp 2 n : CCMCircleL2))
  rw [ccmHardyFlipUnitary_fourierLp]
  by_cases hn : 0 ≤ n
  · have hflip : ¬0 ≤ -n - 1 := by omega
    rw [ccmCircleHardyProjection_fourierLp, if_neg hflip]
    simp [ccmCircleHardyProjection_fourierLp, hn]
  · have hnlt : n < 0 := lt_of_not_ge hn
    have hflip : 0 ≤ -n - 1 := by omega
    rw [ccmCircleHardyProjection_fourierLp, if_pos hflip]
    simp [ccmCircleHardyProjection_fourierLp, hn]

theorem one_sub_ccmCircleHardyProjection_ccmHardyFlipUnitary :
    (1 - ccmCircleHardyProjection).comp
        ccmHardyFlipUnitary.toLinearIsometry.toContinuousLinearMap =
      ccmHardyFlipUnitary.toLinearIsometry.toContinuousLinearMap.comp
        ccmCircleHardyProjection := by
  apply ContinuousLinearMap.ext
  intro f
  have h := DFunLike.congr_fun ccmCircleHardyProjection_ccmHardyFlipUnitary f
  change ccmCircleHardyProjection (ccmHardyFlipUnitary f) =
    ccmHardyFlipUnitary ((1 - ccmCircleHardyProjection) f) at h
  change ccmHardyFlipUnitary f -
      ccmCircleHardyProjection (ccmHardyFlipUnitary f) =
    ccmHardyFlipUnitary (ccmCircleHardyProjection f)
  rw [h, sub_apply, one_apply_eq_self, map_sub]
  module

/-- Paper-oriented Cayley unitary: nonnegative circle Hardy modes map to the source projection. -/
def ccmPaperCircleLineCayleyUnitary : CCMCircleL2 ≃ₗᵢ[ℂ] SoninL2 :=
  ccmHardyFlipUnitary.trans ccmCircleLineCayleyUnitary

/-- Exact paper-oriented Hardy projection transport. -/
theorem ccmHardyProjection_ccmPaperCircleLineCayleyUnitary :
    ccmHardyProjection.comp
        ccmPaperCircleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap =
      ccmPaperCircleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap.comp
        ccmCircleHardyProjection := by
  apply ContinuousLinearMap.ext
  intro f
  change ccmHardyProjection
      (ccmCircleLineCayleyUnitary (ccmHardyFlipUnitary f)) =
    ccmCircleLineCayleyUnitary
      (ccmHardyFlipUnitary (ccmCircleHardyProjection f))
  have hC := DFunLike.congr_fun ccmHardyProjection_ccmCircleLineCayleyUnitary
    (ccmHardyFlipUnitary f)
  change ccmHardyProjection
      (ccmCircleLineCayleyUnitary (ccmHardyFlipUnitary f)) =
    ccmCircleLineCayleyUnitary
      ((1 - ccmCircleHardyProjection) (ccmHardyFlipUnitary f)) at hC
  rw [hC]
  congr 1
  exact DFunLike.congr_fun one_sub_ccmCircleHardyProjection_ccmHardyFlipUnitary f

/-- The literal multiplier expressed in the paper Hardy circle coordinate. -/
def connesConsaniOnePrimeAddCircleMultiplier (p : Nat.Primes) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  circleLpAddCircleLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap.comp
    ((connesConsaniOnePrimeCircleMultiplier p).comp
      circleLpAddCircleLinearIsometryEquiv.symm.toLinearIsometry.toContinuousLinearMap)

@[simp] theorem circleLpAddCircleLinearIsometryEquiv_multiplicativeHardyProjection
    (f : Lp ℂ 2 circleLebesgue) :
    circleLpAddCircleLinearIsometryEquiv
        (ccmMultiplicativeCircleHardyProjection f) =
      ccmCircleHardyProjection (circleLpAddCircleLinearIsometryEquiv f) := by
  change circleLpAddCircleLinearIsometryEquiv
      (circleLpAddCircleLinearIsometryEquiv.symm
        (ccmCircleHardyProjection (circleLpAddCircleLinearIsometryEquiv f))) = _
  rw [circleLpAddCircleLinearIsometryEquiv.apply_symm_apply]

@[simp] theorem circleLpAddCircleLinearIsometryEquiv_one_sub_multiplicativeHardyProjection
    (f : Lp ℂ 2 circleLebesgue) :
    circleLpAddCircleLinearIsometryEquiv
        ((1 - ccmMultiplicativeCircleHardyProjection) f) =
      (1 - ccmCircleHardyProjection) (circleLpAddCircleLinearIsometryEquiv f) := by
  rw [sub_apply, one_apply_eq_self, map_sub,
    circleLpAddCircleLinearIsometryEquiv_multiplicativeHardyProjection]
  rw [sub_apply, one_apply_eq_self]

@[simp] theorem circleLpAddCircleLinearIsometryEquiv_onePrimeCircleMultiplier
    (p : Nat.Primes) (f : Lp ℂ 2 circleLebesgue) :
    circleLpAddCircleLinearIsometryEquiv
        (connesConsaniOnePrimeCircleMultiplier p f) =
      connesConsaniOnePrimeAddCircleMultiplier p
        (circleLpAddCircleLinearIsometryEquiv f) := by
  change circleLpAddCircleLinearIsometryEquiv
      (connesConsaniOnePrimeCircleMultiplier p f) =
    circleLpAddCircleLinearIsometryEquiv
      (connesConsaniOnePrimeCircleMultiplier p
        (circleLpAddCircleLinearIsometryEquiv.symm
          (circleLpAddCircleLinearIsometryEquiv f)))
  rw [circleLpAddCircleLinearIsometryEquiv.symm_apply_apply]

/-- The literal multiplier expressed in the paper Hardy circle coordinate. -/
def connesConsaniOnePrimePaperCircleMultiplier (p : Nat.Primes) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  ccmHardyFlipUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((connesConsaniOnePrimeAddCircleMultiplier p).comp
      ccmHardyFlipUnitary.toLinearIsometry.toContinuousLinearMap)

/-- Paper-oriented circle Hardy defect `(1-Q) M Q`. -/
def connesConsaniOnePrimePaperCircleDefect (p : Nat.Primes) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  (1 - ccmCircleHardyProjection) *
    connesConsaniOnePrimePaperCircleMultiplier p * ccmCircleHardyProjection

/-- Exact full source-defect transport in the paper Hardy circle coordinate. -/
theorem connesConsaniOnePrimeSourceDefect_ccmPaperCircleLineCayleyUnitary
    (p : Nat.Primes) :
    (connesConsaniOnePrimeSourceDefect p).comp
        ccmPaperCircleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap =
      ccmPaperCircleLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap.comp
        (connesConsaniOnePrimePaperCircleDefect p) := by
  let A : CCMCircleL2 ≃ₗᵢ[ℂ] Lp ℂ 2 circleLebesgue :=
    circleLpAddCircleLinearIsometryEquiv.symm
  have hsource := connesConsaniOnePrimeSourceDefect_circleLineCayleyUnitary p
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun T : Lp ℂ 2 circleLebesgue →L[ℂ] SoninL2 =>
      T (A (ccmHardyFlipUnitary f))) hsource
  change connesConsaniOnePrimeSourceDefect p
      (circleLineCayleyUnitary (A (ccmHardyFlipUnitary f))) = _
  change connesConsaniOnePrimeSourceDefect p
      (circleLineCayleyUnitary (A (ccmHardyFlipUnitary f))) =
    circleLineCayleyUnitary
      (A (ccmHardyFlipUnitary (connesConsaniOnePrimePaperCircleDefect p f)))
  calc
    connesConsaniOnePrimeSourceDefect p
        (circleLineCayleyUnitary (A (ccmHardyFlipUnitary f))) =
      circleLineCayleyUnitary
        (connesConsaniOnePrimeCircleSourceDefect p
          (A (ccmHardyFlipUnitary f))) := by
            change connesConsaniOnePrimeSourceDefect p
                (circleLineCayleyUnitary (A (ccmHardyFlipUnitary f))) =
              circleLineCayleyUnitary
                (connesConsaniOnePrimeCircleSourceDefect p
                  (A (ccmHardyFlipUnitary f))) at h
            exact h
    _ = circleLineCayleyUnitary
        (A (ccmHardyFlipUnitary (connesConsaniOnePrimePaperCircleDefect p f))) := by
      congr 1
      apply A.symm.injective
      dsimp [A]
      rw [circleLpAddCircleLinearIsometryEquiv.apply_symm_apply]
      change circleLpAddCircleLinearIsometryEquiv
          (connesConsaniOnePrimeCircleSourceDefect p
            (circleLpAddCircleLinearIsometryEquiv.symm
              (ccmHardyFlipUnitary f))) =
        ccmHardyFlipUnitary (connesConsaniOnePrimePaperCircleDefect p f)
      symm
      simp only [connesConsaniOnePrimePaperCircleDefect,
        connesConsaniOnePrimePaperCircleMultiplier,
        connesConsaniOnePrimeAddCircleMultiplier,
        connesConsaniOnePrimeCircleSourceDefect, mul_apply_eq_comp,
        ContinuousLinearMap.coe_comp, Function.comp_apply]
      let x : CCMCircleL2 := connesConsaniOnePrimeAddCircleMultiplier p
        (ccmHardyFlipUnitary (ccmCircleHardyProjection f))
      change ccmHardyFlipUnitary
          ((1 - ccmCircleHardyProjection) (ccmHardyFlipUnitary.symm x)) =
        circleLpAddCircleLinearIsometryEquiv
          (ccmMultiplicativeCircleHardyProjection
            (connesConsaniOnePrimeCircleMultiplier p
              ((1 - ccmMultiplicativeCircleHardyProjection)
                (circleLpAddCircleLinearIsometryEquiv.symm
                  (ccmHardyFlipUnitary f)))))
      have hx := DFunLike.congr_fun ccmCircleHardyProjection_ccmHardyFlipUnitary
        (ccmHardyFlipUnitary.symm x)
      change ccmCircleHardyProjection
          (ccmHardyFlipUnitary (ccmHardyFlipUnitary.symm x)) =
        ccmHardyFlipUnitary
          ((1 - ccmCircleHardyProjection) (ccmHardyFlipUnitary.symm x)) at hx
      rw [← hx, ccmHardyFlipUnitary.apply_symm_apply]
      rw [circleLpAddCircleLinearIsometryEquiv_multiplicativeHardyProjection,
        circleLpAddCircleLinearIsometryEquiv_onePrimeCircleMultiplier,
        circleLpAddCircleLinearIsometryEquiv_one_sub_multiplicativeHardyProjection,
        circleLpAddCircleLinearIsometryEquiv.apply_symm_apply]
      have hQc := DFunLike.congr_fun one_sub_ccmCircleHardyProjection_ccmHardyFlipUnitary f
      change (1 - ccmCircleHardyProjection) (ccmHardyFlipUnitary f) =
        ccmHardyFlipUnitary (ccmCircleHardyProjection f) at hQc
      rw [hQc]

end

end RHTower

