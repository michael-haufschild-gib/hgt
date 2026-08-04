import GaloisForLFunctions.RHTower.CCMCliffordWeilProduct
import GaloisForLFunctions.RHTower.CCMRationalAdelicHaarMellinBoundaryLaw

/-!
# Closed CCM--Xi Haar--Mellin realization

Every support point of the actual Xi divisor defines a nonzero Haar--Mellin character on degree
zero of the literal closed rational CCM quotient.  Pullback to multiplicity copies gives an exact
quotient-side Weil pairing.  The final theorem evaluates the already-constructed two-sided
Clifford product by that pairing and identifies it term-for-term with the multiplicity-exact Weil
polarization whenever the two spectral packets are represented by test functions.

No positivity, RH, zero simplicity, enumeration, or spectral-range hypothesis is used.
-/

noncomputable section

open CategoryTheory Complex

namespace GaloisForLFunctions.RHTower

private abbrev Relative :=
  CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule
private abbrev ClosedRange :=
  CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0
private abbrev Section := CCMRationalClassSpaceSection

/-- Every actual Xi-divisor support point is a non-pole zeta zero. -/
theorem ccmClosedXiSupport_riemannZeta_eq_zero
    (rho : _root_.RHTower.XiDivisorSupport) :
    riemannZeta (rho : ℂ) = 0 := by
  have hstrip := _root_.RHTower.xi_divisor_support_re_mem_open_unit rho
  have hrhoOne : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  exact (_root_.RHTower.xi_eq_zero_iff hstrip.1 hrhoOne).mp
    (_root_.RHTower.xi_eq_zero_of_mem_divisor_support rho)

/-- Haar--Mellin evaluation at one actual Xi support point, descended through the literal closed
restriction quotient. -/
def ccmClosedXiSupportHaarMellinLM
    (rho : _root_.RHTower.XiDivisorSupport) :
    Relative.simplicial.degree 0 →ₗ[ℂ] ℂ :=
  ClosedRange.liftQ
    (ccmRationalNonunitalStrongHaarMellinLM 0 (rho : ℂ))
    (ccmRationalAdelicClosedNonunitalStrongRestrictionRange_le_mellinKer
      (rho : ℂ)
      (fun x =>
        ccmRationalAdelicReducedNonunitalStrongHaarMellin_zero_at_zeta_zero
          (_root_.RHTower.xi_divisor_support_re_mem_open_unit rho).1
          (_root_.RHTower.xiDivisorSupport_ne_one rho)
          (ccmClosedXiSupport_riemannZeta_eq_zero rho) x))

@[simp]
theorem ccmClosedXiSupportHaarMellinLM_mkQ
    (rho : _root_.RHTower.XiDivisorSupport)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree 0) :
    ccmClosedXiSupportHaarMellinLM rho (ClosedRange.mkQ x) =
      ccmRationalNonunitalStrongHaarMellinLM 0 (rho : ℂ) x := by
  exact LinearMap.congr_fun
    (Submodule.liftQ_mkQ ClosedRange
      (ccmRationalNonunitalStrongHaarMellinLM 0 (rho : ℂ))
      (ccmRationalAdelicClosedNonunitalStrongRestrictionRange_le_mellinKer
        (rho : ℂ)
        (fun y =>
          ccmRationalAdelicReducedNonunitalStrongHaarMellin_zero_at_zeta_zero
            (_root_.RHTower.xi_divisor_support_re_mem_open_unit rho).1
            (_root_.RHTower.xiDivisorSupport_ne_one rho)
            (ccmClosedXiSupport_riemannZeta_eq_zero rho) y))) x

/-- Every Xi support character is genuinely nonzero on the literal closed quotient. -/
theorem ccmClosedXiSupportHaarMellinLM_ne_zero
    (rho : _root_.RHTower.XiDivisorSupport) :
    ccmClosedXiSupportHaarMellinLM rho ≠ 0 := by
  intro hzero
  have hvalue := LinearMap.congr_fun hzero
    (ClosedRange.mkQ ccmRationalNonunitalLogGaussianStrongChain)
  rw [ccmClosedXiSupportHaarMellinLM_mkQ] at hvalue
  exact ccmRationalNonunitalStrongHaarMellinLM_logGaussian_ne_zero
    (rho : ℂ) (by simpa using hvalue)

/-- Multiplicity-exact spectral evaluation of a degree-zero literal closed CCM class. -/
def ccmClosedXiSpectralEvaluation
    (x : Relative.simplicial.degree 0)
    (q : _root_.RHTower.XiZeroCopy) : ℂ :=
  ccmClosedXiSupportHaarMellinLM q.1 x

/-- Spectral evaluation as one linear map into the full multiplicity-copy packet. -/
def ccmClosedXiSpectralEvaluationLM :
    Relative.simplicial.degree 0 →ₗ[ℂ]
      (_root_.RHTower.XiZeroCopy → ℂ) where
  toFun := ccmClosedXiSpectralEvaluation
  map_add' x y := by
    funext q
    exact map_add (ccmClosedXiSupportHaarMellinLM q.1) x y
  map_smul' c x := by
    funext q
    exact map_smul (ccmClosedXiSupportHaarMellinLM q.1) c x

@[simp]
theorem ccmClosedXiSpectralEvaluationLM_apply
    (x : Relative.simplicial.degree 0)
    (q : _root_.RHTower.XiZeroCopy) :
    ccmClosedXiSpectralEvaluationLM x q =
      ccmClosedXiSpectralEvaluation x q :=
  rfl

/-- Literal closed-quotient pairing obtained by critical-line reflection of the complete Xi
evaluation packet. -/
def ccmClosedXiWeilPairing
    (x y : Relative.simplicial.degree 0) : ℂ :=
  ∑' q : _root_.RHTower.XiZeroCopy,
    ccmClosedXiSpectralEvaluation x q *
      (starRingEnd ℂ)
        (ccmClosedXiSpectralEvaluation y
          (_root_.RHTower.xiZeroCopyLineConjEquiv q))

/-- Exact numerical realization theorem: quotient-side critical-reflection pairing is the actual
multiplicity-exact Xi Weil polarization for every pair of represented spectral packets. -/
theorem ccmClosedXiWeilPairing_eq_xiWeilPolarization
    (x y : Relative.simplicial.degree 0)
    (F G : ℂ → ℂ)
    (hF : ∀ q : _root_.RHTower.XiZeroCopy,
      ccmClosedXiSpectralEvaluation x q =
        F (_root_.RHTower.xiSpectralPoint q))
    (hG : ∀ q : _root_.RHTower.XiZeroCopy,
      ccmClosedXiSpectralEvaluation y q =
        G (_root_.RHTower.xiSpectralPoint q)) :
    ccmClosedXiWeilPairing x y =
      _root_.RHTower.xiWeilPolarization F G := by
  unfold ccmClosedXiWeilPairing _root_.RHTower.xiWeilPolarization
  apply tsum_congr
  intro q
  rw [hF q, hG (_root_.RHTower.xiZeroCopyLineConjEquiv q),
    _root_.RHTower.xiSpectralPoint_lineConj]
  rfl

/-- Numerical pairing of the genuine two-sided Clifford-corrected cyclic endomorphism product on
degree zero of the literal closed CCM quotient. -/
def ccmClosedXiCliffordProductPairing
    (c d : Section) (x y : Relative.simplicial.degree 0) : ℂ :=
  ccmClosedXiWeilPairing
    ((ccmRationalAdelicClosedNonunitalStrongCliffordCotransgression c).toHom.simplicial.app
      (.op (.mk 0))
      ((ccmRationalAdelicClosedNonunitalStrongCliffordTransgression d).toHom.simplicial.app
        (.op (.mk 0)) x)) y

/-- Clifford phases cancel inside the quotient before numerical evaluation. -/
theorem ccmClosedXiCliffordProductPairing_eq_lefschetz
    (c d : Section) (x y : Relative.simplicial.degree 0) :
    ccmClosedXiCliffordProductPairing c d x y =
      ccmClosedXiWeilPairing
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz (c * d)).simplicial.app
          (.op (.mk 0)) x) y := by
  rw [ccmClosedXiCliffordProductPairing,
    ccmRationalAdelicClosedNonunitalStrongClifford_corrected_product_degree]

/-- Full bridge theorem: the numerical pairing of the literal closed-CCM Clifford product is
exactly the multiplicity-sensitive Weil form of its two realized evaluation packets. -/
theorem ccmClosedXiCliffordProductPairing_eq_xiWeilPolarization
    (c d : Section) (x y : Relative.simplicial.degree 0)
    (F G : ℂ → ℂ)
    (hF : ∀ q : _root_.RHTower.XiZeroCopy,
      ccmClosedXiSpectralEvaluation
          ((ccmRationalAdelicClosedNonunitalStrongLefschetz (c * d)).simplicial.app
            (.op (.mk 0)) x) q =
        F (_root_.RHTower.xiSpectralPoint q))
    (hG : ∀ q : _root_.RHTower.XiZeroCopy,
      ccmClosedXiSpectralEvaluation y q =
        G (_root_.RHTower.xiSpectralPoint q)) :
    ccmClosedXiCliffordProductPairing c d x y =
      _root_.RHTower.xiWeilPolarization F G := by
  rw [ccmClosedXiCliffordProductPairing_eq_lefschetz]
  exact ccmClosedXiWeilPairing_eq_xiWeilPolarization _ _ F G hF hG

end GaloisForLFunctions.RHTower
