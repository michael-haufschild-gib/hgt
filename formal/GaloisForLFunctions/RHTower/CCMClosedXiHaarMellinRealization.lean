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

open CategoryTheory Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

private abbrev Relative :=
  CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule
private abbrev ClosedRange :=
  CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0
private abbrev Section := CCMRationalClassSpaceSection
private abbrev U := CCMRationalProfiniteUnit

local instance cCMClosedXiHaarMellinRealizationLocalInst1 : MeasurableSpace U := borel U
local instance cCMClosedXiHaarMellinRealizationLocalInst2 : BorelSpace U := ⟨rfl⟩
local instance cCMClosedXiHaarMellinRealizationLocalInst3 : ccmRationalProfiniteUnitHaar.IsMulLeftInvariant := by
  change (Measure.haarMeasure
    ccmRationalProfiniteUnitPositiveCompact).IsMulLeftInvariant
  infer_instance
local instance cCMClosedXiHaarMellinRealizationLocalInst4 : ccmRationalProfiniteUnitHaar.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    simpa only [mul_comm] using
      (map_mul_left_eq_self
        (μ := ccmRationalProfiniteUnitHaar) g)

/-! ## Exact spectral covariance -/

/-- Haar--Mellin diagonalizes the exact class-space right action.  This uses the radial Mellin
translation law and right invariance of probability Haar measure on the profinite-unit factor. -/
theorem ccmRationalStrongClassSpaceTrivialMellinLM_rightAction
    (c : Section) (s : ℂ) (f : CCMRationalStrongClassSpace) :
    ccmRationalStrongClassSpaceTrivialMellinLM s
        (ccmRationalStrongClassSpaceRightAction c f) =
      Complex.exp
          (s * (-(ccmRationalPositiveUnitLog c.2) : ℂ)) *
        ccmRationalStrongClassSpaceTrivialMellinLM s f := by
  rw [ccmRationalStrongClassSpaceTrivialMellinLM_apply,
    ccmRationalStrongClassSpaceTrivialMellinLM_apply]
  change
    (∫ u : U,
      _root_.RHTower.deningerMeyerStrongLogMellin
        (_root_.RHTower.deningerMeyerStrongLogFlow
          (-ccmRationalPositiveUnitLog c.2) (f (u * c.1))) s
        ∂ccmRationalProfiniteUnitHaar) = _
  simp_rw [_root_.RHTower.deningerMeyerStrongLogMellin_flow]
  rw [integral_const_mul]
  simp only [ofReal_neg]
  congr 1
  change
    (∫ u : U,
      _root_.RHTower.deningerMeyerStrongLogMellin (f (u * c.1)) s
        ∂ccmRationalProfiniteUnitHaar) =
      ∫ u : U,
        _root_.RHTower.deningerMeyerStrongLogMellin (f u) s
          ∂ccmRationalProfiniteUnitHaar
  exact integral_mul_right_eq_self
    (μ := ccmRationalProfiniteUnitHaar)
    (fun u : U =>
      _root_.RHTower.deningerMeyerStrongLogMellin (f u) s) c.1

/-- Exact nonunital diagonal coordinate intertwines class-space translation. -/
theorem ccmRationalNonunitalStrongDiagonalCoordinate_rightAction
    (c : Section) (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalNonunitalStrongDiagonalCoordinate n
        (ccmRationalNonunitalStrongCyclicRightActionDegree c n x) =
      ccmRationalStrongClassSpaceRightActionLinear c
        (ccmRationalNonunitalStrongDiagonalCoordinate n x) := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  funext b
  rw [ccmRationalNonunitalStrongDiagonalCoordinate_eval]
  change ccmRationalNonunitalStrongDiagonalTrace n
      (cyclicBarAlgHomDegree
        (ccmRationalNonunitalFieldRightActionAlgHom c) n x.1) b = _
  rw [ccmRationalNonunitalStrongDiagonalTrace_rightAction]
  calc
    ccmRationalNonunitalStrongDiagonalTrace n x.1 (b * c) =
        ccmRationalStrongClassSpaceEvalLinear
          (ccmRationalNonunitalStrongDiagonalCoordinate n x) (b * c) :=
      (congrFun
        (ccmRationalNonunitalStrongDiagonalCoordinate_eval n x) (b * c)).symm
    _ = ccmRationalStrongClassSpaceEval
        (ccmRationalStrongClassSpaceRightAction c
          (ccmRationalNonunitalStrongDiagonalCoordinate n x)) b :=
      (ccmRationalStrongClassSpaceEval_rightAction c
        (ccmRationalNonunitalStrongDiagonalCoordinate n x) b).symm
    _ = ccmRationalStrongClassSpaceEvalLinear
        (ccmRationalStrongClassSpaceRightActionLinear c
          (ccmRationalNonunitalStrongDiagonalCoordinate n x)) b := rfl

/-- Every target Haar--Mellin functional is an exact class-space eigencharacter. -/
theorem ccmRationalNonunitalStrongHaarMellinLM_rightAction
    (c : Section) (n : ℕ) (s : ℂ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalNonunitalStrongHaarMellinLM n s
        (ccmRationalNonunitalStrongCyclicRightActionDegree c n x) =
      Complex.exp
          (s * (-(ccmRationalPositiveUnitLog c.2) : ℂ)) *
        ccmRationalNonunitalStrongHaarMellinLM n s x := by
  rw [ccmRationalNonunitalStrongHaarMellinLM,
    LinearMap.comp_apply,
    ccmRationalNonunitalStrongDiagonalCoordinate_rightAction,
    ccmRationalStrongClassSpaceRightActionLinear]
  exact ccmRationalStrongClassSpaceTrivialMellinLM_rightAction c s
    (ccmRationalNonunitalStrongDiagonalCoordinate n x)

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

/-- Spectral multiplier of the literal Lefschetz correspondence at one Xi support point. -/
def ccmClosedXiLefschetzMultiplier
    (c : Section) (rho : _root_.RHTower.XiDivisorSupport) : ℂ :=
  Complex.exp
    ((rho : ℂ) * (-(ccmRationalPositiveUnitLog c.2) : ℂ))

/-- Every nonzero Xi Haar--Mellin character on the literal closed quotient is an exact
eigencharacter of the descended Lefschetz correspondence. -/
theorem ccmClosedXiSupportHaarMellinLM_lefschetz
    (c : Section) (rho : _root_.RHTower.XiDivisorSupport)
    (x : Relative.simplicial.degree 0) :
    ccmClosedXiSupportHaarMellinLM rho
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) x) =
      ccmClosedXiLefschetzMultiplier c rho *
        ccmClosedXiSupportHaarMellinLM rho x := by
  obtain ⟨y, rfl⟩ := ClosedRange.mkQ_surjective x
  rw [ccmRationalAdelicClosedNonunitalStrongLefschetz_mkQ,
    ccmClosedXiSupportHaarMellinLM_mkQ,
    ccmClosedXiSupportHaarMellinLM_mkQ,
    ccmRationalNonunitalStrongHaarMellinLM_rightAction]
  rfl

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

/-- Multiplicity-exact spectral evaluation intertwines Lefschetz action with pointwise Mellin
multiplication on every Xi zero copy. -/
theorem ccmClosedXiSpectralEvaluation_lefschetz
    (c : Section) (x : Relative.simplicial.degree 0)
    (q : _root_.RHTower.XiZeroCopy) :
    ccmClosedXiSpectralEvaluation
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) x) q =
      ccmClosedXiLefschetzMultiplier c q.1 *
        ccmClosedXiSpectralEvaluation x q := by
  exact ccmClosedXiSupportHaarMellinLM_lefschetz c q.1 x

/-- Function-valued intertwining law for the full multiplicity packet. -/
theorem ccmClosedXiSpectralEvaluationLM_lefschetz
    (c : Section) (x : Relative.simplicial.degree 0) :
    ccmClosedXiSpectralEvaluationLM
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) x) =
      fun q : _root_.RHTower.XiZeroCopy =>
        ccmClosedXiLefschetzMultiplier c q.1 *
          ccmClosedXiSpectralEvaluationLM x q := by
  funext q
  exact ccmClosedXiSpectralEvaluation_lefschetz c x q

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

/-- Non-formal spectral content of phase cancellation: the corrected Clifford product acts on
every multiplicity copy by the actual Haar--Mellin multiplier of the product correspondence. -/
theorem ccmClosedXiSpectralEvaluation_clifford_corrected_product
    (c d : Section) (x : Relative.simplicial.degree 0)
    (q : _root_.RHTower.XiZeroCopy) :
    ccmClosedXiSpectralEvaluation
        ((ccmRationalAdelicClosedNonunitalStrongCliffordCotransgression c).toHom.simplicial.app
          (.op (.mk 0))
          ((ccmRationalAdelicClosedNonunitalStrongCliffordTransgression d).toHom.simplicial.app
            (.op (.mk 0)) x)) q =
      ccmClosedXiLefschetzMultiplier (c * d) q.1 *
        ccmClosedXiSpectralEvaluation x q := by
  rw [ccmRationalAdelicClosedNonunitalStrongClifford_corrected_product_degree]
  exact ccmClosedXiSpectralEvaluation_lefschetz (c * d) x q

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
