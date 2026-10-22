import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEndpointReal
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicTargetReal
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicReducedStrongCyclicHom
import GaloisForLFunctions.RHTower.CCM.CCMRationalWeightedShiftReal
import GaloisForLFunctions.RHTower.KRealCyclicBarAlgHom

/-!
# Real equivariance of exact adelic restriction

Quaternionic conjugation of the actual Morita representation is exactly the
sign-reflection involution on the rational adelic crossed product.  The
identity is proved first for orbit coefficients, then for weighted-shift
monomials, the full finite-support crossed product, both unitizations, and the
continuous trace-norm field.  Cyclic-bar functoriality finally restricts this
identity to the literal simultaneous endpoint kernel and the exact CCM strong
target.
-/

noncomputable section

open ContinuousLinearMap
open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra
private abbrev H := CCMRationalMoritaHilbert
private abbrev Op := H →L[ℂ] H

local instance restrictionRealDecidableEqScale : DecidableEq Scale :=
  Classical.decEq _

/-- Reflection of an adelic Bruhat tensor is conjugation after the antipodal
rational-orbit permutation. -/
theorem ccmRationalAdelicBruhatTensorOrbit_real
    (t : Core) (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    ccmRationalAdelicBruhatTensorOrbit
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma t)
        bInf b q =
      star (ccmRationalAdelicBruhatTensorOrbit t bInf b (-q)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f φ =>
      simp only [ccmRationalAdelicBruhatSimpleTensor_sigma_tmul,
        ccmRationalAdelicBruhatTensorOrbit_tmul,
        ccmRationalAdelicBruhatPureTensorOrbit,
        ccmRationalArchimedeanSchwartzReflection_apply,
        ccmRationalFiniteBruhatReflection_apply]
      calc
        star (f (-(bInf * (q : ℝ)))) *
              star (φ.1 (-(algebraMap ℚ CCMRationalFiniteAdele q * b))) =
            star (f (bInf * ((-q : ℚ) : ℝ))) *
              star (φ.1 (algebraMap ℚ CCMRationalFiniteAdele (-q) * b)) := by
          congr 1
          · congr 1
            push_cast
            ring
          · congr 2
            rw [map_neg]
            push_cast
            ring
        _ = star (f (bInf * ((-q : ℚ) : ℝ)) *
              φ.1 (algebraMap ℚ CCMRationalFiniteAdele (-q) * b)) := by
          exact (map_mul (starRingEnd ℂ) _ _).symm
  | add x y hx hy =>
      rw [map_add, ccmRationalAdelicBruhatTensorOrbit_add,
        ccmRationalAdelicBruhatTensorOrbit_add, hx, hy, star_add]

/-- Source monomial reflection is precisely the coefficient twist appearing
under quaternionic conjugation of weighted shifts. -/
theorem ccmRationalAdelicBruhatTensorOrbitCoefficient_monomialRealTwist
    (k : Scale) (t : Core) (bInf : ℝ)
    (b : CCMRationalFiniteAdeleˣ) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorOrbitCoefficient
        (ccmRationalAdelicMonomialRealTwist k t) bInf b q =
      ccmRationalMoritaCoefficientRealTwist k.val
        (ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b) q := by
  rw [ccmRationalAdelicMonomialRealTwist,
    show ccmRationalAdelicBruhatTensorOrbitCoefficient
        (ccmRationalUnitSign k.val •
          ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma t) bInf b q =
      ccmRationalUnitSign k.val *
        ccmRationalAdelicBruhatTensorOrbit
          (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma t)
          bInf b (q : ℚ) by
      exact ccmRationalAdelicBruhatTensorOrbit_smul _ _ _ _ _]
  rw [ccmRationalAdelicBruhatTensorOrbit_real]
  rfl

/-- Exact operator-level Real covariance of one actual CCM monomial. -/
theorem ccmRationalAdelicMoritaMonomial_real
    (k : Scale) (t : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    ccmRationalMoritaHilbertOperatorRealStructure
        (ccmRationalAdelicMoritaMonomial t hbInf b k) =
      ccmRationalAdelicMoritaMonomial
        (ccmRationalAdelicMonomialRealTwist k t) hbInf b k := by
  change ccmRationalMoritaHilbertOperatorRealStructure
      (ccmRationalMoritaWeightedShift
        (ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b) k.val
        (ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound t bInf b)
        (ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound_nonneg t bInf b)
        (ccmRationalAdelicBruhatTensorOrbitCoefficient_norm_le_lOneBound
          t hbInf b)) = _
  rw [ccmRationalMoritaWeightedShift_real_equivariant]
  apply ContinuousLinearMap.ext
  intro f
  ext q
  simp only [ccmRationalAdelicMoritaMonomial,
    ccmRationalAdelicBruhatTensorWeightedShift,
    ccmRationalMoritaWeightedShift_apply]
  rw [ccmRationalAdelicBruhatTensorOrbitCoefficient_monomialRealTwist]

/-- Quaternionic conjugation of the full finite-support representation equals
the coefficientwise adelic Real involution. -/
theorem ccmRationalAdelicMoritaRepresentation_real
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (F : Crossed) :
    ccmRationalMoritaHilbertOperatorRealStructure
        (ccmRationalAdelicMoritaRepresentation hbInf b F) =
      ccmRationalAdelicMoritaRepresentation hbInf b
        (ccmRationalAdelicCrossedProductRealStructure F) := by
  induction F using Finsupp.induction with
  | zero => exact map_zero ccmRationalMoritaHilbertOperatorRealIsometry
  | @single_add k t F hkt ht hF =>
      rw [ccmRationalAdelicMoritaRepresentation_add,
        ccmRationalMoritaHilbertOperatorRealStructure_add,
        ccmRationalAdelicCrossedProductRealStructure_add,
        ccmRationalAdelicMoritaRepresentation_add,
        ccmRationalAdelicMoritaRepresentation_single,
        ccmRationalAdelicCrossedProductRealStructure_single,
        ccmRationalAdelicMoritaRepresentation_single,
        ccmRationalAdelicMoritaMonomial_real, hF]

/-- Real covariance in the exact trace-norm ideal. -/
theorem ccmRationalAdelicMoritaTraceNormHom_real
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (F : Crossed) :
    ccmRationalMoritaTraceNormRealStructure
        (ccmRationalAdelicMoritaTraceNormHom hbInf b F) =
      ccmRationalAdelicMoritaTraceNormHom hbInf b
        (ccmRationalAdelicCrossedProductRealStructure F) := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  exact ccmRationalAdelicMoritaRepresentation_real hbInf b F

/-- Real covariance after the algebraic and normed minimal unitizations. -/
theorem ccmRationalAdelicMoritaTraceNormL1UnitizedHom_real
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (x : Source) :
    ccmRationalMoritaTraceNormL1RealStructure
        (ccmRationalAdelicMoritaTraceNormL1UnitizedHom hbInf b x) =
      ccmRationalAdelicMoritaTraceNormL1UnitizedHom hbInf b
        (ccmRationalAdelicSourceRealStructure x) := by
  apply WithLp.ofLp_injective
  change ccmRationalMoritaTraceNormUnitizedRealStructure
      (ccmRationalAdelicMoritaTraceNormUnitizedHom hbInf b x) =
    ccmRationalAdelicMoritaTraceNormUnitizedHom hbInf b
      (ccmRationalAdelicSourceRealStructure x)
  apply Unitization.ext
  · simp [ccmRationalAdelicMoritaTraceNormUnitizedHom,
      Unitization.lift_apply, Unitization.algebraMap_eq_inl]
  · simp [ccmRationalAdelicMoritaTraceNormUnitizedHom,
      Unitization.lift_apply, Unitization.algebraMap_eq_inl,
      ccmRationalAdelicMoritaTraceNormHom_real]

/-- Exact full-source continuous-field restriction is Real-equivariant. -/
theorem ccmRationalAdelicSourceContinuousTraceNormFieldHom_real
    (x : Source) :
    ccmRationalContinuousTraceNormFieldReal
        (ccmRationalAdelicSourceContinuousTraceNormFieldHom x) =
      ccmRationalAdelicSourceContinuousTraceNormFieldHom
        (ccmRationalAdelicSourceRealStructure x) := by
  apply ContinuousMap.ext
  intro s
  rw [ccmRationalContinuousTraceNormFieldReal_apply,
    ccmRationalAdelicSourceContinuousTraceNormFieldHom_apply,
    ccmRationalAdelicSourceContinuousTraceNormFieldHom_apply]
  exact ccmRationalAdelicMoritaTraceNormL1UnitizedHom_real _ s.1.val x

/-- Full cyclic-bar restriction as an even Real cyclic morphism. -/
def ccmRationalAdelicSourceContinuousTraceNormFieldCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicSourceCyclicKReal
      (cyclicBarKReal ccmRationalContinuousTraceNormFieldKRealAlgebra) :=
  cyclicBarAlgHomKRealHom
    ccmRationalAdelicSourceKRealAlgebra
    ccmRationalContinuousTraceNormFieldKRealAlgebra
    ccmRationalAdelicSourceContinuousTraceNormFieldHom
    ccmRationalAdelicSourceContinuousTraceNormFieldHom_real

/-- **Exact Real CCM restriction.** The literal reduced adelic source maps
Real-equivariantly to the literal continuous-field/strong-diagonal target. -/
def ccmRationalAdelicReducedStrongCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicReducedSourceCyclicKReal
      ccmRationalStrongCyclicTargetKReal where
  toHom := ccmRationalAdelicReducedStrongCyclicHom
  real_naturality n x := by
    apply Subtype.ext
    exact ccmRationalAdelicSourceContinuousTraceNormFieldCyclicKRealHom.real_naturality
      n x.1.1

end GaloisForLFunctions.RHTower
