import GaloisForLFunctions.RHTower.CCMRationalAdelicTensorClassSectionContinuity
import GaloisForLFunctions.RHTower.CCMRationalContinuousTraceNormField

/-!
# Continuous trace-norm fields for the full rational crossed product

Finite-support induction assembles the continuous fixed-label Morita fields into a nonunital
algebra homomorphism from the full rational algebraic crossed product to continuous fields of
genuine Schatten-`1` operators on the actual class-space section.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev H := CCMRationalMoritaHilbert
private abbrev Op := H →L[ℂ] H
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct

private theorem classSectionReal_ne_zero
    (s : CCMRationalClassSpaceSection) :
    ((s.2.val : NNReal) : ℝ) ≠ 0 := by
  have hspos : 0 < ((s.2.val : NNReal) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr s.2.ne_zero : 0 < s.2.val)
  exact hspos.ne'

/-- Pointwise exact trace-norm representation of the crossed product over the class section. -/
def ccmRationalAdelicCrossedTraceNormClassSection
    (F : Crossed) (s : CCMRationalClassSpaceSection) :
    CCMRationalMoritaTraceNormOperator :=
  ccmRationalAdelicMoritaTraceNormHom
    (classSectionReal_ne_zero s) s.1.val F

@[simp]
theorem ccmRationalAdelicCrossedTraceNormClassSection_zero :
    ccmRationalAdelicCrossedTraceNormClassSection 0 = 0 := by
  funext s
  exact map_zero _

@[simp]
theorem ccmRationalAdelicCrossedTraceNormClassSection_add
    (F G : Crossed) :
    ccmRationalAdelicCrossedTraceNormClassSection (F + G) =
      ccmRationalAdelicCrossedTraceNormClassSection F +
        ccmRationalAdelicCrossedTraceNormClassSection G := by
  funext s
  exact map_add _ F G

@[simp]
theorem ccmRationalAdelicCrossedTraceNormClassSection_smul
    (z : ℂ) (F : Crossed) :
    ccmRationalAdelicCrossedTraceNormClassSection (z • F) =
      z • ccmRationalAdelicCrossedTraceNormClassSection F := by
  funext s
  exact map_smul _ z F

@[simp]
theorem ccmRationalAdelicCrossedTraceNormClassSection_mul
    (F G : Crossed) :
    ccmRationalAdelicCrossedTraceNormClassSection (F * G) =
      ccmRationalAdelicCrossedTraceNormClassSection F *
        ccmRationalAdelicCrossedTraceNormClassSection G := by
  funext s
  exact map_mul _ F G

/-- A single crossed-product sector is the previously constructed continuous fixed-label
Bruhat-tensor field. -/
theorem ccmRationalAdelicCrossedTraceNormClassSection_single
    (k : Scale) (t : Core) :
    ccmRationalAdelicCrossedTraceNormClassSection (Finsupp.single k t) =
      ccmRationalAdelicBruhatTensorTraceNormClassSection t k.val := by
  funext s
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  change ccmRationalAdelicMoritaRepresentation
      (classSectionReal_ne_zero s) s.1.val (Finsupp.single k t) =
    ((ccmRationalAdelicBruhatTensorTraceNormClassSection t k.val s).toTraceClass : Op)
  rw [ccmRationalAdelicMoritaRepresentation_single]
  simpa [ccmRationalAdelicMoritaMonomial] using
    (ccmRationalAdelicBruhatTensorTraceNormClassSection_toOperator
      t k.val s).symm

/-- Every algebraic crossed-product element gives a continuous genuine trace-norm field. -/
theorem ccmRationalAdelicCrossedTraceNormClassSection_continuous
    (F : Crossed) :
    Continuous (ccmRationalAdelicCrossedTraceNormClassSection F) := by
  induction F using Finsupp.induction with
  | zero =>
      rw [ccmRationalAdelicCrossedTraceNormClassSection_zero]
      exact continuous_const
  | @single_add k t F hkt ht hF =>
      rw [ccmRationalAdelicCrossedTraceNormClassSection_add,
        ccmRationalAdelicCrossedTraceNormClassSection_single]
      exact (ccmRationalAdelicBruhatTensorTraceNormClassSection_continuous
        t k.val).add hF

/-- Continuous operator-valued field associated with a crossed-product element. -/
def ccmRationalAdelicCrossedContinuousTraceNormOperatorField
    (F : Crossed) :
    C(CCMRationalClassSpaceSection, CCMRationalMoritaTraceNormOperator) :=
  ⟨ccmRationalAdelicCrossedTraceNormClassSection F,
    ccmRationalAdelicCrossedTraceNormClassSection_continuous F⟩

/-- Full crossed-product representation into continuous trace-norm operator fields. -/
def ccmRationalAdelicCrossedContinuousTraceNormHom :
    Crossed →ₙₐ[ℂ]
      C(CCMRationalClassSpaceSection, CCMRationalMoritaTraceNormOperator) where
  toFun := ccmRationalAdelicCrossedContinuousTraceNormOperatorField
  map_zero' := by
    apply ContinuousMap.ext
    intro s
    exact congrFun ccmRationalAdelicCrossedTraceNormClassSection_zero s
  map_add' F G := by
    apply ContinuousMap.ext
    intro s
    exact congrFun
      (ccmRationalAdelicCrossedTraceNormClassSection_add F G) s
  map_smul' z F := by
    apply ContinuousMap.ext
    intro s
    exact congrFun
      (ccmRationalAdelicCrossedTraceNormClassSection_smul z F) s
  map_mul' F G := by
    apply ContinuousMap.ext
    intro s
    exact congrFun
      (ccmRationalAdelicCrossedTraceNormClassSection_mul F G) s

end RHTower
end GaloisForLFunctions
