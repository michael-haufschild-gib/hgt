import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicClassSectionLOneContinuity

/-!
# Full Bruhat-tensor trace-norm fields on the rational class section

Joint `ℓ1` continuity for pure tensors extends by algebraic tensor-product induction to every
element of the rational adelic Bruhat tensor core.  The exact `ℓ1`--Schatten-`1` isometry then
produces a continuous trace-norm Morita operator field for every fixed crossed-product label.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev H := CCMRationalMoritaHilbert
private abbrev Op := H →L[ℂ] H

/-- Arbitrary Bruhat-tensor orbit coefficient over the actual class-space section. -/
def ccmRationalAdelicBruhatTensorOrbitLOneClassSection
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (s : CCMRationalClassSpaceSection) :
    CCMRationalMoritaLOneCoefficient :=
  ccmRationalAdelicBruhatTensorOrbitLOne t
    (by
      have hspos : 0 < ((s.2.val : NNReal) : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr s.2.ne_zero : 0 < s.2.val)
      exact hspos.ne')
    s.1.val

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbitLOneClassSection_apply
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (s : CCMRationalClassSpaceSection) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorOrbitLOneClassSection t s q =
      ccmRationalAdelicBruhatTensorOrbitCoefficient t
        ((s.2.val : NNReal) : ℝ) s.1.val q :=
  rfl

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbitLOneClassSection_zero :
    ccmRationalAdelicBruhatTensorOrbitLOneClassSection 0 = 0 := by
  funext s
  ext q
  simp [ccmRationalAdelicBruhatTensorOrbitLOneClassSection,
    ccmRationalAdelicBruhatTensorOrbitCoefficient,
    ccmRationalAdelicBruhatTensorOrbit]

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbitLOneClassSection_add
    (t u : CCMRationalAdelicBruhatSimpleTensor) :
    ccmRationalAdelicBruhatTensorOrbitLOneClassSection (t + u) =
      ccmRationalAdelicBruhatTensorOrbitLOneClassSection t +
        ccmRationalAdelicBruhatTensorOrbitLOneClassSection u := by
  funext s
  ext q
  simp [ccmRationalAdelicBruhatTensorOrbitLOneClassSection,
    ccmRationalAdelicBruhatTensorOrbitCoefficient,
    ccmRationalAdelicBruhatTensorOrbit]

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbitLOneClassSection_tmul
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalAdelicBruhatTensorOrbitLOneClassSection (f ⊗ₜ[ℂ] φ) =
      ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection f φ := by
  funext s
  ext q
  rfl

/-- **Full algebraic Bruhat-tensor `ℓ1` landing.** -/
theorem ccmRationalAdelicBruhatTensorOrbitLOneClassSection_continuous
    (t : CCMRationalAdelicBruhatSimpleTensor) :
    Continuous (ccmRationalAdelicBruhatTensorOrbitLOneClassSection t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [ccmRationalAdelicBruhatTensorOrbitLOneClassSection_zero]
      exact continuous_const
  | tmul f φ =>
      rw [ccmRationalAdelicBruhatTensorOrbitLOneClassSection_tmul]
      exact ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection_continuous f φ
  | add t u ht hu =>
      rw [ccmRationalAdelicBruhatTensorOrbitLOneClassSection_add]
      exact ht.add hu

/-- Trace-norm Morita operator field for one algebraic Bruhat tensor and fixed scaling label. -/
def ccmRationalAdelicBruhatTensorTraceNormClassSection
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (k : CCMRationalUnit)
    (s : CCMRationalClassSpaceSection) :
    CCMRationalMoritaTraceNormOperator :=
  ccmRationalMoritaLOneWeightedShift k
    (ccmRationalAdelicBruhatTensorOrbitLOneClassSection t s)

/-- Its underlying operator is exactly the pre-existing fixed-base adelic weighted shift. -/
theorem ccmRationalAdelicBruhatTensorTraceNormClassSection_toOperator
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (k : CCMRationalUnit)
    (s : CCMRationalClassSpaceSection) :
    ((ccmRationalAdelicBruhatTensorTraceNormClassSection t k s).toTraceClass : Op) =
      ccmRationalAdelicBruhatTensorWeightedShift t
        (by
          have hspos : 0 < ((s.2.val : NNReal) : ℝ) := by
            exact_mod_cast (pos_iff_ne_zero.mpr s.2.ne_zero : 0 < s.2.val)
          exact hspos.ne')
        s.1.val k := by
  symm
  apply ccmRationalAdelicBruhatTensorWeightedShift_eq_lOne

/-- Every fixed-label algebraic Bruhat tensor produces a continuous genuine trace-norm field. -/
theorem ccmRationalAdelicBruhatTensorTraceNormClassSection_continuous
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (k : CCMRationalUnit) :
    Continuous (ccmRationalAdelicBruhatTensorTraceNormClassSection t k) :=
  (ccmRationalMoritaLOneWeightedShiftLinearIsometry k).continuous.comp
    (ccmRationalAdelicBruhatTensorOrbitLOneClassSection_continuous t)

end RHTower
end GaloisForLFunctions
