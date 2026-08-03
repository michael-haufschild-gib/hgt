import GaloisForLFunctions.RHTower.CCMRationalAdelicCrossedContinuousTraceNormField

/-!
# Full rational CCM source landing in continuous trace-norm fields

The continuous crossed-product Schatten-`1` representation is inserted isometrically into the
minimal `ℓ1` unitization and extended by the universal property of unitization.  This constructs
an actual algebra homomorphism from the exact rational CCM cyclic source to the continuous
trace-norm field algebra used by the strong cyclic target.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra
private abbrev Ideal := CCMRationalMoritaTraceNormOperator
private abbrev L1Unit := CCMRationalMoritaTraceNormL1Unitization
private abbrev OperatorField :=
  C(CCMRationalClassSpaceSection, CCMRationalMoritaTraceNormOperator)

/-- Canonical nonunital algebra inclusion of the trace-norm ideal into its `ℓ1` unitization. -/
def ccmRationalMoritaTraceNormL1InrHom :
    Ideal →ₙₐ[ℂ] L1Unit :=
  ((WithLp.unitizationAlgEquiv ℂ).symm.toAlgHom.toNonUnitalAlgHom).comp
    (Unitization.inrNonUnitalAlgHom ℂ Ideal)

@[simp]
theorem ccmRationalMoritaTraceNormL1InrHom_apply (T : Ideal) :
    ccmRationalMoritaTraceNormL1InrHom T =
      WithLp.toLp 1 (T : Unitization ℂ Ideal) :=
  rfl

/-- Pointwise ideal inclusion on continuous trace-norm operator fields. -/
def ccmRationalContinuousTraceNormOperatorFieldInr
    (F : OperatorField) : CCMRationalContinuousTraceNormField where
  toFun s := ccmRationalMoritaTraceNormL1InrHom (F s)
  continuous_toFun := by
    change Continuous (fun s =>
      WithLp.toLp 1 ((F s : Ideal) : Unitization ℂ Ideal))
    exact WithLp.unitization_isometry_inr.continuous.comp F.continuous

@[simp]
theorem ccmRationalContinuousTraceNormOperatorFieldInr_apply
    (F : OperatorField) (s : CCMRationalClassSpaceSection) :
    ccmRationalContinuousTraceNormOperatorFieldInr F s =
      ccmRationalMoritaTraceNormL1InrHom (F s) :=
  rfl

/-- Ideal inclusion as a nonunital algebra homomorphism on continuous fields. -/
def ccmRationalContinuousTraceNormOperatorFieldInrHom :
    OperatorField →ₙₐ[ℂ] CCMRationalContinuousTraceNormField where
  toFun := ccmRationalContinuousTraceNormOperatorFieldInr
  map_zero' := by
    apply ContinuousMap.ext
    intro s
    exact map_zero ccmRationalMoritaTraceNormL1InrHom
  map_add' F G := by
    apply ContinuousMap.ext
    intro s
    exact map_add ccmRationalMoritaTraceNormL1InrHom (F s) (G s)
  map_smul' z F := by
    apply ContinuousMap.ext
    intro s
    exact map_smul ccmRationalMoritaTraceNormL1InrHom z (F s)
  map_mul' F G := by
    apply ContinuousMap.ext
    intro s
    exact map_mul ccmRationalMoritaTraceNormL1InrHom (F s) (G s)

/-- Crossed-product representation directly into continuous `ℓ1`-unitized fields. -/
def ccmRationalAdelicCrossedContinuousTraceNormL1Hom :
    Crossed →ₙₐ[ℂ] CCMRationalContinuousTraceNormField :=
  ccmRationalContinuousTraceNormOperatorFieldInrHom.comp
    ccmRationalAdelicCrossedContinuousTraceNormHom

/-- **Exact full-source continuous-field landing.** -/
def ccmRationalAdelicSourceContinuousTraceNormFieldHom :
    Source →ₐ[ℂ] CCMRationalContinuousTraceNormField :=
  Unitization.lift ccmRationalAdelicCrossedContinuousTraceNormL1Hom

/-- Evaluation of the global continuous-field hom agrees pointwise with the previously proved
fixed-base exact CCM representation. -/
theorem ccmRationalAdelicSourceContinuousTraceNormFieldHom_apply
    (x : Source) (s : CCMRationalClassSpaceSection) :
    ccmRationalAdelicSourceContinuousTraceNormFieldHom x s =
      ccmRationalAdelicMoritaTraceNormL1UnitizedHom
        (by
          have hspos : 0 < ((s.2.val : NNReal) : ℝ) := by
            exact_mod_cast (pos_iff_ne_zero.mpr s.2.ne_zero : 0 < s.2.val)
          exact hspos.ne')
        s.1.val x := by
  induction x using Unitization.ind with
  | inl_add_inr z F =>
      simp [ccmRationalAdelicSourceContinuousTraceNormFieldHom,
        ccmRationalAdelicCrossedContinuousTraceNormL1Hom,
        ccmRationalContinuousTraceNormOperatorFieldInrHom,
        ccmRationalAdelicCrossedContinuousTraceNormHom,
        ccmRationalAdelicMoritaTraceNormL1UnitizedHom,
        ccmRationalAdelicMoritaTraceNormUnitizedHom]
      rw [Algebra.smul_def, mul_one]
      rfl

end RHTower
end GaloisForLFunctions
