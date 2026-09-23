import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicTopology
import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicTargetReal
import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpaceRealContinuity
import GaloisForLFunctions.RHTower.KRealCyclicBarAlgHom
import GaloisForLFunctions.RHTower.KRealPiTensorProductProjective

/-!
# Real continuity on exact CCM strong cyclic chains

Quaternionic conjugation is isometric in every Schatten-`1` fibre.  Its
componentwise tensor action is therefore isometric for the projective
seminorm, and independent field evaluation intertwines the field and fibre
actions.  On the second graph coordinate, diagonal trace conjugation is the
continuous Real involution on `S(C_ℚ)`.  These two facts prove continuity on
the literal CCM strong cyclic graph topology.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Base := CCMRationalClassSpaceSection
private abbrev Fiber := CCMRationalMoritaTraceNormL1Unitization
private abbrev Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity := CCMRationalContinuousTraceNormField
private abbrev StrongClass := CCMRationalStrongClassSpace

/-- Conjugate-linear bundle on one exact trace-norm fibre. -/
def ccmRationalMoritaTraceNormL1Realₛₗ : Fiber →ₗ⋆[ℂ] Fiber where
  toFun := ccmRationalMoritaTraceNormL1RealStructure
  map_add' := ccmRationalMoritaTraceNormL1RealStructure_add
  map_smul' := ccmRationalMoritaTraceNormL1RealStructure_smul

/-- Exact even Real algebra structure on one Schatten-`1` unitized fibre. -/
def ccmRationalMoritaTraceNormL1KRealAlgebra :
    KRealAlgebraStructure Fiber where
  sigma := ccmRationalMoritaTraceNormL1Realₛₗ
  sq x := by
    change ccmRationalMoritaTraceNormL1RealStructure
        (ccmRationalMoritaTraceNormL1RealStructure x) =
      kRealParityAction false x
    rw [ccmRationalMoritaTraceNormL1RealStructure_sq]
    rfl
  map_one := ccmRationalMoritaTraceNormL1RealStructure_one
  map_mul := ccmRationalMoritaTraceNormL1RealStructure_mul

/-- Evaluation of a continuous trace-norm field as an algebra homomorphism. -/
def ccmRationalContinuousTraceNormFieldEvaluationAlgHom (b : Base) :
    Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity →ₐ[ℂ] Fiber where
  toFun := fun F => F b
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity evaluation is Real-equivariant at algebra level. -/
theorem ccmRationalContinuousTraceNormFieldEvaluationAlgHom_real
    (b : Base) (F : Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity) :
    ccmRationalMoritaTraceNormL1KRealAlgebra.sigma
        (ccmRationalContinuousTraceNormFieldEvaluationAlgHom b F) =
      ccmRationalContinuousTraceNormFieldEvaluationAlgHom b
        (ccmRationalContinuousTraceNormFieldKRealAlgebra.sigma F) :=
  rfl

/-- Independent evaluation intertwines componentwise field and fibre Real
actions in every cyclic degree. -/
theorem ccmRationalContinuousTraceNormFieldDegreeEvaluation_real
    {n : ℕ} (base : Fin (n + 1) → Base)
    (x : CyclicBarTensor ℂ Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity n) :
    ccmRationalContinuousTraceNormFieldDegreeEvaluation base
        ((cyclicBarDegreeKReal
          ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x) =
      (cyclicBarDegreeKReal ccmRationalMoritaTraceNormL1KRealAlgebra n).sigma
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation base x) := by
  -- The displayed degree map evaluates every tensor factor at its own base;
  -- use tensor induction because the bases need not coincide.
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r F =>
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod,
        map_smulₛₗ
          (cyclicBarDegreeKReal
            ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma,
        map_smul
          (ccmRationalContinuousTraceNormFieldDegreeEvaluation base),
        map_smul
          (ccmRationalContinuousTraceNormFieldDegreeEvaluation base),
        map_smulₛₗ
          (cyclicBarDegreeKReal
            ccmRationalMoritaTraceNormL1KRealAlgebra n).sigma]
      congr 1
      change ccmRationalContinuousTraceNormFieldDegreeEvaluation base
          (kRealEvenPiTensorSigma
            (fun _ : Fin (n + 1) =>
              ccmRationalContinuousTraceNormFieldKRealAlgebra.toKRealStructure)
            (PiTensorProduct.tprod ℂ F)) =
        kRealEvenPiTensorSigma
          (fun _ : Fin (n + 1) =>
            ccmRationalMoritaTraceNormL1KRealAlgebra.toKRealStructure)
          (ccmRationalContinuousTraceNormFieldDegreeEvaluation base
            (PiTensorProduct.tprod ℂ F))
      rw [kRealEvenPiTensorSigma_tprod,
        ccmRationalContinuousTraceNormFieldDegreeEvaluation_tprod,
        ccmRationalContinuousTraceNormFieldDegreeEvaluation_tprod,
        kRealEvenPiTensorSigma_tprod]
      congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Componentwise fibre Real action is a projective isometry in every cyclic
degree. -/
def ccmRationalMoritaTraceNormL1DegreeRealIsometry (n : ℕ) :
    CyclicBarTensor ℂ Fiber n ≃ₗᵢ⋆[ℂ] CyclicBarTensor ℂ Fiber n :=
  kRealEvenPiTensorIsometry
    (fun _ : Fin (n + 1) =>
      ccmRationalMoritaTraceNormL1KRealAlgebra.toKRealStructure)
    (fun _ x => ccmRationalMoritaTraceNormL1RealStructure_norm x)

/-- Ambient continuous-field Real action is continuous for the exact
independent-evaluation projective topology. -/
theorem ccmRationalContinuousTraceNormFieldDegreeReal_continuous (n : ℕ) :
    @Continuous (CyclicBarTensor ℂ Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity n) (CyclicBarTensor ℂ Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (cyclicBarDegreeKReal
        ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous (CyclicBarTensor ℂ Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity n)
        (CyclicBarTensor ℂ Fiber n)
        (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
        inferInstance
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation base) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) => z base) :=
      continuous_apply base
    have hAll :
        @Continuous (CyclicBarTensor ℂ Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity n)
          ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n)
          (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
          inferInstance
          (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n) :=
      continuous_induced_dom
    exact hApply.comp hAll
  have h := (ccmRationalMoritaTraceNormL1DegreeRealIsometry n).continuous.comp hEval
  convert h using 1
  funext x
  exact ccmRationalContinuousTraceNormFieldDegreeEvaluation_real base x

/-- Exact covariance of the unique strong diagonal coordinate under Real
conjugation. -/
theorem ccmRationalStrongDiagonalCoordinate_real
    (n : ℕ) (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalStrongDiagonalCoordinate n
        ((ccmRationalStrongCyclicTargetKReal.real n).sigma x) =
      ccmRationalStrongClassSpaceReal
        (ccmRationalStrongDiagonalCoordinate n x) := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  funext b
  rw [ccmRationalStrongDiagonalCoordinate_eval]
  change ccmRationalStrongDiagonalTrace n
      ((cyclicBarDegreeKReal
        ccmRationalContinuousTraceNormFieldKRealAlgebra n).sigma x.1) b = _
  rw [ccmRationalStrongDiagonalTrace_real]
  calc
    star (ccmRationalStrongDiagonalTrace n x.1 b) =
        star (ccmRationalStrongClassSpaceEvalLinear
          (ccmRationalStrongDiagonalCoordinate n x) b) := by
      rw [ccmRationalStrongDiagonalCoordinate_eval]
    _ = ccmRationalStrongClassSpaceEvalLinear
        (ccmRationalStrongClassSpaceReal
          (ccmRationalStrongDiagonalCoordinate n x)) b := by
      exact (ccmRationalStrongClassSpaceEval_real
        (ccmRationalStrongDiagonalCoordinate n x) b).symm

/-- Degreewise strong-chain Real involution is continuous for the literal
ambient/diagonal graph topology. -/
theorem ccmRationalStrongCyclicDegreeReal_continuous (n : ℕ) :
    @Continuous (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalStrongCyclicDegreeTopology n)
      (ccmRationalStrongCyclicDegreeTopology n)
      (ccmRationalStrongCyclicTargetKReal.real n).sigma := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace (CyclicBarTensor ℂ Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  rw [continuous_induced_rng]
  apply Continuous.prodMk
  · exact (ccmRationalContinuousTraceNormFieldDegreeReal_continuous n).comp
      (continuous_ccmRationalStrongCyclicAmbientInclusion n)
  · have h := ccmRationalStrongClassSpaceReal_continuous.comp
        (continuous_ccmRationalStrongDiagonalCoordinate n)
    convert h using 1
    funext x
    exact ccmRationalStrongDiagonalCoordinate_real n x

/-- Exact strong target Real structure is continuous in every cyclic degree. -/
theorem ccmRationalStrongCyclicKRealTopology :
    CyclicModule.KRealTopology ccmRationalStrongCyclicTargetKReal
      ccmRationalStrongCyclicTopology where
  real_continuous := ccmRationalStrongCyclicDegreeReal_continuous

end GaloisForLFunctions.RHTower
