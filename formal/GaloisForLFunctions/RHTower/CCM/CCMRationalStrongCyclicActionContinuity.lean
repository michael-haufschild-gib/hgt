import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicTopology
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongClassSpaceActionContinuity
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicClassSpaceAction

/-!
# Continuity of class-space action on exact strong cyclic chains

On ambient projective chains, right translation merely pulls every independent
evaluation base back by multiplication with the fixed class-space element.  On
the unique strong diagonal coordinate, it is the continuous LF action on
`S(C_ℚ)`.  The strong graph topology therefore makes every degreewise CCM
Lefschetz operator continuous.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Field := CCMRationalContinuousTraceNormField
private abbrev StrongClass := CCMRationalStrongClassSpace

/-- Pullback of an independent evaluation tuple by fixed right translation. -/
def ccmRationalContinuousFieldRightActionBasePullback {n : ℕ}
    (c : Section) (base : Fin (n + 1) → Section) : Fin (n + 1) → Section :=
  fun j => base j * c

theorem ccmRationalContinuousFieldDegreeEvaluation_rightAction
    (c : Section) {n : ℕ} (base : Fin (n + 1) → Section)
    (x : CyclicBarTensor ℂ Field n) :
    ccmRationalContinuousTraceNormFieldDegreeEvaluation base
        (cyclicBarAlgHomDegree
          (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x) =
      ccmRationalContinuousTraceNormFieldDegreeEvaluation
        (ccmRationalContinuousFieldRightActionBasePullback c base) x := by
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r F
    simp [ccmRationalContinuousFieldRightActionBasePullback,
      ccmRationalContinuousTraceNormFieldDegreeEvaluation_tprod]
    congr 2
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- Right translation is continuous on ambient continuous-field projective
chains. -/
theorem ccmRationalContinuousFieldRightActionDegree_continuous
    (c : Section) (n : ℕ) :
    @Continuous (CyclicBarTensor ℂ Field n) (CyclicBarTensor ℂ Field n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (cyclicBarAlgHomDegree
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n) := by
  letI : TopologicalSpace (CyclicBarTensor ℂ Field n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  rw [continuous_induced_rng]
  apply continuous_pi
  intro base
  have hEval :
      @Continuous (CyclicBarTensor ℂ Field n)
        (CyclicBarTensor ℂ CCMRationalMoritaTraceNormL1Unitization n)
        (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
        inferInstance
        (ccmRationalContinuousTraceNormFieldDegreeEvaluation
          (ccmRationalContinuousFieldRightActionBasePullback c base)) := by
    have hApply : Continuous (fun z :
        ((Fin (n + 1) → Section) →
          CyclicBarTensor ℂ CCMRationalMoritaTraceNormL1Unitization n) =>
          z (ccmRationalContinuousFieldRightActionBasePullback c base)) :=
      continuous_apply
        (ccmRationalContinuousFieldRightActionBasePullback c base)
    have hAll :
        @Continuous (CyclicBarTensor ℂ Field n)
          ((Fin (n + 1) → Section) →
            CyclicBarTensor ℂ CCMRationalMoritaTraceNormL1Unitization n)
          (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
          inferInstance
          (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n) :=
      continuous_induced_dom
    exact hApply.comp hAll
  convert hEval using 1
  funext x
  exact ccmRationalContinuousFieldDegreeEvaluation_rightAction c base x

/-- Exact covariance of the unique strong diagonal representative. -/
theorem ccmRationalStrongDiagonalCoordinate_rightAction
    (c : Section) (n : ℕ)
    (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalStrongDiagonalCoordinate n
        (ccmRationalStrongCyclicRightActionDegree c n x) =
      ccmRationalStrongClassSpaceRightActionLinear c
        (ccmRationalStrongDiagonalCoordinate n x) := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  funext b
  rw [ccmRationalStrongDiagonalCoordinate_eval]
  change ccmRationalStrongDiagonalTrace n
      (cyclicBarAlgHomDegree
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n x.1) b = _
  rw [ccmRationalStrongDiagonalTrace_rightAction]
  calc
    ccmRationalStrongDiagonalTrace n x.1 (b * c) =
        ccmRationalStrongClassSpaceEvalLinear
          (ccmRationalStrongDiagonalCoordinate n x) (b * c) :=
      (congrFun
        (ccmRationalStrongDiagonalCoordinate_eval n x) (b * c)).symm
    _ = ccmRationalStrongClassSpaceEval
        (ccmRationalStrongClassSpaceRightAction c
          (ccmRationalStrongDiagonalCoordinate n x)) b :=
      (ccmRationalStrongClassSpaceEval_rightAction c
        (ccmRationalStrongDiagonalCoordinate n x) b).symm
    _ = ccmRationalStrongClassSpaceEvalLinear
        (ccmRationalStrongClassSpaceRightActionLinear c
          (ccmRationalStrongDiagonalCoordinate n x)) b := rfl

/-- Every degreewise CCM class-space action is continuous for the exact strong
cyclic graph topology. -/
theorem ccmRationalStrongCyclicRightActionDegree_continuous
    (c : Section) (n : ℕ) :
    @Continuous (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalStrongCyclicDegreeTopology n)
      (ccmRationalStrongCyclicDegreeTopology n)
      (ccmRationalStrongCyclicRightActionDegree c n) := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace (CyclicBarTensor ℂ Field n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  rw [continuous_induced_rng]
  apply Continuous.prodMk
  · exact (ccmRationalContinuousFieldRightActionDegree_continuous c n).comp
      (continuous_ccmRationalStrongCyclicAmbientInclusion n)
  · have h := (ccmRationalStrongClassSpaceRightAction_continuous c).comp
        (continuous_ccmRationalStrongDiagonalCoordinate n)
    convert h using 1
    funext x
    exact ccmRationalStrongDiagonalCoordinate_rightAction c n x

end GaloisForLFunctions.RHTower
