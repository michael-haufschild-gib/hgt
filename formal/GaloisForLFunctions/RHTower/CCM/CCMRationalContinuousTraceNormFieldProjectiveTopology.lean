import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicTarget
import GaloisForLFunctions.RHTower.CCM.CCMRationalMoritaTraceNormL1NormOne
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Projective evaluation topology on continuous trace-norm field chains

In cyclic degree `n`, evaluate every continuous field factor at an independent
point of the literal rational class-space section.  The fibre tensor carries
its projective seminorm topology.  The initial topology of all such
evaluations is the coefficientwise projective topology on continuous-field
chains; unlike the older all-functions recipient, its underlying algebra is
the exact continuous trace-norm field algebra used by CCM Definition 4.9.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Base := CCMRationalClassSpaceSection
private abbrev Fiber := CCMRationalMoritaTraceNormL1Unitization
private abbrev Field := CCMRationalContinuousTraceNormField

/-- Evaluation of one continuous trace-norm field at one class-space point. -/
def ccmRationalContinuousTraceNormFieldEvaluation (base : Base) :
    Field →ₗ[ℂ] Fiber where
  toFun := fun F => F base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Independent evaluation of every cyclic tensor factor. -/
def ccmRationalContinuousTraceNormFieldDegreeEvaluation {n : ℕ}
    (base : Fin (n + 1) → Base) :
    CyclicBarTensor ℂ Field n →ₗ[ℂ] CyclicBarTensor ℂ Fiber n :=
  PiTensorProduct.map fun j =>
    ccmRationalContinuousTraceNormFieldEvaluation (base j)

@[simp]
theorem ccmRationalContinuousTraceNormFieldDegreeEvaluation_tprod
    {n : ℕ} (base : Fin (n + 1) → Base)
    (F : Fin (n + 1) → Field) :
    ccmRationalContinuousTraceNormFieldDegreeEvaluation base
        (PiTensorProduct.tprod ℂ F) =
      PiTensorProduct.tprod ℂ (fun j => F j (base j)) := by
  simp [ccmRationalContinuousTraceNormFieldDegreeEvaluation,
    ccmRationalContinuousTraceNormFieldEvaluation]

/-- All independent-base evaluations at once. -/
def ccmRationalContinuousTraceNormFieldAllDegreeEvaluations (n : ℕ) :
    CyclicBarTensor ℂ Field n →ₗ[ℂ]
      ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) :=
  LinearMap.pi fun base =>
    ccmRationalContinuousTraceNormFieldDegreeEvaluation base

@[simp]
theorem ccmRationalContinuousTraceNormFieldAllDegreeEvaluations_apply
    (n : ℕ) (x : CyclicBarTensor ℂ Field n)
    (base : Fin (n + 1) → Base) :
    ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n x base =
      ccmRationalContinuousTraceNormFieldDegreeEvaluation base x :=
  rfl

/-- Initial projective topology of independent class-space evaluations. -/
@[reducible]
def ccmRationalContinuousTraceNormFieldProjectiveTopology (n : ℕ) :
    TopologicalSpace (CyclicBarTensor ℂ Field n) :=
  TopologicalSpace.induced
    (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n)
    inferInstance

theorem ccmRationalContinuousTraceNormFieldProjectiveContinuousAdd (n : ℕ) :
    @ContinuousAdd (CyclicBarTensor ℂ Field n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      inferInstance :=
  continuousAdd_induced
    (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n)

theorem ccmRationalContinuousTraceNormFieldProjectiveContinuousSMul (n : ℕ) :
    @ContinuousSMul ℂ (CyclicBarTensor ℂ Field n)
      inferInstance inferInstance
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n) := by
  letI : IsBoundedSMul ℂ (CyclicBarTensor ℂ Fiber n) :=
    IsBoundedSMul.of_norm_smul_le
      PiTensorProduct.projectiveSeminorm_smul_le
  letI : ContinuousSMul ℂ (CyclicBarTensor ℂ Fiber n) := inferInstance
  letI : ContinuousSMul ℂ
      ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) :=
    inferInstance
  exact continuousSMul_induced
    (ccmRationalContinuousTraceNormFieldAllDegreeEvaluations n)

end GaloisForLFunctions.RHTower
