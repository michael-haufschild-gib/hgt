import GaloisForLFunctions.RHTower.CCMRationalAdelicClassSpaceCyclicModule
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Coefficientwise projective topology on adelic class-space chains

The class-space algebra consists of sections over genuine adelic Morita bases with values in the
`ℓ¹`-normed minimal unitization of the trace-class ideal.  In degree `n`, every tuple of bases
evaluates a section tensor into the projective-seminorm tensor power of that normed unitization.
The coefficientwise projective topology is the initial topology for all such evaluation maps.

This is the exact topology layer required before proving continuity of faces, degeneracies, and
rotation and forming the closed CCM cokernel; no discrete or indiscrete surrogate is used.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions
namespace RHTower

private abbrev Base := CCMRationalAdelicMoritaBase
private abbrev Fiber := CCMRationalMoritaTraceClassL1Unitization
private abbrev Sections := CCMRationalAdelicMoritaClassSpaceAlgebra

/-- Evaluation of one class-space section at one genuine adelic Morita base. -/
def ccmRationalAdelicMoritaSectionEvaluation (base : Base) :
    Sections →ₗ[ℂ] Fiber where
  toFun := fun f => f base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of every tensor factor at an independently chosen adelic base. -/
def ccmRationalAdelicClassSpaceDegreeEvaluation {n : ℕ}
    (base : Fin (n + 1) → Base) :
    CyclicBarTensor ℂ Sections n →ₗ[ℂ] CyclicBarTensor ℂ Fiber n :=
  PiTensorProduct.map fun j =>
    ccmRationalAdelicMoritaSectionEvaluation (base j)

@[simp]
theorem ccmRationalAdelicClassSpaceDegreeEvaluation_tprod {n : ℕ}
    (base : Fin (n + 1) → Base)
    (f : Fin (n + 1) → Sections) :
    ccmRationalAdelicClassSpaceDegreeEvaluation base
        (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (fun j => f j (base j)) := by
  simp [ccmRationalAdelicClassSpaceDegreeEvaluation,
    ccmRationalAdelicMoritaSectionEvaluation]

/-- Simultaneous evaluation at every independent adelic base tuple. -/
def ccmRationalAdelicClassSpaceAllDegreeEvaluations (n : ℕ) :
    CyclicBarTensor ℂ Sections n →ₗ[ℂ]
      ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) :=
  LinearMap.pi fun base => ccmRationalAdelicClassSpaceDegreeEvaluation base

@[simp]
theorem ccmRationalAdelicClassSpaceAllDegreeEvaluations_apply
    (n : ℕ) (x : CyclicBarTensor ℂ Sections n)
    (base : Fin (n + 1) → Base) :
    ccmRationalAdelicClassSpaceAllDegreeEvaluations n x base =
      ccmRationalAdelicClassSpaceDegreeEvaluation base x :=
  rfl

/-- Initial topology for all projective tensor evaluations on independent adelic bases. -/
@[reducible]
def ccmRationalAdelicClassSpaceProjectiveTopology (n : ℕ) :
    TopologicalSpace (CyclicBarTensor ℂ Sections n) :=
  TopologicalSpace.induced
    (ccmRationalAdelicClassSpaceAllDegreeEvaluations n) inferInstance

/-- Addition is continuous for the coefficientwise projective topology. -/
theorem ccmRationalAdelicClassSpaceProjectiveContinuousAdd (n : ℕ) :
    @ContinuousAdd (CyclicBarTensor ℂ Sections n)
      (ccmRationalAdelicClassSpaceProjectiveTopology n) inferInstance :=
  continuousAdd_induced (ccmRationalAdelicClassSpaceAllDegreeEvaluations n)

/-- Complex scalar multiplication is continuous for the coefficientwise projective topology. -/
theorem ccmRationalAdelicClassSpaceProjectiveContinuousSMul (n : ℕ) :
    @ContinuousSMul ℂ (CyclicBarTensor ℂ Sections n)
      inferInstance inferInstance
      (ccmRationalAdelicClassSpaceProjectiveTopology n) := by
  letI : IsBoundedSMul ℂ (CyclicBarTensor ℂ Fiber n) :=
    IsBoundedSMul.of_norm_smul_le
      PiTensorProduct.projectiveSeminorm_smul_le
  letI : ContinuousSMul ℂ (CyclicBarTensor ℂ Fiber n) := inferInstance
  letI : ContinuousSMul ℂ
      ((Fin (n + 1) → Base) → CyclicBarTensor ℂ Fiber n) :=
    inferInstance
  exact continuousSMul_induced
    (ccmRationalAdelicClassSpaceAllDegreeEvaluations n)

end RHTower
end GaloisForLFunctions
