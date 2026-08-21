import GaloisForLFunctions.HTGeometry.SeibergWitten.SpinC

/-!
# Smooth spinor connections and the induced Dirac operator

This module uses mathlib's actual `CovariantDerivative` object on a smooth real vector bundle.
`CliffordContractionData` then contracts its one-form-valued derivative pointwise into the negative
spinor fiber, producing the Dirac operator on arbitrary sections.  Smoothness of this operator,
unitarity of the connection, and the local-frame comparison with the pointwise Clifford relation
are deliberately separate layers.
-/

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- A covariant derivative on a smooth positive-spinor bundle over a four-manifold. -/
structure SmoothSpinorConnection
    (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [SmoothFourManifold M]
    (SPlus : M → Type v)
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℝ (SPlus x)]
    [∀ x, TopologicalSpace (SPlus x)] [∀ x, IsTopologicalAddGroup (SPlus x)]
    [∀ x, ContinuousSMul ℝ (SPlus x)]
    [TopologicalSpace (Bundle.TotalSpace (Fin 2 → ℂ) SPlus)]
    [FiberBundle (Fin 2 → ℂ) SPlus] [VectorBundle ℝ (Fin 2 → ℂ) SPlus] where
  covariantDerivative : CovariantDerivative fourModel (Fin 2 → ℂ) SPlus

/-- Fiberwise contraction of covariant derivatives into negative spinors. -/
structure CliffordContractionData
    (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    (SPlus SMinus : M → Type v)
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℝ (SPlus x)]
    [∀ x, AddCommGroup (SMinus x)] [∀ x, Module ℝ (SMinus x)] where
  contract : ∀ x, (TangentSpace fourModel x →ₗ[ℝ] SPlus x) → SMinus x

/-- Dirac operator induced by a smooth positive-spinor connection and a Clifford contraction. -/
def SmoothSpinorConnection.dirac
    {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M] [SmoothFourManifold M]
    {SPlus : M → Type v}
    [∀ x, AddCommGroup (SPlus x)] [∀ x, Module ℝ (SPlus x)]
    [∀ x, TopologicalSpace (SPlus x)] [∀ x, IsTopologicalAddGroup (SPlus x)]
    [∀ x, ContinuousSMul ℝ (SPlus x)]
    [TopologicalSpace (Bundle.TotalSpace (Fin 2 → ℂ) SPlus)]
    [FiberBundle (Fin 2 → ℂ) SPlus] [VectorBundle ℝ (Fin 2 → ℂ) SPlus]
    {SMinus : M → Type v}
    [∀ x, AddCommGroup (SMinus x)] [∀ x, Module ℝ (SMinus x)]
    (connection : SmoothSpinorConnection M SPlus)
    (contraction : CliffordContractionData M SPlus SMinus)
    (sigma : ∀ x, SPlus x) : ∀ x, SMinus x :=
  fun x => contraction.contract x (connection.covariantDerivative sigma x)

end GaloisForLFunctions.HTGeometry.SeibergWitten
