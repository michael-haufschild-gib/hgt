import GaloisForLFunctions.HTGeometry.NumberFieldPrimitiveFrameMinimum
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Canonical real coordinates for vectors over a number ring

Mathlib's mixed-embedding lattice basis is indexed by its free-basis choice type.  Reindexing by the
field degree and taking the finite Pi basis gives canonical flattened real coordinates indexed by
`Fin (n * finrank ℚ K)`.  Integral vectors have exactly the integral coefficients of the canonical
`𝓞 K` basis in these coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField Module.Free
open scoped Classical NumberField

noncomputable section

/-- The mixed-space basis reindexed by the field degree. -/
def numberFieldMixedBasis (K : Type*) [Field K] [NumberField K] :
    Module.Basis (Fin (Module.finrank ℚ K)) ℝ (mixedEmbedding.mixedSpace K) :=
  (mixedEmbedding.latticeBasis K).reindex (numberFieldIntegerBasisIndexEquiv K)

@[simp]
theorem numberFieldMixedBasis_repr_integer
    (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) (i : Fin (Module.finrank ℚ K)) :
    (numberFieldMixedBasis K).repr (mixedEmbedding K (a : K)) i =
      ((numberFieldIntegerBasis K).repr a i : ℝ) := by
  simp [numberFieldMixedBasis, numberFieldIntegerBasis,
    mixedEmbedding.latticeBasis_repr_apply]

/-- Flattened real basis of `n` mixed-space coordinates. -/
def numberFieldMixedVectorBasis (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Module.Basis (Fin (n * Module.finrank ℚ K)) ℝ
      (Fin n → mixedEmbedding.mixedSpace K) :=
  ((Pi.basis fun _ : Fin n ↦ numberFieldMixedBasis K).reindex
      (Equiv.sigmaEquivProd (Fin n) (Fin (Module.finrank ℚ K)))).reindex
    (finProdFinEquiv :
      Fin n × Fin (Module.finrank ℚ K) ≃ Fin (n * Module.finrank ℚ K))

@[simp]
theorem numberFieldMixedVectorBasis_repr_integer
    (K : Type*) [Field K] [NumberField K]
    {n : ℕ} (a : Fin n → 𝓞 K)
    (i : Fin n) (j : Fin (Module.finrank ℚ K)) :
    (numberFieldMixedVectorBasis K n).repr
        (numberFieldIntegerVectorEmbedding K a)
        (finProdFinEquiv (i, j)) =
      ((numberFieldIntegerBasis K).repr (a i) j : ℝ) := by
  simp [numberFieldMixedVectorBasis, numberFieldIntegerVectorEmbedding]

/-- Canonical flattened real coordinates as a continuous linear equivalence. -/
noncomputable def numberFieldMixedVectorContinuousLinearEquiv
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    (Fin n → mixedEmbedding.mixedSpace K) ≃L[ℝ]
      (Fin (n * Module.finrank ℚ K) → ℝ) :=
  (numberFieldMixedVectorBasis K n).equivFun.toContinuousLinearEquiv

end

end GaloisForLFunctions.HTGeometry
