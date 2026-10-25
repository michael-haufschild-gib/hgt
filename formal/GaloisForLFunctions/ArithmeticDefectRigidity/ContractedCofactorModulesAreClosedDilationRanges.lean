import GaloisForLFunctions.ArithmeticDefectRigidity.ContractedCofactorModulesEmbedInTheOriginal
import GaloisForLFunctions.HTGeometry.ClosedOperatorRangesAreClosedFeatureSpans

/-!
# Contracted cofactor modules are closed dilation ranges

The normalized contracted features span the closed range of the selected
dilation. In finite dimension, contraction removes precisely its nullity.
-/

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- The contracted module occupies exactly the closed range of its selected dilation. -/
theorem range_contractedKernelIsometry {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) :
    LinearMap.range (contractedKernelIsometry L M p hp hK).toLinearMap =
      (LinearMap.range (dilation L p).toLinearMap).topologicalClosure := by
  let U := contractedKernelIsometry L M p hp hK
  have hclosed : IsClosed (LinearMap.range U.toLinearMap : Set (Hilbert L)) :=
    U.isometry.isClosedEmbedding.isClosed_range
  have hU := closed_range_eq_closed_span_features U.toContinuousLinearMap (vector M)
    (KernelHilbert.dense_span_vectors (complexKernel M))
  change (LinearMap.range U.toLinearMap).topologicalClosure = _ at hU
  rw [hclosed.submodule_topologicalClosure_eq] at hU
  have hfeature : (fun j => U.toContinuousLinearMap (vector M j)) =
      (fun j => ((Real.sqrt (L.kernel p p) : ℂ)⁻¹) • vector L (p * j)) := by
    funext j
    exact contractedKernelIsometry_vector L M p hp hK j
  rw [hfeature] at hU
  have hc : (Real.sqrt (L.kernel p p) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hp).ne')
  rw [span_scaled_features_eq (fun j => vector L (p * j)) hc] at hU
  have hD := closed_range_eq_closed_span_features (dilation L p) (vector L)
    (KernelHilbert.dense_span_vectors (complexKernel L))
  simp only [dilation_vector] at hD
  exact hU.trans hD.symm

/-- The dimension of a contracted actual module is the dimension of the closed dilation range. -/
theorem finrank_contracted_module_eq_closed_dilation_range {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) :
    Module.finrank ℂ (Hilbert M) = Module.finrank ℂ
      (LinearMap.range (dilation L p).toLinearMap).topologicalClosure := by
  have h := (LinearEquiv.ofInjective (contractedKernelIsometry L M p hp hK).toLinearMap
    (contractedKernelIsometry L M p hp hK).injective).finrank_eq
  rw [range_contractedKernelIsometry L M p hp hK] at h
  exact h

/-- In finite dimension, contraction removes exactly the kernel dimension of the dilation. -/
theorem contracted_finrank_add_dilation_nullity {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)]
    (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) :
    Module.finrank ℂ (Hilbert M) + Module.finrank ℂ (LinearMap.ker (dilation L p).toLinearMap) =
      Module.finrank ℂ (Hilbert L) := by
  rw [finrank_contracted_module_eq_closed_dilation_range L M p hp hK,
    (Submodule.closed_of_finiteDimensional (LinearMap.range (dilation L p).toLinearMap)).submodule_topologicalClosure_eq]
  exact LinearMap.finrank_range_add_finrank_ker (dilation L p).toLinearMap

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.range_contractedKernelIsometry
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.contracted_finrank_add_dilation_nullity
end
