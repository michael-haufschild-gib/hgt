import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Separable Hilbert realizations of countable kernels

The Gram vectors form a countable total family. Their complex linear span and
its closure are separable, hence so is the completed kernel Hilbert space.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.KernelHilbert

variable {X : Type*} [Countable X] (K : X → X → ℂ) [Fact (IsPSDKernel K)]

/-- A countable Gram family generates a separable Hilbert realization. -/
instance separableSpace : TopologicalSpace.SeparableSpace (KernelHilbert K) := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have hs : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range (vector K)) : Set (KernelHilbert K)) :=
    (Set.countable_range _).isSeparable.span
  have h := hs.closure
  rwa [(dense_span_vectors K).closure_eq] at h

end GaloisForLFunctions.HTGeometry.KernelHilbert
