import GaloisForLFunctions.ArithmeticDefectRigidity.TheOriginStepModuleHasTheFullBohrHull
import GaloisForLFunctions.HilbertMetric.Correlation.ExceptionalEnergy

/-!
# Removing exceptional origin steps

The exact max kernel of origin steps admits a Gram realization. Its deletion
error is controlled by the exceptional max-kernel energy, and a loss of
square-root energy forces a reciprocal-index weighted coefficient cost.
-/

open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HilbertMetric
noncomputable section
local instance : InnerProductSpace ℝ Hilbert := InnerProductSpace.rclikeToReal ℂ Hilbert

/-- Complete max-kernel energy of a finite family of origin steps. -/
def originPacketEnergy (s : Finset ℕ+) (c : ℕ+ → ℝ) : ℝ :=
  ∑ j ∈ s, ∑ k ∈ s, c j * c k * kernel j k

private theorem origin_vector_inner (j k : ℕ+) :
    ⟪KernelHilbert.vector complexKernel j, KernelHilbert.vector complexKernel k⟫_ℝ = kernel j k := by
  change (inner ℂ (KernelHilbert.vector complexKernel j)
    (KernelHilbert.vector complexKernel k)).re = _
  rw [KernelHilbert.inner_vector]
  exact kernel_symm k j

private theorem originPacketEnergy_eq (s : Finset ℕ+) (c : ℕ+ → ℝ) :
    originPacketEnergy s c = packetEnergy s (fun j => c j • KernelHilbert.vector complexKernel j) := by
  rw [packetEnergy_eq_gram]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_smul_left, real_inner_smul_right, origin_vector_inner]
  ring

/-- Reciprocal index is the exact self-energy of an origin-step coefficient. -/
theorem origin_coefficient_norm_sq (c : ℝ) (j : ℕ+) :
    ‖c • KernelHilbert.vector complexKernel j‖ ^ 2 = c ^ 2 / (j : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
    origin_vector_inner]
  simp only [kernel, max_self]
  ring

/-- Every cross term of the exceptional origin steps is retained in the error bound. -/
theorem originPacketEnergy_deletion_centered (s e : Finset ℕ+) (c : ℕ+ → ℝ) :
    (originPacketEnergy (s \ e) c - originPacketEnergy s c - originPacketEnergy (s ∩ e) c) ^ 2 ≤
      4 * originPacketEnergy s c * originPacketEnergy (s ∩ e) c := by
  simpa only [originPacketEnergy_eq] using
    packetEnergy_deletion_centered s e (fun j => c j • KernelHilbert.vector complexKernel j)

/-- Loss of max-kernel correlation forces reciprocal-index coefficient mass. -/
theorem originPacketEnergy_deletion_cardinality (s e : Finset ℕ+) (c : ℕ+ → ℝ) :
    (Real.sqrt (originPacketEnergy s c) - Real.sqrt (originPacketEnergy (s \ e) c)) ^ 2 ≤
      ((s ∩ e).card : ℝ) * ∑ j ∈ s ∩ e, c j ^ 2 / (j : ℝ) := by
  simpa only [originPacketEnergy_eq, origin_coefficient_norm_sq] using
    packetEnergy_deletion_cardinality s e (fun j => c j • KernelHilbert.vector complexKernel j)

end
end GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule.originPacketEnergy_deletion_centered
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule.originPacketEnergy_deletion_cardinality
