import GaloisForLFunctions.HTGeometry.StaticCircuitTwoMemoryOrthogonalityLaw
import GaloisForLFunctions.HTGeometry.UnitaryFlowSmoothing

/-!
# Static shortcut histories force centralizer-centered recurrence energy

The two-memory law reduces every finite-dictionary circuit shortcut to alignment between the
oscillatory memory of one static evolution and one fixed preparation-memory vector.  This module
performs the temporal step without freezing the target selector.

For arbitrary weighted times, the square of the total alignment is bounded by the Gram energy of
the dynamical memories.  For a unitary flow this Gram energy is exactly a stationary recurrence
kernel evaluated at all time differences.  Therefore any adaptive collection of shortcuts forces
positive energy in one centralizer-centered recurrence kernel after the completed static baseline
has been subtracted.

The result is unconditional and needs no finite-dimensionality, spectral gap, randomness, Haar
mixing, or differentiability of the flow.  It deliberately makes no decay claim.  Its quadratic
Cauchy loss is the exact classical frontier that a Brown-scale local-circuit argument must improve
using preparation structure.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J F : Type*} [Fintype J]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Weighted sum of a finite family of memory vectors. -/
def weightedMemorySum (r : J → F) (w : J → ℝ) : F :=
  ∑ j, w j • r j

/-- Weighted alignment of a finite memory history with one fixed preparation memory. -/
def weightedAlignment (r : J → F) (q : F) (w : J → ℝ) : ℝ :=
  ∑ j, w j * inner ℝ (r j) q

/-- Gram energy of a weighted finite memory history. -/
def weightedRecurrenceEnergy (r : J → F) (w : J → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * inner ℝ (r i) (r j)

/-- Weighted alignment is the inner product of the weighted memory sum with the probe. -/
theorem weightedAlignment_eq_inner_sum (r : J → F) (q : F) (w : J → ℝ) :
    weightedAlignment r q w = inner ℝ (weightedMemorySum r w) q := by
  simp [weightedAlignment, weightedMemorySum, sum_inner, real_inner_smul_left]

/-- The recurrence Gram energy is exactly a squared Hilbert norm, hence is nonnegative. -/
theorem weightedRecurrenceEnergy_eq_norm_sq (r : J → F) (w : J → ℝ) :
    weightedRecurrenceEnergy r w = ‖weightedMemorySum r w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [weightedRecurrenceEnergy, weightedMemorySum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Alignment--recurrence energy law.**  A fixed preparation memory can recognize a weighted
history only within the Gram energy carried by that history. -/
theorem weightedAlignment_sq_le_recurrenceEnergy (r : J → F) (q : F) (w : J → ℝ) :
    weightedAlignment r q w ^ 2 ≤ ‖q‖ ^ 2 * weightedRecurrenceEnergy r w := by
  rw [weightedAlignment_eq_inner_sum, weightedRecurrenceEnergy_eq_norm_sq]
  nlinarith [abs_real_inner_le_norm (weightedMemorySum r w) q]

/-- **Sharpness of the universal recurrence-energy frontier.**  Choosing the preparation memory
to be the weighted history sum saturates the alignment--energy law exactly.  Any improvement that
loses less than the Cauchy square must therefore use additional preparation structure. -/
theorem weightedAlignment_sq_eq_recurrenceEnergy_of_historyProbe
    (r : J → F) (w : J → ℝ) :
    weightedAlignment r (weightedMemorySum r w) w ^ 2 =
      ‖weightedMemorySum r w‖ ^ 2 * weightedRecurrenceEnergy r w := by
  rw [weightedAlignment_eq_inner_sum, weightedRecurrenceEnergy_eq_norm_sq,
    real_inner_self_eq_norm_sq]

/-- A unitary-flow Gram entry is the stationary recurrence kernel at the time difference. -/
theorem inner_unitaryFlow_eq_recurrenceKernel (U : UnitaryFlow ℝ F) (z : F) (s t : ℝ) :
    inner ℝ (U.op s z) (U.op t z) = inner ℝ z (U.op (t - s) z) := by
  rw [inner_op_left]
  have hadd := U.op_add (-s) t z
  rw [← hadd]
  congr 2
  ring

/-- The complete weighted Gram energy of a static orbit is one stationary recurrence-kernel
quadrature over all time differences. -/
theorem weightedRecurrenceEnergy_flow_eq_kernel
    (U : UnitaryFlow ℝ F) (z : F) (time : J → ℝ) (w : J → ℝ) :
    weightedRecurrenceEnergy (fun j => U.op (time j) z) w =
      ∑ i, ∑ j, w i * w j * inner ℝ z (U.op (time j - time i) z) := by
  simp only [weightedRecurrenceEnergy, inner_unitaryFlow_eq_recurrenceKernel]

/-- Uniformly positive alignment at nonnegative weighted times forces recurrence Gram energy. -/
theorem threshold_sq_le_weightedRecurrenceEnergy
    (r : J → F) (q : F) (w : J → ℝ) {eta : ℝ}
    (heta : 0 ≤ eta) (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) q) :
    (eta * ∑ j, w j) ^ 2 ≤ ‖q‖ ^ 2 * weightedRecurrenceEnergy r w := by
  have hsumw : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => hw j
  have hlin : eta * ∑ j, w j ≤ weightedAlignment r q w := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (halign j) (hw j)
  have halign0 : 0 ≤ weightedAlignment r q w := le_trans (mul_nonneg heta hsumw) hlin
  have hsq : (eta * ∑ j, w j) ^ 2 ≤ weightedAlignment r q w ^ 2 := by
    nlinarith
  exact le_trans hsq (weightedAlignment_sq_le_recurrenceEnergy r q w)

variable {I : Type*} [Fintype I] [Nonempty I]

/-- **Adaptive shortcut-history recurrence law.**  At every sampled time a different target may
witness the shortcut.  Uniform target averaging and the two-memory law nevertheless produce one
fixed preparation memory.  All shortcuts then force the displayed centralizer-centered stationary
recurrence energy. -/
theorem adaptive_shortcuts_force_recurrence_energy
    (PiOp P : F →L[ℝ] F) (U : UnitaryFlow ℝ F) (x : F)
    (target : I → F) (chosen : J → I) (time : J → ℝ) (w : J → ℝ)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ t z, P (U.op t z) = P z)
    (hUP : ∀ t z, U.op t (P z) = P z)
    (hPiMoment : PiOp (finitePreparationMoment target) = PiOp x)
    (hnonneg : ∀ j i, 0 ≤ inner ℝ (U.op (time j) x) (target i))
    {a : ℝ} (hcollision : ∀ j, a ≤ inner ℝ (U.op (time j) x) (target (chosen j)))
    (hw : ∀ j, 0 ≤ w j)
    (heta : 0 ≤ (Fintype.card I : ℝ)⁻¹ * a -
      (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
        inner ℝ (staticMemory PiOp P x)
          (preparationMemory PiOp x (finitePreparationMoment target)))) :
    (((Fintype.card I : ℝ)⁻¹ * a -
        (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (finitePreparationMoment target)))) *
        ∑ j, w j) ^ 2 ≤
      ‖preparationMemory PiOp x (finitePreparationMoment target)‖ ^ 2 *
        ∑ i, ∑ j, w i * w j *
          inner ℝ (x - P x) (U.op (time j - time i) (x - P x)) := by
  let eta : ℝ := (Fintype.card I : ℝ)⁻¹ * a -
    (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
      inner ℝ (staticMemory PiOp P x)
        (preparationMemory PiOp x (finitePreparationMoment target)))
  let q : F := preparationMemory PiOp x (finitePreparationMoment target)
  have halign : ∀ j, eta ≤ inner ℝ (dynamicMemory P (U.op (time j)) x) q := by
    intro j
    exact one_target_forces_memory_realign PiOp P (U.op (time j)) x target (chosen j)
      hPisa hPiid hPiP (hPU (time j)) hPiMoment (hnonneg j) (hcollision j)
  have henergy := threshold_sq_le_weightedRecurrenceEnergy
    (r := fun j => dynamicMemory P (U.op (time j)) x) q w
    (eta := eta) heta hw halign
  have hdynamic : (fun j => dynamicMemory P (U.op (time j)) x) =
      fun j => U.op (time j) (x - P x) := by
    funext j
    simp only [dynamicMemory, map_sub, hUP]
  rw [hdynamic, weightedRecurrenceEnergy_flow_eq_kernel] at henergy
  exact henergy

end

end GaloisForLFunctions.HTGeometry
