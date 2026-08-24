import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.CompactCalibrationGlobalization

/-!
# Predicate Hasse principle for common calibration

Weak-star compactness makes existence of one functional norming an arbitrary vector family
equivalent to existence on every finite packet.  The predicate formulation packages both
globalization and finite obstruction detection for reuse.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

noncomputable section

variable {E ι : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Common normability is a Hasse predicate over finite index packets. -/
def commonNormerHassePredicate : HassePredicate (ι → E) (Finset ι) where
  global v := ∃ phi : StrongDual ℝ E, ‖phi‖ ≤ 1 ∧ ∀ i, phi (v i) = ‖v i‖
  atPlace s v := ∃ phi : StrongDual ℝ E,
    ‖phi‖ ≤ 1 ∧ ∀ i ∈ s, phi (v i) = ‖v i‖
  local_global v := common_normer_iff_finset v

/-- Failure of one global normer is equivalent to obstruction on one finite packet. -/
theorem not_common_normer_iff_exists_finset_obstruction (v : ι → E) :
    (¬ ∃ phi : StrongDual ℝ E, ‖phi‖ ≤ 1 ∧ ∀ i, phi (v i) = ‖v i‖) ↔
      ∃ s : Finset ι,
        ¬ ∃ phi : StrongDual ℝ E, ‖phi‖ ≤ 1 ∧ ∀ i ∈ s, phi (v i) = ‖v i‖ :=
  commonNormerHassePredicate.not_global_iff_exists_local_not v

end


end GaloisForLFunctions.HTGeometry
