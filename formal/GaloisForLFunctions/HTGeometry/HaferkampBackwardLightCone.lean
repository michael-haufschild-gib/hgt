import GaloisForLFunctions.HTGeometry.HaferkampQubitPathTransport

/-!
# Time-ordered backwards-light-cone certificates

The paper's condition is represented by a directed path from every non-root
qubit to a designated output qubit, with its edge word occurring in the
ordered block word. This is the exact temporal datum needed by the local
Pauli-transport construction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A time-ordered backwards light cone in an ordered two-qubit block. -/
structure BackwardsLightCone (n : ℕ) (edges : List (Fin n × Fin n))
    (root : Fin n) where
  path : ∀ source : Fin n, source ≠ root → QubitMergePath (Fin n) source root
  path_sublist : ∀ source hsource,
    List.Sublist (path source hsource).edgeList edges

namespace BackwardsLightCone

/-- Every Pauli direction nontrivial at a non-root source has a certified
merge schedule embedded in the ordered light-cone block and ending in `Z` at
the root. -/
theorem exists_embedded_root_schedule
    {n : ℕ} {edges : List (Fin n × Fin n)} {root source : Fin n}
    (cone : BackwardsLightCone n edges root) (hsource : source ≠ root)
    (P : Fin n → Option (Fin 3)) (hP : P source ≠ none) :
    ∃ R : Fin n → Option (Fin 3),
      ∃ schedule : PauliMergeSchedule (Fin n) P R,
        List.Sublist schedule.edgeList edges ∧ R root = some 2 := by
  let path := cone.path source hsource
  let schedule := path.toPauliMergeSchedule P hP
  refine ⟨path.transportLabel P, schedule, ?_, ?_⟩
  · change List.Sublist (path.toPauliMergeSchedule P hP).edgeList edges
    rw [path.toPauliMergeSchedule_edgeList]
    exact cone.path_sublist source hsource
  · exact path.transportLabel_target_eq_Z P

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
