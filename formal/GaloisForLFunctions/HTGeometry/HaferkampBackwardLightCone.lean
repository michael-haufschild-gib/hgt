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

/-- If a Pauli direction is already nontrivial on the root, the final edge of
any non-root light-cone path normalizes that root support to `Z`. -/
theorem exists_embedded_root_schedule_of_root_nontrivial
    {n : ℕ} {edges : List (Fin n × Fin n)} {root source : Fin n}
    (cone : BackwardsLightCone n edges root) (hsource : source ≠ root)
    (P : Fin n → Option (Fin 3)) (hroot : P root ≠ none) :
    ∃ R : Fin n → Option (Fin 3),
      ∃ schedule : PauliMergeSchedule (Fin n) P R,
        List.Sublist schedule.edgeList edges ∧ R root = some 2 := by
  let path := cone.path source hsource
  let a := path.finalEdge.1
  have htarget : path.finalEdge.2 = root := path.finalEdge_second_eq_target
  have ha : a ≠ root := by
    intro haroot
    apply path.finalEdge_fst_ne_snd
    simp [a, htarget, haroot]
  let R := updateTwoQubitPauliLabel P a root none (some 2)
  let schedule : PauliMergeSchedule (Fin n) P R :=
    PauliMergeSchedule.step P a root ha (Or.inr hroot)
      (PauliMergeSchedule.done R)
  refine ⟨R, schedule, ?_, ?_⟩
  · change [(a, root)].Sublist edges
    have hfinal : path.finalEdge = (a, root) := by
      apply Prod.ext
      · simp [a]
      · simpa using htarget
    rw [← hfinal]
    exact (path.singleton_finalEdge_sublist_edgeList).trans
      (cone.path_sublist source hsource)
  · simp [R, updateTwoQubitPauliLabel]

/-- Every nonidentity Pauli direction is transported to `Z` at the light-cone
root.  A non-root support uses its certified path; root-only support uses the
final light-cone edge.  The condition `1 < n` is exactly the existence of a
second qubit required in the latter case. -/
theorem exists_embedded_root_schedule_of_nontrivial
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ R : Fin n → Option (Fin 3),
      ∃ schedule : PauliMergeSchedule (Fin n) P R,
        List.Sublist schedule.edgeList edges ∧ R root = some 2 := by
  by_cases hnonroot : ∃ source : Fin n, source ≠ root ∧ P source ≠ none
  · rcases hnonroot with ⟨source, hsource, hsourceP⟩
    exact cone.exists_embedded_root_schedule hsource P hsourceP
  · have hroot : P root ≠ none := by
      rcases hP with ⟨q, hq⟩
      by_cases hqroot : q = root
      · simpa [hqroot] using hq
      · exact False.elim (hnonroot ⟨q, hqroot, hq⟩)
    let zero : Fin n := ⟨0, lt_trans Nat.zero_lt_one hn⟩
    let one : Fin n := ⟨1, hn⟩
    letI : Nontrivial (Fin n) := ⟨zero, one, by simp [zero, one]⟩
    obtain ⟨source, hsource⟩ := exists_ne root
    exact cone.exists_embedded_root_schedule_of_root_nontrivial hsource P hroot

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
