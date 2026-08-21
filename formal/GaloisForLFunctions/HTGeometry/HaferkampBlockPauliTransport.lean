import GaloisForLFunctions.HTGeometry.HaferkampBackwardLightCone
import GaloisForLFunctions.HTGeometry.HaferkampPauliMergeGateWord

/-!
# Exact Pauli transport by a full backwards-light-cone block

A Pauli schedule need not use every location of its supplied light-cone block.
This module fills the omitted locations with identity `SU(4)` gates and proves
that the resulting full block still transports every nonidentity Pauli label
to `Z` on the designated root.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reverse-chronological contraction of an ordered edge-list block with a
literal aligned list of local `SU(4)` gate values. -/
def edgeListBlockContraction {n : ℕ}
    (edges : List (Fin n × Fin n))
    (gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  haferkampGateWordReverseProduct totalTwoQubitLift edges gates

namespace BackwardsLightCone

/-- Every nonidentity Pauli direction has a full-gate-word realization inside
one BLC block.  The returned list has exactly one local `SU(4)` value per
original block location and sends the input label to `Z` at the root. -/
theorem exists_full_block_transport
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      gates.length = edges.length ∧
      ∃ R : Fin n → Option (Fin 3), ∃ c : ℂ, c ≠ 0 ∧
        ((edgeListBlockContraction edges gates :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose
            (edgeListBlockContraction edges gates :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          c • finitePauliMatrix R) ∧ R root = some 2 := by
  obtain ⟨R, schedule, hsub, hroot⟩ :=
    cone.exists_embedded_root_schedule_of_nontrivial hn P hP
  obtain ⟨selectedGates, hselectedLength, c, hc, htransport⟩ :=
    schedule.exists_localGateWord_transport
  obtain ⟨gates, embedding⟩ :=
    exists_haferkampGateWordEmbedding 1 hsub selectedGates hselectedLength
  refine ⟨gates, embedding.blockGates_length_eq, R, c, hc, ?_, hroot⟩
  change ((haferkampGateWordReverseProduct totalTwoQubitLift edges gates :
      Matrix.unitaryGroup (Fin n → Bool) ℂ) :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
      Matrix.conjTranspose
        ((haferkampGateWordReverseProduct totalTwoQubitLift edges gates :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      c • finitePauliMatrix R
  rw [embedding.reverseProduct_eq totalTwoQubitLift_one]
  exact htransport

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
