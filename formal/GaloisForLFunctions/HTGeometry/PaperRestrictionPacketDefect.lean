import GaloisForLFunctions.HTGeometry.ConstitutiveRestrictionFormationHistory

/-!
# Coherent accounting for restriction-packet compression

The literal packet operator loses its source-support complement. Retaining that complement as a
second complex vector gives exact reconstruction and conservation of squared norm, including the
squared distance between any two inputs. This supplies the native amplitude infrastructure for
finite-law information bounds without identifying probabilities with the full coherent record.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RestrictionPacket
open scoped InnerProductSpace

variable {E G : Type*} [SemilatticeInf E] [OrderBot E] [Group G]
  [SupportGradeAction G E]

/-- The complex amplitudes excluded from a packet's source support. -/
def paperPacketDefect (s : RestrictionPacket E G) :
    PacketHilbert (E := E) (G := G) →L[ℂ] PacketHilbert (E := E) (G := G) :=
  ContinuousLinearMap.id ℂ _ - supportProjection (sourceSupport s)

theorem paperPacketDefect_apply (s : RestrictionPacket E G)
    (x : PacketHilbert (E := E) (G := G)) :
    paperPacketDefect s x = x - supportProjection (sourceSupport s) x := rfl

/-- Applying the packet adjoint to the retained branch and restoring the defect recovers every
complex coefficient, with no support or finite-dimensional assumption on the input. -/
theorem paperPacketDefect_reconstruction (s : RestrictionPacket E G)
    (x : PacketHilbert (E := E) (G := G)) :
    (packetOperator s).adjoint (packetOperator s x) + paperPacketDefect s x = x := by
  rw [← ContinuousLinearMap.comp_apply, packetOperator_adjoint_mul,
    paperPacketDefect_apply]
  abel

/-- The retained norm is precisely the norm of the source-support projection. -/
theorem paperPacket_norm_sq (s : RestrictionPacket E G)
    (x : PacketHilbert (E := E) (G := G)) :
    ‖packetOperator s x‖ ^ 2 = ‖supportProjection (sourceSupport s) x‖ ^ 2 := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    packetOperator_adjoint_mul,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    adjoint_supportProjection, supportProjection_idempotent]

/-- Exact conservation of coherent energy across the retained and discarded branches. -/
theorem paperPacketDefect_energy (s : RestrictionPacket E G)
    (x : PacketHilbert (E := E) (G := G)) :
    ‖packetOperator s x‖ ^ 2 + ‖paperPacketDefect s x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hp := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
    (supportProjection (G := G) (sourceSupport s)) x
  rw [adjoint_supportProjection, supportProjection_idempotent] at hp
  rw [paperPacketDefect_apply, norm_sub_sq (𝕜 := ℂ), paperPacket_norm_sq]
  rw [← hp]
  ring

/-- Compression plus the complex defect is faithful on the whole native Hilbert space. -/
theorem paperPacketDefect_record_injective (s : RestrictionPacket E G) :
    Function.Injective (fun x : PacketHilbert (E := E) (G := G) =>
      (packetOperator s x, paperPacketDefect s x)) := by
  intro x y h
  have ht : packetOperator s x = packetOperator s y := congrArg Prod.fst h
  have hd : paperPacketDefect s x = paperPacketDefect s y := congrArg Prod.snd h
  calc
    x = (packetOperator s).adjoint (packetOperator s x) + paperPacketDefect s x :=
      (paperPacketDefect_reconstruction s x).symm
    _ = (packetOperator s).adjoint (packetOperator s y) + paperPacketDefect s y := by
      rw [ht, hd]
    _ = y := paperPacketDefect_reconstruction s y

/-- The two branches retain the exact squared distance, hence relative complex amplitudes. -/
theorem paperPacketDefect_distance (s : RestrictionPacket E G)
    (x y : PacketHilbert (E := E) (G := G)) :
    ‖packetOperator s x - packetOperator s y‖ ^ 2 +
      ‖paperPacketDefect s x - paperPacketDefect s y‖ ^ 2 = ‖x - y‖ ^ 2 := by
  simpa only [map_sub] using paperPacketDefect_energy s (x - y)

/-- A packet preserves a vector's full energy exactly when its discarded component vanishes. -/
theorem paperPacketDefect_eq_zero_iff (s : RestrictionPacket E G)
    (x : PacketHilbert (E := E) (G := G)) :
    paperPacketDefect s x = 0 ↔ ‖packetOperator s x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := paperPacketDefect_energy s x
  constructor
  · intro hd
    simpa [hd] using h
  · intro hn
    have hz : ‖paperPacketDefect s x‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end

end GaloisForLFunctions.HTGeometry
