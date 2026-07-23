import GaloisForLFunctions.HTGeometry.PacketValueFamilyJet
import GaloisForLFunctions.HTGeometry.TranslatedFamilyGauge

/-!
# Translated Herglotz packet-relation descent universality

A differential relation among translated Herglotz presentations descends through the polynomial
Nevanlinna gauge to the translated Cauchy family.  Expanded packet values are exactly the family-jet
coordinates.  Combining the two transports gives a nonzero polynomial relation directly on every
packet row whose base node lies in the relation domain.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- **Translated Herglotz packet-relation descent universality law.**  Any family differential
relation on the translated Herglotz presentations produces one nonzero polynomial which vanishes
on the exact expanded packet-jet vector at every packet row inside the domain. -/
theorem exists_packetRelation_of_translatedHerglotzPresentation_relation
    {m : ℕ} {row : Type} [Fintype row]
    (eta : Measure (OnePoint ℝ))
    (density : Lp ℝ (⊤ : ENNReal) eta)
    [IsFiniteMeasure (weightedBoundaryCarrier F.base.toBoundaryFamily eta density)]
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration (Fin m))
    (M : ℂ) (U : Set ℂ)
    (hU : ∀ z ∈ U, ∀ i, (z + shift.1 i).im ≠ 0)
    (hrow : ∀ r, packet.1 r ∈ U)
    (hrel : FamilyDifferentiallyAlgebraicOn
      (fun i z => (z + shift.1 i) * M + (1 + (z + shift.1 i) ^ 2) *
        cauchyTransform
          (weightedBoundaryCarrier F.base.toBoundaryFamily eta density)
          (z + shift.1 i)) U) :
    ∃ (n : ℕ) (P : MvPolynomial (FamilyJetIndex m n) ℂ), P ≠ 0 ∧
      ∀ r : row,
        MvPolynomial.eval
          (Sum.elim (fun _ : Unit => packet.1 r)
            (fun p : Fin m × Fin (n + 1) =>
              F.weightedBoundaryCarrierExpandedPacketValue eta density
                (fun _ : Fin m => n + 1) packet shift
                (r, Fintype.equivFin (Σ _ : Fin m, Fin (n + 1)) ⟨p.1, p.2⟩))) P = 0 := by
  have hcauchy := familyDifferentiallyAlgebraicOn_translatedCauchy_of_presentation
    (weightedBoundaryCarrier F.base.toBoundaryFamily eta density) M shift.1 hU hrel
  obtain ⟨n, P, hP, hzero⟩ := hcauchy
  refine ⟨n, P, hP, fun r => ?_⟩
  have hvec :
      Sum.elim (fun _ : Unit => packet.1 r)
          (fun p : Fin m × Fin (n + 1) =>
            F.weightedBoundaryCarrierExpandedPacketValue eta density
              (fun _ : Fin m => n + 1) packet shift
              (r, Fintype.equivFin (Σ _ : Fin m, Fin (n + 1)) ⟨p.1, p.2⟩)) =
        familyJetVec (n := n)
          (fun i w => cauchyTransform
            (weightedBoundaryCarrier F.base.toBoundaryFamily eta density)
            (w + shift.1 i)) (packet.1 r) := by
    funext q
    cases q with
    | inl u => cases u; rfl
    | inr p =>
        simpa using
          F.weightedBoundaryCarrierExpandedPacketValue_eq_familyJetVec
            eta density packet shift r (⟨p.1, p.2⟩ : Σ _ : Fin m, Fin (n + 1))
  rw [hvec]
  exact hzero (packet.1 r) (hrow r)

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
