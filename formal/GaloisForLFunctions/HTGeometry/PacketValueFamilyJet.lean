import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge
import GaloisForLFunctions.HTGeometry.IteratedDerivTranslate
import GaloisForLFunctions.HTGeometry.RegularizedTransformGauge

/-!
# Packet values are family jets of translated Cauchy transforms

The packet formalism evaluates one function at shifted nodes; the family gauge evaluates a jet
vector of translated functions at one node.  This file records that they are the same data, at an
arbitrary number of shifts.

The packet value is already generic in its shift index type, so nothing here is restricted to a
single translate.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- **Packet values are family jets of the translated Cauchy transforms.**  The packet formalism
reads one function at shifted nodes; the family gauge reads one jet vector of translated functions.
They agree. -/
theorem weightedBoundaryCarrierExpandedPacketValue_eq_familyJetVec
    {m n : ℕ} {row : Type} [Fintype row]
    (eta : Measure (OnePoint ℝ))
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration (Fin m)) (r : row)
    (t : Σ _ : Fin m, Fin (n + 1)) :
    F.weightedBoundaryCarrierExpandedPacketValue eta density (fun _ : Fin m => n + 1) packet shift
        (r, Fintype.equivFin (Σ _ : Fin m, Fin (n + 1)) t)
      = familyJetVec (n := n)
          (fun i w => cauchyTransform
            (weightedBoundaryCarrier F.base.toBoundaryFamily eta density) (w + shift.1 i))
          (packet.1 r) (Sum.inr (t.1, t.2)) := by
  rw [ClassicalAnalyticNevanlinnaCarrierFamily.weightedBoundaryCarrierExpandedPacketValue]
  show iteratedDeriv _ _ _ = _
  rw [(Fintype.equivFin (Σ _ : Fin m, Fin (n + 1))).symm_apply_apply t]
  show _ = iteratedDeriv (t.2 : ℕ)
    (fun w => cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily eta density)
      (w + shift.1 t.1)) (packet.1 r)
  rw [iteratedDeriv_comp_add_right]
  rfl

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
