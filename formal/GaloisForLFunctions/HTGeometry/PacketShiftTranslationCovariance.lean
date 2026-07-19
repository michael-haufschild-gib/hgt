import GaloisForLFunctions.HTGeometry.TranslateFamilyEscapesPatch
import GaloisForLFunctions.HTGeometry.CompactNoncriticalProjectiveRowPacketAtlas

/-!
# Translation covariance of the combined node family

The source nodes seen by the evaluation geometry are the sums of a row packet and a shift
configuration.  Translating the packet and the shift oppositely therefore leaves every combined node
fixed.

Everything downstream — the jets, the evaluation matrix, its determinant — depends on the packet and
shift only through this combined family, so all of it inherits the covariance.  This is what lets a
family of translated packets sweep a compact patch of shifts.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Translating a row packet preserves injectivity. -/
def translatePacket {row : Type*} [Fintype row]
    (packet : InjectiveProjectiveRowPacket row) (t : ℂ) :
    InjectiveProjectiveRowPacket row :=
  ⟨fun r => packet.1 r - t, fun _ _ hab => packet.2 (sub_left_inj.mp hab)⟩

@[simp]
theorem translatePacket_apply {row : Type*} [Fintype row]
    (packet : InjectiveProjectiveRowPacket row) (t : ℂ) (r : row) :
    (translatePacket packet t).1 r = packet.1 r - t := rfl

/-- Translating a shift configuration preserves injectivity. -/
def translateShift {ι : Type*} [Fintype ι]
    (shift : InjectiveShiftConfiguration ι) (t : ℂ) :
    InjectiveShiftConfiguration ι :=
  ⟨fun i => shift.1 i - t, fun _ _ hab => shift.2 (sub_left_inj.mp hab)⟩

@[simp]
theorem translateShift_apply {ι : Type*} [Fintype ι]
    (shift : InjectiveShiftConfiguration ι) (t : ℂ) (i : ι) :
    (translateShift shift t).1 i = shift.1 i - t := rfl

/-- **Translation covariance of the combined nodes.**  Translating the packet is the same as
translating the shift: the combined node family is unchanged. -/
theorem combinedProjectiveRowShiftPacket_translatePacket
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) (t : ℂ) :
    combinedProjectiveRowShiftPacket (translatePacket packet t) shift =
      combinedProjectiveRowShiftPacket packet (translateShift shift t) := by
  funext x
  simp only [combinedProjectiveRowShiftPacket, translatePacket_apply, translateShift_apply]
  ring

/-- Any quantity determined by the combined node family is covariant under opposite translation of
packet and shift. -/
theorem eq_of_combined_translate
    {row ι V : Type*} [Fintype row] [Fintype ι]
    (Φ : (row × ι → ℂ) → V)
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) (t : ℂ) :
    Φ (combinedProjectiveRowShiftPacket (translatePacket packet t) shift) =
      Φ (combinedProjectiveRowShiftPacket packet (translateShift shift t)) := by
  rw [combinedProjectiveRowShiftPacket_translatePacket]

/-- Translating the packet twice composes additively. -/
theorem translatePacket_translatePacket {row : Type*} [Fintype row]
    (packet : InjectiveProjectiveRowPacket row) (s t : ℂ) :
    translatePacket (translatePacket packet s) t = translatePacket packet (s + t) := by
  apply Subtype.ext
  funext r
  simp only [translatePacket_apply]
  ring

end

end GaloisForLFunctions.HTGeometry
