import GaloisForLFunctions.HTGeometry.PositivePrecisionOverlap

/-! The likelihood overlap has an explicit precision kernel and exact separation law. -/

noncomputable section
open GaloisForLFunctions.HTGeometry

namespace RHTower

def finiteWeilQuadraticTiltAffinity (s S : {s : ℝ // s < 2}) : ℝ :=
  positivePrecisionOverlap ⟨2 - s.val, sub_pos.mpr s.property⟩
    ⟨2 - S.val, sub_pos.mpr S.property⟩

theorem finiteWeilQuadraticTiltAffinity_pos (s S : {s : ℝ // s < 2}) :
    0 < finiteWeilQuadraticTiltAffinity s S :=
  positivePrecisionOverlap_pos _ _

theorem finiteWeilQuadraticTiltAffinity_le_one (s S : {s : ℝ // s < 2}) :
    finiteWeilQuadraticTiltAffinity s S ≤ 1 :=
  positivePrecisionOverlap_le_one _ _

theorem finiteWeilQuadraticTiltAffinity_eq_one_iff (s S : {s : ℝ // s < 2}) :
    finiteWeilQuadraticTiltAffinity s S = 1 ↔ s.val = S.val := by
  rw [finiteWeilQuadraticTiltAffinity, positivePrecisionOverlap_eq_one_iff]
  constructor <;> intro h <;> dsimp at h ⊢ <;> linarith

theorem finiteWeilQuadraticTiltAffinity_lt_one_iff (s S : {s : ℝ // s < 2}) :
    finiteWeilQuadraticTiltAffinity s S < 1 ↔ s.val ≠ S.val := by
  rw [lt_iff_le_and_ne, and_iff_right (finiteWeilQuadraticTiltAffinity_le_one s S)]
  exact not_congr (finiteWeilQuadraticTiltAffinity_eq_one_iff s S)

theorem finiteWeilQuadraticTiltAffinity_jeffreys (s S : {s : ℝ // s < 2}) :
    finiteWeilQuadraticTiltAffinity s S ^ 4 *
      (1 + ((s.val - S.val) ^ 2 / (2 * (2 - s.val) * (2 - S.val))) / 2) = 1 := by
  have h := positivePrecisionOverlap_jeffreys
    ⟨2 - s.val, sub_pos.mpr s.property⟩ ⟨2 - S.val, sub_pos.mpr S.property⟩
  have he : ((2 - s.val) - (2 - S.val)) ^ 2 = (s.val - S.val) ^ 2 := by ring
  simpa only [finiteWeilQuadraticTiltAffinity, he] using h

end RHTower
