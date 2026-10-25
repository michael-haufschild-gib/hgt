import GaloisForLFunctions.BezoutValuationIncidence.FixedVaughanPacketsHaveTwoExplicitObstructions

/-!
An empty cutoff removes the small-small row and the smooth obstruction.
Replacing its unused coefficient reduces packet admission to the linear
mean and the remaining receiver direction.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- An empty cutoff removes the small-small piece identically. -/
theorem pmPronicVaughanPiece_smallSmall_eq_zero_of_zero_cutoff (ε : ℝ) {U V : ℕ}
    (hUV : U = 0 ∨ V = 0) (n : ℕ) : pmPronicVaughanPiece ε U V n 2 = 0 := by
  rcases hUV with rfl | rfl <;> simp [pmPronicVaughanPiece]

/-- The corresponding linear mean also vanishes. -/
theorem pmPronicVaughanMean_smallSmall_eq_zero_of_zero_cutoff (ε : ℝ) {U V : ℕ}
    (hUV : U = 0 ∨ V = 0) : pmPronicVaughanMean ε U V 2 = 0 := by
  rcases hUV with rfl | rfl <;> simp [pmPronicVaughanMean, pmPronicVaughanSmallDensity]

/-- An empty cutoff removes the smooth-power obstruction for every coefficient vector. -/
theorem pmPronicVaughanPacketSmoothMean_eq_zero_of_zero_cutoff (ε : ℝ) {U V : ℕ}
    (hUV : U = 0 ∨ V = 0) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketSmoothMean ε U V w = 0 := by
  rcases hUV with rfl | rfl <;> simp [pmPronicVaughanPacketSmoothMean]

/-- Replacing the unused small-small coefficient changes neither the packet nor its mean. -/
theorem pmPronicVaughanPacket_replace_smallSmall_of_zero_cutoff (ε : ℝ) {U V : ℕ}
    (hUV : U = 0 ∨ V = 0) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacket ε U V ![w 0, w 1, w 3, w 3, w 4] =
        pmPronicVaughanPacket ε U V w ∧
      pmPronicVaughanPacketLinearMean ε U V ![w 0, w 1, w 3, w 3, w 4] =
        pmPronicVaughanPacketLinearMean ε U V w := by
  constructor
  · funext n
    simp only [pmPronicVaughanPacket, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change w 0 * pmPronicVaughanPiece ε U V n 0 +
      (w 1 * pmPronicVaughanPiece ε U V n 1 +
        (w 3 * pmPronicVaughanPiece ε U V n 2 +
          (w 3 * pmPronicVaughanPiece ε U V n 3 + w 4 * pmPronicVaughanPiece ε U V n 4))) = _
    simp only [pmPronicVaughanPiece_smallSmall_eq_zero_of_zero_cutoff ε hUV n, mul_zero]
  · simp only [pmPronicVaughanPacketLinearMean, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change w 0 * pmPronicVaughanMean ε U V 0 +
      (w 1 * pmPronicVaughanMean ε U V 1 +
        (w 3 * pmPronicVaughanMean ε U V 2 +
          (w 3 * pmPronicVaughanMean ε U V 3 + w 4 * pmPronicVaughanMean ε U V 4))) = _
    simp only [pmPronicVaughanMean_smallSmall_eq_zero_of_zero_cutoff ε hUV, mul_zero]

/-- At an empty cutoff the original receiver is the sole obstruction after linear centering. -/
theorem pmPronicVaughanPacketAdmitted_iff_of_zero_cutoff {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketAdmitted ε U V w ↔
      pmPronicVaughanPacketLinearMean ε U V w = 0 ∧
        (w 3 = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) := by
  have heq := pmPronicVaughanPacket_replace_smallSmall_of_zero_cutoff ε hUV w
  have hclass (hL : pmPronicVaughanPacketLinearMean ε U V w = 0) :
      pmPronicVaughanPacketAdmitted ε U V w ↔
        w 3 = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
    have h := pmPronicVaughanPacketAdmitted_iff_of_equal_convolution_coefficients hε.le U V
      ![w 0, w 1, w 3, w 3, w 4] rfl (heq.2.trans hL)
    simpa only [pmPronicVaughanPacketAdmitted, heq.1] using h
  constructor
  · intro hw
    have hL := pmPronicVaughanPacketLinearMean_eq_zero_of_admitted hε U V w hw
    exact ⟨hL, (hclass hL).mp hw⟩
  · rintro ⟨hL, hI⟩
    exact (hclass hL).mpr hI

#print axioms pmPronicVaughanPiece_smallSmall_eq_zero_of_zero_cutoff
#print axioms pmPronicVaughanMean_smallSmall_eq_zero_of_zero_cutoff
#print axioms pmPronicVaughanPacketSmoothMean_eq_zero_of_zero_cutoff
#print axioms pmPronicVaughanPacket_replace_smallSmall_of_zero_cutoff
#print axioms pmPronicVaughanPacketAdmitted_iff_of_zero_cutoff
end GaloisForLFunctions.BezoutValuationIncidence
