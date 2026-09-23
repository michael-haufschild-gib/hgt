import GaloisForLFunctions.RHTower.SoninScaledPacketHighTailBound
import GaloisForLFunctions.RHTower.SoninShellCutBandBound

/-!
# The high-side estimate under a tail condition

The high-side bound was proved with the packet mean assumed below one.  That assumption is itself a
consequence of the reference tail being small, so the estimate can be stated with a single condition
on the product of half-width and carrier — the same condition the orthonormality and the energy
floor already require.

Specialized to a shell cut, this gives the third of the budget's three squared bounds in the terms
the cut supplies.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- **The high-side bound from a tail condition.**  The mean hypothesis is discharged by the
reference tail. -/
theorem exists_norm_sq_sub_evenFourierCutoff_le_of_tail (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m δ w t : ℝ) (hδ : 0 < δ), 0 < w → 2 * w ≤ t →
      2 * soninRefTailSup (δ * |w|) ≤ ∫ y : ℝ, soninUnitBumpData y →
        ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ -
            evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ^ (2 : ℕ) ≤
          2 * (K * δ ^ (2 : ℕ) / δ ^ (2 * N)) *
            (t ^ (1 - (2 * N : ℝ)) / ((2 * N : ℝ) - 1)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le N hN
  refine ⟨K, hK0, ?_⟩
  intro m δ w t hδ hw ht htail
  exact hK m δ w t hδ hw ht (abs_soninScaledPacketMean_le_one m δ w hδ htail)

/-- **The high-side bound for a cut packet.**  With the carrier ratio at most half the outer radius,
the band at `r b` sits above twice the carrier. -/
theorem exists_norm_sq_sub_evenFourierCutoff_soninShellCutPacket_le (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b c q : ℝ) (hbc : b < c) {M : ℕ} (hM : 0 < M) {r : ℝ},
      1 < r → 0 < q → 2 * q ≤ b →
      2 * soninRefTailSup (soninShellCutWidth b c M * |r * q|) ≤ ∫ y : ℝ, soninUnitBumpData y →
        ∀ i : Fin M,
          ‖soninScaledPacketEven (soninShellCutCentre b c M i) (soninShellCutWidth b c M)
              (2 * Real.pi * (r * q)) (soninShellCutWidth_pos b c hbc hM) -
            evenFourierCutoff (r * b)
              (soninScaledPacketEven (soninShellCutCentre b c M i) (soninShellCutWidth b c M)
                (2 * Real.pi * (r * q)) (soninShellCutWidth_pos b c hbc hM))‖ ^ (2 : ℕ) ≤
          2 * (K * soninShellCutWidth b c M ^ (2 : ℕ) / soninShellCutWidth b c M ^ (2 * N)) *
            ((r * b) ^ (1 - (2 * N : ℝ)) / ((2 * N : ℝ) - 1)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sq_sub_evenFourierCutoff_le_of_tail N hN
  refine ⟨K, hK0, ?_⟩
  intro b c q hbc M hM r hr hq hqb htail i
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans hr
  have hwpos : (0 : ℝ) < r * q := by positivity
  have hband : 2 * (r * q) ≤ r * b := by nlinarith [hqb, hrpos]
  exact hK (soninShellCutCentre b c M i) (soninShellCutWidth b c M) (r * q) (r * b)
    (soninShellCutWidth_pos b c hbc hM) hwpos hband htail

end RHTower
