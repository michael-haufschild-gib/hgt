import GaloisForLFunctions.RHTower.SoninShellCutHighTail

/-!
# The cut packet's band budget, fully estimated

The two below-carrier bands are instances of the uniform band estimate at radii `b` and `r a`, each
needing only that the radius sits below the carrier `r q`; the above-carrier term is the high-side
tail.  Feeding all three into the square-root interface bounds the band budget of every packet of a
shell cut.

Only three conditions on the schedule are used: the carrier ratio between the inner radius and half
the outer one, the scale large enough that the carrier clears the outer radius, and the reference
tail small at the product of half-width and carrier.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The uniform band estimate at a cut packet. -/
theorem norm_sq_evenFourierCutoff_soninShellCutPacket_le
    (b c w : ℝ) (hbc : b < c) {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t) (htw : t < w)
    (i : Fin M) :
    ‖evenFourierCutoff t
        (soninScaledPacketEven (soninShellCutCentre b c M i) (soninShellCutWidth b c M)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hM))‖ ^ (2 : ℕ) ≤
      2 * t * (2 * soninShellCutWidth b c M *
            soninRefTailSup (soninShellCutWidth b c M * (w - t)) +
          |soninScaledPacketMean (soninShellCutCentre b c M i) (soninShellCutWidth b c M)
              (2 * Real.pi * w)| *
            (2 * soninShellCutWidth b c M * soninRefTailSup 0)) ^ (2 : ℕ) :=
  norm_sq_evenFourierCutoff_soninScaledPacketEven_le_uniform _ _ w t
    (soninShellCutWidth_pos b c hbc hM) ht htw

/-- **The band budget of a cut packet, estimated.**  Three spectral bounds, entering through their
square roots. -/
theorem exists_soninCouplingBandTotal_soninShellCutPacket_le (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c q : ℝ) (hbc : b < c)
      {M : ℕ} (hM : 0 < M) {r : ℝ} (hr : 1 < r),
      0 < b → a ≤ b → 0 < a → a < q → 2 * q ≤ b → b < r * q →
      2 * soninRefTailSup (soninShellCutWidth b c M * |r * q|) ≤ ∫ y : ℝ, soninUnitBumpData y →
      ∀ i : Fin M,
        soninCouplingBandTotal a b (inv_pos.mpr (zero_lt_one.trans hr))
            (soninScaledPacketEven (soninShellCutCentre b c M i) (soninShellCutWidth b c M)
              (2 * Real.pi * (r * q)) (soninShellCutWidth_pos b c hbc hM)) ≤
          Real.sqrt (2 * (K * soninShellCutWidth b c M ^ (2 : ℕ) /
                soninShellCutWidth b c M ^ (2 * N)) *
              ((r * b) ^ (1 - (2 * N : ℝ)) / ((2 * N : ℝ) - 1))) +
            Real.sqrt (2 * (r * a) * (2 * soninShellCutWidth b c M *
                  soninRefTailSup (soninShellCutWidth b c M * (r * q - r * a)) +
                |soninScaledPacketMean (soninShellCutCentre b c M i) (soninShellCutWidth b c M)
                    (2 * Real.pi * (r * q))| *
                  (2 * soninShellCutWidth b c M * soninRefTailSup 0)) ^ (2 : ℕ)) +
            Real.sqrt (2 * b * (2 * soninShellCutWidth b c M *
                  soninRefTailSup (soninShellCutWidth b c M * (r * q - b)) +
                |soninScaledPacketMean (soninShellCutCentre b c M i) (soninShellCutWidth b c M)
                    (2 * Real.pi * (r * q))| *
                  (2 * soninShellCutWidth b c M * soninRefTailSup 0)) ^ (2 : ℕ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sq_sub_evenFourierCutoff_soninShellCutPacket_le N hN
  refine ⟨K, hK0, ?_⟩
  intro a b c q hbc M hM r hr hb hab ha haq hqb hbrq htail i
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans hr
  have hqpos : (0 : ℝ) < q := ha.trans haq
  refine soninCouplingBandTotal_soninShellCutPacket_le_of_sq_bounds a b c hb hab hbc hM hr
    (r * q) i _ _ _ (hK b c q hbc hM hr hqpos hqb htail i) ?_ ?_
  · exact norm_sq_evenFourierCutoff_soninShellCutPacket_le b c (r * q) hbc hM (r * a)
      (by positivity) (by nlinarith [haq, hrpos]) i
  · exact norm_sq_evenFourierCutoff_soninShellCutPacket_le b c (r * q) hbc hM b hb.le hbrq i

end RHTower
