import GaloisForLFunctions.RHTower.SoninShellCutBandTotalBound
import GaloisForLFunctions.RHTower.SoninShellCutEnergyExplicitFloor

/-!
# A band bound free of the annulus

The band estimate carries the packet's mean, which depends on the annulus.  Replacing the mean by
one — legitimate under the same tail condition the rest of the construction needs — makes the bound
depend only on the shell, the cut's size, the carrier and the radius.

With that, the band budget of every packet of a cut is below one expression, and the energy bound
can be stated with no free parameters beyond the schedule.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The annulus-free band bound at radius `t` for a cut with carrier `w`. -/
def soninShellCutBandBoundAt (b c : ℝ) (N : ℕ) (w t : ℝ) : ℝ :=
  2 * t * (2 * soninShellCutWidth b c N *
      soninRefTailSup (soninShellCutWidth b c N * (w - t)) +
    2 * soninShellCutWidth b c N * soninRefTailSup 0) ^ (2 : ℕ)

/-- The annulus-free high-side bound at radius `t`. -/
def soninShellCutHighBoundAt (b c : ℝ) (N : ℕ) (K : ℝ) (N₀ : ℕ) (t : ℝ) : ℝ :=
  2 * (K * soninShellCutWidth b c N ^ (2 : ℕ) / soninShellCutWidth b c N ^ (2 * N₀)) *
    (t ^ (1 - (2 * N₀ : ℝ)) / ((2 * N₀ : ℝ) - 1))

/-- **The band estimate without the mean.**  Under the tail condition the mean is below one, so it
can be dropped from the bound. -/
theorem norm_sq_evenFourierCutoff_soninShellCutPacket_le_uniform
    (b c w : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) (htw : t < w)
    (hmeanTail : 2 * soninRefTailSup (soninShellCutWidth b c N * |w|) ≤
      ∫ y : ℝ, soninUnitBumpData y)
    (i : Fin N) :
    ‖evenFourierCutoff t
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖ ^ (2 : ℕ) ≤
      soninShellCutBandBoundAt b c N w t := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hmean : |soninScaledPacketMean (soninShellCutCentre b c N i)
      (soninShellCutWidth b c N) (2 * Real.pi * w)| ≤ 1 :=
    abs_soninScaledPacketMean_le_one _ _ w hδ hmeanTail
  refine le_trans (norm_sq_evenFourierCutoff_soninShellCutPacket_le b c w hbc hN t ht htw i) ?_
  rw [soninShellCutBandBoundAt]
  set A : ℝ := 2 * soninShellCutWidth b c N *
    soninRefTailSup (soninShellCutWidth b c N * (w - t)) with hAdef
  set B : ℝ := 2 * soninShellCutWidth b c N * soninRefTailSup 0 with hBdef
  set μ : ℝ := |soninScaledPacketMean (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
    (2 * Real.pi * w)| with hμdef
  have hA : (0 : ℝ) ≤ A := by
    have := soninRefTailSup_nonneg (soninShellCutWidth b c N * (w - t))
    rw [hAdef]
    positivity
  have hB : (0 : ℝ) ≤ B := by
    have := soninRefTailSup_nonneg (0 : ℝ)
    rw [hBdef]
    positivity
  have hmeannn : (0 : ℝ) ≤ μ := abs_nonneg _
  have hle : A + μ * B ≤ A + B := by nlinarith [hmean, hB]
  have hnn : (0 : ℝ) ≤ A + μ * B := by positivity
  have hsq : (A + μ * B) ^ (2 : ℕ) ≤ (A + B) ^ (2 : ℕ) := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hnn hle
  exact mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 2 * t)

/-- **The annulus-free band budget of a cut packet.** -/
theorem exists_soninCouplingBandTotal_soninShellCutPacket_le_uniform (N₀ : ℕ) (hN₀ : 1 ≤ N₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c q : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r),
      0 < b → a ≤ b → 0 < a → a < q → 2 * q ≤ b → b < r * q →
      2 * soninRefTailSup (soninShellCutWidth b c N * |r * q|) ≤ ∫ y : ℝ, soninUnitBumpData y →
      ∀ i : Fin N,
        soninCouplingBandTotal a b (inv_pos.mpr (zero_lt_one.trans hr))
            (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
              (2 * Real.pi * (r * q)) (soninShellCutWidth_pos b c hbc hN)) ≤
          Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (r * b)) +
            Real.sqrt (soninShellCutBandBoundAt b c N (r * q) (r * a)) +
            Real.sqrt (soninShellCutBandBoundAt b c N (r * q) b) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sq_sub_evenFourierCutoff_soninShellCutPacket_le N₀ hN₀
  refine ⟨K, hK0, ?_⟩
  intro a b c q hbc N hN r hr hb hab ha haq hqb hbrq htail i
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans hr
  have hqpos : (0 : ℝ) < q := ha.trans haq
  refine soninCouplingBandTotal_soninShellCutPacket_le_of_sq_bounds a b c hb hab hbc hN hr
    (r * q) i _ _ _ (hK b c q hbc hN hr hqpos hqb htail i) ?_ ?_
  · exact norm_sq_evenFourierCutoff_soninShellCutPacket_le_uniform b c (r * q) hbc hN (r * a)
      (by positivity) (by nlinarith [haq, hrpos]) htail i
  · exact norm_sq_evenFourierCutoff_soninShellCutPacket_le_uniform b c (r * q) hbc hN b
      hb.le hbrq htail i

end RHTower
