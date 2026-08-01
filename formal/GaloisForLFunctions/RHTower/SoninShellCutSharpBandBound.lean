import GaloisForLFunctions.RHTower.SoninShellCutUniformBandBound

/-!
# A band bound with the mean kept

Replacing the packet mean by one loses too much at a band whose radius grows with the scale: there
the band's length cancels the half-width, and what remains is the global majorant, which does not
shrink.  Keeping the mean's own estimate repairs this, because the mean is itself a tail at the
carrier, and the carrier is further from the origin than the gap.

So the whole bound becomes one tail at the gap times a constant of the reference profile, and every
occurrence of the global majorant is multiplied by a factor that vanishes with the gap.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The band bound with the mean estimated rather than discarded: one tail at the gap, times a
constant of the reference profile. -/
def soninShellCutSharpBandBoundAt (b c : ℝ) (N : ℕ) (w t : ℝ) : ℝ :=
  2 * t * (2 * soninShellCutWidth b c N *
      soninRefTailSup (soninShellCutWidth b c N * (w - t)) *
    (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) ^ 2

/-- **The sharp band estimate.**  The mean is a tail at the carrier, hence below the tail at the
gap, so the whole bound is one tail at the gap times a profile constant. -/
theorem norm_sq_evenFourierCutoff_soninShellCutPacket_le_sharp
    (b c w : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) (htw : t < w) (i : Fin N) :
    ‖evenFourierCutoff t
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖ ^ 2 ≤
      soninShellCutSharpBandBoundAt b c N w t := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hJ₀ : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpData y := integral_soninUnitBumpData_pos
  set δ : ℝ := soninShellCutWidth b c N with hδdef
  set μ : ℝ := |soninScaledPacketMean (soninShellCutCentre b c N i) δ (2 * Real.pi * w)| with hμdef
  set S₁ : ℝ := soninRefTailSup (δ * (w - t)) with hS₁def
  set S₀ : ℝ := soninRefTailSup 0 with hS₀def
  have hS₁nn : 0 ≤ S₁ := soninRefTailSup_nonneg _
  have hS₀nn : 0 ≤ S₀ := soninRefTailSup_nonneg _
  have hμnn : 0 ≤ μ := abs_nonneg _
  -- the mean is a tail at the carrier
  have hmeanbd : μ * (∫ y : ℝ, soninUnitBumpData y) ≤ 2 * soninRefTailSup (δ * |w|) :=
    abs_soninScaledPacketMean_le_tailSup _ δ w hδ
  -- the carrier is further out than the gap
  have hanti : soninRefTailSup (δ * |w|) ≤ S₁ := by
    refine soninRefTailSup_antitone ?_
    have hwabs : w - t ≤ |w| := by
      have : w ≤ |w| := le_abs_self w
      linarith
    exact mul_le_mul_of_nonneg_left hwabs hδ.le
  have hμle : μ * (∫ y : ℝ, soninUnitBumpData y) ≤ 2 * S₁ := by linarith
  -- assemble the bound on the tail factor
  have hM : 2 * δ * S₁ + μ * (2 * δ * S₀) ≤
      2 * δ * S₁ * (1 + 2 * S₀ / (∫ y : ℝ, soninUnitBumpData y)) := by
    rw [mul_add, mul_one]
    have hprod : μ * (∫ y : ℝ, soninUnitBumpData y) * (2 * δ * S₀) ≤ (2 * S₁) * (2 * δ * S₀) :=
      mul_le_mul_of_nonneg_right hμle (by positivity)
    have hkey : μ * (2 * δ * S₀) ≤ 2 * δ * S₁ * (2 * S₀ / (∫ y : ℝ, soninUnitBumpData y)) := by
      have hgoal : 2 * δ * S₁ * (2 * S₀ / (∫ y : ℝ, soninUnitBumpData y)) =
          (4 * δ * S₁ * S₀) / (∫ y : ℝ, soninUnitBumpData y) := by ring
      rw [hgoal, le_div_iff₀ hJ₀]
      linarith [hprod]
    linarith
  have hbase := norm_sq_evenFourierCutoff_soninShellCutPacket_le b c w hbc hN t ht htw i
  rw [soninShellCutSharpBandBoundAt]
  refine le_trans hbase ?_
  have hnn : (0 : ℝ) ≤ 2 * δ * S₁ + μ * (2 * δ * S₀) := by positivity
  have hsq : (2 * δ * S₁ + μ * (2 * δ * S₀)) ^ 2 ≤
      (2 * δ * S₁ * (1 + 2 * S₀ / (∫ y : ℝ, soninUnitBumpData y))) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hnn hM
  exact mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 2 * t)

end RHTower
