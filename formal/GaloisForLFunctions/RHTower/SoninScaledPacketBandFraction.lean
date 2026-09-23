import GaloisForLFunctions.RHTower.SoninScaledPacketBandEscape

/-!
# The band fraction of a rescaled packet, quantitatively

The escape estimate answers whether the band keeps half the energy.  Some bands are wide enough that
the crude threshold cannot decide them, yet the packet still escapes because its spectrum is far
away: the band radius may be large as long as the *gap* to the carrier is large too.

Dividing the band bound by the energy floor gives the fraction itself rather than a threshold: it is
the band's length times the half-width, times the squared tail at the gap, over the reference
square's mass.  Rapid decay of the tail then beats any polynomial growth of the band.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The tail majorant of the reference profile shrinks as the band grows. -/
theorem soninRefTailSup_antitone : Antitone soninRefTailSup :=
  GaloisForLFunctions.HTGeometry.fourierTailSup_antitone soninUnitBumpC

/-- **The energy floor under the two smallness inputs.**  Half the half-width times the reference
square's mass. -/
theorem norm_sq_soninScaledPacketEven_ge_half (m δ w : ℝ) (hδ : 0 < δ) (hm : δ < m)
    (hmean : |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1)
    (hSq : soninRefSqTailSup (δ * |w|) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    δ * (∫ y : ℝ, soninUnitBumpSq y) / 2 ≤
      ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ (2 : ℕ) := by
  refine le_trans ?_ (norm_sq_soninScaledPacketEven_ge m δ w hδ hm)
  have hSqnn : 0 ≤ soninRefSqTailSup (δ * |w|) := soninRefSqTailSup_nonneg _
  have h4 : 0 ≤ 4 * δ * soninRefSqTailSup (δ * |w|) :=
    mul_nonneg (mul_nonneg (by norm_num) hδ.le) hSqnn
  have hterm : |soninScaledPacketMean m δ (2 * Real.pi * w)| *
      (4 * δ * soninRefSqTailSup (δ * |w|)) ≤ 4 * δ * soninRefSqTailSup (δ * |w|) := by
    nlinarith [hmean, h4]
  have hdS : δ * soninRefSqTailSup (δ * |w|) ≤ δ * ((∫ y : ℝ, soninUnitBumpSq y) / 20) :=
    mul_le_mul_of_nonneg_left hSq hδ.le
  linarith [hterm, hdS]

/-- **The band fraction.**  The share of a packet's energy inside a band of radius `t` below its
carrier is at most the band's length times the half-width, times the squared tail bound at the gap,
over the reference square's mass. -/
theorem norm_sq_evenFourierCutoff_le_fraction_mul_norm_sq
    (m δ w t : ℝ) (hδ : 0 < δ) (hm : δ < m) (ht : 0 ≤ t) (htw : t < w)
    (hmean : |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1)
    (hSq : soninRefSqTailSup (δ * |w|) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    ‖evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ^ (2 : ℕ) ≤
      (16 * t * δ * (soninRefTailSup (δ * (w - t)) +
            |soninScaledPacketMean m δ (2 * Real.pi * w)| * soninRefTailSup 0) ^ (2 : ℕ) /
          (∫ y : ℝ, soninUnitBumpSq y)) *
        ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ (2 : ℕ) := by
  set I : ℝ := ∫ y : ℝ, soninUnitBumpSq y with hIdef
  set A : ℝ := soninRefTailSup (δ * (w - t)) +
    |soninScaledPacketMean m δ (2 * Real.pi * w)| * soninRefTailSup 0 with hAdef
  set N : ℝ := ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ (2 : ℕ) with hNdef
  have hI : 0 < I := integral_soninUnitBumpSq_pos
  have hAnn : 0 ≤ A := by
    have h1 : 0 ≤ soninRefTailSup (δ * (w - t)) := soninRefTailSup_nonneg _
    have h2 : 0 ≤ |soninScaledPacketMean m δ (2 * Real.pi * w)| * soninRefTailSup 0 :=
      mul_nonneg (abs_nonneg _) (soninRefTailSup_nonneg _)
    rw [hAdef]
    linarith
  have hfloor : δ * I / 2 ≤ N := norm_sq_soninScaledPacketEven_ge_half m δ w hδ hm hmean hSq
  have hband := norm_sq_evenFourierCutoff_soninScaledPacketEven_le_uniform m δ w t hδ ht htw
  -- the band bound in terms of `A`
  have hMA : 2 * δ * soninRefTailSup (δ * (w - t)) +
      |soninScaledPacketMean m δ (2 * Real.pi * w)| * (2 * δ * soninRefTailSup 0) =
      2 * δ * A := by
    rw [hAdef]
    ring
  rw [hMA] at hband
  have hband' : ‖evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ^ (2 : ℕ) ≤
      8 * t * δ ^ (2 : ℕ) * A ^ (2 : ℕ) := by
    refine le_trans hband ?_
    nlinarith [ht, sq_nonneg (δ * A)]
  -- trade one half-width for the energy
  have hδle : δ ≤ 2 * N / I := by
    rw [le_div_iff₀ hI]
    linarith [hfloor]
  have hcoef : (0 : ℝ) ≤ 8 * t * δ * A ^ (2 : ℕ) := by positivity
  have hstep : 8 * t * δ ^ (2 : ℕ) * A ^ (2 : ℕ) ≤ (8 * t * δ * A ^ (2 : ℕ)) * (2 * N / I) := by
    have := mul_le_mul_of_nonneg_left hδle hcoef
    nlinarith [this]
  refine le_trans hband' (le_trans hstep (le_of_eq ?_))
  ring

end RHTower
