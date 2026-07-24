import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCenteredGreenPacket
import GaloisForLFunctions.RHTower.PrimeArchThetaHalfDensityDampedTail

/-!
# Theta completed-Green first-atom domination universality

The centered completed-potential packet is an exact Green integral of the full theta source.
Whenever the translated window remains in the positive source half-line, uniform higher-atom
domination passes through the nonnegative Green kernel.  The packet is therefore quantitatively
controlled by the literal first theta atom.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The literal first-atom contribution to the centered hyperbolic Green packet. -/
def thetaCuspFirstAtomCenteredGreenPacket (L x : ℝ) : ℝ :=
  ∫ u : ℝ in 0..L,
    2 * Real.sinh ((L - u) / 2) *
      (thetaCuspSourceTerm (x + u) 1 +
        thetaCuspSourceTerm (x - u) 1)

/-- **Theta completed-Green first-atom domination universality law.**  A centered packet contained
in the positive source half-line is nonnegative and is bounded by the literal first-atom packet
with exactly the global higher-atom loss. -/
theorem thetaCuspCompletedTailPotentialCenteredDifference_firstAtomDomination
    {L x : ℝ} (hL : 0 ≤ L) (hLx : L < x) :
    0 ≤ thetaCuspCompletedTailPotentialCenteredDifference L x ∧
      thetaCuspCompletedTailPotentialCenteredDifference L x ≤
        (1 + thetaCuspHigherAtomDominationWeight) *
          thetaCuspFirstAtomCenteredGreenPacket L x := by
  constructor
  · exact thetaCuspCompletedTailPotentialCenteredDifference_nonneg hL x
  · rw [thetaCuspCompletedTailPotential_centeredDifference_eq_integral,
      thetaCuspFirstAtomCenteredGreenPacket,
      ← intervalIntegral.integral_const_mul]
    have hkernel :
        Continuous (fun u : ℝ => 2 * Real.sinh ((L - u) / 2)) := by
      fun_prop
    have hfirst :
        Continuous (fun y : ℝ => thetaCuspSourceTerm y 1) := by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop
    have hfullIntegrable :
        IntervalIntegrable
          (fun u : ℝ =>
            2 * Real.sinh ((L - u) / 2) *
              (thetaCuspFullSource (x + u) +
                thetaCuspFullSource (x - u)))
          volume 0 L := by
      apply Continuous.intervalIntegrable
      exact hkernel.mul
        ((contDiff_thetaCuspFullSource.continuous.comp
            (continuous_const.add continuous_id)).add
          (contDiff_thetaCuspFullSource.continuous.comp
            (continuous_const.sub continuous_id)))
    have hfirstIntegrable :
        IntervalIntegrable
          (fun u : ℝ =>
            2 * Real.sinh ((L - u) / 2) *
              (thetaCuspSourceTerm (x + u) 1 +
                thetaCuspSourceTerm (x - u) 1))
          volume 0 L := by
      apply Continuous.intervalIntegrable
      exact hkernel.mul
        ((hfirst.comp (continuous_const.add continuous_id)).add
          (hfirst.comp (continuous_const.sub continuous_id)))
    apply intervalIntegral.integral_mono_on hL
      hfullIntegrable (hfirstIntegrable.const_mul _)
    intro u hu
    have hxplus : 0 < x + u := by
      linarith [hu.1]
    have hxminus : 0 < x - u := by
      linarith [hu.2]
    have hplus :=
      thetaCuspFullSource_sub_first_le (x := x + u) hxplus.le
    have hminus :=
      thetaCuspFullSource_sub_first_le (x := x - u) hxminus.le
    have hsource :
        thetaCuspFullSource (x + u) +
            thetaCuspFullSource (x - u) ≤
          (1 + thetaCuspHigherAtomDominationWeight) *
            (thetaCuspSourceTerm (x + u) 1 +
              thetaCuspSourceTerm (x - u) 1) := by
      linarith
    have hkernelNonneg :
        0 ≤ 2 * Real.sinh ((L - u) / 2) :=
      mul_nonneg (by norm_num)
        (Real.sinh_nonneg_iff.mpr (by linarith [hu.2]))
    calc
      2 * Real.sinh ((L - u) / 2) *
            (thetaCuspFullSource (x + u) +
              thetaCuspFullSource (x - u)) ≤
          2 * Real.sinh ((L - u) / 2) *
            ((1 + thetaCuspHigherAtomDominationWeight) *
              (thetaCuspSourceTerm (x + u) 1 +
                thetaCuspSourceTerm (x - u) 1)) :=
        mul_le_mul_of_nonneg_left hsource hkernelNonneg
      _ = (1 + thetaCuspHigherAtomDominationWeight) *
          (2 * Real.sinh ((L - u) / 2) *
            (thetaCuspSourceTerm (x + u) 1 +
              thetaCuspSourceTerm (x - u) 1)) := by ring

end

end RHTower
