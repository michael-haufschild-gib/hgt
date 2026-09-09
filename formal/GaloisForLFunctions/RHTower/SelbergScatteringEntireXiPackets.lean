import GaloisForLFunctions.RHTower.SelbergScatteringEntireCusp
import GaloisForLFunctions.RHTower.SelbergScatteringEntirePreimage

/-!
# Full Xi-parameter audit of the constructed entire-operator cusp packets

The pre-divisor cusp construction gives unit vectors in the actual transformed
operator domain at every real frequency. For an actual Xi copy, choose half its
ordinate as that frequency. At the full complex transformed scattering target,
their limiting residual is exactly the norm of the difference between the
ordinate-only hyperbolic cosine and the full Casimir transform. It vanishes
exactly when that original Xi zero is critical. This is an exact audit of the
constructed sequence, not an assumption that its defect vanishes for all zeros.
The scalar transform also preserves the fixed quarter shift of the exponent;
no domain intertwiner for that shift is asserted.
-/

open Filter Topology
open RHTower.D4BMModularCore RHTower.SelbergScatteringEntireCusp
open RHTower.SelbergScatteringEntireOperator RHTower.SelbergScatteringEntireTransform

namespace RHTower.SelbergScatteringEntireXiPackets
noncomputable section

/-- The entire Casimir transform is invariant under the fixed quarter shift of its exponent. -/
theorem casimirTransform_quarter_exponent_shift (s : ℂ) :
    casimirTransform ((s + 1 / 4) * (1 - (s + 1 / 4))) =
      casimirTransform (s * (1 - s)) := by
  rw [casimirTransform_casimir, casimirTransform_casimir]
  convert Complex.cos_periodic (8 * Real.pi * (s - 1 / 2)) using 1
  congr 1
  ring

/-- Full transformed scattering parameter; the original zero's real part is retained. -/
def xiEntireTarget (q : XiZeroCopy) : ℂ :=
  casimirTransform (((q.1 : ℂ) / 2) * (1 - (q.1 : ℂ) / 2))

/-- Apply the pre-divisor cusp construction to the ordinate of an actual Xi copy. -/
def xiEntirePacket (q : XiZeroCopy) (n : ℕ) : entireOperator.domain :=
  entireCuspPacket ((q.1 : ℂ).im / 2) n

theorem xiEntirePacket_norm (q : XiZeroCopy) (n : ℕ) : ‖(xiEntirePacket q n : Space)‖ = 1 :=
  entireCuspPacket_norm _ _

theorem cuspEntireValue_half (t : ℝ) : cuspEntireValue (t / 2) = Real.cosh (4 * Real.pi * t) := by
  unfold cuspEntireValue
  congr 1
  ring

theorem cuspEntireValue_half_eq_nativePartner (t : ℝ) :
    (cuspEntireValue (t / 2) : ℂ) = casimirTransform (nativePartner t) := by
  rw [casimirTransform_nativePartner, casimirTransform_criticalCasimir, cuspEntireValue_half]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_cosh]

/-- The exact mismatch of these constructed packets with the full transformed Xi parameter. -/
def xiEntirePacketDefect (q : XiZeroCopy) : ℝ :=
  ‖(Real.cosh (4 * Real.pi * (q.1 : ℂ).im) : ℂ) - xiEntireTarget q‖

theorem xiEntirePacketDefect_zero_iff (q : XiZeroCopy) :
    xiEntirePacketDefect q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [xiEntirePacketDefect, norm_eq_zero, sub_eq_zero, ← cuspEntireValue_half,
    cuspEntireValue_half_eq_nativePartner]
  exact (xi_real_native_preimage_iff q (nativePartner (q.1 : ℂ).im)).trans (and_iff_left rfl)

/-- The full complex Xi target has precisely this limiting residual on the constructed packets. -/
theorem xiEntirePacket_residual_tendsto (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => ‖entireOperator (xiEntirePacket q n) -
      xiEntireTarget q • (xiEntirePacket q n : Space)‖) atTop (𝓝 (xiEntirePacketDefect q)) := by
  simpa only [xiEntirePacket, xiEntirePacketDefect, cuspEntireValue_half] using
    entireCuspPacket_residual_at_tendsto ((q.1 : ℂ).im / 2) (xiEntireTarget q)

/-- This actual source sequence reaches the original transformed target exactly on the critical line. -/
theorem xiEntirePacket_residual_zero_iff (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => ‖entireOperator (xiEntirePacket q n) -
      xiEntireTarget q • (xiEntirePacket q n : Space)‖) atTop (𝓝 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hz
    exact (xiEntirePacketDefect_zero_iff q).mp
      (tendsto_nhds_unique (xiEntirePacket_residual_tendsto q) hz)
  · intro hq
    have hz := (xiEntirePacketDefect_zero_iff q).mpr hq
    simpa only [hz] using xiEntirePacket_residual_tendsto q

end
end RHTower.SelbergScatteringEntireXiPackets
