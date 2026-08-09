import GaloisForLFunctions.RHTower.BesselWeightedPrimitiveInterior
import GaloisForLFunctions.RHTower.XiBesselWeightDeriv
import GaloisForLFunctions.RHTower.XiCoordinate
import GaloisForLFunctions.RHTower.ProlateDunsterBesselOffDiagonal

/-!
# The compact-range primitive for the prolate Bessel profile

Every ingredient is now available: the transport identity turns the Liouville–Green amplitude into
the phase-variable weight, the substitution carries the integral into the phase variable, the weight
is bounded above and below with bounded derivative, and the primitive estimate tolerates the weight's
degeneracy at the origin.

Assembling them bounds the integral of the corpus's own regular Bessel profile over the compact
exterior range by a constant over the frequency, uniformly in the endpoint.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

theorem xiInverse_le_two {s r X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r)
    (hX1 : 1 ≤ X) (hX2 : X ≤ 2) (hrle : r ≤ xiEndpointPhase s X) : xiInverse s r ≤ 2 := by
  have h2 : (0 : ℝ) < xiEndpointPhase s 2 := by
    rw [← xiEndpointPhase_one s]
    exact strictMonoOn_xiEndpointPhase hs0 hs1 (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by norm_num))
      (by norm_num)
  have hmono : xiEndpointPhase s X ≤ xiEndpointPhase s 2 :=
    (strictMonoOn_xiEndpointPhase hs0 hs1).monotoneOn (mem_Ici.mpr hX1)
      (mem_Ici.mpr (by norm_num)) hX2
  have hinv : xiInverse s (xiEndpointPhase s 2) = 2 :=
    xiInverse_xiEndpointPhase hs0 hs1 (by norm_num)
  have := (strictMonoOn_xiInverse hs0 hs1).monotoneOn (mem_Ioi.mpr hr) (mem_Ioi.mpr h2)
    (le_trans hrle hmono)
  rwa [hinv] at this

/-- **The compact-range primitive in the phase variable.** -/
theorem abs_integral_xiBesselWeight_le {s X c : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hX1 : 1 < X) (hX2 : X ≤ 2) (hc : 0 < c) :
    |∫ r in (0 : ℝ)..(xiEndpointPhase s X),
        r * xiBesselWeight s r * besselJ0 (c * r)|
      ≤ 648 * 64 / (c * Real.sqrt c) := by
  have hR0 : 0 < xiEndpointPhase s X := by
    rw [← xiEndpointPhase_one s]
    exact strictMonoOn_xiEndpointPhase hs0 hs1 (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr (le_of_lt hX1)) hX1
  have hR : xiEndpointPhase s X ≤ 2 :=
    xiEndpointPhase_le_two hs0 (by linarith) (le_of_lt hX1) hX2
  refine abs_integral_mul_besselJ0_le_interior hc hR0 hR
    (fun r hr => hasDerivAt_xiBesselWeight' hs0 hs1 hr.1)
    (fun r hr => ((hasDerivAt_xiBesselWeight' hs0 hs1 hr.1).continuousAt).continuousWithinAt)
    ((continuousOn_xiBesselWeightDeriv hs0 hs1).mono (fun r hr => mem_Ioi.mpr hr.1))
    (fun r hr => ?_) (fun r hr => ?_)
  · have h := xiBesselWeight_le_two hs0 hs1 hr.1
    have h0 : 0 ≤ xiBesselWeight s r :=
      le_trans (by positivity) (inv_le_xiBesselWeight hs0 hs1 hr.1
        (xiInverse_le_two hs0 hs1 hr.1 (le_of_lt hX1) hX2 hr.2))
    rw [abs_of_nonneg h0]
    linarith
  · exact abs_xiBesselWeightDeriv_le' hs0 hs1 hr.1
      (xiInverse_le_two hs0 hs1 hr.1 (le_of_lt hX1) hX2 hr.2)

/-- The transported integrand is the Liouville–Green amplitude, by the transport identity. -/
theorem integral_xiAmplitude_besselJ0_eq {s X c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hX1 : 1 ≤ X) :
    (∫ x in (1 : ℝ)..X, xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x))
      = ∫ r in (0 : ℝ)..(xiEndpointPhase s X),
          r * xiBesselWeight s r * besselJ0 (c * r) := by
  rw [intervalIntegral_comp_xiEndpointPhase hs0 hs1 hX1
    (fun r : ℝ => r * xiBesselWeight s r * besselJ0 (c * r))]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hX1] at hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]
    have h1 : xiSpeed s 1 = 0 := by
      rw [xiSpeed]
      norm_num
    have h2 : xiAmplitude s 1 = 0 := by
      rw [xiAmplitude, xiEndpointPhase_one]
      norm_num
    rw [h1, h2]
    ring
  · have hr : 0 < xiEndpointPhase s x := by
      rw [← xiEndpointPhase_one s]
      exact strictMonoOn_xiEndpointPhase hs0 hs1 (mem_Ici.mpr le_rfl)
        (mem_Ici.mpr (le_of_lt h)) h
    have hinv : xiInverse s (xiEndpointPhase s x) = x :=
      xiInverse_xiEndpointPhase hs0 hs1 h
    have h41 := xiAmplitude_mul_inv_xiSpeed_eq hs0 hs1 hr
    rw [hinv] at h41
    have hspeed : xiSpeed s x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_xiSpeed (by linarith) h))
    have hkey : xiAmplitude s x
        = xiSpeed s x * (xiEndpointPhase s x * xiBesselWeight s (xiEndpointPhase s x)) := by
      field_simp at h41
      linarith [h41]
    rw [hkey]
    ring

/-- **`(47)`: the compact-range primitive of the regular prolate Bessel profile.**  The integral of
the corpus's own profile over the compact exterior range is bounded by a constant over the
frequency, uniformly in the endpoint. -/
theorem abs_integral_radialProlateBesselProfile_le {s X c : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hX1 : 1 < X) (hX2 : X ≤ 2) (hc : 0 < c) :
    |∫ x in (1 : ℝ)..X, radialProlateBesselProfile s c x| ≤ 648 * 64 / c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hrw : (∫ x in (1 : ℝ)..X, radialProlateBesselProfile s c x)
      = Real.sqrt c * ∫ x in (1 : ℝ)..X,
          xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [radialProlateBesselProfile]
    ring
  rw [hrw, integral_xiAmplitude_besselJ0_eq hs0 hs1 (le_of_lt hX1), abs_mul,
    abs_of_pos hsc]
  have hbase := abs_integral_xiBesselWeight_le hs0 hs1 hX1 hX2 hc
  have hstep : Real.sqrt c * |∫ r in (0 : ℝ)..(xiEndpointPhase s X),
      r * xiBesselWeight s r * besselJ0 (c * r)|
      ≤ Real.sqrt c * (648 * 64 / (c * Real.sqrt c)) :=
    mul_le_mul_of_nonneg_left hbase hsc.le
  refine le_trans hstep (le_of_eq ?_)
  field_simp


end GaloisForLFunctions.RHTower
