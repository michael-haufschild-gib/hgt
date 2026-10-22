import GaloisForLFunctions.RHTower.XiBesselWeightBounds
import GaloisForLFunctions.RHTower.XiEndpointCancellation
import GaloisForLFunctions.RHTower.ExteriorDunsterPrimitive
import GaloisForLFunctions.RHTower.CCM.CCMFirstRowVanDerCorputBlocks
import GaloisForLFunctions.RHTower.ProlateDunsterComparisonBridge

/-!
# Differentiability of Dunster's weight

The weight is the amplitude at the inverse coordinate divided by the speed there and by the phase.
Each of those three has a known derivative — the amplitude's from the comparison bridge, the speed's
from the stationary-phase layer, and the inverse coordinate's from the inverse function theorem — so
the weight's derivative follows by the chain and quotient rules.

The transport identity is what lets the weight be presented in that quotient form in the first
place; without it the weight is a fourth root of a composite and its derivative is not accessible.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The amplitude at the inverse coordinate, differentiated. -/
theorem hasDerivAt_xiAmplitude_comp {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => xiAmplitude s (xiInverse s t))
      (xiAmplitudeDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹) r := by
  have hmem : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  exact (hasDerivAt_xiAmplitude hs0 hs1 hmem).comp r (hasDerivAt_xiInverse hs0 hs1 hr)

/-- The speed at the inverse coordinate, differentiated. -/
theorem hasDerivAt_xiSpeed_comp {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => xiSpeed s (xiInverse s t))
      (xiSpeedDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹) r := by
  have hmem : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hbase : HasDerivAt (xiSpeed s) (xiSpeedDeriv s (xiInverse s r)) (xiInverse s r) := by
    have h := hasDerivAt_xiSpeed (by linarith : s ≤ 1) hmem
    rwa [show xiInverse s r * (s - 1) / ((xiInverse s r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s (xiInverse s r))
      = xiSpeedDeriv s (xiInverse s r) from rfl] at h
  exact hbase.comp r (hasDerivAt_xiInverse hs0 hs1 hr)

/-- The weight in its quotient form, on the positive ray. -/
theorem xiBesselWeight_eq_quotient {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    xiBesselWeight s r
      = xiAmplitude s (xiInverse s r) / (xiSpeed s (xiInverse s r) * r) := by
  have hmem : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hspeed : 0 < xiSpeed s (xiInverse s r) :=
    lt_of_lt_of_le zero_lt_one (one_le_xiSpeed (by linarith) hmem)
  have h := xiAmplitude_mul_inv_xiSpeed_eq hs0 hs1 hr
  field_simp at h ⊢
  linarith [h]

/-- **The weight is differentiable.**  Its derivative is expressed through the amplitude and speed
derivatives at the inverse coordinate. -/
theorem hasDerivAt_xiBesselWeight {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    HasDerivAt (xiBesselWeight s)
      ((xiAmplitudeDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹
          * (xiSpeed s (xiInverse s r) * r)
        - xiAmplitude s (xiInverse s r)
          * (xiSpeedDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹ * r
              + xiSpeed s (xiInverse s r) * 1))
        / (xiSpeed s (xiInverse s r) * r) ^ (2 : ℕ)) r := by
  have hmem : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hspeed : 0 < xiSpeed s (xiInverse s r) :=
    lt_of_lt_of_le zero_lt_one (one_le_xiSpeed (by linarith) hmem)
  have hden : xiSpeed s (xiInverse s r) * r ≠ 0 := by positivity
  have hnum := hasDerivAt_xiAmplitude_comp hs0 hs1 hr
  have hd : HasDerivAt (fun t : ℝ => xiSpeed s (xiInverse s t) * t)
      (xiSpeedDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹ * r
        + xiSpeed s (xiInverse s r) * 1) r :=
    (hasDerivAt_xiSpeed_comp hs0 hs1 hr).mul (hasDerivAt_id r)
  have hquot := hnum.div hd hden
  refine hquot.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
  exact xiBesselWeight_eq_quotient hs0 hs1 ht

/-- The explicit derivative is the weight times its logarithmic derivative. -/
theorem xiBesselWeightDeriv_eq_mul {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    (xiAmplitudeDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹
          * (xiSpeed s (xiInverse s r) * r)
        - xiAmplitude s (xiInverse s r)
          * (xiSpeedDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹ * r
              + xiSpeed s (xiInverse s r) * 1))
        / (xiSpeed s (xiInverse s r) * r) ^ (2 : ℕ)
      = xiBesselWeight s r
        * (xiInverse s r
              / (2 * Real.sqrt (xiInverse s r ^ (2 : ℕ) - 1) * Real.sqrt (xiInverse s r ^ (2 : ℕ) - s))
            - 1 / (2 * r)
            - 3 * xiInverse s r * Real.sqrt (xiInverse s r ^ (2 : ℕ) - 1)
                / (2 * (xiInverse s r ^ (2 : ℕ) - s) * Real.sqrt (xiInverse s r ^ (2 : ℕ) - s))) := by
  have hx1 : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hxi : xiEndpointPhase s (xiInverse s r) = r := xiEndpointPhase_xiInverse hs0 hs1 hr
  set x : ℝ := xiInverse s r with hxdef
  have hu : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hv : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  set a : ℝ := Real.sqrt (x ^ (2 : ℕ) - 1) with hadef
  set b : ℝ := Real.sqrt (x ^ (2 : ℕ) - s) with hbdef
  have ha : 0 < a := Real.sqrt_pos.mpr hu
  have hb : 0 < b := Real.sqrt_pos.mpr hv
  have ha2 : a ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt hu.le
  have hb2 : b ^ (2 : ℕ) = x ^ (2 : ℕ) - s := Real.sq_sqrt hv.le
  have hrel : a ^ (2 : ℕ) - b ^ (2 : ℕ) = s - 1 := by rw [ha2, hb2]; ring
  have hV : xiSpeed s x = b / a := by
    rw [xiSpeed, Real.sqrt_div hv.le (x ^ (2 : ℕ) - 1), ← hadef, ← hbdef]
  have hVpos : (0 : ℝ) < xiSpeed s x := by rw [hV]; positivity
  have hA : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hx1
  have hBq : xiBesselWeight s r = xiAmplitude s x / (xiSpeed s x * r) :=
    xiBesselWeight_eq_quotient hs0 hs1 hr
  have hA' : xiAmplitudeDeriv s x
      = xiAmplitude s x * (phaseLogDefect s x / 2 - x / (2 * (x ^ (2 : ℕ) - s))) := rfl
  have hPLD : phaseLogDefect s x = xiSpeed s x / xiEndpointPhase s x - x / (x ^ (2 : ℕ) - 1) := rfl
  have hV' : xiSpeedDeriv s x = x * (s - 1) / ((x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s x) := rfl
  rw [hBq, hA', hPLD, hV', hxi, hV, ← ha2, ← hb2]
  have hApos : xiAmplitude s x ≠ 0 := ne_of_gt hA
  field_simp
  ring_nf
  linear_combination (2 * r * x) * hrel

/-- **The derivative of Dunster's weight is bounded on the compact phase range.**  This is the
derivative half of the `C^(1 : ℕ)` estimate: the weight is bounded by `2` and its logarithmic derivative
by `32`. -/
theorem abs_xiBesselWeightDeriv_le {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r)
    (hxle : xiInverse s r ≤ 2) :
    |(xiAmplitudeDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹
          * (xiSpeed s (xiInverse s r) * r)
        - xiAmplitude s (xiInverse s r)
          * (xiSpeedDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹ * r
              + xiSpeed s (xiInverse s r) * 1))
        / (xiSpeed s (xiInverse s r) * r) ^ (2 : ℕ)| ≤ 64 := by
  have hx1 : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hxi : xiEndpointPhase s (xiInverse s r) = r := xiEndpointPhase_xiInverse hs0 hs1 hr
  rw [xiBesselWeightDeriv_eq_mul hs0 hs1 hr, abs_mul]
  have hB : |xiBesselWeight s r| ≤ 2 := by
    rw [abs_of_nonneg (le_trans (by positivity) (inv_le_xiBesselWeight hs0 hs1 hr hxle))]
    exact xiBesselWeight_le_two hs0 hs1 hr
  have hL := abs_besselWeight_logDeriv_le hs0 hs1 hx1 hxle
  rw [hxi] at hL
  have hB0 : 0 ≤ |xiBesselWeight s r| := abs_nonneg _
  have hL0 : 0 ≤ |xiInverse s r
      / (2 * Real.sqrt (xiInverse s r ^ (2 : ℕ) - 1) * Real.sqrt (xiInverse s r ^ (2 : ℕ) - s))
      - 1 / (2 * r)
      - 3 * xiInverse s r * Real.sqrt (xiInverse s r ^ (2 : ℕ) - 1)
          / (2 * (xiInverse s r ^ (2 : ℕ) - s) * Real.sqrt (xiInverse s r ^ (2 : ℕ) - s))| := abs_nonneg _
  nlinarith [hB, hL, hB0, hL0]


/-- The derivative of Dunster's weight, as a function. -/
def xiBesselWeightDeriv (s r : ℝ) : ℝ :=
  (xiAmplitudeDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹
      * (xiSpeed s (xiInverse s r) * r)
    - xiAmplitude s (xiInverse s r)
      * (xiSpeedDeriv s (xiInverse s r) * (xiSpeed s (xiInverse s r))⁻¹ * r
          + xiSpeed s (xiInverse s r) * 1))
    / (xiSpeed s (xiInverse s r) * r) ^ (2 : ℕ)

theorem hasDerivAt_xiBesselWeight' {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    HasDerivAt (xiBesselWeight s) (xiBesselWeightDeriv s r) r :=
  hasDerivAt_xiBesselWeight hs0 hs1 hr

theorem abs_xiBesselWeightDeriv_le' {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r)
    (hxle : xiInverse s r ≤ 2) : |xiBesselWeightDeriv s r| ≤ 64 :=
  abs_xiBesselWeightDeriv_le hs0 hs1 hr hxle

theorem continuousOn_xiInverse {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (xiInverse s) (Set.Ioi 0) :=
  fun _ hr => (continuousAt_xiInverse hs0 hs1 hr).continuousWithinAt

theorem mapsTo_xiInverse {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Set.MapsTo (xiInverse s) (Set.Ioi 0) (Set.Ioi 1) :=
  fun _ hr => xiInverse_mem_Ioi hs0 hs1 hr

/-- The derivative of the weight is continuous on the positive ray. -/
theorem continuousOn_xiBesselWeightDeriv {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (xiBesselWeightDeriv s) (Set.Ioi 0) := by
  have hXc := continuousOn_xiInverse hs0 hs1
  have hmap := mapsTo_xiInverse hs0 hs1
  have hA : ContinuousOn (fun r : ℝ => xiAmplitude s (xiInverse s r)) (Set.Ioi 0) :=
    (continuousOn_xiAmplitude hs0 hs1).comp hXc hmap
  have hA' : ContinuousOn (fun r : ℝ => xiAmplitudeDeriv s (xiInverse s r)) (Set.Ioi 0) :=
    (continuousOn_xiAmplitudeDeriv hs0 hs1).comp hXc hmap
  have hV : ContinuousOn (fun r : ℝ => xiSpeed s (xiInverse s r)) (Set.Ioi 0) :=
    (continuousOn_xiSpeed s).comp hXc hmap
  have hV' : ContinuousOn (fun r : ℝ => xiSpeedDeriv s (xiInverse s r)) (Set.Ioi 0) :=
    (continuousOn_xiSpeedDeriv (by linarith)).comp hXc hmap
  have hVne : ∀ r ∈ Set.Ioi (0 : ℝ), xiSpeed s (xiInverse s r) ≠ 0 := by
    intro r hr
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_xiSpeed (by linarith) (xiInverse_mem_Ioi hs0 hs1 hr)))
  have hden : ∀ r ∈ Set.Ioi (0 : ℝ), (xiSpeed s (xiInverse s r) * r) ^ (2 : ℕ) ≠ 0 := by
    intro r hr
    exact pow_ne_zero 2 (mul_ne_zero (hVne r hr) (ne_of_gt hr))
  refine ContinuousOn.div ?_ ((hV.mul continuousOn_id).pow 2) hden
  refine ContinuousOn.sub ?_ ?_
  · exact (hA'.mul (hV.inv₀ hVne)).mul (hV.mul continuousOn_id)
  · exact hA.mul (((hV'.mul (hV.inv₀ hVne)).mul continuousOn_id).add
      (hV.mul continuousOn_const))


end GaloisForLFunctions.RHTower
