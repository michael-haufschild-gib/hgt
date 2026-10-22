import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCanonicalMetricAction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalAngularSourceXi
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification

/-! # The canonical QNM value vanishes with the physical self-source coefficient

Every term of the canonical radial cutoff and of the temporal corner carries the factor
`physicalSelfSourceCoefficient q`.  When it vanishes, the canonical action is zero on the whole
nonreal half-strip `-2 < Re w`, hence so is its QNM limit.  At a strict-right Xi zero the unit
canonical left sources never vanish, so no pointwise equivalence between QNM zeros and left-source
extinction can hold there. -/

open Set Filter Topology Complex

namespace RHTower.D4BMOriginalCanonicalAction
open D4BMJointSource D4BMOriginalHorizonGreenMatch D4BMOriginalMetricRadial
open D4BMOriginalCornerForcing D4BMOriginalCanonicalMetricCutoff D4BMOriginalCanonicalMetricGerm

set_option autoImplicit false

/-- With vanishing self-source coefficient, every cutoff `0 < e < 1` of the canonical radial
density is zero. -/
theorem canonicalMetricCutoff_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
    (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwr : -2 < w.re)
    (hP : physicalSelfSourceCoefficient q = 0) {e : ℝ} (he : e ∈ Ioo (0 : ℝ) 1) :
    canonicalMetricCutoff q br amp w e = 0 := by
  have hT := tortoiseOf_neg he
  have hI : (∫ x in tortoiseOf e..0, D4BMOriginalMetricOuter.outerDensity q br amp w x) = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (0 : ℂ)) fun x hx => ?_,
      intervalIntegral.integral_zero]
    rw [uIoo_of_le hT.le] at hx
    rw [D4BMOriginalMetricOuter.outerDensity_decomposition q br amp w hwr hx.2, hP]
    simp
  simp [canonicalMetricCutoff, hI, greenCoefficient, forcingCoefficient, hP]

/-- With vanishing self-source coefficient, the canonical radial value vanishes. -/
theorem canonicalRadialValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
    (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwr : -2 < w.re)
    (hP : physicalSelfSourceCoefficient q = 0) :
    canonicalRadialValue q br amp w = 0 := by
  have ht : Tendsto (canonicalMetricCutoff q br amp w) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with e he
    exact (canonicalMetricCutoff_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
      q br amp w hwr hP he).symm
  exact ht.limUnder_eq

/-- With vanishing self-source coefficient, the retained temporal corner vanishes identically. -/
theorem physicalCornerCandidate_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
    (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hP : physicalSelfSourceCoefficient q = 0) :
    physicalCornerCandidate q br amp w = 0 := by
  have hA : continuedCornerAmplitude q br amp = fun _ => 0 := by
    funext u
    simp [continuedCornerAmplitude, hP]
  simp [physicalCornerCandidate, hA, hP]

/-- With vanishing self-source coefficient, the canonical action vanishes on the physical
half-strip. -/
theorem canonicalAction_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
    (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwr : -2 < w.re)
    (hP : physicalSelfSourceCoefficient q = 0) :
    canonicalAction q br amp w = 0 := by
  rw [canonicalAction, canonicalRadialValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
    q br amp w hwr hP, physicalCornerCandidate_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
    q br amp w hP, add_zero]

/-- **Canonical QNM self-source zero law.**  If the physical self-source coefficient of `q`
vanishes, the canonical QNM value is zero for every branch, QNM side and amplitude. -/
theorem canonicalQNMValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
    (q : XiZeroCopy) (br side : Bool) (amp : ℂ) (hP : physicalSelfSourceCoefficient q = 0) :
    canonicalQNMValue q br side amp = 0 := by
  have hwr := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  have hopen : IsOpen {w : ℂ | -2 < w.re} := isOpen_lt continuous_const continuous_re
  have ht : Tendsto (canonicalAction q br amp) (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hwr)] with w hw
    exact (canonicalAction_eq_zero_of_physicalSelfSourceCoefficient_eq_zero
      q br amp w hw hP).symm
  exact ht.limUnder_eq

end RHTower.D4BMOriginalCanonicalAction

namespace RHTower
open D4BMJointSource D4BMOriginalCanonicalAction

set_option autoImplicit false

/-- The unit canonical left sources vanish exactly on the critical line. -/
theorem hbXiPeierlsMinusLeftSource_eq_zero_iff (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsMinusLeftSource n 1 q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsMinusLeftSource_eq, hbXiPeierlsMinusSource_eq_zero_iff one_ne_zero]

theorem hbXiPeierlsPlusLeftSource_eq_zero_iff (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsPlusLeftSource n 1 q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsPlusLeftSource_eq, hbXiPeierlsPlusSource_eq_zero_iff one_ne_zero]

/-- **Self-source-zero obstruction.**  At a strict-right Xi zero with vanishing physical
self-source coefficient, every canonical QNM value is zero, every unit canonical left source is
nonzero, and one of the three affine Xi collisions `ξ(5q/2 - 1) = 0`, `ξ(q/2) = 0`,
`ξ(3q/2) = 0` occurs. -/
theorem canonicalQNMValue_zero_ne_unitLeftSource_of_physicalSelfSourceCoefficient_eq_zero
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re) (hP : physicalSelfSourceCoefficient q = 0) :
    (∀ br side amp, canonicalQNMValue q br side amp = 0) ∧
      (∀ n, hbXiPeierlsMinusLeftSource n 1 q ≠ 0) ∧
      (∀ n, hbXiPeierlsPlusLeftSource n 1 q ≠ 0) ∧
      (xi (5 * (q.1 : ℂ) / 2 - 1) = 0 ∨ xi ((q.1 : ℂ) / 2) = 0 ∨ xi (3 * (q.1 : ℂ) / 2) = 0) :=
  ⟨fun br side amp =>
      canonicalQNMValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero q br side amp hP,
    fun n h => hq.ne' ((hbXiPeierlsMinusLeftSource_eq_zero_iff n q).mp h),
    fun n h => hq.ne' ((hbXiPeierlsPlusLeftSource_eq_zero_iff n q).mp h),
    (physicalSelfSourceCoefficient_zero_iff_xi q hq).mp hP⟩

/-- At such a zero, no pointwise bridge between QNM zeros and unit left-source extinction holds. -/
theorem not_canonicalQNMValue_eq_zero_iff_unitLeftSource_eq_zero
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re) (hP : physicalSelfSourceCoefficient q = 0)
    (br side : Bool) (amp : ℂ) (n : ℕ) :
    ¬ (canonicalQNMValue q br side amp = 0 ↔ hbXiPeierlsMinusLeftSource n 1 q = 0) := fun h =>
  (canonicalQNMValue_zero_ne_unitLeftSource_of_physicalSelfSourceCoefficient_eq_zero q hq hP).2.1
    n (h.mp (canonicalQNMValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero q br side amp hP))

end RHTower
