import GaloisForLFunctions.RHTower.XiEndpointReflectionDefectEnergy
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiThermalQuartetCubicChargeBound

/-!
# The bounded thermal endpoint-resolvent gap

The signed-quarter boundary value of the completed prime--Gamma moment germ admits a second,
positive thermal comparison.  For a reciprocal-square Xi coordinate `z = x + iy`, with
`x = xiThermalNode q > 0`, the exact pointwise identity is

`re (z / (1 + z / 4)) - x / (1 + x / 4)
  = y^2 / (4 * (1 + x / 4) * normSq (1 + z / 4))`.

Summing gives the endpoint curvature as the thermal value of the bounded rational observable
`x |-> x / (1 + x / 4)` plus a nonnegative orientation defect.  The defect vanishes exactly
under RH.  Consequently the remaining prime--polar absolute-abscissa inequality is equivalent
to one scalar equality between the explicit thermal resolvent value and the already evaluated
endpoint source constant.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The bounded rational observable evaluated on the positive Xi thermal spectrum. -/
def xiThermalEndpointResolventValue : ℝ :=
  ∑' q : XiZeroCopy,
    xiThermalNode q / (1 + xiThermalNode q / 4)

/-- The same bounded observable on the first `N` atoms of the canonical finite Xi thermal
system. -/
def xiThermalEndpointResolventTruncation (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
    xiThermalNode (xiThermalEnumeration j) /
      (1 + xiThermalNode (xiThermalEnumeration j) / 4)

/-- The positive atomwise gap between the holomorphic endpoint resolvent and its real thermal
compression. -/
def xiThermalEndpointResolventDefectTerm (q : XiZeroCopy) : ℝ :=
  (xiZeroCopyReciprocalSquare q).im ^ 2 /
    (4 * (1 + xiThermalNode q / 4) *
      Complex.normSq (1 + xiZeroCopyReciprocalSquare q / 4))

/-- The complete bounded-resolvent orientation defect. -/
def xiThermalEndpointResolventDefect : ℝ :=
  ∑' q : XiZeroCopy, xiThermalEndpointResolventDefectTerm q

/-- The unit-modulus scattering phase of the quarter resolvent. -/
def quarterResolventScatteringPhase (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (1 + z / 4) / (1 + z / 4)

/-- The Xi endpoint scattering phase attached to one reciprocal-square divisor coordinate. -/
def xiThermalEndpointScatteringPhase (q : XiZeroCopy) : ℂ :=
  quarterResolventScatteringPhase (xiZeroCopyReciprocalSquare q)

lemma one_add_quarter_ne_zero {z : ℂ} (hz : 0 < z.re) :
    (1 + z / 4 : ℂ) ≠ 0 := by
  intro hzero
  have hre0 := congrArg Complex.re hzero
  rw [Complex.add_re, Complex.div_re, Complex.zero_re] at hre0
  norm_num [Complex.normSq_apply] at hre0
  linarith

/-- Accretivity makes the quarter-resolvent scattering factor a unitary scalar. -/
theorem norm_quarterResolventScatteringPhase {z : ℂ} (hz : 0 < z.re) :
    ‖quarterResolventScatteringPhase z‖ = 1 := by
  rw [quarterResolventScatteringPhase, norm_div]
  have hnorm : ‖(starRingEnd ℂ) (1 + z / 4)‖ = ‖1 + z / 4‖ := by
    simpa only using norm_star (1 + z / 4 : ℂ)
  rw [hnorm]
  exact div_self (norm_ne_zero_iff.mpr (one_add_quarter_ne_zero hz))

/-- The phase displacement is exactly the normalized transverse square. -/
theorem normSq_one_sub_quarterResolventScatteringPhase
    {z : ℂ} (hz : 0 < z.re) :
    Complex.normSq (1 - quarterResolventScatteringPhase z) =
      z.im ^ 2 / (4 * Complex.normSq (1 + z / 4)) := by
  let w : ℂ := 1 + z / 4
  have hw : w ≠ 0 := one_add_quarter_ne_zero hz
  have hone : 1 - (starRingEnd ℂ) w / w =
      (w - (starRingEnd ℂ) w) / w := by
    field_simp [hw]
  rw [quarterResolventScatteringPhase]
  change Complex.normSq (1 - (starRingEnd ℂ) w / w) = _
  rw [hone, Complex.normSq_div]
  have hwre : w.re = 1 + z.re / 4 := by
    simp [w]
  have hwim : w.im = z.im / 4 := by
    simp [w]
  have hnum : Complex.normSq (w - (starRingEnd ℂ) w) = z.im ^ 2 / 4 := by
    rw [Complex.normSq_apply]
    simp [hwre, hwim]
    ring_nf
  rw [hnum]
  ring

/-- Phase locking occurs exactly when the accretive coordinate is real. -/
theorem quarterResolventScatteringPhase_eq_one_iff_im_eq_zero
    {z : ℂ} (hz : 0 < z.re) :
    quarterResolventScatteringPhase z = 1 ↔ z.im = 0 := by
  constructor
  · intro hphase
    have henergy := normSq_one_sub_quarterResolventScatteringPhase hz
    rw [hphase, sub_self, Complex.normSq_zero] at henergy
    have hw : (1 + z / 4 : ℂ) ≠ 0 := one_add_quarter_ne_zero hz
    have hden : (4 * Complex.normSq (1 + z / 4)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Complex.normSq_pos.mpr hw).ne'
    exact sq_eq_zero_iff.mp ((div_eq_zero_iff.mp henergy.symm).resolve_right hden)
  · intro him
    have hzstar : (starRingEnd ℂ) z = z := by
      apply Complex.ext
      · simp
      · simp [him]
    have hstar : (starRingEnd ℂ) (1 + z / 4) = 1 + z / 4 := by
      rw [map_add, map_one, map_div₀, hzstar, map_ofNat]
    rw [quarterResolventScatteringPhase, hstar,
      div_self (one_add_quarter_ne_zero hz)]

theorem norm_xiThermalEndpointScatteringPhase (q : XiZeroCopy) :
    ‖xiThermalEndpointScatteringPhase q‖ = 1 := by
  exact norm_quarterResolventScatteringPhase (xiThermalNode_pos q)

theorem xiThermalEndpointScatteringPhase_eq_one_iff_im_eq_zero
    (q : XiZeroCopy) :
    xiThermalEndpointScatteringPhase q = 1 ↔
      (xiZeroCopyReciprocalSquare q).im = 0 := by
  exact quarterResolventScatteringPhase_eq_one_iff_im_eq_zero
    (xiThermalNode_pos q)

/-- The atomwise resolvent defect is the weighted squared displacement of a unitary scattering
phase from the identity. -/
theorem xiThermalEndpointResolventDefectTerm_eq_phaseLockingEnergy
    (q : XiZeroCopy) :
    xiThermalEndpointResolventDefectTerm q =
      Complex.normSq (1 - xiThermalEndpointScatteringPhase q) /
        (1 + xiThermalNode q / 4) := by
  rw [xiThermalEndpointResolventDefectTerm,
    xiThermalEndpointScatteringPhase,
    normSq_one_sub_quarterResolventScatteringPhase (xiThermalNode_pos q)]
  have ha : (1 + xiThermalNode q / 4) ≠ 0 := by
    nlinarith [xiThermalNode_pos q]
  have hw : (1 + xiZeroCopyReciprocalSquare q / 4 : ℂ) ≠ 0 :=
    one_add_quarter_ne_zero (xiThermalNode_pos q)
  have hn : Complex.normSq (1 + xiZeroCopyReciprocalSquare q / 4) ≠ 0 :=
    (Complex.normSq_pos.mpr hw).ne'
  field_simp [ha, hn]

/-- The complete endpoint defect is the weighted locking energy of the unitary scattering
phases. -/
theorem xiThermalEndpointResolventDefect_eq_phaseLockingEnergy :
    xiThermalEndpointResolventDefect =
      ∑' q : XiZeroCopy,
        Complex.normSq (1 - xiThermalEndpointScatteringPhase q) /
          (1 + xiThermalNode q / 4) := by
  rw [xiThermalEndpointResolventDefect]
  exact tsum_congr xiThermalEndpointResolventDefectTerm_eq_phaseLockingEnergy

/-- Elementary resolvent polarization: replacing a right-half-plane complex coordinate by its
real part loses exactly one positively weighted transverse square. -/
lemma re_quarterResolvent_sub_realQuarterResolvent
    (z : ℂ) (hz : 0 < z.re) :
    (z / (1 + z / 4)).re - z.re / (1 + z.re / 4) =
      z.im ^ 2 /
        (4 * (1 + z.re / 4) * Complex.normSq (1 + z / 4)) := by
  have ha : 0 < 1 + z.re / 4 := by linarith
  have hre : (1 + z / 4 : ℂ).re = 1 + z.re / 4 := by
    rw [Complex.add_re, Complex.div_re]
    norm_num [Complex.normSq_apply]
    ring
  have him : (1 + z / 4 : ℂ).im = z.im / 4 := by
    rw [Complex.add_im, Complex.div_im]
    norm_num [Complex.normSq_apply]
    ring
  have hnormSq : Complex.normSq (1 + z / 4) =
      (1 + z.re / 4) ^ 2 + (z.im / 4) ^ 2 := by
    rw [Complex.normSq_apply, hre, him]
    ring
  have hden : (1 + z / 4 : ℂ) ≠ 0 := by
    intro hzero
    have hre0 := congrArg Complex.re hzero
    rw [hre, Complex.zero_re] at hre0
    nlinarith
  have hnorm : Complex.normSq (1 + z / 4) ≠ 0 :=
    (Complex.normSq_pos.mpr hden).ne'
  rw [Complex.div_re]
  rw [hre, him, hnormSq]
  field_simp [ha.ne', hnorm]
  ring

theorem xiThermalEndpointResolventDefectTerm_nonneg (q : XiZeroCopy) :
    0 ≤ xiThermalEndpointResolventDefectTerm q := by
  have hx : 0 < 1 + xiThermalNode q / 4 := by
    nlinarith [xiThermalNode_pos q]
  have hre : (1 + xiZeroCopyReciprocalSquare q / 4 : ℂ).re =
      1 + xiThermalNode q / 4 := by
    rw [Complex.add_re, Complex.div_re]
    norm_num [Complex.normSq_apply, xiThermalNode]
    ring
  have hden : (1 + xiZeroCopyReciprocalSquare q / 4 : ℂ) ≠ 0 := by
    intro hzero
    have hre0 := congrArg Complex.re hzero
    rw [hre, Complex.zero_re] at hre0
    nlinarith [xiThermalNode_pos q]
  rw [xiThermalEndpointResolventDefectTerm]
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hx.le)
      (Complex.normSq_pos.mpr hden).le)

/-- The thermal endpoint-resolvent series is absolutely summable. -/
theorem summable_xiThermalEndpointResolventValue :
    Summable (fun q : XiZeroCopy =>
      xiThermalNode q / (1 + xiThermalNode q / 4)) := by
  have hnode : Summable (fun q : XiZeroCopy => xiThermalNode q) := by
    simpa using summable_xiThermalNode_pow 0
  apply Summable.of_norm_bounded hnode
  intro q
  have hx := (xiThermalNode_pos q).le
  have hden : 1 ≤ 1 + xiThermalNode q / 4 := by
    nlinarith [xiThermalNode_pos q]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx (by positivity))]
  exact div_le_self hx hden

theorem xiThermalEndpointResolventSummand_pos (q : XiZeroCopy) :
    0 < xiThermalNode q / (1 + xiThermalNode q / 4) :=
  div_pos (xiThermalNode_pos q) (by nlinarith [xiThermalNode_pos q])

set_option maxHeartbeats 500000 in
/-- The finite static thermal resolvent values converge unconditionally to the complete positive
thermal value. -/
theorem tendsto_xiThermalEndpointResolventTruncation :
    Tendsto xiThermalEndpointResolventTruncation atTop
      (nhds xiThermalEndpointResolventValue) := by
  let e : ℕ ≃ XiZeroCopy :=
    Equiv.ofBijective xiThermalEnumeration xiThermalEnumeration_bijective
  have hsum : HasSum (fun q : XiZeroCopy =>
      xiThermalNode q / (1 + xiThermalNode q / 4))
      xiThermalEndpointResolventValue := by
    simpa [xiThermalEndpointResolventValue] using
      summable_xiThermalEndpointResolventValue.hasSum
  have hsumNat : HasSum (fun j : ℕ =>
      xiThermalNode (e j) / (1 + xiThermalNode (e j) / 4))
      xiThermalEndpointResolventValue := e.hasSum_iff.mpr hsum
  have ht := hsumNat.tendsto_sum_nat
  simpa [xiThermalEndpointResolventTruncation, e] using ht

theorem xiThermalEndpointResolventValue_pos :
    0 < xiThermalEndpointResolventValue := by
  obtain ⟨z, hz⟩ := xiDivisorSupport_infinite.nonempty
  let rho : XiDivisorSupport := ⟨z, hz⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by omega
    exact ⟨rho, ⟨0, hn⟩⟩
  have hterm := summable_xiThermalEndpointResolventValue.le_tsum q
    (fun j _ => (xiThermalEndpointResolventSummand_pos j).le)
  rw [← xiThermalEndpointResolventValue] at hterm
  exact (xiThermalEndpointResolventSummand_pos q).trans_le hterm

/-- The holomorphic quarter-resolvent series is the endpoint reciprocal-square resolvent. -/
theorem summable_xiCenteredQuarterResolvent :
    Summable (fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q /
        (1 + xiZeroCopyReciprocalSquare q / 4)) := by
  apply (summable_xiReciprocalSquareResolventTerm XiC_I_half_ne).congr
  intro q
  rw [xiReciprocalSquareResolventTerm]
  have hsq : (I / 2 : ℂ) ^ 2 = -1 / 4 := by
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hsq]
  ring

/-- The evaluated endpoint curvature is the real part of the holomorphic quarter resolvent over
the complete multiplicity-exact Xi divisor. -/
theorem xiEndpointCompletedCurvature_eq_tsum_centeredQuarterResolvent_re :
    xiEndpointCompletedCurvature =
      ∑' q : XiZeroCopy,
        (xiZeroCopyReciprocalSquare q /
          (1 + xiZeroCopyReciprocalSquare q / 4)).re := by
  rw [← Complex.re_tsum summable_xiCenteredQuarterResolvent,
    xiEndpointCompletedCurvature_eq_cross_re]
  congr 1
  apply tsum_congr
  intro q
  rw [← endpoint_term_eq q, xiReciprocalSquareResolventTerm]
  have hsq : (I / 2 : ℂ) ^ 2 = -1 / 4 := by
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hsq]
  ring

/-- The positive endpoint-resolvent defect is summable. -/
theorem summable_xiThermalEndpointResolventDefect :
    Summable xiThermalEndpointResolventDefectTerm := by
  have hsource : Summable (fun q : XiZeroCopy =>
      (xiZeroCopyReciprocalSquare q /
        (1 + xiZeroCopyReciprocalSquare q / 4)).re) :=
    summable_xiCenteredQuarterResolvent.mapL Complex.reCLM
  have hdiff := hsource.sub summable_xiThermalEndpointResolventValue
  apply hdiff.congr
  intro q
  simpa only [xiThermalNode, xiThermalEndpointResolventDefectTerm] using
    re_quarterResolvent_sub_realQuarterResolvent
      (xiZeroCopyReciprocalSquare q) (xiThermalNode_pos q)

/-- **Bounded thermal endpoint-resolvent gap law.** -/
theorem xiEndpointCompletedCurvature_sub_thermalEndpointResolventValue_eq_defect :
    xiEndpointCompletedCurvature - xiThermalEndpointResolventValue =
      xiThermalEndpointResolventDefect := by
  rw [xiEndpointCompletedCurvature_eq_tsum_centeredQuarterResolvent_re,
    xiThermalEndpointResolventValue, xiThermalEndpointResolventDefect]
  have hsource : Summable (fun q : XiZeroCopy =>
      (xiZeroCopyReciprocalSquare q /
        (1 + xiZeroCopyReciprocalSquare q / 4)).re) :=
    summable_xiCenteredQuarterResolvent.mapL Complex.reCLM
  rw [← hsource.tsum_sub summable_xiThermalEndpointResolventValue]
  apply tsum_congr
  intro q
  simpa only [xiThermalNode, xiThermalEndpointResolventDefectTerm] using
    re_quarterResolvent_sub_realQuarterResolvent
      (xiZeroCopyReciprocalSquare q) (xiThermalNode_pos q)

theorem xiThermalEndpointResolventDefect_nonneg :
    0 ≤ xiThermalEndpointResolventDefect :=
  tsum_nonneg xiThermalEndpointResolventDefectTerm_nonneg

/-- The bounded endpoint defect is at most one quarter of the unsmoothed transverse thermal
energy.  Thus the resolvent observable is a contractive detector of the same RH obstruction. -/
theorem xiThermalEndpointResolventDefectTerm_le_quarter_orientationTerm
    (q : XiZeroCopy) :
    xiThermalEndpointResolventDefectTerm q ≤
      (xiZeroCopyReciprocalSquare q).im ^ 2 / 4 := by
  let z := xiZeroCopyReciprocalSquare q
  have hx : 1 ≤ 1 + z.re / 4 := by
    have hzre : 0 < z.re := by
      simpa only [z, xiThermalNode] using xiThermalNode_pos q
    nlinarith
  have hnorm : 1 ≤ Complex.normSq (1 + z / 4) := by
    rw [Complex.normSq_apply]
    have hre : (1 + z / 4 : ℂ).re = 1 + z.re / 4 := by
      simp
    rw [hre]
    nlinarith [sq_nonneg ((1 + z / 4 : ℂ).im),
      sq_nonneg (z.re / 4)]
  have hprod : 1 ≤ (1 + z.re / 4) * Complex.normSq (1 + z / 4) :=
    one_le_mul_of_one_le_of_one_le hx hnorm
  have hden : 4 ≤
      4 * (1 + z.re / 4) * Complex.normSq (1 + z / 4) := by
    nlinarith
  rw [xiThermalEndpointResolventDefectTerm]
  change z.im ^ 2 /
      (4 * (1 + z.re / 4) * Complex.normSq (1 + z / 4)) ≤ z.im ^ 2 / 4
  exact div_le_div_of_nonneg_left (sq_nonneg z.im) (by norm_num) hden

/-- Global quantitative transfer from the bounded resolvent gap to the quadratic thermal/source
gap. -/
theorem xiThermalEndpointResolventDefect_le_quarter_orientationEnergy :
    xiThermalEndpointResolventDefect ≤ xiThermalOrientationEnergy / 4 := by
  rw [xiThermalEndpointResolventDefect, xiThermalOrientationEnergy, ← tsum_div_const]
  exact summable_xiThermalEndpointResolventDefect.tsum_le_tsum
    xiThermalEndpointResolventDefectTerm_le_quarter_orientationTerm
    (summable_xiThermalOrientationTerm.div_const 4)

/-- The endpoint gap is controlled by the cube of the exact source-selected off-line radius. -/
theorem xiThermalEndpointResolventDefect_le_endpointRadius_cube :
    xiThermalEndpointResolventDefect ≤
      (xiEndpointCompletedCurvature /
        (4 - xiEndpointCompletedCurvature)) ^ 3 := by
  calc
    xiThermalEndpointResolventDefect ≤ xiThermalOrientationEnergy / 4 :=
      xiThermalEndpointResolventDefect_le_quarter_orientationEnergy
    _ ≤ xiThermalExactCubicEndpointBudget / 4 :=
      (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
        xiThermalOrientationEnergy_le_exactCubicEndpointBudget
    _ = (xiEndpointCompletedCurvature /
        (4 - xiEndpointCompletedCurvature)) ^ 3 := by
      rw [xiThermalExactCubicEndpointBudget]
      ring

/-- The remaining bounded-resolvent obstruction is already below `1 / 600000`. -/
theorem xiThermalEndpointResolventDefect_lt_one_over_sixHundredThousand :
    xiThermalEndpointResolventDefect < 1 / 600000 := by
  have h := xiThermalEndpointResolventDefect_le_quarter_orientationEnergy
  have hE := xiThermalOrientationEnergy_lt_one_over_oneHundredFiftyThousand
  nlinarith

/-- **Sharp unconditional endpoint window.**  The positive thermal resolvent lies within
`1 / 600000` of the completed source value; exact saturation remains equivalent to RH. -/
theorem xiThermalEndpointResolventValue_source_window :
    0 ≤ xiEndpointCompletedCurvature - xiThermalEndpointResolventValue ∧
      xiEndpointCompletedCurvature - xiThermalEndpointResolventValue < 1 / 600000 := by
  rw [xiEndpointCompletedCurvature_sub_thermalEndpointResolventValue_eq_defect]
  exact ⟨xiThermalEndpointResolventDefect_nonneg,
    xiThermalEndpointResolventDefect_lt_one_over_sixHundredThousand⟩

theorem endpointCompletedCurvature_sub_one_over_sixHundredThousand_lt_thermalResolvent :
    xiEndpointCompletedCurvature - 1 / 600000 <
      xiThermalEndpointResolventValue := by
  linarith [xiThermalEndpointResolventValue_source_window.2]

/-- The bounded positive thermal observable lies below the exact endpoint source value. -/
theorem xiThermalEndpointResolventValue_le_endpointCompletedCurvature :
    xiThermalEndpointResolventValue ≤ xiEndpointCompletedCurvature := by
  have h := xiThermalEndpointResolventDefect_nonneg
  rw [← xiEndpointCompletedCurvature_sub_thermalEndpointResolventValue_eq_defect] at h
  linarith

/-- Vanishing of the bounded-resolvent defect is exactly RH. -/
theorem xiThermalEndpointResolventDefect_eq_zero_iff_rh :
    xiThermalEndpointResolventDefect = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    apply xiThermalOrientationEnergy_eq_zero_iff_rh.mp
    rw [xiThermalOrientationEnergy]
    rw [show (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q).im ^ 2) = 0 by
      funext q
      have hterm := summable_xiThermalEndpointResolventDefect.le_tsum q
        (fun j _ => xiThermalEndpointResolventDefectTerm_nonneg j)
      rw [← xiThermalEndpointResolventDefect, hzero] at hterm
      have htermzero : xiThermalEndpointResolventDefectTerm q = 0 :=
        le_antisymm hterm (xiThermalEndpointResolventDefectTerm_nonneg q)
      have hx : 0 < 1 + xiThermalNode q / 4 := by
        nlinarith [xiThermalNode_pos q]
      have hre : (1 + xiZeroCopyReciprocalSquare q / 4 : ℂ).re =
          1 + xiThermalNode q / 4 := by
        rw [Complex.add_re, Complex.div_re]
        norm_num [Complex.normSq_apply, xiThermalNode]
        ring
      have hden : (1 + xiZeroCopyReciprocalSquare q / 4 : ℂ) ≠ 0 := by
        intro hbad
        have hre0 := congrArg Complex.re hbad
        rw [hre, Complex.zero_re] at hre0
        linarith
      rw [xiThermalEndpointResolventDefectTerm] at htermzero
      have hdenpos : 0 <
          4 * (1 + xiThermalNode q / 4) *
            Complex.normSq (1 + xiZeroCopyReciprocalSquare q / 4) :=
        mul_pos (mul_pos (by norm_num) hx) (Complex.normSq_pos.mpr hden)
      exact (div_eq_zero_iff.mp htermzero).resolve_right hdenpos.ne']
    exact tsum_zero

  · intro hRH
    rw [xiThermalEndpointResolventDefect]
    rw [show xiThermalEndpointResolventDefectTerm = 0 by
      funext q
      obtain ⟨x, _hx, hcoord⟩ :=
        xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
      rw [xiThermalEndpointResolventDefectTerm, xiZeroCopyReciprocalSquare_eq,
        hcoord]
      simp]
    exact tsum_zero

/-- RH is exact locking of every unitary quarter-resolvent scattering phase. -/
theorem forall_xiThermalEndpointScatteringPhase_eq_one_iff_rh :
    (∀ q : XiZeroCopy, xiThermalEndpointScatteringPhase q = 1) ↔
      RiemannHypothesis := by
  constructor
  · intro hphase
    apply xiThermalOrientationEnergy_eq_zero_iff_rh.mp
    rw [xiThermalOrientationEnergy]
    rw [show (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q).im ^ 2) = 0 by
      funext q
      rw [(xiThermalEndpointScatteringPhase_eq_one_iff_im_eq_zero q).mp
        (hphase q)]
      norm_num]
    exact tsum_zero
  · intro hRH q
    apply (xiThermalEndpointScatteringPhase_eq_one_iff_im_eq_zero q).mpr
    obtain ⟨x, _hx, hcoord⟩ :=
      xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
    rw [xiZeroCopyReciprocalSquare_eq, hcoord]
    simp

/-- Equality in the unconditional bounded-resolvent contraction is exactly RH. -/
theorem xiThermalEndpointResolventValue_eq_endpointCompletedCurvature_iff_rh :
    xiThermalEndpointResolventValue = xiEndpointCompletedCurvature ↔
      RiemannHypothesis := by
  rw [← xiThermalEndpointResolventDefect_eq_zero_iff_rh,
    ← xiEndpointCompletedCurvature_sub_thermalEndpointResolventValue_eq_defect]
  constructor <;> intro h <;> linarith

/-- Convergence of one bounded static-observable expectation to the completed source value is
already equivalent to RH; no all-moment thermodynamic limit is required. -/
theorem tendsto_xiThermalEndpointResolventTruncation_endpointCurvature_iff_rh :
    Tendsto xiThermalEndpointResolventTruncation atTop
      (nhds xiEndpointCompletedCurvature) ↔ RiemannHypothesis := by
  constructor
  · intro hsource
    have heq : xiThermalEndpointResolventValue = xiEndpointCompletedCurvature :=
      tendsto_nhds_unique tendsto_xiThermalEndpointResolventTruncation hsource
    exact xiThermalEndpointResolventValue_eq_endpointCompletedCurvature_iff_rh.mp heq
  · intro hRH
    have heq :=
      xiThermalEndpointResolventValue_eq_endpointCompletedCurvature_iff_rh.mpr hRH
    simpa only [heq] using tendsto_xiThermalEndpointResolventTruncation

/-- The normalized bounded thermal endpoint-resolvent scalar. -/
def xiThermalEndpointResolventContraction : ℝ :=
  xiThermalEndpointResolventValue / xiEndpointCompletedCurvature

theorem xiThermalEndpointResolventContraction_pos :
    0 < xiThermalEndpointResolventContraction :=
  div_pos xiThermalEndpointResolventValue_pos xiEndpointCompletedCurvature_pos

/-- The bounded thermal endpoint resolvent is an unconditional scalar contraction. -/
theorem xiThermalEndpointResolventContraction_le_one :
    xiThermalEndpointResolventContraction ≤ 1 := by
  rw [xiThermalEndpointResolventContraction,
    div_le_one xiEndpointCompletedCurvature_pos]
  exact xiThermalEndpointResolventValue_le_endpointCompletedCurvature

/-- Saturation of the scalar contraction is exactly RH. -/
theorem xiThermalEndpointResolventContraction_eq_one_iff_rh :
    xiThermalEndpointResolventContraction = 1 ↔ RiemannHypothesis := by
  rw [xiThermalEndpointResolventContraction,
    div_eq_one_iff_eq xiEndpointCompletedCurvature_pos.ne']
  exact xiThermalEndpointResolventValue_eq_endpointCompletedCurvature_iff_rh

/-- Saturation of the scalar contraction is equivalent to locking every unitary scattering
phase. -/
theorem xiThermalEndpointResolventContraction_eq_one_iff_phaseLocking :
    xiThermalEndpointResolventContraction = 1 ↔
      ∀ q : XiZeroCopy, xiThermalEndpointScatteringPhase q = 1 :=
  xiThermalEndpointResolventContraction_eq_one_iff_rh.trans
    forall_xiThermalEndpointScatteringPhase_eq_one_iff_rh.symm

/-- Failure of RH makes the bounded thermal resolvent a strict contraction of the endpoint
source value. -/
theorem xiThermalEndpointResolventValue_lt_endpointCompletedCurvature_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    xiThermalEndpointResolventValue < xiEndpointCompletedCurvature := by
  exact lt_of_le_of_ne xiThermalEndpointResolventValue_le_endpointCompletedCurvature
    (fun h => hRH
      (xiThermalEndpointResolventValue_eq_endpointCompletedCurvature_iff_rh.mp h))

/-- **Single bounded-value form of the prime--polar target.**  The remaining critical
absolute-abscissa inequality is equivalent to saturation of one explicit bounded thermal
resolvent value. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalEndpointResolvent_saturation
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal)) ↔
      xiThermalEndpointResolventValue = xiEndpointCompletedCurvature :=
  (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    hL hN).symm.trans
      xiThermalEndpointResolventValue_eq_endpointCompletedCurvature_iff_rh.symm

/-- The same prime--polar target as convergence of a single bounded static-observable value in
the canonical finite Xi thermal systems. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_tendsto_thermalEndpointResolvent
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal)) ↔
      Tendsto xiThermalEndpointResolventTruncation atTop
        (nhds xiEndpointCompletedCurvature) :=
  (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    hL hN).symm.trans
      tendsto_xiThermalEndpointResolventTruncation_endpointCurvature_iff_rh.symm

/-- The prime--polar target is equivalently exact locking of the complete unitary endpoint
scattering phase field. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointPhaseLocking
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal)) ↔
      ∀ q : XiZeroCopy, xiThermalEndpointScatteringPhase q = 1 :=
  (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    hL hN).symm.trans
      forall_xiThermalEndpointScatteringPhase_eq_one_iff_rh.symm

end

end RHTower
