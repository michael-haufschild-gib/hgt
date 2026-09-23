import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveShearAdjacentDefect

/-!
# Outgoing-ray integral law for adaptive shifted-Xi shear

The source-first differential law becomes an actual improper-integral identity once the adaptive
shear is nonnegative on an outgoing mass ray.  This module supplies every analytic step:

* each shifted reciprocal atom and every shifted moment vanish at `+∞`;
* every finite polynomial moment functional and moment pairing vanishes at `+∞`;
* outgoing nonnegative adaptive shear is integrable;
* the odd crossing current is exactly twice its outgoing adaptive-shear integral.

Consequently a negative odd current forces a strictly negative adaptive-shear event later on the
same mass ray.  Applying the statement to the canonical null amplitude shows that every genuine
Hankel crossing produces such a future source defect.  Thus the remaining arithmetic theorem is
precisely exclusion of this negative source event, not another local orientation map.
-/

open Complex Matrix MeasureTheory Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every individual shifted reciprocal Xi atom vanishes along the outgoing mass ray. -/
theorem tendsto_xiShiftedReciprocalSquare_atTop_zero (q : XiZeroCopy) :
    Tendsto (fun y : ℝ => xiShiftedReciprocalSquare y q) atTop (nhds 0) := by
  let z : ℂ := xiZeroCopyReciprocalSquare q
  have hz : z ≠ 0 := by
    intro hz0
    have hre := congrArg Complex.re hz0
    change (xiZeroCopyReciprocalSquare q).re = 0 at hre
    exact (ne_of_gt (xiZeroCopyReciprocalSquare_re_pos q)) hre
  have hinv : Tendsto (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.ofReal
  have hden : Tendsto (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ) + z) atTop (nhds z) := by
    simpa using hinv.add_const z
  have hfrac : Tendsto (fun y : ℝ => z / (((y⁻¹ : ℝ) : ℂ) + z))
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := z)).div hden hz
    convert h using 1
    · funext y
      simp only [Pi.div_apply]
    · simp [div_self hz]
  have hprod := hinv.mul hfrac
  have hprod0 : Tendsto
      (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ) *
        (z / (((y⁻¹ : ℝ) : ℂ) + z))) atTop (nhds 0) := by
    simpa using hprod
  apply hprod0.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  dsimp only [xiShiftedReciprocalSquare, z]
  rw [inv_eq_one_div]
  push_cast
  field_simp [hy.ne']

/-- Dominated convergence upgrades atomwise extinction to extinction of every shifted reciprocal
moment, without any RH assumption. -/
theorem tendsto_xiShiftedReciprocalMoment_atTop_zero (n : ℕ) :
    Tendsto (fun y : ℝ => xiShiftedReciprocalMoment y n) atTop (nhds 0) := by
  rw [show (0 : ℂ) = ∑' _q : XiZeroCopy, (0 : ℂ) by simp]
  apply tendsto_tsum_of_dominated_convergence
      (summable_xiZeroCopyReciprocalSquare_pow n).norm
  · intro q
    simpa using (tendsto_xiShiftedReciprocalSquare_atTop_zero q).pow (n + 1)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy q
    simp only [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_xiShiftedReciprocalSquare_le hy q) (n + 1)

/-- Real shifted moments vanish on the outgoing ray. -/
theorem tendsto_re_xiShiftedReciprocalMoment_atTop_zero (n : ℕ) :
    Tendsto (fun y : ℝ => (xiShiftedReciprocalMoment y n).re) atTop (nhds 0) := by
  change Tendsto (Complex.re ∘ fun y : ℝ => xiShiftedReciprocalMoment y n)
    atTop (nhds 0)
  simpa only [Complex.zero_re] using
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_xiShiftedReciprocalMoment_atTop_zero n)

/-- Every finite polynomial observation of the shifted moment tower vanishes at `+∞`. -/
theorem tendsto_xiShiftedMomentFunctional_atTop_zero (p : Polynomial ℝ) :
    Tendsto
      (fun y : ℝ => HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) p)
      atTop (nhds 0) := by
  rw [show (0 : ℝ) = ∑ k ∈ p.support, (0 : ℝ) by simp]
  simpa [HTGeometry.momentFunctional_eq_support_sum] using
    tendsto_finsetSum p.support (fun k _ =>
      (tendsto_re_xiShiftedReciprocalMoment_atTop_zero k).const_mul (p.coeff k))

/-- Every fixed polynomial pairing vanishes at the far end of the mass ray. -/
theorem tendsto_xiShiftedMomentInner_atTop_zero (p q : Polynomial ℝ) :
    Tendsto
      (fun y : ℝ => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) p q)
      atTop (nhds 0) := by
  simpa only [HTGeometry.momentInner_def] using
    tendsto_xiShiftedMomentFunctional_atTop_zero (p * q)

/-- If source-selected adaptive shear is nonnegative on an outgoing ray, it is genuinely
integrable there.  This rules out the convention that a nonintegrable Bochner integral is merely
reported as zero. -/
theorem integrableOn_xiShiftedAdaptiveShear_of_nonneg
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ)
    (hnonneg : ∀ v ∈ Ioi y,
      0 ≤ HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)) :
    IntegrableOn
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A))
      (Ioi y) := by
  let B : ℝ → ℝ := fun v => HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment v k).re) A (X * A)
  let S : ℝ → ℝ := fun v => HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment v k).re)
    (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)
  have hbase := hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear hy A
  have hcont : ContinuousWithinAt B (Ici y) y :=
    hbase.continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ Ioi y, HasDerivAt B (-2 * S v) v := by
    intro v hv
    exact hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear
      (hy.trans hv) A
  have hnonpos : ∀ v ∈ Ioi y, -2 * S v ≤ 0 := by
    intro v hv
    dsimp only [S]
    nlinarith [hnonneg v hv]
  have hlim : Tendsto B atTop (nhds 0) :=
    tendsto_xiShiftedMomentInner_atTop_zero A (X * A)
  have hderivInt : IntegrableOn (fun v => -2 * S v) (Ioi y) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos hcont hderiv hnonpos hlim
  have hscaled := hderivInt.const_mul (-1 / 2)
  change Integrable S (volume.restrict (Ioi y))
  convert hscaled using 1
  · funext v
    ring

/-- **Actual outgoing-ray integral source law.** Under nonnegative adaptive shear, the negative
source derivative integrates exactly from the contact mass to infinity. -/
theorem xiShiftedMomentInner_oddCrossing_eq_two_integral_adaptiveShear
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ)
    (hnonneg : ∀ v ∈ Ioi y,
      0 ≤ HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) A (X * A) =
      2 * ∫ v in Ioi y, HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) := by
  let B : ℝ → ℝ := fun v => HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment v k).re) A (X * A)
  let S : ℝ → ℝ := fun v => HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment v k).re)
    (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)
  have hbase := hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear hy A
  have hcont : ContinuousWithinAt B (Ici y) y := by
    exact hbase.continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ Ioi y, HasDerivAt B (-2 * S v) v := by
    intro v hv
    exact hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear
      (hy.trans hv) A
  have hnonpos : ∀ v ∈ Ioi y, -2 * S v ≤ 0 := by
    intro v hv
    dsimp only [S]
    nlinarith [hnonneg v hv]
  have hlim : Tendsto B atTop (nhds 0) := by
    exact tendsto_xiShiftedMomentInner_atTop_zero A (X * A)
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos
    hcont hderiv hnonpos hlim
  change HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) A (X * A) = _
  change (∫ v in Ioi y, -2 * S v) = 0 - B y at hFTC
  rw [MeasureTheory.integral_const_mul] at hFTC
  dsimp only [B, S] at hFTC ⊢
  linarith

/-- Outgoing nonnegative adaptive shear makes the odd crossing current nonnegative. -/
theorem xiShiftedMomentInner_oddCrossing_nonneg_of_outgoing_adaptiveShear_nonneg
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ)
    (hnonneg : ∀ v ∈ Ioi y,
      0 ≤ HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)) :
    0 ≤ HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) A (X * A) := by
  rw [xiShiftedMomentInner_oddCrossing_eq_two_integral_adaptiveShear hy A hnonneg]
  exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi hnonneg)

/-- **Negative-source propagation.** A negative odd current cannot decay to zero without a later
strictly negative adaptive shear. -/
theorem exists_xiShifted_adaptiveShear_neg_on_outgoingRay_of_oddCrossing_neg
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ)
    (hneg : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) A (X * A) < 0) :
    ∃ v ∈ Ioi y, HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment v k).re)
      (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) < 0 := by
  by_contra hnone
  push Not at hnone
  have hnonneg : ∀ v ∈ Ioi y,
      0 ≤ HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) := by
    intro v hv
    exact hnone v hv
  exact (not_lt_of_ge
    (xiShiftedMomentInner_oddCrossing_nonneg_of_outgoing_adaptiveShear_nonneg
      hy A hnonneg)) hneg

/-- **Genuine-crossing source consequence.** Every genuine shifted-Hankel crossing in the
prime--Gamma window selects an admitted null amplitude whose adaptive mixed shear becomes strictly
negative at a later mass. -/
theorem exists_xiShifted_adaptiveShear_neg_on_outgoingRay_of_genuine_crossing
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ, ∃ v ∈ Ioi y,
      let A := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
      HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) < 0 := by
  obtain ⟨m, _hzero, hnegPA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  let A := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hseq : (fun k => (primeArchShiftedReciprocalMoment y k).re) =
      (fun k => (xiShiftedReciprocalMoment y k).re) := by
    funext k
    simpa using congrArg Complex.re
      (xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
        hy.le hymax k).symm
  have hnegXi : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) A (X * A) < 0 := by
    rw [HTGeometry.momentInner_def, ← hseq]
    change HTGeometry.momentFunctional
      (fun k => (primeArchShiftedReciprocalMoment y k).re)
      (X * A ^ (2 : ℕ)) < 0 at hnegPA
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnegPA
  obtain ⟨v, hv, hshear⟩ :=
    exists_xiShifted_adaptiveShear_neg_on_outgoingRay_of_oddCrossing_neg
      hy A hnegXi
  exact ⟨m, v, hv, hshear⟩

/-- A negative odd current forces the actual completed adaptive `P^sharp` successor packet to be
strictly negative at some later mass. -/
theorem exists_xiShiftedCompletedAdaptiveOddPacket_neg_on_outgoingRay_of_oddCrossing_neg
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ)
    (hneg : HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) A (X * A) < 0) :
    ∃ v ∈ Ioi y,
      xiShiftedCompletedMomentAggregate v 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket A)) < 0 := by
  obtain ⟨v, hv, hshear⟩ :=
    exists_xiShifted_adaptiveShear_neg_on_outgoingRay_of_oddCrossing_neg hy A hneg
  refine ⟨v, hv, ?_⟩
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear
    (hy.trans hv) A]
  linarith

/-- **Pre-aggregation arithmetic obstruction.** Every genuine crossing above the quarter-mass
threshold forces the completed archimedean-plus-Chebyshev-discrepancy adaptive packet to become
strictly negative at a later Euler aperture.  Proving this packet nonnegative on admitted
outgoing rays is therefore the exact arithmetic source theorem which excludes crossings. -/
theorem exists_xiShiftedCompletedAdaptiveSource_neg_on_outgoingRay_of_genuine_crossing
    {y : ℝ} (hyquarter : 1 / 4 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ, ∃ w : ℝ,
      1 / 2 < w ∧ y < w ^ (2 : ℕ) ∧
      let A := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
      xiShiftedBoundaryArchimedeanAggregate w 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket A)) +
        xiShiftedHankelBoundaryRadialDiscrepancy w 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket A)) < 0 := by
  have hy : 0 < y := by linarith
  obtain ⟨m, v, hv, hshear⟩ :=
    exists_xiShifted_adaptiveShear_neg_on_outgoingRay_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  change y < v at hv
  let A := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  let w := Real.sqrt v
  have hvpos : 0 < v := hy.trans hv
  have hw : 1 / 2 < w := by
    dsimp only [w]
    apply (Real.lt_sqrt (by norm_num)).2
    nlinarith [hyquarter, hv]
  have hwsq : w ^ (2 : ℕ) = v := Real.sq_sqrt hvpos.le
  have hsource := xiShiftedCompletedAdaptiveOddPacketSource_eq_two_sourceShear hw A
  have hpair :=
    xiShiftedAperturePairGap_eq_archimedeanSourcePair_add_discrepancySourcePair
      hw (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)
  rw [xiShiftedAperturePairGap_eq_momentInner
    (sq_pos_of_pos (by linarith : 0 < w)), hwsq] at hpair
  refine ⟨m, w, hw, ?_, ?_⟩
  · rw [hwsq]
    exact hv
  · dsimp only
    rw [hsource, ← hpair]
    dsimp only at hshear
    exact mul_neg_of_pos_of_neg (by norm_num) hshear

end

end RHTower
