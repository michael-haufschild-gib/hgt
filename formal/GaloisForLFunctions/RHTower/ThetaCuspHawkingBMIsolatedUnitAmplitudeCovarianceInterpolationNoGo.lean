import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVacuumDifferentiableNonlinearEvolutionNoGo

/-!
# Isolated unit-amplitude nonlinear covariance is not an HB producer

Full source-FE covariance of a vacuum-differentiable nonlinear evolution forces covariance of its
centered Birmingham--Mokhtari clock first variation, hence RH at nonzero time. The sole regular
escape left by that theorem was covariance asserted only at isolated finite source amplitudes.

This module kills that escape at its strongest source-universal form. For every centered BM clock,
it constructs one finite-support-preserving coordinatewise polynomial evolution

`E(x)_q = m_q x_q + x_q^2 (x_q - 1) K_q`

whose vacuum first variation is the original clock and which is source-FE covariant on the unit
basis packet of every Xi copy. The correction is mixed quadratic--cubic: it vanishes to second
order at vacuum and at unit input, but at the transported cocycle amplitude it interpolates the
entire off-wall clock defect. Thus even universal isolated unit-amplitude covariance holds
unconditionally and cannot select the critical line.

The boundary is exact. At any nonzero time, upgrading this same interpolant to full-packet
covariance is equivalent to RH. A surviving HB producer must therefore force covariance on an
amplitude family accumulating at vacuum/full packet space, change the vacuum clock or literal
source law, or be singular at vacuum.

`[HB ROUTE KILL] [FINITE-AMPLITUDE INTERPOLATION] [LEAN-PROVED]`
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Axiswise interpolation coefficient. -/
def hbXiPeierlsIsolatedUnitClockCorrectionCoefficient
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  let r := xiZeroCopyReflectEquiv q
  let c := hbXiPeierlsUnitSourceFECocycle r
  if c = 1 then 0 else
    ((starRingEnd ℂ) (hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t r) -
        hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q) /
      (c * (c - 1))

/-- Coordinatewise degree-three isolated-unit interpolant. -/
def hbXiPeierlsIsolatedUnitClockInterpolant
    (n : ℕ) (t : ℝ) (x : HBXiPeierlsPacket) : HBXiPeierlsPacket :=
  Finsupp.onFinset x.support
    (fun q =>
      hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q * x q +
        x q ^ 2 * (x q - 1) *
          hbXiPeierlsIsolatedUnitClockCorrectionCoefficient n t q)
    (by
      intro q hq
      rw [Finsupp.mem_support_iff]
      intro hx
      apply hq
      rw [hx]
      simp)

@[simp]
theorem hbXiPeierlsIsolatedUnitClockInterpolant_apply
    (n : ℕ) (t : ℝ) (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsIsolatedUnitClockInterpolant n t x q =
      hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q * x q +
        x q ^ 2 * (x q - 1) *
          hbXiPeierlsIsolatedUnitClockCorrectionCoefficient n t q := by
  rw [hbXiPeierlsIsolatedUnitClockInterpolant, Finsupp.onFinset_apply]

@[simp]
theorem hbXiPeierlsIsolatedUnitClockInterpolant_single_one
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    hbXiPeierlsIsolatedUnitClockInterpolant n t (Finsupp.single q 1) =
      Finsupp.single q (hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q) := by
  ext r
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

theorem hbXiPeierlsCenteredQNMPhysicalClockMultiplier_reflect_eq_conj_of_re_eq_half
    (n : ℕ) (t : ℝ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2) :
    hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t
        (xiZeroCopyReflectEquiv q) =
      (starRingEnd ℂ) (hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q) := by
  have him : (hbXiPeierlsCenteredQNMFrequency n q).im = 0 := by
    rw [hbXiPeierlsCenteredQNMFrequency_im_eq, hline]
    norm_num
  have hreal :
      (starRingEnd ℂ) (hbXiPeierlsCenteredQNMFrequency n q) =
        hbXiPeierlsCenteredQNMFrequency n q := by
    apply Complex.ext
    · simp
    · simp [him]
  unfold hbXiPeierlsCenteredQNMPhysicalClockMultiplier
  rw [hbXiPeierlsCenteredQNMFrequency_reflect, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg]
  rw [hreal]
  simp

theorem hbXiPeierlsIsolatedUnitClockCorrection_reflect_eval
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle q ^ 2 *
          (hbXiPeierlsUnitSourceFECocycle q - 1) *
          hbXiPeierlsIsolatedUnitClockCorrectionCoefficient n t
            (xiZeroCopyReflectEquiv q) =
      hbXiPeierlsUnitSourceFECocycle q *
        ((starRingEnd ℂ) (hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q) -
          hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t
            (xiZeroCopyReflectEquiv q)) := by
  by_cases hc : hbXiPeierlsUnitSourceFECocycle q = 1
  · have hline : (q.1 : ℂ).re = 1 / 2 := by
      apply (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mp
      rw [hc]
      norm_num
    rw [hc]
    simp [hbXiPeierlsCenteredQNMPhysicalClockMultiplier_reflect_eq_conj_of_re_eq_half
      n t q hline]
  · simp only [hbXiPeierlsIsolatedUnitClockCorrectionCoefficient,
      xiZeroCopyReflectEquiv_apply_apply]
    rw [if_neg hc]
    have hc0 : hbXiPeierlsUnitSourceFECocycle q ≠ 0 :=
      hbXiPeierlsUnitSourceFECocycle_ne_zero q
    field_simp [hc, hc0]

theorem hbXiPeierlsIsolatedUnitClockInterpolant_transport_single_one
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    hbXiPeierlsIsolatedUnitClockInterpolant n t
        (hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q 1)) =
      Finsupp.single (xiZeroCopyReflectEquiv q)
        (hbXiPeierlsUnitSourceFECocycle q *
          (starRingEnd ℂ) (hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q)) := by
  rw [hbXiPeierlsUnitSourceFEPacketTransport_single]
  simp only [map_one]
  ext r
  by_cases h : r = xiZeroCopyReflectEquiv q
  · subst r
    simp only [hbXiPeierlsIsolatedUnitClockInterpolant_apply,
      Finsupp.single_eq_same]
    simp only [mul_one]
    rw [hbXiPeierlsIsolatedUnitClockCorrection_reflect_eval]
    ring
  · simp [hbXiPeierlsIsolatedUnitClockInterpolant_apply, h]

/-- Covariance imposed only on the isolated unit packet of every Xi coordinate. -/
def HBXiPeierlsNonlinearEvolutionUnitBasisSourceFECovariant
    (evolution : HBXiPeierlsPacket → HBXiPeierlsPacket) : Prop :=
  ∀ q : XiZeroCopy,
    hbXiPeierlsUnitSourceFEPacketTransport
        (evolution (Finsupp.single q 1)) =
      evolution
        (hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q 1))

theorem hbXiPeierlsIsolatedUnitClockInterpolant_unitBasisSourceFECovariant
    (n : ℕ) (t : ℝ) :
    HBXiPeierlsNonlinearEvolutionUnitBasisSourceFECovariant
      (hbXiPeierlsIsolatedUnitClockInterpolant n t) := by
  intro q
  calc
    hbXiPeierlsUnitSourceFEPacketTransport
          (hbXiPeierlsIsolatedUnitClockInterpolant n t (Finsupp.single q 1)) =
        Finsupp.single (xiZeroCopyReflectEquiv q)
          (hbXiPeierlsUnitSourceFECocycle q *
            (starRingEnd ℂ)
              (hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q)) := by
      rw [hbXiPeierlsIsolatedUnitClockInterpolant_single_one,
        hbXiPeierlsUnitSourceFEPacketTransport_single]
    _ = hbXiPeierlsIsolatedUnitClockInterpolant n t
          (hbXiPeierlsUnitSourceFEPacketTransport (Finsupp.single q 1)) :=
      (hbXiPeierlsIsolatedUnitClockInterpolant_transport_single_one n t q).symm

theorem hbXiPeierlsIsolatedUnitClockInterpolant_vacuumFirstVariation
    (n : ℕ) (t : ℝ) :
    HBXiPeierlsVacuumFirstVariation
      (hbXiPeierlsIsolatedUnitClockInterpolant n t)
      (hbXiPeierlsCenteredQNMPhysicalClockStep n t) := by
  intro x r
  simp only [hbXiPeierlsIsolatedUnitClockInterpolant_apply,
    hbXiPeierlsCenteredQNMPhysicalClockStep_apply,
    hbXiPeierlsCenteredQNMPhysicalClockMultiplier,
    Finsupp.smul_apply, smul_eq_mul]
  have ha : Tendsto (fun amplitude : ℝ => (amplitude : ℂ))
      (𝓝[≠] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left inf_le_left
  have hax2 : Tendsto
      (fun amplitude : ℝ => (amplitude : ℂ) * x r ^ 2)
      (𝓝[≠] 0) (𝓝 (0 * x r ^ 2)) :=
    ha.mul tendsto_const_nhds
  have haxsub : Tendsto
      (fun amplitude : ℝ => (amplitude : ℂ) * x r - 1)
      (𝓝[≠] 0) (𝓝 (0 * x r - 1)) :=
    (ha.mul tendsto_const_nhds).sub tendsto_const_nhds
  have hcorr : Tendsto
      (fun amplitude : ℝ =>
        (amplitude : ℂ) * x r ^ 2 * ((amplitude : ℂ) * x r - 1) *
          hbXiPeierlsIsolatedUnitClockCorrectionCoefficient n t r)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hax2.mul haxsub).mul tendsto_const_nhds
  have hsum : Tendsto
      (fun amplitude : ℝ =>
        Complex.exp (-I * (t : ℂ) * hbXiPeierlsCenteredQNMFrequency n r) * x r +
          (amplitude : ℂ) * x r ^ 2 * ((amplitude : ℂ) * x r - 1) *
            hbXiPeierlsIsolatedUnitClockCorrectionCoefficient n t r)
      (𝓝[≠] 0)
      (𝓝 (Complex.exp (-I * (t : ℂ) * hbXiPeierlsCenteredQNMFrequency n r) * x r)) := by
    simpa using (tendsto_const_nhds.add hcorr)
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with amplitude hamplitude
  have ha0 : amplitude ≠ 0 := by simpa using hamplitude
  have haC : (amplitude : ℂ) ≠ 0 := by exact_mod_cast ha0
  field_simp [haC]

theorem hbXiPeierlsIsolatedUnitClockCorrectionCoefficient_eq_zero_of_re_eq_half
    (n : ℕ) (t : ℝ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2) :
    hbXiPeierlsIsolatedUnitClockCorrectionCoefficient n t q = 0 := by
  have hrefline : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 := by
    rw [xiZeroCopyReflect_re_eq_one_sub]
    linarith
  have hclock :=
    hbXiPeierlsCenteredQNMPhysicalClockMultiplier_reflect_eq_conj_of_re_eq_half
      n t (xiZeroCopyReflectEquiv q) hrefline
  rw [xiZeroCopyReflectEquiv_apply_apply] at hclock
  have hnum :
      (starRingEnd ℂ)
          (hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t
            (xiZeroCopyReflectEquiv q)) -
        hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q = 0 := by
    rw [← hclock]
    simp
  simp [hbXiPeierlsIsolatedUnitClockCorrectionCoefficient, hnum]

theorem hbXiPeierlsIsolatedUnitClockInterpolant_eq_clock_of_rh
    (hRH : RiemannHypothesis) (n : ℕ) (t : ℝ) (x : HBXiPeierlsPacket) :
    hbXiPeierlsIsolatedUnitClockInterpolant n t x =
      hbXiPeierlsCenteredQNMPhysicalClockStep n t x := by
  ext q
  rw [hbXiPeierlsIsolatedUnitClockInterpolant_apply,
    hbXiPeierlsCenteredQNMPhysicalClockStep_apply]
  have hline : (q.1 : ℂ).re = 1 / 2 :=
    xi_divisor_support_re_eq_half_of_rh hRH q.1
  rw [hbXiPeierlsIsolatedUnitClockCorrectionCoefficient_eq_zero_of_re_eq_half
    n t q hline]
  simp [hbXiPeierlsCenteredQNMPhysicalClockMultiplier]

theorem hbXiPeierlsIsolatedUnitClockInterpolant_fullCovariant_iff_rh
    (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HBXiPeierlsNonlinearEvolutionSourceFECovariant
        (hbXiPeierlsIsolatedUnitClockInterpolant n t) ↔
      RiemannHypothesis := by
  constructor
  · intro hcovariant
    apply (hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff_rh n ht).mp
    exact hbXiPeierlsVacuumDifferentiableNonlinearEvolution_forces_linearClockCovariance
      n t
      (hbXiPeierlsIsolatedUnitClockInterpolant_vacuumFirstVariation n t)
      hcovariant
  · intro hRH x
    rw [hbXiPeierlsIsolatedUnitClockInterpolant_eq_clock_of_rh hRH,
      hbXiPeierlsIsolatedUnitClockInterpolant_eq_clock_of_rh hRH]
    exact (hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff_rh n ht).mpr hRH x

/-- Existence of a vacuum-differentiable evolution satisfying only universal isolated unit-basis
source-FE covariance. -/
def HBXiPeierlsExistsVacuumDifferentiableIsolatedUnitEvolution
    (n : ℕ) (t : ℝ) : Prop :=
  ∃ evolution : HBXiPeierlsPacket → HBXiPeierlsPacket,
    HBXiPeierlsVacuumFirstVariation evolution
      (hbXiPeierlsCenteredQNMPhysicalClockStep n t) ∧
    HBXiPeierlsNonlinearEvolutionUnitBasisSourceFECovariant evolution

theorem hbXiPeierlsExistsVacuumDifferentiableIsolatedUnitEvolution_holds
    (n : ℕ) (t : ℝ) :
    HBXiPeierlsExistsVacuumDifferentiableIsolatedUnitEvolution n t := by
  exact ⟨hbXiPeierlsIsolatedUnitClockInterpolant n t,
    hbXiPeierlsIsolatedUnitClockInterpolant_vacuumFirstVariation n t,
    hbXiPeierlsIsolatedUnitClockInterpolant_unitBasisSourceFECovariant n t⟩

/-- Closed no-go package: isolated unit-amplitude covariance is unconditionally interpolable
without changing the centered BM vacuum clock, so it cannot be the missing HB producer. -/
def D4HBIsolatedUnitAmplitudeNonlinearEvolutionRouteKilled : Prop :=
  ∀ (n : ℕ) (t : ℝ),
    HBXiPeierlsExistsVacuumDifferentiableIsolatedUnitEvolution n t

theorem d4HBIsolatedUnitAmplitudeNonlinearEvolutionRouteKilled :
    D4HBIsolatedUnitAmplitudeNonlinearEvolutionRouteKilled := by
  intro n t
  exact hbXiPeierlsExistsVacuumDifferentiableIsolatedUnitEvolution_holds n t

end
end RHTower
