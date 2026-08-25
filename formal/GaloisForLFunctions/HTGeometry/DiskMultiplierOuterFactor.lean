import GaloisForLFunctions.HTGeometry.BoundaryLogFatou
import GaloisForLFunctions.HTGeometry.CircleIntegrabilityReverse
import GaloisForLFunctions.HTGeometry.SzegoOuterAnalytic
import GaloisForLFunctions.HTGeometry.SzegoHInfty

/-!
# Canonical outer factor of a bounded analytic multiplier

This file constructs the exact positive periodic boundary weight used by the Szegő outer
factor of an arbitrary nonzero bounded analytic multiplier.  Exceptional boundary points are
patched pointwise; the patch is almost everywhere invisible and keeps positivity and the sharp
analytic bound available without introducing a lower-modulus assumption.
-/

open Complex MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Standard angular parametrization of the unit circle, expressed through the additive circle. -/
def angularCircle (theta : ℝ) : Circle :=
  AddCircle.toCircle (↑(theta / (2 * Real.pi)) : AddCircle (1 : ℝ))

theorem coe_angularCircle (theta : ℝ) :
    (angularCircle theta : ℂ) = circleMap 0 1 theta := by
  rw [angularCircle, AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
  simp only [zero_add]
  push_cast
  field_simp [Real.pi_ne_zero]

theorem angularCircle_periodic : Function.Periodic angularCircle (2 * Real.pi) := by
  intro theta
  apply Subtype.ext
  rw [coe_angularCircle, coe_angularCircle]
  simp only [circleMap, zero_add, one_mul]
  have hexp : ((theta + 2 * Real.pi : ℝ) : ℂ) * I =
      (theta : ℂ) * I + 2 * (Real.pi : ℂ) * I := by
    push_cast
    ring
  rw [hexp, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Pointwise-safe boundary representative: nonzero and bounded everywhere, and equal almost
everywhere to the actual multiplier boundary. -/
def diskMultiplierBoundarySafe (phi : DiskMultiplier) (z : Circle) : ℂ :=
  let v := diskMultiplierBoundaryMeasurableRep phi z
  if v ≠ 0 ∧ ‖v‖ ≤ max 1 phi.bd then v else 1

theorem measurable_diskMultiplierBoundarySafe (phi : DiskMultiplier) :
    Measurable (diskMultiplierBoundarySafe phi) := by
  let v : Circle → ℂ := diskMultiplierBoundaryMeasurableRep phi
  have hv : Measurable v := measurable_diskMultiplierBoundaryMeasurableRep phi
  have hs : MeasurableSet {z | v z ≠ 0 ∧ ‖v z‖ ≤ max 1 phi.bd} :=
    ((hv (measurableSet_singleton 0)).compl).inter (hv.norm measurableSet_Iic)
  exact Measurable.ite hs hv measurable_const

theorem diskMultiplierBoundarySafe_ne_zero (phi : DiskMultiplier) (z : Circle) :
    diskMultiplierBoundarySafe phi z ≠ 0 := by
  rw [diskMultiplierBoundarySafe]
  split_ifs with hz
  · exact hz.1
  · exact one_ne_zero

theorem norm_diskMultiplierBoundarySafe_le (phi : DiskMultiplier) (z : Circle) :
    ‖diskMultiplierBoundarySafe phi z‖ ≤ max 1 phi.bd := by
  rw [diskMultiplierBoundarySafe]
  split_ifs with hz
  · exact hz.2
  · simpa using le_max_left (1 : ℝ) phi.bd

theorem diskMultiplierBoundarySafe_ae
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    diskMultiplierBoundarySafe phi =ᵐ[circleLebesgue]
      diskMultiplierBoundaryFun phi := by
  filter_upwards [diskMultiplierBoundaryMeasurableRep_ae phi,
    diskMultiplierBoundary_ne_zero_ae phi hphi,
    ae_norm_diskMultiplierBoundaryFun_le phi] with z hrep hne hbd
  rw [diskMultiplierBoundarySafe, hrep]
  simp [hne, hbd.trans (le_max_right (1 : ℝ) phi.bd)]

theorem integrable_log_norm_diskMultiplierBoundarySafe
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Integrable (fun z => Real.log ‖diskMultiplierBoundarySafe phi z‖)
      circleLebesgue :=
  (integrable_log_norm_diskMultiplierBoundaryFun phi hphi).congr
    ((diskMultiplierBoundarySafe_ae phi hphi).mono fun z hz =>
      (congrArg (fun w : ℂ => Real.log ‖w‖) hz).symm)

/-- Positive periodic squared boundary modulus defining the canonical Szegő outer factor. -/
def diskMultiplierOuterWeight (phi : DiskMultiplier) (theta : ℝ) : ℝ :=
  ‖diskMultiplierBoundarySafe phi (angularCircle theta)‖ ^ 2

theorem diskMultiplierOuterWeight_pos (phi : DiskMultiplier) (theta : ℝ) :
    0 < diskMultiplierOuterWeight phi theta := by
  rw [diskMultiplierOuterWeight]
  exact sq_pos_of_pos (norm_pos_iff.mpr (diskMultiplierBoundarySafe_ne_zero phi _))

theorem diskMultiplierOuterWeight_le (phi : DiskMultiplier) (theta : ℝ) :
    diskMultiplierOuterWeight phi theta ≤ (max 1 phi.bd) ^ 2 := by
  rw [diskMultiplierOuterWeight]
  nlinarith [norm_nonneg (diskMultiplierBoundarySafe phi (angularCircle theta)),
    norm_diskMultiplierBoundarySafe_le phi (angularCircle theta)]

theorem diskMultiplierOuterWeight_periodic (phi : DiskMultiplier) :
    Function.Periodic (diskMultiplierOuterWeight phi) (2 * Real.pi) := by
  intro theta
  rw [diskMultiplierOuterWeight, diskMultiplierOuterWeight,
    angularCircle_periodic theta]

theorem log_diskMultiplierOuterWeight (phi : DiskMultiplier) (theta : ℝ) :
    Real.log (diskMultiplierOuterWeight phi theta) =
      2 * Real.log ‖diskMultiplierBoundarySafe phi (angularCircle theta)‖ := by
  rw [diskMultiplierOuterWeight, Real.log_pow]
  norm_num

theorem intervalIntegrable_log_diskMultiplierOuterWeight
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    IntervalIntegrable (fun theta => Real.log (diskMultiplierOuterWeight phi theta))
      volume 0 (2 * Real.pi) := by
  have hangular := intervalIntegrable_angularCircle_of_integrable_circleLebesgue
    (fun z => Real.log ‖diskMultiplierBoundarySafe phi z‖)
    (Real.measurable_log.comp (measurable_diskMultiplierBoundarySafe phi).norm)
    (integrable_log_norm_diskMultiplierBoundarySafe phi hphi)
  have htwo := hangular.const_mul 2
  simpa only [angularCircle, two_mul, mul_comm, mul_left_comm, mul_assoc,
    log_diskMultiplierOuterWeight] using htwo

theorem periodic_log_diskMultiplierOuterWeight (phi : DiskMultiplier) :
    Function.Periodic (fun theta => Real.log (diskMultiplierOuterWeight phi theta))
      (2 * Real.pi) := by
  intro theta
  change Real.log (diskMultiplierOuterWeight phi (theta + 2 * Real.pi)) =
    Real.log (diskMultiplierOuterWeight phi theta)
  rw [diskMultiplierOuterWeight_periodic phi theta]

theorem locallyIntegrable_log_diskMultiplierOuterWeight
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    LocallyIntegrable (fun theta => Real.log (diskMultiplierOuterWeight phi theta))
      volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  rcases k.eq_empty_or_nonempty with rfl | hkne
  · simp
  obtain ⟨R, hkR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hk.isBounded
  obtain ⟨x, hx⟩ := hkne
  have hxR : |x| ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hkR hx
  have hR : 0 ≤ R := le_trans (abs_nonneg x) hxR
  have hper := periodic_log_diskMultiplierOuterWeight phi
  have hperiod : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hbase : IntervalIntegrable
      (fun theta => Real.log (diskMultiplierOuterWeight phi theta)) volume
      0 (0 + 2 * Real.pi) := by
    simpa using intervalIntegrable_log_diskMultiplierOuterWeight phi hphi
  have hI := hper.intervalIntegrable hperiod hbase (-R) R
  have hIcc : IntegrableOn
      (fun theta => Real.log (diskMultiplierOuterWeight phi theta))
      (Set.Icc (-R) R) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp hI
  exact hIcc.mono_set fun y hy => by
    have hyR : |y| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hkR hy
    exact (abs_le.mp hyR)

theorem intervalIntegrable_log_diskMultiplierOuterWeight_shift
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (a b : ℝ) :
    IntervalIntegrable (fun theta => Real.log (diskMultiplierOuterWeight phi theta))
      volume a b := by
  have hbase : IntervalIntegrable
      (fun theta => Real.log (diskMultiplierOuterWeight phi theta)) volume
      0 (0 + 2 * Real.pi) := by
    simpa using intervalIntegrable_log_diskMultiplierOuterWeight phi hphi
  exact (periodic_log_diskMultiplierOuterWeight phi).intervalIntegrable
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) hbase a b

theorem integral_poissonKer_sub_zero_two_pi
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    (∫ theta in (0 : ℝ)..(2 * Real.pi), poissonKer r (theta - varphi)) =
      2 * Real.pi := by
  have hcomp := intervalIntegral.integral_comp_add_left
    (poissonKer r) (-varphi) (a := (0 : ℝ)) (b := 2 * Real.pi)
  have hshift := (poissonKer_periodic r).intervalIntegral_add_eq (-varphi) 0
  calc
    (∫ theta in (0 : ℝ)..(2 * Real.pi), poissonKer r (theta - varphi)) =
        ∫ theta in (-varphi + 0)..(-varphi + 2 * Real.pi), poissonKer r theta := by
          simpa only [sub_eq_add_neg, add_comm] using hcomp
    _ = ∫ theta in (0 : ℝ)..(0 + 2 * Real.pi), poissonKer r theta := by
      simpa only [add_zero] using hshift
    _ = 2 * Real.pi := by simpa using poissonKer_integral hr0 hr1

theorem poissonMean_zero_two_pi_le {g : ℝ → ℝ} {M : ℝ}
    (hgI : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hgM : ∀ theta, g theta ≤ M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    (2 * Real.pi)⁻¹ *
        ∫ theta in (0 : ℝ)..(2 * Real.pi),
          poissonKer r (theta - varphi) * g theta ≤ M := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (fun theta => poissonKer r (theta - varphi)) :=
    (poissonKer_continuous habs).comp (continuous_id.sub continuous_const)
  have hnn : ∀ theta, 0 ≤ poissonKer r (theta - varphi) :=
    fun theta => poissonKer_nonneg hr0 hr1 (theta - varphi)
  have hmono :
      (∫ theta in (0 : ℝ)..(2 * Real.pi),
          poissonKer r (theta - varphi) * g theta) ≤
        ∫ theta in (0 : ℝ)..(2 * Real.pi),
          poissonKer r (theta - varphi) * M := by
    apply intervalIntegral.integral_mono_on (by positivity)
      (hgI.continuousOn_mul hcont.continuousOn)
      ((hcont.mul continuous_const).intervalIntegrable _ _)
    intro theta _
    exact mul_le_mul_of_nonneg_left (hgM theta) (hnn theta)
  rw [intervalIntegral.integral_mul_const,
    integral_poissonKer_sub_zero_two_pi hr0 hr1 varphi] at hmono
  have htwo : 0 < (2 * Real.pi : ℝ) := by positivity
  rw [inv_mul_eq_div, div_le_iff₀ htwo]
  linarith

theorem poissonMean_zero_two_pi_ge {g : ℝ → ℝ} {L : ℝ}
    (hgI : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hgL : ∀ theta, L ≤ g theta)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    L ≤ (2 * Real.pi)⁻¹ *
        ∫ theta in (0 : ℝ)..(2 * Real.pi),
          poissonKer r (theta - varphi) * g theta := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (fun theta => poissonKer r (theta - varphi)) :=
    (poissonKer_continuous habs).comp (continuous_id.sub continuous_const)
  have hnn : ∀ theta, 0 ≤ poissonKer r (theta - varphi) :=
    fun theta => poissonKer_nonneg hr0 hr1 (theta - varphi)
  have hmono :
      (∫ theta in (0 : ℝ)..(2 * Real.pi),
          poissonKer r (theta - varphi) * L) ≤
        ∫ theta in (0 : ℝ)..(2 * Real.pi),
          poissonKer r (theta - varphi) * g theta := by
    apply intervalIntegral.integral_mono_on (by positivity)
      ((hcont.mul continuous_const).intervalIntegrable _ _)
      (hgI.continuousOn_mul hcont.continuousOn)
    intro theta _
    exact mul_le_mul_of_nonneg_left (hgL theta) (hnn theta)
  rw [intervalIntegral.integral_mul_const,
    integral_poissonKer_sub_zero_two_pi hr0 hr1 varphi] at hmono
  have htwo : 0 < (2 * Real.pi : ℝ) := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ htwo]
  linarith

theorem normSq_szegoOuter_le_from_weight_bound {w : ℝ → ℝ} {C : ℝ}
    (hC : 0 < C)
    (hlog : IntervalIntegrable (fun theta => Real.log (w theta)) volume
      0 (2 * Real.pi))
    (hwpos : ∀ theta, 0 < w theta)
    (hwC : ∀ theta, w theta ≤ C)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    ‖szegoOuter w (circleMap 0 r varphi)‖ ^ 2 ≤ C := by
  rw [normSq_szegoOuter_circleMap hlog hr0 hr1 varphi,
    show C = Real.exp (Real.log C) from (Real.exp_log hC).symm]
  apply Real.exp_le_exp.mpr
  simpa only [one_div] using poissonMean_zero_two_pi_le hlog
    (fun theta => Real.log_le_log (hwpos theta) (hwC theta)) hr0 hr1 varphi

theorem weight_lower_le_normSq_szegoOuter {w : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hlog : IntervalIntegrable (fun theta => Real.log (w theta)) volume
      0 (2 * Real.pi))
    (hwc : ∀ theta, c ≤ w theta)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    c ≤ ‖szegoOuter w (circleMap 0 r varphi)‖ ^ 2 := by
  rw [normSq_szegoOuter_circleMap hlog hr0 hr1 varphi,
    show c = Real.exp (Real.log c) from (Real.exp_log hc).symm]
  apply Real.exp_le_exp.mpr
  simpa only [one_div] using poissonMean_zero_two_pi_ge hlog
    (fun theta => Real.log_le_log hc (hwc theta)) hr0 hr1 varphi

theorem normSq_inv_szegoOuter_le_from_weight_lower {w : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hlog : IntervalIntegrable (fun theta => Real.log (w theta)) volume
      0 (2 * Real.pi))
    (hwc : ∀ theta, c ≤ w theta)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    ‖(szegoOuter w (circleMap 0 r varphi))⁻¹‖ ^ 2 ≤ c⁻¹ := by
  have hlower := weight_lower_le_normSq_szegoOuter hc hlog hwc hr0 hr1 varphi
  rw [norm_inv, inv_pow]
  exact (inv_le_inv₀ (sq_pos_of_pos (norm_pos_iff.mpr
    (szegoOuter_ne_zero w _))) hc).mpr hlower

theorem circleMap_norm_arg (z : ℂ) : circleMap 0 ‖z‖ z.arg = z := by
  rw [circleMap]
  simp only [zero_add]
  rw [Complex.exp_mul_I]
  apply Complex.ext <;> simp

/-- Canonical bounded analytic outer factor with the same boundary modulus as `phi`. -/
noncomputable def diskMultiplierOuterFactor
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) : DiskMultiplier where
  fn := szegoOuter (diskMultiplierOuterWeight phi)
  diff := (analyticOnNhd_szegoOuter
    (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi)).differentiableOn
  bd := max 1 phi.bd
  bd_nonneg := le_trans zero_le_one (le_max_left 1 phi.bd)
  bd_le := by
    intro z hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hz1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hsq := normSq_szegoOuter_le_from_weight_bound
      (show 0 < (max 1 phi.bd) ^ 2 by positivity)
      (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi)
      (diskMultiplierOuterWeight_pos phi)
      (diskMultiplierOuterWeight_le phi)
      hz0 hz1 z.arg
    rw [circleMap_norm_arg] at hsq
    have hbd : 0 ≤ max 1 phi.bd := le_trans zero_le_one (le_max_left 1 phi.bd)
    nlinarith [norm_nonneg (szegoOuter (diskMultiplierOuterWeight phi) z)]

theorem angularCircle_two_pi_mul (a : ℝ) :
    angularCircle (2 * Real.pi * a) =
      AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) := by
  rw [angularCircle]
  congr 2
  field_simp [Real.pi_ne_zero]

theorem circleMap_eq_radius_mul_angularCircle (r theta : ℝ) :
    circleMap 0 r theta = (r : ℂ) * (angularCircle theta : ℂ) := by
  simp [coe_angularCircle, circleMap]

/-- The canonical outer factor has exactly the original multiplier's boundary modulus. -/
theorem ae_norm_sq_diskMultiplierOuterFactor_boundary
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun (diskMultiplierOuterFactor phi hphi) z‖ ^ 2 =
        ‖diskMultiplierBoundarySafe phi z‖ ^ 2 := by
  let outer := diskMultiplierOuterFactor phi hphi
  obtain ⟨ns, hns, hboundary⟩ := exists_diskMultiplierRadialBoundary_subseq_ae outer
  have hszego := tendsto_normSq_szegoOuter_ae
    (locallyIntegrable_log_diskMultiplierOuterWeight phi hphi)
    (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi)
    (periodic_log_diskMultiplierOuterWeight phi)
    (diskMultiplierOuterWeight_pos phi)
  have hscale : Measure.QuasiMeasurePreserving
      (fun a : ℝ => (2 * Real.pi) • a) volume volume :=
    Measure.quasiMeasurePreserving_smul volume
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hszegoScaled : ∀ᵐ a ∂volume,
      Tendsto
        (fun r => ‖szegoOuter (diskMultiplierOuterWeight phi)
          (circleMap 0 r ((2 * Real.pi) • a))‖ ^ 2)
        (𝓝[<] 1)
        (𝓝 (diskMultiplierOuterWeight phi ((2 * Real.pi) • a))) :=
    hscale.ae hszego
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hvh : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  let circleHomeo := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hhomeo : MeasurePreserving circleHomeo volume circleLebesgue := by
    refine ⟨circleHomeo.continuous.measurable, ?_⟩
    rw [circleLebesgue, hvh]
  have hcircle : MeasurePreserving
      (circleHomeo ∘ QuotientAddGroup.mk)
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) circleLebesgue :=
    hhomeo.comp (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  have hboundaryPull : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      Tendsto
        (fun i => diskMultiplierRadialBoundaryFun (ns i) outer
          (circleHomeo (QuotientAddGroup.mk a)))
        atTop
        (𝓝 (diskMultiplierBoundaryFun outer
          (circleHomeo (QuotientAddGroup.mk a)))) :=
    hcircle.quasiMeasurePreserving.ae hboundary
  have hrepPull : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      diskMultiplierBoundaryMeasurableRep outer
          (circleHomeo (QuotientAddGroup.mk a)) =
        diskMultiplierBoundaryFun outer
          (circleHomeo (QuotientAddGroup.mk a)) :=
    hcircle.quasiMeasurePreserving.ae (diskMultiplierBoundaryMeasurableRep_ae outer)
  have hszegoPull : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      Tendsto
        (fun r => ‖szegoOuter (diskMultiplierOuterWeight phi)
          (circleMap 0 r ((2 * Real.pi) • a))‖ ^ 2)
        (𝓝[<] 1)
        (𝓝 (diskMultiplierOuterWeight phi ((2 * Real.pi) • a))) :=
    hszegoScaled.filter_mono (ae_mono Measure.restrict_le_self)
  have hsource : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      ‖diskMultiplierBoundaryMeasurableRep outer
          (circleHomeo (QuotientAddGroup.mk a))‖ ^ 2 =
        ‖diskMultiplierBoundarySafe phi
          (circleHomeo (QuotientAddGroup.mk a))‖ ^ 2 := by
    filter_upwards [hboundaryPull, hrepPull, hszegoPull] with a hba hrep hsa
    have hradius : Tendsto (fun i => hardyDiskAbelRadius (ns i)) atTop (𝓝[<] (1 : ℝ)) :=
      tendsto_hardyDiskAbelRadius.comp hns.tendsto_atTop
    have hsseq := hsa.comp hradius
    have hbnorm : Tendsto
        (fun i => ‖diskMultiplierRadialBoundaryFun (ns i) outer
          (circleHomeo (QuotientAddGroup.mk a))‖ ^ 2)
        atTop
        (𝓝 (‖diskMultiplierBoundaryFun outer
          (circleHomeo (QuotientAddGroup.mk a))‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto _).comp hba
    have hsame : (fun i => ‖szegoOuter (diskMultiplierOuterWeight phi)
          (circleMap 0 (hardyDiskAbelRadius (ns i)) ((2 * Real.pi) • a))‖ ^ 2) =
        fun i => ‖diskMultiplierRadialBoundaryFun (ns i) outer
          (circleHomeo (QuotientAddGroup.mk a))‖ ^ 2 := by
      funext i
      congr 3
      have hang : angularCircle ((2 * Real.pi) • a) =
          circleHomeo (QuotientAddGroup.mk a) := by
        simpa only [smul_eq_mul, circleHomeo, AddCircle.homeomorphCircle_apply] using
          angularCircle_two_pi_mul a
      rw [circleMap_eq_radius_mul_angularCircle, hang]
    change Tendsto
      (fun i => ‖szegoOuter (diskMultiplierOuterWeight phi)
        (circleMap 0 (hardyDiskAbelRadius (ns i)) ((2 * Real.pi) • a))‖ ^ 2)
      atTop (𝓝 (diskMultiplierOuterWeight phi ((2 * Real.pi) • a))) at hsseq
    rw [hsame] at hsseq
    have hlimit := tendsto_nhds_unique hbnorm hsseq
    rw [← hrep] at hlimit
    simpa only [diskMultiplierOuterWeight, smul_eq_mul, circleHomeo,
      angularCircle_two_pi_mul, AddCircle.homeomorphCircle_apply] using hlimit
  have hmeasSet : MeasurableSet {z : Circle |
      ‖diskMultiplierBoundaryMeasurableRep outer z‖ ^ 2 =
        ‖diskMultiplierBoundarySafe phi z‖ ^ 2} :=
    measurableSet_eq_fun
      ((measurable_diskMultiplierBoundaryMeasurableRep outer).norm.pow_const 2)
      ((measurable_diskMultiplierBoundarySafe phi).norm.pow_const 2)
  have hmeasMap : AEMeasurable (circleHomeo ∘ QuotientAddGroup.mk)
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) :=
    hcircle.measurable.aemeasurable
  have hrepTarget : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryMeasurableRep outer z‖ ^ 2 =
        ‖diskMultiplierBoundarySafe phi z‖ ^ 2 := by
    rw [← hcircle.map_eq]
    exact (ae_map_iff hmeasMap hmeasSet).2 hsource
  filter_upwards [hrepTarget, diskMultiplierBoundaryMeasurableRep_ae outer] with z hz hrep
  rwa [hrep] at hz

end

end GaloisForLFunctions.HTGeometry
