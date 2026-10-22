import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularGoursatTransposition
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCutoffSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWOrderedCTPNullTransport
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWSourceBoundaryNullAdmission

/-!
# PW-B uncut physical source: finite two-chart Goursat transport

At fixed receiver time s ≥ 0, onset forces each literal source arm to vanish
when u+v ≥ 2s. Direct and reflected-image arms therefore have exact finite
Goursat transpositions on [0,2s]²; no inner noncompact limit is required.

This does not identify the two arm integrals with the ordered CTP current,
or prove the outer noncompact current limit, PW magnitude, or extinction.
-/

open Complex MeasureTheory Set Topology

namespace RHTower.D4BMPWTwoChartGoursat
open D4BMFullAngularGoursatTransposition D4BMGeneralTemporalTransposition
open D4BMJointSource D4BMModularCore D4BMGlobalAngularResponse
open D4BMFullAngularCircle D4BMFullAngularReconstruction
open D4BMFullAngularCircleAction D4BMFullAngularGoursat
open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

/-- The physical source without an artificial cutoff: radial zero-extension
already enforces the original event set because onset kills nonpositive time. -/
def physicalSource (s a : ℂ) : ℝ × ℝ → ℂ :=
  fun p => if p.2 < 0 then timeReducedCoefficient s a p.1 p.2 else 0

theorem physicalSource_continuous (s a : ℂ) : Continuous (physicalSource s a) := by
  classical
  apply Continuous.if
    (p := fun p : ℝ × ℝ => p.2 < 0)
    (fun p hp => ?_)
    (timeReducedCoefficient_joint_continuous s a) continuous_const
  have hfront := (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2)).frontier_preimage_subset
    (Iio (0 : ℝ)) hp
  have hp0 : p.2 = 0 := by
    simpa only [mem_preimage, frontier_Iio, mem_singleton_iff] using hfront
  simp [hp0, timeReducedCoefficient_zero_at_radial_wall]

theorem physicalSource_eq_event_indicator (s a : ℂ) :
    physicalSource s a =
      (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)).indicator
        (fun p : ℝ × ℝ => timeReducedCoefficient s a p.1 p.2) := by
  funext p
  by_cases hx : p.2 < 0
  · by_cases ht : 0 < p.1
    · simp [physicalSource, hx, ht, Set.indicator]
    · have hz := timeReducedCoefficient_zero_at_nonpositive_time_negative_radius
        s a p.1 p.2 (le_of_not_gt ht) hx
      simp [physicalSource, hx, ht, hz, Set.indicator]
  · simp [physicalSource, hx, Set.indicator]

def nullPhysicalTest (q : XiZeroCopy) (b c : Bool) (a d : ℂ)
    (r : ℝ × ℝ) (η : ℝ) (z : ℝ × ℝ) : ℂ :=
  physicalSource (physicalRate q b) a (pastVertex r.1 η z) *
    physicalSource (physicalRate q c) d r

theorem nullPhysicalTest_continuous (q : XiZeroCopy) (b c : Bool) (a d : ℂ)
    (r : ℝ × ℝ) (η : ℝ) : Continuous (nullPhysicalTest q b c a d r η) := by
  have hp : Continuous (pastVertex r.1 η) := by unfold pastVertex; fun_prop
  exact ((physicalSource_continuous (physicalRate q b) a).comp hp).mul continuous_const

theorem nullPhysicalTest_zero_of_sum (q : XiZeroCopy) (b c : Bool)
    (a d : ℂ) (r : ℝ × ℝ) (η : ℝ) (z : ℝ × ℝ)
    (hz : 2 * r.1 ≤ z.1 + z.2) :
    nullPhysicalTest q b c a d r η z = 0 := by
  let p := pastVertex r.1 η z
  have ht : p.1 ≤ 0 := by dsimp [p, pastVertex]; linarith
  by_cases hx : p.2 < 0
  · have hzero := timeReducedCoefficient_zero_at_nonpositive_time_negative_radius
      (physicalRate q b) a p.1 p.2 ht hx
    unfold nullPhysicalTest physicalSource
    rw [if_pos hx, hzero, zero_mul]
  · unfold nullPhysicalTest physicalSource
    rw [if_neg hx, zero_mul]

theorem actual_arm_physical_finite_transposition (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (r : ℝ × ℝ)
    (η X k : ℝ) (hr : 0 ≤ r.1) :
    (∫ u in (0 : ℝ)..(2 * r.1), ∫ v in (0 : ℝ)..(2 * r.1),
      fullAngularRiemannKernel q branch ((u + v) / 2)
        (η + (u - v) / 2) η X k *
          nullPhysicalTest q b c a d r η (u,v)) =
      fullAngularField q branch ![X, Real.exp k] *
        backwardRectanglePrimitive (nullPhysicalTest q b c a d r η)
          (2 * r.1) (2 * r.1) (0,0) +
        ∫ u in (0 : ℝ)..(2 * r.1), ∫ v in (0 : ℝ)..(2 * r.1),
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2)
                (η + (u - v) / 2) η X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2)
                (η + (u - v) / 2) η X k) /
            (4 * (Real.cosh (η + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
              backwardRectanglePrimitive (nullPhysicalTest q b c a d r η)
                (2 * r.1) (2 * r.1) (u,v) :=
  fullAngularRiemannKernel_continuous_test_transposition q branch η X k
    (2 * r.1) (2 * r.1) (by linarith) (by linarith)
    (nullPhysicalTest q b c a d r η) (nullPhysicalTest_continuous q b c a d r η)

private theorem quadrant_eq_box_of_sum_support (F : ℝ × ℝ → ℂ)
    (hF : Continuous F) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ z : ℝ × ℝ, R ≤ z.1 + z.2 → F z = 0) :
    (∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ), F z) =
      ∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R, F (u,v) := by
  have he : (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)).indicator F =
      (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R).indicator F := by
    funext z
    by_cases hq : z ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)
    · by_cases hb : z ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R
      · simp only [Set.indicator_of_mem hq, Set.indicator_of_mem hb]
      · have hs : R ≤ z.1 + z.2 := by
          have hq1 : 0 ≤ z.1 := hq.1
          have hq2 : 0 ≤ z.2 := hq.2
          have hh : R < z.1 ∨ R < z.2 := by
            by_contra! hh
            exact hb ⟨⟨hq.1, hh.1⟩, ⟨hq.2, hh.2⟩⟩
          rcases hh with hh | hh <;> linarith
        simp only [Set.indicator_of_mem hq, Set.indicator_of_notMem hb, hzero z hs]
    · have hb : z ∉ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R :=
        fun h => hq ⟨h.1.1, h.2.1⟩
      simp only [Set.indicator_of_notMem hq, Set.indicator_of_notMem hb]
  rw [← integral_indicator (measurableSet_Ici.prod measurableSet_Ici), he,
    integral_indicator (measurableSet_Icc.prod measurableSet_Icc), Measure.volume_eq_prod]
  rw [setIntegral_prod F
    (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))]
  simp_rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hR]

def closedPhysicalArm (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (r : ℝ × ℝ) (η X k : ℝ) (z : ℝ × ℝ) : ℂ :=
  angularMean q branch (Real.arcosh (max 1
    (D4BMCausalKernel.invariant ((z.1 + z.2) / 2)
      (η + (z.1 - z.2) / 2) η))) X k *
    nullPhysicalTest q b c a d r η z

theorem closedPhysicalArm_continuous (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (r : ℝ × ℝ) (η X k : ℝ) :
    Continuous (closedPhysicalArm q branch b c a d r η X k) := by
  have hi : Continuous (fun z : ℝ × ℝ =>
      D4BMCausalKernel.invariant ((z.1 + z.2) / 2)
        (η + (z.1 - z.2) / 2) η) := by
    unfold D4BMCausalKernel.invariant
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have hr : Continuous (fun z : ℝ × ℝ => Real.arcosh (max 1
      (D4BMCausalKernel.invariant ((z.1 + z.2) / 2)
        (η + (z.1 - z.2) / 2) η))) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
      (fun z => by
        change 1 ≤ max 1
          (D4BMCausalKernel.invariant ((z.1 + z.2) / 2)
            (η + (z.1 - z.2) / 2) η)
        exact le_max_left 1 _)
  exact ((angularMean_smooth q branch X k).continuous.comp hr).mul
    (nullPhysicalTest_continuous q b c a d r η)

theorem closedPhysicalArm_zero_of_sum (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (r : ℝ × ℝ) (η X k : ℝ) (z : ℝ × ℝ)
    (hz : 2 * r.1 ≤ z.1 + z.2) :
    closedPhysicalArm q branch b c a d r η X k z = 0 := by
  simp [closedPhysicalArm, nullPhysicalTest_zero_of_sum q b c a d r η z hz]

theorem closedPhysicalArm_quadrant_eq_finite (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (r : ℝ × ℝ) (η X k : ℝ)
    (hr : 0 ≤ r.1) :
    (∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
      closedPhysicalArm q branch b c a d r η X k z) =
      ∫ u in (0 : ℝ)..(2 * r.1), ∫ v in (0 : ℝ)..(2 * r.1),
        fullAngularRiemannKernel q branch ((u + v) / 2)
          (η + (u - v) / 2) η X k *
          nullPhysicalTest q b c a d r η (u,v) := by
  rw [quadrant_eq_box_of_sum_support _
    (closedPhysicalArm_continuous q branch b c a d r η X k)
    (2 * r.1) (by linarith)
    (closedPhysicalArm_zero_of_sum q branch b c a d r η X k)]
  apply intervalIntegral.integral_congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro v hv
  have hu0 : 0 ≤ u := (show u ∈ Icc 0 (2 * r.1) by
    simpa [uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * r.1)] using hu).1
  have hv0 : 0 ≤ v := (show v ∈ Icc 0 (2 * r.1) by
    simpa [uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * r.1)] using hv).1
  unfold closedPhysicalArm
  change angularMean q branch (Real.arcosh (max 1
      (D4BMCausalKernel.invariant ((u + v) / 2) (η + (u - v) / 2) η))) X k *
      nullPhysicalTest q b c a d r η (u,v) =
    fullAngularRiemannKernel q branch ((u + v) / 2)
      (η + (u - v) / 2) η X k * nullPhysicalTest q b c a d r η (u,v)
  rw [fullAngularRiemannKernel_null_closed q branch η u v X k hu0 hv0]

/-- Exact Goursat right side for one physical source arm. -/
def physicalArmGoursatRHS (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (r : ℝ × ℝ) (η X k : ℝ) : ℂ :=
  fullAngularField q branch ![X, Real.exp k] *
    backwardRectanglePrimitive (nullPhysicalTest q b c a d r η)
      (2 * r.1) (2 * r.1) (0,0) +
    ∫ u in (0 : ℝ)..(2 * r.1), ∫ v in (0 : ℝ)..(2 * r.1),
      parameter q branch *
        (fullAngularRiemannKernel q branch ((u + v) / 2)
            (η + (u - v) / 2) η X k +
          D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2)
            (η + (u - v) / 2) η X k) /
        (4 * (Real.cosh (η + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
          backwardRectanglePrimitive (nullPhysicalTest q b c a d r η)
            (2 * r.1) (2 * r.1) (u,v)

/-- The literal physical source has an exact quadrant-to-finite Goursat law
in either direct or reflected-image chart. -/
theorem physicalArm_quadrant_transposition (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (r : ℝ × ℝ) (η X k : ℝ)
    (hr : 0 ≤ r.1) :
    (∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
      closedPhysicalArm q branch b c a d r η X k z) =
      physicalArmGoursatRHS q branch b c a d r η X k := by
  rw [closedPhysicalArm_quadrant_eq_finite q branch b c a d r η X k hr]
  exact actual_arm_physical_finite_transposition q branch b c a d r η X k hr

/-- The direct-minus-image physical source transposition keeps both center
radii, so the image radial wedge remains inside its own literal test. -/
theorem direct_image_physicalArm_transposition (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (r : ℝ × ℝ) (X k : ℝ)
    (hr : 0 ≤ r.1) :
    (∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
      closedPhysicalArm q branch b c a d r r.2 X k z) -
    (∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
      closedPhysicalArm q branch b c a d r (-r.2) X k z) =
      physicalArmGoursatRHS q branch b c a d r r.2 X k -
      physicalArmGoursatRHS q branch b c a d r (-r.2) X k := by
  rw [physicalArm_quadrant_transposition q branch b c a d r r.2 X k hr,
    physicalArm_quadrant_transposition q branch b c a d r (-r.2) X k hr]

end
end RHTower.D4BMPWTwoChartGoursat

