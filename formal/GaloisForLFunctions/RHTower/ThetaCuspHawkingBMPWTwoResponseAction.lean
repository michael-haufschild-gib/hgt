import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWRetardedRegularity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWRetardedWeakNative
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCutoff

/-!
# Inserting both literal retarded responses into the wave action

The tests are products of the actual retarded event integrals and a compact
cutoff inside the physical onset wedge. All wave, source, and coupled bulk
integrals are absolutely admitted. The skew action retains the native anomaly.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.D4BMPWTwoResponseAction
open D4BMModularCore D4BMJointSource D4BMFullAngularCausalPeierls
open D4BMGlobalAngularResponse D4BMGeneralTemporalTransposition
open D4BMPWRetardedRegularity D4BMPWRetardedWeakNative

noncomputable section
set_option autoImplicit false

def physicalWedge : Set Event := {p | 0 < p.1 + p.2 ∧ p.2 < 0}

/-- A concrete smooth exhaustion staying away from both characteristic onset and wall. -/
def wedgeWindow (n : ℕ) (p : Event) : ℝ :=
  physicalWindow n p * physicalWindow n (-p.2, -(p.1 + p.2))

theorem wedgeWindow_smooth (n : ℕ) : ContDiff ℝ ∞ (wedgeWindow n) :=
  (physicalWindow_smooth n).mul ((physicalWindow_smooth n).comp (by fun_prop))

theorem wedgeWindow_compact (n : ℕ) : HasCompactSupport (wedgeWindow n) :=
  (physicalWindow_hasCompactSupport n).mul_right

theorem wedgeWindow_nonneg (n : ℕ) (p : Event) : 0 ≤ wedgeWindow n p :=
  mul_nonneg (physicalWindow_nonneg n p) (physicalWindow_nonneg n _)

theorem wedgeWindow_le_one (n : ℕ) (p : Event) : wedgeWindow n p ≤ 1 :=
  mul_le_one₀ (physicalWindow_le_one n p) (physicalWindow_nonneg n _)
    (physicalWindow_le_one n _)

theorem wedgeWindow_support (n : ℕ) : tsupport (wedgeWindow n) ⊆ physicalWedge := by
  intro p hp
  have hl : p ∈ tsupport (physicalWindow n) := tsupport_mul_subset_left hp
  have hr : p ∈ tsupport (fun z : Event => physicalWindow n (-z.2, -(z.1 + z.2))) :=
    tsupport_mul_subset_right hp
  have hg : Continuous (fun z : Event => (-z.2, -(z.1 + z.2))) := by fun_prop
  have hh := tsupport_comp_subset_preimage (physicalWindow n) hg hr
  have hneg := physicalWindow_tsupport_subset_physical n hh
  exact ⟨by simpa using hneg, physicalWindow_tsupport_subset_physical n hl⟩

theorem wedgeWindow_eventually_one (p : Event) (hp : p ∈ physicalWedge) :
    ∀ᶠ n in atTop, wedgeWindow n p = 1 := by
  filter_upwards [physicalWindow_eventually_eq_one p hp.2,
    physicalWindow_eventually_eq_one (-p.2, -(p.1 + p.2)) (by simpa using hp.1)]
    with n hn hn'
  simp only [wedgeWindow, hn, hn', mul_one]

/-- A response-valued test, defined using the full source event integral. -/
def responseTest (chi : Event → ℝ) (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (p : Event) : ℂ :=
  (chi p : ℂ) * fullRetardedResponse q branch b a p.1 p.2 X k

theorem responseTest_smooth (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hw : tsupport chi ⊆ physicalWedge) (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) : ContDiff ℝ ∞ (responseTest chi q branch b a X k) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport chi
  · exact (Complex.ofRealCLM.contDiff.comp hs).contDiffAt.mul
      (fullRetardedResponse_contDiffAt q branch b a X k p (hw hp).1 (hw hp).2)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with r hr
    change (chi r : ℂ) * _ = 0
    simp only [Pi.zero_apply] at hr
    rw [hr, Complex.ofReal_zero, zero_mul]

theorem responseTest_compact (chi : Event → ℝ) (hc : HasCompactSupport chi)
    (q : XiZeroCopy) (branch b : Bool) (a : ℂ) (X k : ℝ) :
    HasCompactSupport (responseTest chi q branch b a X k) :=
  (hc.comp_left Complex.ofReal_zero).mul_right

theorem responseTest_zero_nonnegative_radius (chi : Event → ℝ)
    (hw : tsupport chi ⊆ physicalWedge) (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (p : Event) (hp : 0 ≤ p.2) :
    responseTest chi q branch b a X k p = 0 := by
  have hn : p ∉ tsupport chi := fun h => (not_lt_of_ge hp) (hw h).2
  simp only [responseTest, image_eq_zero_of_notMem_tsupport hn, Complex.ofReal_zero, zero_mul]

theorem eventMeasure_physical : ∀ᵐ p : Event ∂eventMeasure, 0 < p.1 ∧ p.2 < 0 := by
  rw [eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Iio)

theorem responseTest_source_integrable (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      responseTest chi q branch c d X k p) eventMeasure := by
  apply ((timeReducedCoefficient_joint_continuous (physicalRate q b) a).mul
    (responseTest_smooth chi hs hw q branch c d X k).continuous).integrable_of_hasCompactSupport
  exact (responseTest_compact chi hc q branch c d X k).mul_left

theorem responseTest_wave_integrable (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event => fullRetardedResponse q branch b a p.1 p.2 X k *
      eventWave (responseTest chi q branch c d X k) p) := by
  obtain ⟨hcont, hcompact⟩ := eventWave_continuous_compact
    (responseTest_smooth chi hs hw q branch c d X k)
    (responseTest_compact chi hc q branch c d X k)
  exact fullRetardedResponse_test_integrable q branch b a X k _ hcont hcompact

private theorem physical_weak_integrable (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event =>
      fullAngularField q branch ![X, Real.exp k] *
        (timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          responseTest chi q branch c d X k p) +
      retardedCoupledBulkAt q branch b a X k (responseTest chi q branch c d X k) p)
        eventMeasure := by
  apply (fullRetardedResponse_weak_source_integrable q branch b a X k _
    (responseTest_smooth chi hs hw q branch c d X k)
    (responseTest_compact chi hc q branch c d X k)).congr
  filter_upwards [eventMeasure_physical] with p hp
  rw [responseTest_zero_nonnegative_radius chi hw q branch c d X k
    (p.1, -p.2) (by simpa using hp.2.le)]
  ring

theorem responseTest_bulk_integrable (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (retardedCoupledBulkAt q branch b a X k
      (responseTest chi q branch c d X k)) eventMeasure := by
  have htotal := physical_weak_integrable chi hs hc hw q branch b c a d X k
  have hsource := (responseTest_source_integrable chi hs hc hw q branch b c a d X k).const_mul
    (fullAngularField q branch ![X, Real.exp k])
  simpa only [Pi.sub_apply, add_sub_cancel_left] using htotal.sub hsource

private theorem responseTest_weak (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    (∫ p : Event, fullRetardedResponse q branch b a p.1 p.2 X k *
      eventWave (responseTest chi q branch c d X k) p) =
      fullAngularField q branch ![X, Real.exp k] *
        (∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          responseTest chi q branch c d X k p ∂eventMeasure) +
      ∫ p : Event, retardedCoupledBulkAt q branch b a X k
        (responseTest chi q branch c d X k) p ∂eventMeasure := by
  rw [fullRetardedResponse_weak_with_native q branch b a X k _
    (responseTest_smooth chi hs hw q branch c d X k)
    (responseTest_compact chi hc q branch c d X k)]
  have he : (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      (fullAngularField q branch ![X, Real.exp k] *
        (responseTest chi q branch c d X k p - responseTest chi q branch c d X k (p.1, -p.2))) +
      retardedCoupledBulkAt q branch b a X k (responseTest chi q branch c d X k) p) =ᵐ[eventMeasure]
    (fun p : Event => fullAngularField q branch ![X, Real.exp k] *
      (timeReducedCoefficient (physicalRate q b) a p.1 p.2 * responseTest chi q branch c d X k p) +
      retardedCoupledBulkAt q branch b a X k (responseTest chi q branch c d X k) p) := by
    filter_upwards [eventMeasure_physical] with p hp
    rw [responseTest_zero_nonnegative_radius chi hw q branch c d X k
      (p.1, -p.2) (by simpa using hp.2.le)]
    ring
  rw [integral_congr_ae he, integral_add
    ((responseTest_source_integrable chi hs hc hw q branch b c a d X k).const_mul _)
    (responseTest_bulk_integrable chi hs hc hw q branch b c a d X k), integral_const_mul]

/-- The wave action with both literal responses inserted and the coupled native
bulk retained. It is defined from differential and kernel actions, not a source pairing. -/
def twoResponseAction (chi : Event → ℝ) (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) : ℂ :=
  ((∫ p : Event, fullRetardedResponse q branch b a p.1 p.2 X k *
      eventWave (responseTest chi q branch c d X k) p) -
    (∫ p : Event, fullRetardedResponse q branch c d p.1 p.2 X k *
      eventWave (responseTest chi q branch b a X k) p)) -
  ((∫ p : Event, retardedCoupledBulkAt q branch b a X k
      (responseTest chi q branch c d X k) p ∂eventMeasure) -
    (∫ p : Event, retardedCoupledBulkAt q branch c d X k
      (responseTest chi q branch b a X k) p ∂eventMeasure))

/-- Exact two-response insertion for the original full angular source vertex. -/
theorem twoResponseAction_eq_contact (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    twoResponseAction chi q branch b c a d X k =
      fullAngularField q branch ![X, Real.exp k] *
        ((∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
            responseTest chi q branch c d X k p ∂eventMeasure) -
          (∫ p : Event, timeReducedCoefficient (physicalRate q c) d p.1 p.2 *
            responseTest chi q branch b a X k p ∂eventMeasure)) := by
  unfold twoResponseAction
  rw [responseTest_weak chi hs hc hw q branch b c a d X k,
    responseTest_weak chi hs hc hw q branch c b d a X k]
  ring

end
end RHTower.D4BMPWTwoResponseAction
