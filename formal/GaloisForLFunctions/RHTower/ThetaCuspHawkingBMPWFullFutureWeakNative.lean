import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursatTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing

/-!
# PW-B infinite full-future weak response with native coupling

The literal full causal source is transposed through its infinite source-event integral.
The physical wave contact keeps the full angular vertex, reflected image, and
coupled full-plus-native bulk action. This closes one-leg weak transport only;
identification of the two-leg action boundary and source extinction remain open.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMPWFullFutureWeakNative
open D4BMGeneralTemporalTransposition D4BMFullAngularGoursatTransposition
open D4BMFullAngularCausalPeierls D4BMModularCore D4BMHorizon
open D4BMJointSource D4BMGlobalAngularResponse D4BMLiteralCyclicPeierls
open D4BMNativeCircle D4BMFullAngularReconstruction

noncomputable section
set_option autoImplicit false

private theorem eventWave_continuous_compact {phi : Event → ℂ}
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Continuous (eventWave phi) ∧ HasCompactSupport (eventWave phi) := by
  have hd (v : Event) : ContDiff ℝ ∞ (eventDir v phi) :=
    (hp.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdd (v w : Event) : ContDiff ℝ ∞ (eventDir v (eventDir w phi)) :=
    ((hd w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  constructor
  · exact ((hdd (1,0) (1,0)).sub (hdd (0,1) (0,1))).continuous
  · unfold eventWave eventDir
    exact ((hc.fderiv_apply ℝ (1,0)).fderiv_apply ℝ (1,0)).sub
      ((hc.fderiv_apply ℝ (0,1)).fderiv_apply ℝ (0,1))

def sourceLeg (q : XiZeroCopy) (b : Bool) (a : ℂ) (p : Event) : ℂ :=
  timeReducedCoefficient (physicalRate q b) a p.1 p.2

def fullKernel (q : XiZeroCopy) (branch : Bool) (X k : ℝ)
    (p r : Event) : ℂ :=
  angularDirichletKernel q branch (p.1-r.1) r.2 p.2 X k

def nativeKernel (q : XiZeroCopy) (X k : ℝ) (p r : Event) : ℂ :=
  D4BMNativeCircle.nativeDirichletCausalKernel q (p.1-r.1) r.2 p.2 X k

def coupledBulkDensity (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (phi : Event → ℂ) (p r : Event) : ℂ :=
  sourceLeg q b a p * parameter q branch *
    (fullKernel q branch X k p r + nativeKernel q X k p r) /
      (Real.cosh r.2 : ℂ) ^ (2 : ℕ) * phi r

def coupledBulkAt (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (phi : Event → ℂ) (p : Event) : ℂ :=
  ∫ r : Event, coupledBulkDensity q branch b a X k phi p r

private theorem residual_integrable (q : XiZeroCopy) (branch : Bool)
    (p : Event) (X k : ℝ) (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (fullDirichletTemporalResidual q branch p.1 p.2 X k phi) := by
  unfold fullDirichletTemporalResidual
  exact ((fullTemporalConeResidual_integrable q branch p.1 p.2 X k phi hp hc).sub
    (fullTemporalConeResidual_integrable q branch p.1 (-p.2) X k phi hp hc)).div_const 2

/-- Exact infinite-source weak equation for the full future response. The
source vertex and image remain literal, and the native lift remains in the
bulk term; no current or cusp boundary is assumed. -/
theorem fullFutureResponse_weak_with_native (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ r : Event, fullFutureResponse q branch b a r.1 r.2 X k * eventWave phi r) =
      ∫ p : Event, sourceLeg q b a p *
          (fullAngularField q branch ![X, Real.exp k] *
            (phi p - phi (p.1,-p.2))) +
        coupledBulkAt q branch b a X k phi p ∂eventMeasure := by
  obtain ⟨hwcont,hwcompact⟩ := eventWave_continuous_compact hp hc
  have hi := futureTestDensity_integrable q branch b a X k (eventWave phi)
    hwcont hwcompact
  change Integrable (fun z : Event × Event =>
    eventWave phi z.2 * (fullKernel q branch X k z.1 z.2 * sourceLeg q b a z.1))
      (eventMeasure.prod volume) at hi
  rw [fullFutureResponse_test_fubini q branch b a X k (eventWave phi)
    hwcont hwcompact]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with p hfull
  have hres : Integrable (fun r : Event => sourceLeg q b a p *
      fullDirichletTemporalResidual q branch p.1 p.2 X k phi r) :=
    (residual_integrable q branch p X k phi hp hc).const_mul _
  have hpoint (r : Event) :
      eventWave phi r * (fullKernel q branch X k p r * sourceLeg q b a p) =
        sourceLeg q b a p *
          fullDirichletTemporalResidual q branch p.1 p.2 X k phi r +
          coupledBulkDensity q branch b a X k phi p r := by
    rw [fullDirichletTemporalResidual_kernel]
    dsimp only [fullKernel,nativeKernel,coupledBulkDensity]
    ring
  have hbulk : Integrable (coupledBulkDensity q branch b a X k phi p) := by
    apply (hfull.sub hres).congr
    filter_upwards with r
    simp only [Pi.sub_apply]
    linear_combination (hpoint r)
  change sourceLeg q b a p *
      (∫ r : Event, fullKernel q branch X k p r * eventWave phi r) = _
  rw [← integral_const_mul]
  calc
    (∫ r : Event, sourceLeg q b a p *
        (fullKernel q branch X k p r * eventWave phi r)) =
      ∫ r : Event, sourceLeg q b a p *
        fullDirichletTemporalResidual q branch p.1 p.2 X k phi r +
        coupledBulkDensity q branch b a X k phi p r := by
          apply integral_congr_ae
          filter_upwards with r
          linear_combination hpoint r
    _ = (∫ r : Event, sourceLeg q b a p *
          fullDirichletTemporalResidual q branch p.1 p.2 X k phi r) +
        coupledBulkAt q branch b a X k phi p := by
          rw [integral_add hres hbulk]
          rfl
    _ = _ := by
      rw [integral_const_mul,
        fullDirichletTemporalResidual_integral q branch p.1 p.2 X k phi hp hc]

/-- On physical negative-radius tests, source's reflected vertex vanishes and
the exact infinite-source contact is the original full angular field. -/
theorem fullFutureResponse_physical_weak_with_native (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hphysical : tsupport phi ⊆ {r : Event | r.2 < 0}) :
    (∫ r : Event, fullFutureResponse q branch b a r.1 r.2 X k * eventWave phi r) =
      ∫ p : Event, sourceLeg q b a p *
          (fullAngularField q branch ![X, Real.exp k] * phi p) +
        coupledBulkAt q branch b a X k phi p ∂eventMeasure := by
  rw [fullFutureResponse_weak_with_native q branch b a X k phi hp hc]
  have he : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_snd continuous_const).measurableSet :
        MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  apply integral_congr_ae
  filter_upwards [he] with p hneg
  have hz : phi (p.1,-p.2) = 0 := by
    by_contra hn
    have h := hphysical (subset_tsupport phi
      (show (p.1,-p.2) ∈ Function.support phi from hn))
    change -p.2 < 0 at h
    linarith
  rw [hz]
  ring

end
end RHTower.D4BMPWFullFutureWeakNative
