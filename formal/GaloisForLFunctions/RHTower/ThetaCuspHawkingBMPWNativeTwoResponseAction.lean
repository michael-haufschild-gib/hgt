import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWTwoResponseActionLimit

/-!
# The native anomaly in the admitted two-response action

The full/full bulk cancels after absolute Fubini admission. What remains is
the original native Dirichlet kernel, with its original causal gates and image.
The resulting wave-minus-native action has a cutoff-independent source limit.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.D4BMPWNativeTwoResponseAction
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse
open D4BMFullAngularCausalPeierls D4BMFullAngularReconstruction D4BMNativeCircle
open D4BMGeneralTemporalTransposition D4BMPWRetardedWeakNative
open D4BMPWTwoResponseAction D4BMPWTwoResponseActionLimit

noncomputable section
set_option autoImplicit false

private def bulkTest (q : XiZeroCopy) (branch : Bool) (phi : Event → ℂ) (r : Event) : ℂ :=
  parameter q branch / (Real.cosh r.2 : ℂ) ^ (2 : ℕ) * phi r

private theorem bulkTest_continuous (q : XiZeroCopy) (branch : Bool) (phi : Event → ℂ)
    (hp : Continuous phi) : Continuous (bulkTest q branch phi) := by
  have hd : Continuous (fun r : Event => (Real.cosh r.2 : ℂ) ^ (2 : ℕ)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp continuous_snd)).pow 2
  have hn (r : Event) : (Real.cosh r.2 : ℂ) ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (Real.cosh_pos r.2).ne')
  exact (continuous_const.div hd hn).mul hp

private theorem bulkTest_compact (q : XiZeroCopy) (branch : Bool) (phi : Event → ℂ)
    (hc : HasCompactSupport phi) : HasCompactSupport (bulkTest q branch phi) :=
  hc.mul_left

/-- The undropped native kernel action, integrated over the target event. -/
def nativeBulkAt (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (phi : Event → ℂ) (p : Event) : ℂ :=
  ∫ r : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 * parameter q branch *
    nativeDirichletCausalKernel q (r.1 - p.1) r.2 p.2 X k /
      (Real.cosh r.2 : ℂ) ^ (2 : ℕ) * phi r

private theorem nativeBulkAt_split (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (phi : Event → ℂ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    nativeBulkAt q branch b a X k phi =ᵐ[eventMeasure]
      (fun p : Event => retardedCoupledBulkAt q branch b a X k phi p -
        timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          (∫ r : Event, angularDirichletKernel q branch (r.1 - p.1) r.2 p.2 X k *
            bulkTest q branch phi r)) := by
  have hcont := bulkTest_continuous q branch phi hp.continuous
  have hcompact := bulkTest_compact q branch phi hc
  filter_upwards [retardedCoupledBulkDensity_target_integrable_ae q branch b a X k phi hp hc,
    fullRetardedResponse_test_target_integrable_ae q branch b a X k _ hcont hcompact]
    with p hcoupled hfull
  rw [nativeBulkAt, retardedCoupledBulkAt, ← integral_const_mul, ← integral_sub hcoupled hfull]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by unfold retardedCoupledBulkDensity bulkTest; ring)

theorem responseTest_native_integrable (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (nativeBulkAt q branch b a X k (responseTest chi q branch c d X k))
      eventMeasure := by
  have hp := responseTest_smooth chi hs hw q branch c d X k
  have hcompact := responseTest_compact chi hc q branch c d X k
  have hfull := fullRetardedResponse_source_test_integrable q branch b a X k _
    (bulkTest_continuous q branch _ hp.continuous) (bulkTest_compact q branch _ hcompact)
  exact ((responseTest_bulk_integrable chi hs hc hw q branch b c a d X k).sub hfull).congr
    (nativeBulkAt_split q branch b a X k _ hp hcompact).symm

private theorem nativeBulk_integral (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    (∫ p : Event, nativeBulkAt q branch b a X k (responseTest chi q branch c d X k) p
      ∂eventMeasure) =
    (∫ p : Event, retardedCoupledBulkAt q branch b a X k (responseTest chi q branch c d X k) p
      ∂eventMeasure) -
    ∫ r : Event, fullRetardedResponse q branch b a r.1 r.2 X k *
      bulkTest q branch (responseTest chi q branch c d X k) r := by
  have hp := responseTest_smooth chi hs hw q branch c d X k
  have hcompact := responseTest_compact chi hc q branch c d X k
  have hcont := bulkTest_continuous q branch _ hp.continuous
  have hc' := bulkTest_compact q branch _ hcompact
  rw [integral_congr_ae (nativeBulkAt_split q branch b a X k _ hp hcompact),
    integral_sub (responseTest_bulk_integrable chi hs hc hw q branch b c a d X k)
      (fullRetardedResponse_source_test_integrable q branch b a X k _ hcont hc'),
    ← fullRetardedResponse_test_fubini q branch b a X k _ hcont hc']

/-- Literal wave action with only the surviving native kernel correction. -/
def nativeTwoResponseAction (chi : Event → ℝ) (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) : ℂ :=
  ((∫ p : Event, fullRetardedResponse q branch b a p.1 p.2 X k *
      eventWave (responseTest chi q branch c d X k) p) -
    (∫ p : Event, fullRetardedResponse q branch c d p.1 p.2 X k *
      eventWave (responseTest chi q branch b a X k) p)) -
  ((∫ p : Event, nativeBulkAt q branch b a X k
      (responseTest chi q branch c d X k) p ∂eventMeasure) -
    (∫ p : Event, nativeBulkAt q branch c d X k
      (responseTest chi q branch b a X k) p ∂eventMeasure))

/-- Absolute Fubini admission cancels the full/full bulk exactly. -/
theorem nativeTwoResponseAction_eq (chi : Event → ℝ) (hs : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hw : tsupport chi ⊆ physicalWedge)
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    nativeTwoResponseAction chi q branch b c a d X k =
      twoResponseAction chi q branch b c a d X k := by
  unfold nativeTwoResponseAction twoResponseAction
  rw [nativeBulk_integral chi hs hc hw q branch b c a d X k,
    nativeBulk_integral chi hs hc hw q branch c b d a X k]
  have he : (∫ r : Event, fullRetardedResponse q branch b a r.1 r.2 X k *
      bulkTest q branch (responseTest chi q branch c d X k) r) =
    (∫ r : Event, fullRetardedResponse q branch c d r.1 r.2 X k *
      bulkTest q branch (responseTest chi q branch b a X k) r) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun r => by unfold bulkTest responseTest; ring)
  rw [he]
  ring

theorem nativeTwoResponseAction_tendsto_of_exhaustion (chi : ℕ → Event → ℝ)
    (hs : ∀ n, ContDiff ℝ ∞ (chi n)) (hc : ∀ n, HasCompactSupport (chi n))
    (hw : ∀ n, tsupport (chi n) ⊆ physicalWedge)
    (hb : ∀ n p, 0 ≤ chi n p ∧ chi n p ≤ 1)
    (hl : ∀ p ∈ physicalWedge, Tendsto (fun n => chi n p) atTop (𝓝 1))
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => nativeTwoResponseAction (chi n) q branch b c a d X k) atTop
      (𝓝 (fullAngularField q branch ![X, Real.exp k] *
        fullCausalSourcePair q branch b c a d X k)) := by
  apply (twoResponseAction_tendsto_of_exhaustion chi hs hc hw hb hl q branch b c a d X k).congr'
  exact Eventually.of_forall (fun n =>
    (nativeTwoResponseAction_eq (chi n) (hs n) (hc n) (hw n) q branch b c a d X k).symm)

/-- The two complementary retarded responses have an unconditional native-corrected
action limit, equal to the original full causal source contact. -/
theorem complementary_native_action_tendsto (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => nativeTwoResponseAction (wedgeWindow n) q branch true false a d X k) atTop
      (𝓝 (fullAngularField q branch ![X, Real.exp k] *
        fullCausalSourcePair q branch true false a d X k)) := by
  apply (complementary_twoResponseAction_tendsto q branch a d X k).congr'
  exact Eventually.of_forall (fun n =>
    (nativeTwoResponseAction_eq (wedgeWindow n) (wedgeWindow_smooth n) (wedgeWindow_compact n)
      (wedgeWindow_support n) q branch true false a d X k).symm)

end
end RHTower.D4BMPWNativeTwoResponseAction
