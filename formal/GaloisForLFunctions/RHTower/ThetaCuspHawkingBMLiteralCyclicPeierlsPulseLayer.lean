import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCorrectedFutureCap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleZeroJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRetardedHorizonGeometry
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCharacteristicGlobalGrowth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCharacteristicGlobalGrowth
import GaloisForLFunctions.HTGeometry.KleinGordonSynthesis
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Literal cyclic Peierls pulse boundary layer

On the ingoing cap trajectory, the future pulse has a co-moving direct layer.
Putting source tortoise coordinate `y = x - z` freezes its direct cone to
`|z| ≤ h`; its image cone becomes `|2x-z| ≤ h`.  Hence the direct layer is a
genuine cap-scale contribution while the image is a separate escaping-face
term.  This file records that exact geometry before any dominated convergence
or cusp limit is attempted.

Proof-chain role:
`corrected future residual -> direct/image pulse layer -> cap-scale layer
evaluation + image control -> corrected-future cap action -> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsPulseLayer

open D4BMJointSource D4BMModularCore D4BMFullAngularCircle
open D4BMFullAngularGoursat D4BMFullAngularReconstruction D4BMNativeCircle
open D4BMFuturePulseAdmission D4BMCapNormalTrace
open D4BMLiteralCyclicPeierlsCorrectedFutureCap
open D4BMRetardedHorizonGeometry
open MeasureTheory Set
open Filter

noncomputable section
set_option autoImplicit false

/-- The unmodified onset kernel in co-moving ingoing-cap coordinates. -/
def pulseLayerKernel (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) : ℂ :=
  onsetDirichletKernel q branch amp (v - x + h) (x - z) h x (x - z) X k

/-- The literal direct face of the co-moving kernel.  This definition retains
the full angular and native source corrections; it is not a scalar proxy for
the response. -/
def pulseLayerDirectKernel (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) : ℂ :=
  ((if |z| ≤ h then
      fullSourceOnsetPulse q branch amp (v - x + h) (x - z)
        ![X, Real.exp k] else 0) +
    onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
      fullAngularCorrection q branch h x (x - z) X k +
    onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
      nativeAngularCorrection q h x (x - z) X k) / 2

/-- The literal reflected face of the co-moving kernel.  It stays explicit
until an independent noncompact domination theorem has been proved. -/
def pulseLayerImageKernel (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) : ℂ :=
  ((if |2 * x - z| ≤ h then
      fullSourceOnsetPulse q branch amp (v - x + h) (x - z)
        ![X, Real.exp k] else 0) +
    onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
      fullAngularCorrection q branch h x (-(x - z)) X k +
    onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
      nativeAngularCorrection q h x (-(x - z)) X k) / 2

/-- The direct face in its undecomposed, actual circular form.  This is the
object for the cap-limit analysis; the Goursat expansion above is retained
only to expose its literal source and correction content. -/
def pulseLayerDirectCircleKernel (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) : ℂ :=
  (if |z| ≤ h then
      onsetAngularMean q branch amp (v - x + h) (x - z)
        (Real.arcosh (invariant h x (x - z))) X k else 0) / 2

/-- The reflected face in its undecomposed, actual circular form. -/
def pulseLayerImageCircleKernel (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) : ℂ :=
  (if |2 * x - z| ≤ h then
      onsetAngularMean q branch amp (v - x + h) (x - z)
        (Real.arcosh (invariant h x (-(x - z)))) X k else 0) / 2

/-- Fixed original clock read by the direct co-moving pulse layer. -/
def pulseLayerClock (q : XiZeroCopy) (branch : Bool) (u : ℝ) : ℂ :=
  timeOnsetFirst (2 * physicalRate q branch) u -
    2 * physicalRate q branch * timeOnset (2 * physicalRate q branch) u

/-- The direct layer clock is precisely the derivative of the fixed original
transition profile times its unchanged physical frequency. -/
theorem pulseLayerClock_eq (q : XiZeroCopy) (branch : Bool) (u : ℝ) :
    pulseLayerClock q branch u =
      ((deriv Real.smoothTransition u : ℝ) : ℂ) *
        Complex.exp (2 * physicalRate q branch * (u : ℂ)) := by
  unfold pulseLayerClock timeOnsetFirst timeOnset
  ring

/-- Fixed-clock localization: outside its original transition strip the
co-moving pulse layer is identically zero. -/
theorem pulseLayerClock_zero_outside (q : XiZeroCopy) (branch : Bool) (u : ℝ)
    (hu : u ∉ Set.Icc (0 : ℝ) 1) :
    pulseLayerClock q branch u = 0 := by
  rw [pulseLayerClock_eq,
    GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem hu]
  simp

/-- Compact original-clock bound used by the literal normal-layer envelope. -/
private theorem pulseLayerClock_continuous (q : XiZeroCopy) (branch : Bool) :
    Continuous (pulseLayerClock q branch) := by
  have hderiv : Continuous (fun u : ℝ => (deriv Real.smoothTransition u : ℂ)) :=
    Complex.continuous_ofReal.comp
      GaloisForLFunctions.HTGeometry.continuous_deriv_smoothTransition
  have harg : Continuous (fun u : ℝ =>
      2 * physicalRate q branch * (u : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  rw [show pulseLayerClock q branch = fun u : ℝ =>
      ((deriv Real.smoothTransition u : ℝ) : ℂ) *
        Complex.exp (2 * physicalRate q branch * (u : ℂ)) by
      funext u
      exact pulseLayerClock_eq q branch u]
  exact hderiv.mul (Complex.continuous_exp.comp harg)

private theorem pulseLayerClock_bounded (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 →
      ‖pulseLayerClock q branch u‖ ≤ C := by
  have hclock : Continuous (pulseLayerClock q branch) :=
    pulseLayerClock_continuous q branch
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hclock.norm.continuousOn
  let C := max A 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro u hu
  exact (hA u hu).trans (le_max_left _ _)

private theorem pulseLayer_sourceSeedSecond_continuous (s w a T lam : ℂ) :
    Continuous (sourceSeedFieldSecond s w a T lam) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hA := (sourceAmplitude_hasDerivAt s w a T t).continuousAt
  have hU := ((radialUnit_hasDerivAt t).ofReal_comp).continuousAt
  unfold sourceSeedFieldSecond
  fun_prop

private theorem pulseLayer_radialLiftSecond_continuous (s w a T : ℂ) :
    Continuous (radialLiftSecond s w a T) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hA := (sourceAmplitude_hasDerivAt s w a T t).continuousAt
  have hU := ((radialUnit_hasDerivAt t).ofReal_comp).continuousAt
  unfold radialLiftSecond
  fun_prop

/-- Both literal onset coefficients factor through the same fixed layer clock. -/
theorem onsetCoefficients_layerClock (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau t : ℝ) :
    onsetResponseCoefficient q branch amp tau t =
      -2 * sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
        (parameter q branch) t * pulseLayerClock q branch (tau + t) ∧
    onsetSourceCoefficient q branch amp tau t =
      parameter q branch * (2 * radialLiftFirst (physicalRate q branch) 0 amp 1 t) *
        pulseLayerClock q branch (tau + t) := by
  constructor <;> unfold onsetResponseCoefficient onsetSourceCoefficient pulseLayerClock
    timeOnsetFirst timeOnset <;> ring

/-- Entire literal co-moving kernel is supported on the fixed original onset
strip. This retains both direct and image channels. -/
theorem pulseLayerKernel_zero_outside (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) (hu : v + h - z ∉ Set.Icc (0 : ℝ) 1) :
    pulseLayerKernel q branch amp v x h z X k = 0 := by
  rw [pulseLayerKernel, onsetDirichletKernel_reconstruction]
  obtain ⟨hresponse, hsource⟩ :=
    onsetCoefficients_layerClock q branch amp (v - x + h) (x - z)
  have hclock : (v - x + h) + (x - z) = v + h - z := by ring
  rw [hresponse, hsource, hclock, pulseLayerClock_zero_outside q branch _ hu]
  ring

/-- Fixed-clock localization holds facewise for the literal direct circle
face, not merely after direct-minus-image cancellation. -/
theorem pulseLayerDirectCircleKernel_zero_outside (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) (hu : v + h - z ∉ Set.Icc (0 : ℝ) 1) :
    pulseLayerDirectCircleKernel q branch amp v x h z X k = 0 := by
  obtain ⟨hresponse, hsource⟩ :=
    onsetCoefficients_layerClock q branch amp (v - x + h) (x - z)
  have hclock : (v - x + h) + (x - z) = v + h - z := by ring
  unfold pulseLayerDirectCircleKernel
  rw [onsetAngularMean_eq, hresponse, hsource, hclock,
    pulseLayerClock_zero_outside q branch _ hu]
  ring

/-- Fixed-clock localization holds facewise for the literal reflected circle
face as well.  Its escaping geometry is therefore independent of the onset
support statement. -/
theorem pulseLayerImageCircleKernel_zero_outside (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) (hu : v + h - z ∉ Set.Icc (0 : ℝ) 1) :
    pulseLayerImageCircleKernel q branch amp v x h z X k = 0 := by
  obtain ⟨hresponse, hsource⟩ :=
    onsetCoefficients_layerClock q branch amp (v - x + h) (x - z)
  have hclock : (v - x + h) + (x - z) = v + h - z := by ring
  unfold pulseLayerImageCircleKernel
  rw [onsetAngularMean_eq, hresponse, hsource, hclock,
    pulseLayerClock_zero_outside q branch _ hu]
  ring

/-- Exact direct/image Volterra decomposition of the co-moving pulse layer.
The direct cone is independent of cap radius; the image cone is not replaced
by it or discarded. -/
theorem pulseLayerKernel_volterra (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) :
    pulseLayerKernel q branch amp v x h z X k =
      ((if |z| ≤ h then
          fullSourceOnsetPulse q branch amp (v - x + h) (x - z)
            ![X, Real.exp k] else 0) -
        (if |2 * x - z| ≤ h then
          fullSourceOnsetPulse q branch amp (v - x + h) (x - z)
            ![X, Real.exp k] else 0)) / 2 +
      onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
        (fullAngularCorrection q branch h x (x - z) X k -
          fullAngularCorrection q branch h x (-(x - z)) X k) / 2 +
      onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
        (nativeAngularCorrection q h x (x - z) X k -
          nativeAngularCorrection q h x (-(x - z)) X k) / 2 := by
  have hd : |x - (x - z)| = |z| := by
    congr 1
    ring
  have hi : |x + (x - z)| = |2 * x - z| := by
    congr 1
    ring
  simpa only [pulseLayerKernel, hd, hi] using
    onsetDirichletKernel_volterra q branch amp (v - x + h) (x - z) h x (x - z) X k

/-- The full co-moving kernel is literally direct face minus reflected face.
This is an identity of kernels only: it does not distribute the admitted
noncompact action across two as-yet-unadmitted improper integrals. -/
theorem pulseLayerKernel_direct_sub_image (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) :
    pulseLayerKernel q branch amp v x h z X k =
      pulseLayerDirectKernel q branch amp v x h z X k -
        pulseLayerImageKernel q branch amp v x h z X k := by
  rw [pulseLayerKernel_volterra]
  unfold pulseLayerDirectKernel pulseLayerImageKernel
  ring

/-- The original circular realization itself is direct face minus reflected
face in co-moving cap coordinates.  Thus both the source-expanded and the
undecomposed full-circle descriptions retain exactly the same image channel. -/
theorem pulseLayerKernel_circle_direct_sub_image (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) :
    pulseLayerKernel q branch amp v x h z X k =
      pulseLayerDirectCircleKernel q branch amp v x h z X k -
        pulseLayerImageCircleKernel q branch amp v x h z X k := by
  have hd : |x - (x - z)| = |z| := by
    congr 1
    ring
  have hi : |x + (x - z)| = |2 * x - z| := by
    congr 1
    ring
  unfold pulseLayerKernel onsetDirichletKernel pulseLayerDirectCircleKernel
    pulseLayerImageCircleKernel
  rw [hd, hi]
  ring

/-- Exact reflected-affine transport from the original inward source ray to
the literal co-moving ray.  It is stated locally to the pulse realization so
the proof chain exposes the orientation and moving endpoint rather than
importing an unrelated integral normal form. -/
private theorem setIntegral_Iio_reflect_sub (f : ℝ → ℂ) (x : ℝ) :
    (∫ y in Set.Iio (0 : ℝ), f y) = ∫ z in Set.Ioi x, f (x - z) := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding f (Set.Iio (0 : ℝ))
  have hreflect : (∫ y in Set.Iio (0 : ℝ), f y) =
      ∫ y in Set.Ioi (0 : ℝ), f (-y) := by
    simpa [show (fun y : ℝ => -y) ⁻¹' (Set.Iio (0 : ℝ)) = Set.Ioi (0 : ℝ) by
      ext y
      simp] using hneg.symm
  have hshift : (∫ y in Set.Ioi (0 : ℝ), f (-y)) =
      ∫ z in Set.Ioi x, f (x - z) := by
    have hmp : MeasurePreserving (fun y : ℝ => y + x) volume volume :=
      measurePreserving_add_right volume x
    have hemb : MeasurableEmbedding (fun y : ℝ => y + x) :=
      measurableEmbedding_addRight x
    have hpre : (fun y : ℝ => y + x) ⁻¹' (Set.Ioi x) = Set.Ioi (0 : ℝ) := by
      ext y
      simp [sub_lt_iff_lt_add]
    have h := hmp.setIntegral_preimage_emb hemb (fun z : ℝ => f (x - z)) (Set.Ioi x)
    rw [hpre] at h
    have hcongr : (∫ y in Set.Ioi (0 : ℝ), f (-y)) =
        ∫ y in Set.Ioi (0 : ℝ), f (x - (y + x)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      congr 1
      ring
    rw [hcongr]
    exact h
  exact hreflect.trans hshift

/-- Exact reflected-affine transport from a source ray to an original-clock
ray.  The endpoint is displayed, because its eventual disappearance for the
direct face must be proved from support rather than silently replaced. -/
private theorem setIntegral_Ioi_reflect_shift (f : ℝ → ℂ) (x w : ℝ) :
    (∫ z in Set.Ioi x, f z) = ∫ u in Set.Iio (w - x), f (w - u) := by
  have hreflect := setIntegral_Iio_reflect_sub (fun y : ℝ => f (x - y)) x
  have hreflect' : (∫ z in Set.Ioi x, f z) =
      ∫ y in Set.Iio (0 : ℝ), f (x - y) := by
    calc
      (∫ z in Set.Ioi x, f z) = ∫ z in Set.Ioi x, f (x - (x - z)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
        congr 1
        ring
      _ = ∫ y in Set.Iio (0 : ℝ), f (x - y) := hreflect.symm
  have hshift : (∫ u in Set.Iio (w - x), f (w - u)) =
      ∫ y in Set.Iio (0 : ℝ), f (x - y) := by
    have hmp : MeasurePreserving (fun u : ℝ => u + (x - w)) volume volume :=
      measurePreserving_add_right volume (x - w)
    have hemb : MeasurableEmbedding (fun u : ℝ => u + (x - w)) :=
      measurableEmbedding_addRight (x - w)
    have hpre : (fun u : ℝ => u + (x - w)) ⁻¹' (Set.Iio (0 : ℝ)) =
        Set.Iio (w - x) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Iio]
      constructor <;> intro hu <;> linarith
    have h := hmp.setIntegral_preimage_emb hemb (fun y : ℝ => f (x - y))
      (Set.Iio (0 : ℝ))
    rw [hpre] at h
    have hcongr : (∫ u in Set.Iio (w - x), f (w - u)) =
        ∫ u in Set.Iio (w - x), f (x - (u + (x - w))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Iio (fun u _ => ?_)
      congr 1
      ring
    exact hcongr.trans h
  exact hreflect'.trans hshift.symm

/-- **Literal cyclic Peierls realization on the ingoing cap.**  The admitted
future pulse action is exactly the original direct-minus-image kernel on the
moving source ray `z > x`.  No cap limit, direct/image separation, or source
replacement enters this equality. -/
theorem response_ingoing_pulseLayer (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x X k : ℝ) :
    response q branch amp (v - x) x X k =
      ∫ h in Set.Ioi (0 : ℝ), ∫ z in Set.Ioi x,
        pulseLayerKernel q branch amp v x h z X k := by
  rw [response_fubini]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun h _ => ?_)
  have htransport := setIntegral_Iio_reflect_sub
    (fun y : ℝ => onsetDirichletKernel q branch amp (v - x + h) y h x y X k) x
  simpa only [pulseLayerKernel] using htransport

/-- Once the cap target has passed below `v-1`, the whole fixed onset strip
lies strictly inside the transported source ray for every positive delay.  It
is the exact statement that removes the moving lower endpoint from the direct
face, not an asymptotic replacement of that endpoint. -/
theorem directClockStrip_inside_sourceRay (v x h u : ℝ)
    (hx : x < v - 1) (hh : 0 < h) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    x < v + h - u := by
  linarith [hu.2]

/-- **Fixed-clock direct-face realization.**  Below the explicit cap
threshold `x < v-1`, the direct face of the exact pulse action is an integral
over the fixed original onset interval.  This is a literal equality of
improper integrals; no dominance or limiting interchange is used. -/
theorem directCircleKernel_inner_integral_fixedClock (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h X k : ℝ) (hx : x < v - 1) (hh : 0 < h) :
    (∫ z in Set.Ioi x, pulseLayerDirectCircleKernel q branch amp v x h z X k) =
      ∫ u in Set.Icc (0 : ℝ) 1,
        pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k := by
  calc
    (∫ z in Set.Ioi x, pulseLayerDirectCircleKernel q branch amp v x h z X k) =
        ∫ u in Set.Iio (v + h - x),
          pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k :=
      setIntegral_Ioi_reflect_shift
        (fun z : ℝ => pulseLayerDirectCircleKernel q branch amp v x h z X k) x (v + h)
    _ = ∫ u in Set.Icc (0 : ℝ) 1,
        pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k := by
      refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        measurableSet_Iio.nullMeasurableSet ?_ ?_
      · intro u hu
        exact directClockStrip_inside_sourceRay v x h u hx hh hu
      · filter_upwards with u hu
        apply pulseLayerDirectCircleKernel_zero_outside q branch amp v x h (v + h - u) X k
        have hclock : v + h - (v + h - u) = u := by ring
        rw [hclock]
        exact hu.2

/-- Every term in the literal direct face has the same fixed direct cone.
This is stronger than pointwise cancellation of the full kernel and is the
geometric input for a future direct-layer domination argument. -/
theorem pulseLayerDirectKernel_zero_of_not_directCone (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) (hz : ¬ |z| ≤ h) :
    pulseLayerDirectKernel q branch amp v x h z X k = 0 := by
  have hdirect : ¬ |x - (x - z)| ≤ h := by
    simpa only [sub_sub_cancel_left] using hz
  unfold pulseLayerDirectKernel
  rw [if_neg hz, fullAngularCorrection, if_neg hdirect,
    nativeAngularCorrection, if_neg hdirect]
  ring

/-- Every term in the literal reflected face has the same escaping image
cone.  This does not claim a noncompact limit; it identifies exactly which
face still needs a global majorant. -/
theorem pulseLayerImageKernel_zero_of_not_imageCone (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) (hz : ¬ |2 * x - z| ≤ h) :
    pulseLayerImageKernel q branch amp v x h z X k = 0 := by
  have himage : ¬ |x - (-(x - z))| ≤ h := by
    intro hcone
    apply hz
    have heq : |x - (-(x - z))| = |2 * x - z| := by
      congr 1
      ring
    rwa [heq] at hcone
  unfold pulseLayerImageKernel
  rw [if_neg hz, fullAngularCorrection, if_neg himage,
    nativeAngularCorrection, if_neg himage]
  ring

/-- The undecomposed direct circle face has no support beyond the fixed direct
cone. -/
theorem pulseLayerDirectCircleKernel_zero_of_not_directCone (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x h z X k : ℝ) (hz : ¬ |z| ≤ h) :
    pulseLayerDirectCircleKernel q branch amp v x h z X k = 0 := by
  unfold pulseLayerDirectCircleKernel
  rw [if_neg hz]
  ring

/-- The retained original onset strip is disjoint from the literal direct cone
after its unit transition.  This is a finite-depth identity: no cap scaling,
dominated convergence, or normal derivative is involved. -/
theorem pulseLayerDirectCircleKernel_fixedClock_eq_zero_of_one_lt
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x h u X k : ℝ)
    (hv : 1 < v) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k = 0 := by
  apply pulseLayerDirectCircleKernel_zero_of_not_directCone
  intro hcone
  have hright := (abs_le.mp hcone).2
  linarith [hu.2]

/-- The undecomposed reflected circle face has no support beyond its literal
image cone. -/
theorem pulseLayerImageCircleKernel_zero_of_not_imageCone (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x h z X k : ℝ) (hz : ¬ |2 * x - z| ≤ h) :
    pulseLayerImageCircleKernel q branch amp v x h z X k = 0 := by
  unfold pulseLayerImageCircleKernel
  rw [if_neg hz]
  ring

/-- A nonzero direct face is confined simultaneously to its literal direct
cone and to the unchanged original onset strip. -/
theorem pulseLayerDirectCircleKernel_nonzero_support (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ)
    (hK : pulseLayerDirectCircleKernel q branch amp v x h z X k ≠ 0) :
    |z| ≤ h ∧ v + h - z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · by_contra hz
    exact hK (pulseLayerDirectCircleKernel_zero_of_not_directCone
      q branch amp v x h z X k hz)
  · by_contra hu
    exact hK (pulseLayerDirectCircleKernel_zero_outside
      q branch amp v x h z X k hu)

/-- On the nonzero direct layer, the source coordinate is locked to the
delay up to the fixed onset-width one.  This produces the tail factor needed
for a cap-scale majorant; it does not yet assert that majorant. -/
theorem pulseLayerDirectCircleKernel_nonzero_geometry (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ)
    (hK : pulseLayerDirectCircleKernel q branch amp v x h z X k ≠ 0) :
    h + v - 1 ≤ z ∧ z ≤ h := by
  obtain ⟨hcone, hclock⟩ := pulseLayerDirectCircleKernel_nonzero_support
    q branch amp v x h z X k hK
  constructor
  · linarith [hclock.2]
  · exact (abs_le.mp hcone).2

/-- A nonzero reflected face would have to lie in both the literal image cone
and the unchanged original onset strip. -/
theorem pulseLayerImageCircleKernel_nonzero_support (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ)
    (hK : pulseLayerImageCircleKernel q branch amp v x h z X k ≠ 0) :
    |2 * x - z| ≤ h ∧ v + h - z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · by_contra hz
    exact hK (pulseLayerImageCircleKernel_zero_of_not_imageCone
      q branch amp v x h z X k hz)
  · by_contra hu
    exact hK (pulseLayerImageCircleKernel_zero_outside
      q branch amp v x h z X k hu)

/-- **Uniform reflected-face elimination.**  Below this finite ingoing cap
threshold, the literal image cone and fixed original onset strip are
disjoint for every delay and source point.  This is stronger than a pointwise
limit and removes the image face from the actual cyclic Peierls kernel. -/
theorem pulseLayerImageCircleKernel_eq_zero_below_cap (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) (hx : x < (v - 1) / 2) :
    pulseLayerImageCircleKernel q branch amp v x h z X k = 0 := by
  by_contra hK
  obtain ⟨hcone, hclock⟩ := pulseLayerImageCircleKernel_nonzero_support
    q branch amp v x h z X k hK
  have hleft := (abs_le.mp hcone).1
  linarith [hclock.2]

/-- At the same finite cap threshold, the actual full original circle kernel
is exactly its literal direct face.  No image majorant or dominated
convergence argument remains. -/
theorem pulseLayerKernel_eq_directCircle_below_cap (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) (hx : x < (v - 1) / 2) :
    pulseLayerKernel q branch amp v x h z X k =
      pulseLayerDirectCircleKernel q branch amp v x h z X k := by
  rw [pulseLayerKernel_circle_direct_sub_image,
    pulseLayerImageCircleKernel_eq_zero_below_cap q branch amp v x h z X k hx]
  ring

/-- **Literal cyclic Peierls cap realization.**  At a finite ingoing cap
depth, the complete admitted future pulse action equals the direct full-circle
face integrated over its fixed original onset interval.  The equality retains
the exact angular field, native source channel, and source measure; it kills
the reflected face by a proved support incompatibility. -/
theorem response_ingoing_fixedClock_directCircle (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x X k : ℝ) (hsource : x < v - 1)
    (himage : x < (v - 1) / 2) :
    response q branch amp (v - x) x X k =
      ∫ h in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1,
        pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k := by
  calc
    response q branch amp (v - x) x X k =
        ∫ h in Set.Ioi (0 : ℝ), ∫ z in Set.Ioi x,
          pulseLayerKernel q branch amp v x h z X k :=
      response_ingoing_pulseLayer q branch amp v x X k
    _ = ∫ h in Set.Ioi (0 : ℝ), ∫ z in Set.Ioi x,
          pulseLayerDirectCircleKernel q branch amp v x h z X k := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun h _ => ?_)
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      exact pulseLayerKernel_eq_directCircle_below_cap q branch amp v x h z X k himage
    _ = ∫ h in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1,
          pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun h hh => ?_)
      exact directCircleKernel_inner_integral_fixedClock q branch amp v x h X k hsource hh

/-- **Corrected-future literal cyclic Peierls realization.**  The actual
corrected future, after only its forced bulk contact is removed, is exactly
the fixed-clock direct pulse action plus the literal combined cap at every
finite ingoing depth satisfying the displayed geometric thresholds. -/
theorem correctedFutureCapResidual_ingoing_fixedClock_directCircle
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) (hx : x ≤ 0)
    (hsource : x < v - 1) (himage : x < (v - 1) / 2) :
    correctedFutureCapResidual q branch amp (v - x) x X k =
      (∫ h in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1,
        pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k) +
        (seedCapField q branch amp (v - x) x X k -
          parameter q branch * capBoundaryField q branch amp (v - x) x X k) := by
  rw [correctedFutureCapResidual_ingoing_eq q branch amp v x X k hx,
    response_ingoing_fixedClock_directCircle q branch amp v x X k hsource himage]

/-- Below the reflected-face threshold, the literal direct circle face is not
an auxiliary decomposition term: after the fixed-clock substitution it is
exactly the corpus's admitted original future density. -/
theorem pulseLayerDirectCircleKernel_eq_density_below_cap (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x h u X k : ℝ) (himage : x < (v - 1) / 2) :
    pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k =
      density q branch amp (v - x) x X k (h, x - v - h + u) := by
  rw [← pulseLayerKernel_eq_directCircle_below_cap q branch amp v x h (v + h - u)
    X k himage]
  unfold pulseLayerKernel density
  congr 4 <;> ring

/-- The literal full-circle direct face is measurable after the fixed-clock
change of variables.  The proof retains the causal gate and replaces
`arcosh invariant` by its globally continuous `arcosh (max 1 invariant)`
extension only on that gate, where the two are exactly equal.  This supplies
the measurability input for the direct action DCT without introducing a
surrogate density. -/
theorem pulseLayerDirectCircleKernel_fixedClock_measurable (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x X k : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      pulseLayerDirectCircleKernel q branch amp v x p.1 (v + p.1 - p.2) X k) := by
  let z : ℝ × ℝ → ℝ := fun p => v + p.1 - p.2
  let y : ℝ × ℝ → ℝ := fun p => x - z p
  have hz : Continuous z := by
    dsimp only [z]
    fun_prop
  have hy : Continuous y := by
    dsimp only [y]
    exact continuous_const.sub hz
  have hcone : MeasurableSet {p : ℝ × ℝ | |z p| ≤ p.1} :=
    (isClosed_le hz.abs continuous_fst).measurableSet
  have hinvariant : Continuous (fun p : ℝ × ℝ => invariant p.1 x (y p)) := by
    unfold invariant
    exact ((Real.continuous_cosh.comp continuous_fst).add
      ((Real.continuous_sinh.comp hy).const_mul (Real.sinh x))).div
      ((Real.continuous_cosh.comp hy).const_mul (Real.cosh x))
      (fun p => mul_ne_zero (Real.cosh_pos x).ne' (Real.cosh_pos (y p)).ne')
  have hradius : Continuous (fun p : ℝ × ℝ =>
      Real.arcosh (max 1 (invariant p.1 x (y p))) ) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max hinvariant)
      (fun p => le_max_left 1 (invariant p.1 x (y p)))
  have hseed : Continuous (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
      (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (sourceSeedFieldFirst_hasDerivAt (physicalRate q branch) 0 amp 1
        (parameter q branch) t).continuousAt)
  have hlift : Continuous (radialLiftFirst (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (radialLiftFirst_hasDerivAt (physicalRate q branch) 0 amp 1 t).continuousAt)
  have hclockBase : Continuous (pulseLayerClock q branch) := by
    unfold pulseLayerClock
    have h0 : Continuous (timeOnset (2 * physicalRate q branch)) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (timeOnset_hasDerivAt (2 * physicalRate q branch) t).continuousAt)
    have h1 : Continuous (timeOnsetFirst (2 * physicalRate q branch)) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (timeOnsetFirst_hasDerivAt (2 * physicalRate q branch) t).continuousAt)
    exact h1.sub (h0.const_mul _)
  have hclockArg : Continuous (fun p : ℝ × ℝ => v + p.1 - z p) := by
    exact (continuous_const.add continuous_fst).sub hz
  have hclock : Continuous (fun p : ℝ × ℝ =>
      pulseLayerClock q branch (v + p.1 - z p)) := hclockBase.comp hclockArg
  have hresponse : Continuous (fun p : ℝ × ℝ =>
      -2 * sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
        (parameter q branch) (y p) * pulseLayerClock q branch (v + p.1 - z p)) := by
    exact ((continuous_const.mul (hseed.comp hy)).mul hclock)
  have hsource : Continuous (fun p : ℝ × ℝ =>
      parameter q branch * (2 * radialLiftFirst (physicalRate q branch) 0 amp 1 (y p)) *
        pulseLayerClock q branch (v + p.1 - z p)) := by
    exact ((continuous_const.mul ((hlift.comp hy).const_mul 2)).mul hclock)
  have hangular : Continuous (fun p : ℝ × ℝ =>
      angularMean q branch (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k) :=
    (angularMean_smooth q branch X k).continuous.comp hradius
  have hnative : Continuous (fun p : ℝ × ℝ =>
      D4BMNativeCircle.mean q (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k) :=
    (D4BMNativeCircle.mean_radial_smooth q X k).continuous.comp hradius
  have hvalue : Measurable (fun p : ℝ × ℝ =>
      ((-2 * sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
          (parameter q branch) (y p) * pulseLayerClock q branch (v + p.1 - z p)) *
          angularMean q branch (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k +
        (parameter q branch * (2 * radialLiftFirst (physicalRate q branch) 0 amp 1 (y p)) *
          pulseLayerClock q branch (v + p.1 - z p)) *
          D4BMNativeCircle.mean q (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k) / 2) :=
    ((hresponse.mul hangular).add (hsource.mul hnative)).div_const (2 : ℂ) |>.measurable
  have hite := Measurable.ite hcone hvalue measurable_const
  convert hite using 1
  funext p
  by_cases hp : |z p| ≤ p.1
  · have hcausal : 1 ≤ invariant p.1 x (y p) := by
      apply invariant_causal
      refine ⟨p.1, x, y p, ?_⟩
      dsimp only [y]
      have hxy : x - (x - z p) = z p := by ring
      rwa [hxy]
    have htime : (v - x + p.1) + (x - z p) = v + p.1 - z p := by ring
    unfold pulseLayerDirectCircleKernel
    rw [show v + p.1 - p.2 = z p by rfl, if_pos hp, onsetAngularMean_eq,
      (onsetCoefficients_layerClock q branch amp (v - x + p.1) (x - z p)).1,
      (onsetCoefficients_layerClock q branch amp (v - x + p.1) (x - z p)).2,
      htime, max_eq_right hcausal]
    dsimp only [z, y]
    ring
  · unfold pulseLayerDirectCircleKernel
    rw [show v + p.1 - p.2 = z p by rfl, if_neg hp]
    simp

/-- At every fixed layer point, the literal image cone eventually leaves the
ingoing cap.  This is pointwise geometry only; the noncompact image estimate
still has to supply an integrable majorant. -/
theorem imageCone_eventually_off (h z : ℝ) :
    ∀ᶠ x : ℝ in atBot, ¬ |2 * x - z| ≤ h := by
  filter_upwards [eventually_lt_atBot ((z - h) / 2)] with x hx
  intro hi
  have hleft := (abs_le.mp hi).1
  nlinarith

private theorem capScale_exp_form (x : ℝ) :
    capScale x = 2 * Real.exp (2 * x) / (1 + Real.exp (2 * x)) := by
  have hden : 1 + Real.exp (2 * x) ≠ 0 := ne_of_gt (by positivity)
  rw [eq_div_iff hden]
  have hc : capScale x = 1 - radialUnit x := by
    rw [capScale, radialUnit, ← Real.cosh_add_sinh x]
    field_simp [(Real.cosh_pos x).ne']
    ring
  rw [hc]
  have hh := radialUnit_one_sub x
  nlinarith

private theorem capScale_tendsto_atBot_zero :
    Tendsto capScale atBot (𝓝 (0 : ℝ)) := by
  rw [show capScale = fun x : ℝ =>
      2 * Real.exp (2 * x) / (1 + Real.exp (2 * x)) by
        funext x
        exact capScale_exp_form x]
  have he : Tendsto (fun x : ℝ => Real.exp (2 * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
  simpa only [mul_comm] using (he.const_mul (2 : ℝ)).div
    (tendsto_const_nhds.add he) (by norm_num : (1 : ℝ) ≠ 0)

/-- Exact direct-layer scale identity. -/
theorem pulseLayer_direct_scale_eq (x z : ℝ) :
    (Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ) =
      (Real.exp (-2 * z) : ℂ) * (1 + (Real.exp (2 * x) : ℂ)) / 2 := by
  rw [capScale_exp_form]
  have hx : (Real.exp (2 * x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have he : (Real.exp (2 * (x - z)) : ℂ) =
      (Real.exp (-2 * z) : ℂ) * (Real.exp (2 * x) : ℂ) := by
    push_cast
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  field_simp
  ring

/-- The direct-layer radial factor has a nonzero finite cap-scale limit. -/
theorem pulseLayer_direct_scale_tendsto (z : ℝ) :
    Tendsto (fun x : ℝ => (Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) atBot
      (𝓝 ((Real.exp (-2 * z) : ℂ) / 2)) := by
  rw [show (fun x : ℝ => (Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) =
      fun x : ℝ => (Real.exp (-2 * z) : ℂ) *
        (1 + (Real.exp (2 * x) : ℂ)) / 2 by
        funext x
        exact pulseLayer_direct_scale_eq x z]
  have he : Tendsto (fun x : ℝ => Real.exp (2 * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
  have hec : Tendsto (fun x : ℝ => (Real.exp (2 * x) : ℂ)) atBot (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp he
  have ht := (tendsto_const_nhds.add hec).const_mul
    ((Real.exp (-2 * z) : ℂ) / 2)
  convert ht using 1 <;> ring

/-- The finite-radius correction in the exact direct cap factor never
enlarges that factor on the ingoing half-line.  Together with
`pulseLayer_direct_scale_eq`, this is the uniform radial envelope before the
full direct-face angular estimate is supplied. -/
theorem pulseLayer_direct_scale_correction_le_one (x : ℝ) (hx : x ≤ 0) :
    (1 + Real.exp (2 * x)) / 2 ≤ 1 := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have he : Real.exp (2 * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- Real form of the cap-scale correction used by the admitted-density
majorant. -/
theorem exp_two_div_capScale_eq (x : ℝ) :
    Real.exp (2 * x) / capScale x = (1 + Real.exp (2 * x)) / 2 := by
  rw [capScale_exp_form]
  field_simp
  ring

/-- Uniform cap-scale majorant for remaining direct face. It comes from the
already admitted full density only after finite-depth image elimination proves
that full density is the direct face. -/
theorem pulseLayerDirectCircleKernel_scaled_majorant (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x h u : ℝ, x ≤ 0 → x < v - 1 →
      x < (v - 1) / 2 → 0 < h → u ∈ Set.Icc (0 : ℝ) 1 →
      ‖pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k /
          (capScale x : ℂ)‖ ≤ B * Real.exp ((decayExponent q - 2) * h) := by
  obtain ⟨C, hC, hbound⟩ := density_bound q branch amp X k
  let B := C * Real.exp (-2 * v + (2 - pulseDecayExponent q))
  refine ⟨B, mul_nonneg hC (Real.exp_pos _).le, fun x h u hx0 hsource himage hh hu => ?_⟩
  have hy : x - v - h + u < 0 := by
    linarith [hu.2]
  have hdensity := hbound (v - x) x h (x - v - h + u) hh hy
  have hcap : 0 < capScale x := by
    unfold capScale
    positivity
  have hscale : Real.exp (2 * x) / capScale x ≤ 1 := by
    rw [exp_two_div_capScale_eq]
    exact pulseLayer_direct_scale_correction_le_one x hx0
  have huExp : Real.exp (-2 * v + (2 - pulseDecayExponent q) * u) ≤
      Real.exp (-2 * v + (2 - pulseDecayExponent q)) := by
    apply Real.exp_le_exp.mpr
    have hp : 0 < 2 - pulseDecayExponent q := by
      linarith [(pulseDecayExponent_bounds q).2]
    nlinarith [hu.2]
  have hexp :
      Real.exp (-pulseDecayExponent q * (v - x)) *
        (Real.exp ((decayExponent q - pulseDecayExponent q) * h) *
          Real.exp ((2 - pulseDecayExponent q) * (x - v - h + u))) =
        Real.exp (-2 * v + (2 - pulseDecayExponent q) * u) *
          Real.exp ((decayExponent q - 2) * h) * Real.exp (2 * x) := by
    calc
      _ = Real.exp
          (-pulseDecayExponent q * (v - x) +
            (decayExponent q - pulseDecayExponent q) * h +
            (2 - pulseDecayExponent q) * (x - v - h + u)) := by
          rw [Real.exp_add, Real.exp_add]
          ring
      _ = Real.exp
          ((-2 * v + (2 - pulseDecayExponent q) * u) +
            (decayExponent q - 2) * h + 2 * x) := by
          congr 1
          ring
      _ = Real.exp (-2 * v + (2 - pulseDecayExponent q) * u) *
          Real.exp ((decayExponent q - 2) * h) * Real.exp (2 * x) := by
          rw [Real.exp_add, Real.exp_add]
          ring
  rw [pulseLayerDirectCircleKernel_eq_density_below_cap q branch amp v x h u X k himage,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcap]
  have hdiv := div_le_div_of_nonneg_right hdensity hcap.le
  calc
    ‖density q branch amp (v - x) x X k (h, x - v - h + u)‖ / capScale x ≤
        (C * Real.exp (-pulseDecayExponent q * (v - x)) *
          (Real.exp ((decayExponent q - pulseDecayExponent q) * h) *
            Real.exp ((2 - pulseDecayExponent q) * (x - v - h + u)))) / capScale x := hdiv
    _ = C * Real.exp (-2 * v + (2 - pulseDecayExponent q) * u) *
          Real.exp ((decayExponent q - 2) * h) *
          (Real.exp (2 * x) / capScale x) := by
          rw [hexp]
          field_simp [hcap.ne']
          ring
    _ ≤ C * Real.exp (-2 * v + (2 - pulseDecayExponent q)) *
          Real.exp ((decayExponent q - 2) * h) := by
          have h1 :
              (C * Real.exp ((decayExponent q - 2) * h) *
                (Real.exp (2 * x) / capScale x)) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q) * u) ≤
              (C * Real.exp ((decayExponent q - 2) * h) *
                (Real.exp (2 * x) / capScale x)) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q)) :=
            mul_le_mul_of_nonneg_left huExp (by positivity)
          have h2 :
              (C * Real.exp ((decayExponent q - 2) * h) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q))) *
                (Real.exp (2 * x) / capScale x) ≤
              (C * Real.exp ((decayExponent q - 2) * h) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q))) * 1 :=
            mul_le_mul_of_nonneg_left hscale (by positivity)
          calc
            _ = (C * Real.exp ((decayExponent q - 2) * h) *
              (Real.exp (2 * x) / capScale x)) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q) * u) := by ring
            _ ≤ (C * Real.exp ((decayExponent q - 2) * h) *
              (Real.exp (2 * x) / capScale x)) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q)) := h1
            _ = (C * Real.exp ((decayExponent q - 2) * h) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q))) *
                (Real.exp (2 * x) / capScale x) := by ring
            _ ≤ (C * Real.exp ((decayExponent q - 2) * h) *
                Real.exp (-2 * v + (2 - pulseDecayExponent q))) * 1 := h2
            _ = _ := by ring
    _ = B * Real.exp ((decayExponent q - 2) * h) := by
      dsimp only [B]
      ring

/-- The fixed-clock direct-layer envelope is genuinely integrable on its
two-dimensional action domain.  This is the global tail condition needed to
pass the literal cap coefficient through the pulse action; it uses only the
strict corpus gap `decayExponent q < 2`, not a truncation of the delay ray. -/
theorem pulseLayerDirectCapMajorant_integrable (q : XiZeroCopy) (B : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ =>
      B * Real.exp ((decayExponent q - 2) * p.1))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hh := integrableOn_exp_mul_Ioi
    (show decayExponent q - 2 < 0 by linarith [(decayExponent_bounds q).2]) 0
  have hu : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (0 : ℝ) 1) := by
    rw [integrableOn_const_iff]
    right
    rw [Real.volume_Icc]
    norm_num
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa only [mul_one] using (hh.mul_prod hu).const_mul B

/-- The actual compact radial coordinate tends to its physical horizon value
one along the incoming source ray.  This is proved through the corpus's exact
compact coordinate, not by substituting a formal endpoint. -/
theorem radialUnit_tendsto_atBot_one :
    Tendsto radialUnit atBot (𝓝 (1 : ℝ)) := by
  rw [show radialUnit = fun y : ℝ => compactUnit (Real.exp (2 * y)) by
    funext y
    exact radialUnit_compact y]
  have he : Tendsto (fun y : ℝ => Real.exp (2 * y)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
  have hc : ContinuousAt compactUnit (0 : ℝ) := by
    unfold compactUnit
    fun_prop
  simpa [compactUnit] using hc.tendsto.comp he

/-- The same endpoint law holds on every fixed co-moving source ray. -/
theorem radialUnit_shift_tendsto_atBot_one (z : ℝ) :
    Tendsto (fun x : ℝ => radialUnit (x - z)) atBot (𝓝 (1 : ℝ)) := by
  rw [show (fun x : ℝ => radialUnit (x - z)) =
      fun x : ℝ => compactUnit (Real.exp (2 * (x - z))) by
        funext x
        exact radialUnit_compact (x - z)]
  have he : Tendsto (fun x : ℝ => Real.exp (2 * (x - z))) atBot (𝓝 0) := by
    rw [show (fun x : ℝ => Real.exp (2 * (x - z))) =
        fun x : ℝ => Real.exp (-2 * z) * Real.exp (2 * x) by
          funext x
          rw [← Real.exp_add]
          congr 1
          ring]
    have hx : Tendsto (fun x : ℝ => Real.exp (2 * x)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
    simpa using hx.const_mul (Real.exp (-2 * z))
  have hc : ContinuousAt compactUnit (0 : ℝ) := by
    unfold compactUnit
    fun_prop
  simpa [compactUnit] using hc.tendsto.comp he

/-- Along every fixed co-moving direct point, the literal hyperbolic causal
invariant reaches its true radius-zero value.  The proof uses the exact
two-radial compact invariant from the corpus, retaining both target and
source compact coordinates. -/
theorem pulseLayer_directInvariant_tendsto (h z : ℝ) :
    Tendsto (fun x : ℝ => invariant h x (x - z)) atBot (𝓝 (1 : ℝ)) := by
  have hform : (fun x : ℝ => invariant h x (x - z)) =
      fun x : ℝ => compactInvariant false (Real.exp (h + z))
        (Real.exp (2 * x)) (Real.exp (2 * (x - z))) := by
    funext x
    convert invariant_compact false (h + z) x (x - z) using 1 <;> ring
  rw [hform]
  unfold compactInvariant
  have hrho : Tendsto (fun x : ℝ => Real.exp (2 * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
  have hzeta : Tendsto (fun x : ℝ => Real.exp (2 * (x - z))) atBot (𝓝 0) := by
    rw [show (fun x : ℝ => Real.exp (2 * (x - z))) =
        fun x : ℝ => Real.exp (-2 * z) * Real.exp (2 * x) by
          funext x
          rw [← Real.exp_add]
          congr 1
          ring]
    simpa using hrho.const_mul (Real.exp (-2 * z))
  have hratio : Tendsto (fun x : ℝ => Real.exp (2 * x) / Real.exp (h + z))
      atBot (𝓝 0) := by
    have h := hrho.div (tendsto_const_nhds (x := Real.exp (h + z)))
      (Real.exp_pos _).ne'
    simpa using h
  have hleft : Tendsto (fun x : ℝ => Real.exp (h + z) - Real.exp (2 * x))
      atBot (𝓝 (Real.exp (h + z))) := by
    simpa using (tendsto_const_nhds.sub hrho)
  have hright : Tendsto (fun x : ℝ => Real.exp (2 * (x - z)) -
      Real.exp (2 * x) / Real.exp (h + z)) atBot (𝓝 0) := by
    simpa using hzeta.sub hratio
  have hnum : Tendsto (fun x : ℝ => 2 *
      ((Real.exp (h + z) - Real.exp (2 * x)) *
        (Real.exp (2 * (x - z)) - Real.exp (2 * x) / Real.exp (h + z))))
      atBot (𝓝 0) := by
    simpa using (hleft.mul hright).const_mul (2 : ℝ)
  have hden : Tendsto (fun x : ℝ => (1 + Real.exp (2 * x)) *
      (1 + Real.exp (2 * (x - z)))) atBot (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hrho).mul (tendsto_const_nhds.add hzeta)
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simpa using tendsto_const_nhds.add hquot

/-- Exact first cap factor of the literal direct causal invariant.  It is the
normal-geometry input absent from a value-only layer limit: after the original
cap scale is extracted, the remaining factor has a finite, source-dependent
limit.  No radial or angular endpoint is inserted in this identity. -/
theorem pulseLayer_directInvariant_sub_one_div_capScale_eq (h x z : ℝ) :
    (invariant h x (x - z) - 1) / capScale x =
      (Real.exp (h + z) - 1) *
        (Real.exp (-2 * z) - Real.exp (-(h + z))) /
          (1 + Real.exp (2 * (x - z))) := by
  have hform : invariant h x (x - z) =
      compactInvariant false (Real.exp (h + z)) (Real.exp (2 * x))
        (Real.exp (2 * (x - z))) := by
    convert invariant_compact false (h + z) x (x - z) using 1 <;> ring
  have hshift : Real.exp (2 * (x - z)) =
      Real.exp (2 * x) * Real.exp (-2 * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrho : Real.exp (2 * x) ≠ 0 := (Real.exp_pos _).ne'
  have hE : Real.exp (h + z) ≠ 0 := (Real.exp_pos _).ne'
  have hdenrho : 1 + Real.exp (2 * x) ≠ 0 := ne_of_gt (by positivity)
  have hdenz : 1 + Real.exp (2 * (x - z)) ≠ 0 := ne_of_gt (by positivity)
  rw [hform, capScale_exp_form, hshift, Real.exp_neg]
  unfold compactInvariant
  simp only [Bool.false_eq_true, ↓reduceIte]
  field_simp [hrho, hE, hdenrho, hdenz]
  ring

/-- The exact direct invariant has a finite first cap coefficient.  This is
the coefficient controlling the even circle-radius correction in the normal
layer; it is retained for the differentiated action rather than discarded
with the value-level limit. -/
theorem pulseLayer_directInvariant_sub_one_div_capScale_tendsto (h z : ℝ) :
    Tendsto (fun x : ℝ =>
      (invariant h x (x - z) - 1) / capScale x) atBot
      (𝓝 ((Real.exp (h + z) - 1) *
        (Real.exp (-2 * z) - Real.exp (-(h + z))))) := by
  rw [show (fun x : ℝ =>
      (invariant h x (x - z) - 1) / capScale x) =
      fun x : ℝ => (Real.exp (h + z) - 1) *
        (Real.exp (-2 * z) - Real.exp (-(h + z))) /
          (1 + Real.exp (2 * (x - z))) by
        funext x
        exact pulseLayer_directInvariant_sub_one_div_capScale_eq h x z]
  have he : Tendsto (fun x : ℝ => Real.exp (2 * (x - z))) atBot (𝓝 0) := by
    rw [show (fun x : ℝ => Real.exp (2 * (x - z))) =
        fun x : ℝ => Real.exp (-2 * z) * Real.exp (2 * x) by
          funext x
          rw [← Real.exp_add]
          congr 1
          ring]
    have hx : Tendsto (fun x : ℝ => Real.exp (2 * x)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
    simpa using hx.const_mul (Real.exp (-2 * z))
  have hden : Tendsto (fun x : ℝ => 1 + Real.exp (2 * (x - z))) atBot (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add he
  simpa using (tendsto_const_nhds.div hden (by norm_num : (1 : ℝ) ≠ 0))

/-- Exact hyperbolic distance from the characteristic surface on the moving
direct source ray.  This exposes the strict interior of the literal cone,
rather than extending the angular kernel through an unphysical `I < 1`
region. -/
theorem pulseLayer_directInvariant_sub_one_hyperbolic (h x z : ℝ) :
    invariant h x (x - z) - 1 =
      (Real.cosh h - Real.cosh z) /
        (Real.cosh x * Real.cosh (x - z)) := by
  have hx : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hy : Real.cosh (x - z) ≠ 0 := (Real.cosh_pos (x - z)).ne'
  have hcosh : Real.cosh z =
      Real.cosh x * Real.cosh (x - z) - Real.sinh x * Real.sinh (x - z) := by
    convert Real.cosh_sub x (x - z) using 1 <;> ring
  unfold invariant
  field_simp [hx, hy]
  linear_combination hcosh

/-- A strict direct cone point remains strictly within the physical
characteristic chart for every finite cap depth.  This is the domain fact
needed to differentiate the literal `arcosh` circle kernels themselves. -/
theorem pulseLayer_directInvariant_one_lt (h x z : ℝ) (hz : |z| < h) :
    1 < invariant h x (x - z) := by
  have hh : 0 < h := lt_of_le_of_lt (abs_nonneg z) hz
  have hcoshAbs : Real.cosh |z| < Real.cosh h := by
    by_contra hbad
    have hle : Real.cosh h ≤ Real.cosh |z| := le_of_not_gt hbad
    have habs := Real.cosh_le_cosh.mp hle
    have hle' : h ≤ |z| := by
      simpa only [abs_of_pos hh, abs_abs] using habs
    linarith
  have hcosh : Real.cosh z < Real.cosh h := by
    rcases le_total 0 z with hz0 | hz0
    · simpa only [abs_of_nonneg hz0] using hcoshAbs
    · rw [abs_of_nonpos hz0, Real.cosh_neg] at hcoshAbs
      exact hcoshAbs
  apply sub_pos.mp
  rw [pulseLayer_directInvariant_sub_one_hyperbolic]
  exact div_pos (sub_pos.mpr hcosh)
    (mul_pos (Real.cosh_pos x) (Real.cosh_pos (x - z)))

/-- At a literal direct-cone boundary the moving causal invariant is
identically characteristic, at every cap depth. -/
theorem pulseLayer_directInvariant_eq_one_of_abs_eq (h x z : ℝ) (hz : |z| = h) :
    invariant h x (x - z) = 1 := by
  have hcosh : Real.cosh h = Real.cosh z := by
    rw [← hz]
    rcases le_total 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0]
    · rw [abs_of_nonpos hz0, Real.cosh_neg]
  have hsub := pulseLayer_directInvariant_sub_one_hyperbolic h x z
  rw [hcosh] at hsub
  norm_num at hsub
  linarith

/-- A smooth odd radial numerator has a finite characteristic quotient by
`sinh`.  This is the exact regularity mechanism for literal circle kernels;
it does not extend `arcosh` below its physical chart. -/
private theorem pulseLayer_sinh_ratio_tendsto {f : ℝ → ℂ} {a : ℂ}
    (hf : HasDerivAt f a 0) (h0 : f 0 = 0) :
    Tendsto (fun d => f d / (Real.sinh d : ℂ)) (𝓝[≠] 0) (𝓝 a) := by
  have h1 : Tendsto (fun d : ℝ => f d / (d : ℂ)) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [zero_add, h0, sub_zero, Complex.real_smul, Complex.ofReal_inv,
      div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero
  have h2 : Tendsto (fun d : ℝ => (Real.sinh d : ℂ) / (d : ℂ))
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have h := ((Real.hasDerivAt_sinh 0).ofReal_comp).tendsto_slope_zero
    simpa only [Real.cosh_zero, Real.sinh_zero, Complex.ofReal_one, Complex.ofReal_zero,
      zero_add, sub_zero, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
      using h
  have h := h1.div h2 (by simp)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hn : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  change (f d / (d : ℂ)) / ((Real.sinh d : ℂ) / (d : ℂ)) =
    f d / (Real.sinh d : ℂ)
  field_simp [hn]

private theorem pulseLayer_deriv_zero_of_even {f : ℝ → ℂ}
    (heven : Function.Even f) (hf : Differentiable ℝ f) : deriv f 0 = 0 := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) 0 := (hasDerivAt_id 0).neg
  have hbase : HasDerivAt f (deriv f (-0)) (-0) := (hf (-0)).hasDerivAt
  have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-0) * (-1)) 0 := by
    simpa [Function.comp_def, Complex.real_smul] using hbase.scomp 0 hneg
  have heq : (fun y : ℝ => f (-y)) = f := funext heven
  have hderiv := congrArg (fun g : ℝ → ℂ => deriv g 0) heq
  change deriv (fun y : ℝ => f (-y)) 0 = deriv f 0 at hderiv
  rw [hcomp.deriv] at hderiv
  norm_num at hderiv
  have hsum : deriv f 0 + deriv f 0 = 0 := eq_neg_iff_add_eq_zero.mp hderiv.symm
  have htwo : (2 : ℂ) * deriv f 0 = 0 := by
    simpa only [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The full circle's literal characteristic quotient is finite.  Its limit
is kept as the actual second radial jet; identifying that jet with the
full-plus-half-square contact is a separate corpus theorem. -/
private theorem pulseLayer_fullAngular_sinh_ratio_tendsto (q : XiZeroCopy)
    (branch : Bool) (X k : ℝ) :
    Tendsto (fun d : ℝ => deriv (fun r => angularMean q branch r X k) d /
      (Real.sinh d : ℂ)) (𝓝[≠] 0)
      (𝓝 (deriv (deriv (fun r => angularMean q branch r X k)) 0)) := by
  have hs1 := (contDiff_infty_iff_deriv.mp (angularMean_smooth q branch X k)).2
  have hsecond := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  exact pulseLayer_sinh_ratio_tendsto hsecond
    (angularMean_radial_oddJets_zero q branch X k).1

/-- The native circle has the same finite literal characteristic quotient.
Its radius parity is derived from the native circle itself, rather than from
the full-circle equation. -/
private theorem pulseLayer_nativeAngular_sinh_ratio_tendsto (q : XiZeroCopy)
    (X k : ℝ) :
    Tendsto (fun d : ℝ => deriv (fun r => D4BMNativeCircle.mean q r X k) d /
      (Real.sinh d : ℂ)) (𝓝[≠] 0)
      (𝓝 (deriv (deriv (fun r => D4BMNativeCircle.mean q r X k)) 0)) := by
  let f : ℝ → ℂ := fun d => D4BMNativeCircle.mean q d X k
  have hs := D4BMNativeCircle.mean_radial_smooth q X k
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hsecond := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  have heven : Function.Even f := by
    intro d
    exact D4BMNativeCircle.mean_neg_radius q d X k
  exact pulseLayer_sinh_ratio_tendsto hsecond
    (pulseLayer_deriv_zero_of_even heven (hs.differentiable (by simp)))

/-- Exact normal transport of the direct causal invariant along the incoming
source ray.  The coefficient is a product of the invariant defect and the
two actual tortoise slopes; this identity keeps the source motion and target
motion together instead of differentiating a frozen-radius proxy. -/
theorem pulseLayer_directInvariant_ingoing_hasDerivAt (h x z : ℝ) :
    HasDerivAt (fun r : ℝ => invariant h r (r - z))
      (-(Real.tanh x + Real.tanh (x - z)) * (invariant h x (x - z) - 1)) x := by
  have hy : HasDerivAt (fun r : ℝ => r - z) 1 x := (hasDerivAt_id x).sub_const z
  have hsx := Real.hasDerivAt_sinh x
  have hsy := (Real.hasDerivAt_sinh (x - z)).scomp x hy
  have hcx := Real.hasDerivAt_cosh x
  have hcy := (Real.hasDerivAt_cosh (x - z)).scomp x hy
  have hnum := (hasDerivAt_const x (Real.cosh h)).add (hsx.mul hsy)
  have hden := hcx.mul hcy
  have hden0 : Real.cosh x * Real.cosh (x - z) ≠ 0 :=
    mul_ne_zero (Real.cosh_pos x).ne' (Real.cosh_pos (x - z)).ne'
  convert! hnum.div hden hden0 using 1
  unfold invariant
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos (x - z)).ne']
  ring

/-- Exact finite-depth normal derivative of the actual full circle mean on a
strict direct cone point.  The derivative is taken inside the physical
`I > 1` chart and retains the literal moving invariant factor. -/
theorem pulseLayer_fullAngular_directInvariant_hasDerivAt (q : XiZeroCopy)
    (branch : Bool) (h x z X k : ℝ) (hz : |z| < h) :
    HasDerivAt (fun r : ℝ =>
      angularMean q branch (Real.arcosh (invariant h r (r - z))) X k)
      ((deriv (fun d : ℝ => angularMean q branch d X k)
        (Real.arcosh (invariant h x (x - z))) /
        (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (-(Real.tanh x + Real.tanh (x - z)) * (invariant h x (x - z) - 1))) x := by
  have hgt := pulseLayer_directInvariant_one_lt h x z hz
  have har : HasDerivAt Real.arcosh
      (1 / Real.sinh (Real.arcosh (invariant h x (x - z))))
      (invariant h x (x - z)) := by
    simpa only [one_div, Real.sinh_arcosh hgt.le] using Real.hasDerivAt_arcosh hgt
  have hm := ((angularMean_smooth q branch X k).contDiffAt
    (x := Real.arcosh (invariant h x (x - z)))).differentiableAt (by simp)).hasDerivAt
  have hd := hm.scomp x (har.scomp x (pulseLayer_directInvariant_ingoing_hasDerivAt h x z))
  convert! hd using 1
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- Exact finite-depth normal derivative of the actual native circle mean on
the strict direct cone.  Its scalar-Laplacian characteristic contact is not
inserted here; it will arise only from this literal derivative's cap limit. -/
theorem pulseLayer_nativeAngular_directInvariant_hasDerivAt (q : XiZeroCopy)
    (h x z X k : ℝ) (hz : |z| < h) :
    HasDerivAt (fun r : ℝ =>
      D4BMNativeCircle.mean q (Real.arcosh (invariant h r (r - z))) X k)
      ((deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
        (Real.arcosh (invariant h x (x - z))) /
        (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (-(Real.tanh x + Real.tanh (x - z)) * (invariant h x (x - z) - 1))) x := by
  have hgt := pulseLayer_directInvariant_one_lt h x z hz
  have har : HasDerivAt Real.arcosh
      (1 / Real.sinh (Real.arcosh (invariant h x (x - z))))
      (invariant h x (x - z)) := by
    simpa only [one_div, Real.sinh_arcosh hgt.le] using Real.hasDerivAt_arcosh hgt
  have hm := ((D4BMNativeCircle.mean_radial_smooth q X k).contDiffAt
    (x := Real.arcosh (invariant h x (x - z)))).differentiableAt (by simp)).hasDerivAt
  have hd := hm.scomp x (har.scomp x (pulseLayer_directInvariant_ingoing_hasDerivAt h x z))
  convert! hd using 1
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- The direct invariant's normal derivative has precisely twice its first
cap coefficient.  This is the leading geometric contribution needed when the
literal pulse action is differentiated; it is independent of any contact
pairing or value-level cancellation. -/
theorem pulseLayer_directInvariant_normal_div_capScale_tendsto (h z : ℝ) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => invariant h r (r - z)) x / capScale x) atBot
      (𝓝 (2 * ((Real.exp (h + z) - 1) *
        (Real.exp (-2 * z) - Real.exp (-(h + z)))))) := by
  rw [show (fun x : ℝ =>
      deriv (fun r : ℝ => invariant h r (r - z)) x / capScale x) =
      fun x : ℝ => -(Real.tanh x + Real.tanh (x - z)) *
        ((invariant h x (x - z) - 1) / capScale x) by
        funext x
        rw [(pulseLayer_directInvariant_ingoing_hasDerivAt h x z).deriv]
        ring]
  have htanh : Tendsto (fun x : ℝ => Real.tanh x) atBot (𝓝 (-1 : ℝ)) := by
    rw [show (fun x : ℝ => Real.tanh x) = fun x : ℝ => -radialUnit x by
      funext x
      rw [Real.tanh_eq_sinh_div_cosh]
      unfold radialUnit
      ring]
    simpa using radialUnit_tendsto_atBot_one.neg
  have htanhShift : Tendsto (fun x : ℝ => Real.tanh (x - z)) atBot (𝓝 (-1 : ℝ)) := by
    rw [show (fun x : ℝ => Real.tanh (x - z)) = fun x : ℝ => -radialUnit (x - z) by
      funext x
      rw [Real.tanh_eq_sinh_div_cosh]
      unfold radialUnit
      ring]
    simpa using (radialUnit_shift_tendsto_atBot_one z).neg
  have hgeometry := (htanh.add htanhShift).neg.mul
    (pulseLayer_directInvariant_sub_one_div_capScale_tendsto h z)
  convert hgeometry using 1 <;> ring

/-- Uniform normal-geometry estimate on the literal fixed-clock direct cone.
After division by the original cap scale, the moving invariant has no hidden
growth in cap depth.  This is the geometric factor needed to combine the two
actual characteristic-current bounds with the original source coefficients. -/
theorem pulseLayer_directInvariant_normal_div_capScale_bound (v x h u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hcone : |v + h - u| ≤ h) :
    |deriv (fun r : ℝ => invariant h r (r - (v + h - u))) x / capScale x| ≤
      2 * Real.exp (1 - v) := by
  let z : ℝ := v + h - u
  have hcone' : |z| ≤ h := by simpa only [z] using hcone
  have hbottom : -h ≤ z := (abs_le.mp hcone').1
  have htop : z ≤ h := (abs_le.mp hcone').2
  have hplus : 0 ≤ h + z := by linarith
  have hfirst : 0 ≤ Real.exp (h + z) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr hplus)
  have horder : -(h + z) ≤ -2 * z := by linarith
  have hdelta : 0 ≤ Real.exp (-2 * z) - Real.exp (-(h + z)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr horder)
  have hnum : 0 ≤
      (Real.exp (h + z) - 1) *
        (Real.exp (-2 * z) - Real.exp (-(h + z))) :=
    mul_nonneg hfirst hdelta
  have hnum_bound :
      (Real.exp (h + z) - 1) *
          (Real.exp (-2 * z) - Real.exp (-(h + z))) ≤ Real.exp (h - z) := by
    calc
      _ ≤ Real.exp (h + z) *
          (Real.exp (-2 * z) - Real.exp (-(h + z))) :=
        mul_le_mul_of_nonneg_right
          (sub_le_self _ (Real.exp_pos _).le) hdelta
      _ ≤ Real.exp (h + z) * Real.exp (-2 * z) :=
        mul_le_mul_of_nonneg_left
          (sub_le_self _ (Real.exp_pos _).le) (Real.exp_nonneg _)
      _ = Real.exp (h - z) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hden : 1 ≤ 1 + Real.exp (2 * (x - z)) := by positivity
  have hdefect_bound :
      (invariant h x (x - z) - 1) / capScale x ≤ Real.exp (1 - v) := by
    rw [pulseLayer_directInvariant_sub_one_div_capScale_eq]
    calc
      (Real.exp (h + z) - 1) *
          (Real.exp (-2 * z) - Real.exp (-(h + z))) /
          (1 + Real.exp (2 * (x - z))) ≤
          (Real.exp (h + z) - 1) *
            (Real.exp (-2 * z) - Real.exp (-(h + z))) :=
        div_le_self hnum hden
      _ ≤ Real.exp (h - z) := hnum_bound
      _ = Real.exp (u - v) := by
        congr 1
        dsimp only [z]
        ring
      _ ≤ Real.exp (1 - v) := Real.exp_le_exp.mpr (by linarith [hu.2])
  have hcausal : 1 ≤ invariant h x (x - z) := by
    apply invariant_causal
    refine ⟨h, x, x - z, ?_⟩
    simpa only [sub_sub_cancel_left] using hcone'
  have hcap : 0 < capScale x := by
    unfold capScale
    positivity
  have hdefect : 0 ≤ (invariant h x (x - z) - 1) / capScale x :=
    div_nonneg (sub_nonneg.mpr hcausal) hcap.le
  have htanh (a : ℝ) : |Real.tanh a| ≤ 1 :=
    abs_le.mpr ⟨(Real.neg_one_lt_tanh a).le, (Real.tanh_lt_one a).le⟩
  have hsum : |Real.tanh x + Real.tanh (x - z)| ≤ 2 := by
    calc
      _ ≤ |Real.tanh x| + |Real.tanh (x - z)| := abs_add _ _
      _ ≤ 1 + 1 := add_le_add (htanh x) (htanh (x - z))
      _ = 2 := by norm_num
  rw [show (fun r : ℝ => invariant h r (r - (v + h - u))) =
      fun r : ℝ => invariant h r (r - z) by
        funext r
        rfl]
  rw [show deriv (fun r : ℝ => invariant h r (r - z)) x / capScale x =
      -(Real.tanh x + Real.tanh (x - z)) *
        ((invariant h x (x - z) - 1) / capScale x) by
        rw [(pulseLayer_directInvariant_ingoing_hasDerivAt h x z).deriv]
        ring]
  rw [abs_neg, abs_mul, abs_of_nonneg hdefect]
  calc
    |Real.tanh x + Real.tanh (x - z)| *
        ((invariant h x (x - z) - 1) / capScale x) ≤
        2 * ((invariant h x (x - z) - 1) / capScale x) :=
      mul_le_mul_of_nonneg_right hsum hdefect
    _ ≤ 2 * Real.exp (1 - v) :=
      mul_le_mul_of_nonneg_left hdefect_bound (by norm_num)

private theorem pulseLayer_weighted_pair_pair_bound (a b m n c p : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hc : 0 ≤ c) (hp : 0 ≤ p) :
    2 * a * c * m + p * b * c * n ≤ (2 + p) * c * (a + b) * (m + n) := by
  have hfirst : 2 * a * c * m ≤ 2 * (a + b) * c * (m + n) := by
    gcongr
  have hsecond : p * b * c * n ≤ p * (a + b) * c * (m + n) := by
    gcongr
  calc
    _ ≤ 2 * (a + b) * c * (m + n) + p * (a + b) * c * (m + n) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

private theorem pulseLayer_directInvariant_normal_tendsto_zero (h z : ℝ) :
    Tendsto (fun x : ℝ => deriv (fun r : ℝ => invariant h r (r - z)) x) atBot (𝓝 0) := by
  rw [show (fun x : ℝ => deriv (fun r : ℝ => invariant h r (r - z)) x) =
      fun x : ℝ =>
        (deriv (fun r : ℝ => invariant h r (r - z)) x / capScale x) * capScale x by
        funext x
        have hcap : capScale x ≠ 0 := ne_of_gt (by
          unfold capScale
          positivity)
        field_simp [hcap]]
  simpa using (pulseLayer_directInvariant_normal_div_capScale_tendsto h z).mul
    capScale_tendsto_atBot_zero

private theorem pulseLayer_directInvariant_normal_complex_tendsto_zero (h z : ℝ) :
    Tendsto (fun x : ℝ =>
      (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ)) atBot (𝓝 0) :=
  simpa using (Complex.continuous_ofReal.tendsto 0).comp
    (pulseLayer_directInvariant_normal_tendsto_zero h z)

/-- The causal radius in a fixed direct layer tends to zero.  The direct-cone
hypothesis is retained to justify the physical `arcosh` branch at every
finite target radius. -/
theorem pulseLayer_directRadius_tendsto (h z : ℝ) (hz : |z| ≤ h) :
    Tendsto (fun x : ℝ => Real.arcosh (invariant h x (x - z))) atBot (𝓝 (0 : ℝ)) := by
  have hcausal (x : ℝ) : 1 ≤ invariant h x (x - z) := by
    apply invariant_causal
    refine ⟨h, x, x - z, ?_⟩
    simpa only [sub_sub_cancel_left] using hz
  have hcont : Continuous (fun r : ℝ => Real.arcosh (max 1 r)) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
      (fun r => le_max_left 1 r)
  rw [show (fun x : ℝ => Real.arcosh (invariant h x (x - z))) =
      fun x : ℝ => Real.arcosh (max 1 (invariant h x (x - z))) by
        funext x
        rw [max_eq_right (hcausal x)]]
  simpa using hcont.continuousAt.tendsto.comp (pulseLayer_directInvariant_tendsto h z)

/-- Along a strict direct layer, the full circle's actual radial derivative
quotient reaches its finite characteristic jet.  This is a consequence of
the literal even radius germ, not an imposed corner extension. -/
theorem pulseLayer_fullAngular_direct_sinh_ratio_tendsto (q : XiZeroCopy)
    (branch : Bool) (h z X k : ℝ) (hz : |z| < h) :
    Tendsto (fun x : ℝ =>
      deriv (fun d : ℝ => angularMean q branch d X k)
        (Real.arcosh (invariant h x (x - z))) /
        (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) atBot
      (𝓝 (deriv (deriv (fun d : ℝ => angularMean q branch d X k)) 0)) := by
  have hradius := pulseLayer_directRadius_tendsto h z hz.le
  have hnonzero : ∀ᶠ x : ℝ in atBot,
      Real.arcosh (invariant h x (x - z)) ≠ 0 :=
    Eventually.of_forall (fun x =>
      (Real.arcosh_pos (pulseLayer_directInvariant_one_lt h x z hz)).ne')
  have hwithin : Tendsto (fun x : ℝ =>
      Real.arcosh (invariant h x (x - z))) atBot (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hradius hnonzero
  exact (pulseLayer_fullAngular_sinh_ratio_tendsto q branch X k).comp hwithin

/-- The strict direct face's characteristic quotient reaches the literal
full-plus-half-square vertex.  The zero jet is forced by the full circle ODE,
not supplied as a contact datum. -/
theorem pulseLayer_fullAngular_direct_sinh_ratio_tendsto_literalVertex
    (q : XiZeroCopy) (branch : Bool) (h z X k : ℝ) (hz : |z| < h) :
    Tendsto (fun x : ℝ =>
      deriv (fun d : ℝ => angularMean q branch d X k)
        (Real.arcosh (invariant h x (x - z))) /
        (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) atBot
      (𝓝 (parameter q branch *
        (fullAngularField q branch ![X, Real.exp k] +
          fullSquarePotential q ![X, Real.exp k]) / 2)) := by
  convert pulseLayer_fullAngular_direct_sinh_ratio_tendsto q branch h z X k hz using 1
  rw [angularMean_second_deriv_zero]

/-- The corresponding literal native-circle quotient has its finite
characteristic jet on every strict direct layer. -/
theorem pulseLayer_nativeAngular_direct_sinh_ratio_tendsto (q : XiZeroCopy)
    (h z X k : ℝ) (hz : |z| < h) :
    Tendsto (fun x : ℝ =>
      deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
        (Real.arcosh (invariant h x (x - z))) /
        (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) atBot
      (𝓝 (deriv (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)) 0)) := by
  have hradius := pulseLayer_directRadius_tendsto h z hz.le
  have hnonzero : ∀ᶠ x : ℝ in atBot,
      Real.arcosh (invariant h x (x - z)) ≠ 0 :=
    Eventually.of_forall (fun x =>
      (Real.arcosh_pos (pulseLayer_directInvariant_one_lt h x z hz)).ne')
  have hwithin : Tendsto (fun x : ℝ =>
      Real.arcosh (invariant h x (x - z))) atBot (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hradius hnonzero
  exact (pulseLayer_nativeAngular_sinh_ratio_tendsto q X k).comp hwithin

/-- The seed profile is bounded on its actual compact radial range.  This
small interface is exposed here because the direct cap layer needs the exact
profile, rather than the coarser whole-pulse majorant. -/
private theorem seedHorizonProfile_continuousOn (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContinuousOn (seedHorizonProfile q branch amp) (Set.Icc 0 1) := by
  intro u hu
  have hp : ContinuousAt (fun u : ℝ => power (2 * physicalRate q branch) (1 + u)) u :=
    (power_derivatives (2 * physicalRate q branch) (by linarith [hu.1])).1.continuousAt.comp
      (continuous_const.add continuous_id).continuousAt
  have hc : ContinuousAt (fun u : ℝ => parameter q branch *
      power (2 * physicalRate q branch) (1 + u) * amp ^ 2 * (1 + (u : ℂ)) *
        ((2 * physicalRate q branch + 1) * (u : ℂ) + 1)) u := by
    fun_prop
  exact hc.continuousWithinAt

private theorem seedHorizonProfile_continuousAt_one (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) : ContinuousAt (seedHorizonProfile q branch amp) 1 := by
  unfold seedHorizonProfile
  have hp : ContinuousAt (fun u : ℝ => power (2 * physicalRate q branch) (1 + u)) 1 :=
    (power_derivatives (2 * physicalRate q branch) (by norm_num : (0 : ℝ) < 1 + 1)).1
      .continuousAt.comp (continuous_const.add continuous_id).continuousAt
  fun_prop

private theorem sourceHorizonProfile_continuousAt_one (q : XiZeroCopy) (amp : ℂ) :
    ContinuousAt (sourceHorizonProfile (physicalRate q branch) amp 1) 1 := by
  unfold sourceHorizonProfile
  simp only [show (1 : Fin 2) ≠ 0 by norm_num, ↓reduceIte]
  have hp : ContinuousAt (fun u : ℝ => power (2 * physicalRate q branch) (1 + u)) 1 :=
    (power_derivatives (2 * physicalRate q branch) (by norm_num : (0 : ℝ) < 1 + 1)).1
      .continuousAt.comp (continuous_const.add continuous_id).continuousAt
  fun_prop

/-- Compact profile left after extracting the same horizon exponential from
the second radial derivative of the literal seed coefficient. -/
def pulseLayerSeedSecondProfile (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (u : ℝ) : ℂ :=
  let s := physicalRate q branch
  power (2 * s) (1 + u) * amp ^ 2 * (1 + (u : ℂ)) *
    (4 * s ^ 2 * (1 - (u : ℂ)) * sourceSeedPolynomial s (parameter q branch) (u : ℂ) -
      2 * s * (1 + (u : ℂ)) * sourceSeedPolynomial s (parameter q branch) (u : ℂ) -
      (4 * s * ((u : ℂ) - 1) + 2 * (u : ℂ)) * (1 + (u : ℂ)) *
        sourceSeedFirst s (parameter q branch) (u : ℂ) +
      (1 - (u : ℂ)) * (1 + (u : ℂ)) ^ 2 *
        sourceSeedSecond s (parameter q branch) (u : ℂ))

/-- Compact profile left after extracting the same horizon exponential from
twice the second derivative of the literal lift coefficient. -/
def pulseLayerLiftSecondProfile (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (u : ℝ) : ℂ :=
  let s := physicalRate q branch
  2 * (-s * (s - 1) / 4) * power (2 * s) (1 + u) * amp ^ 2 * (1 + (u : ℂ)) *
    (4 * s ^ 2 * (1 - (u : ℂ)) * (u : ℂ) ^ 3 +
      12 * s * (1 - (u : ℂ)) * (u : ℂ) ^ 2 * (1 + (u : ℂ)) -
      2 * s * (1 + (u : ℂ)) * (u : ℂ) ^ 3 +
      6 * (u : ℂ) * (1 - (u : ℂ)) * (1 + (u : ℂ)) ^ 2 -
      6 * (u : ℂ) ^ 3 * (1 + (u : ℂ)))

/-- Exact horizon exponential factor of the seed's second radial derivative. -/
theorem pulseLayer_seedSecond_horizon (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (t : ℝ) :
    sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) t =
      (Real.exp (2 * t) : ℂ) *
        pulseLayerSeedSecondProfile q branch amp (radialUnit t) := by
  let s := physicalRate q branch
  let u : ℂ := radialUnit t
  have he : 1 - u = (Real.exp (2 * t) : ℂ) * (1 + u) := by
    exact_mod_cast radialUnit_one_sub t
  have hminus : u - 1 = -(Real.exp (2 * t) : ℂ) * (1 + u) := by
    linear_combination -he
  have hsq : u ^ 2 - 1 = -(Real.exp (2 * t) : ℂ) * (1 + u) ^ 2 := by
    calc
      u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
      _ = _ := by rw [hminus]; ring
  unfold sourceSeedFieldSecond sourceAmplitude amplitudeRate pulseLayerSeedSecondProfile
  dsimp only [s, u]
  simp only [zero_mul, Complex.exp_zero, one_mul, mul_one]
  rw [he, hminus, hsq]
  ring

/-- Exact horizon exponential factor of twice the lift's second radial
derivative, in the normalization that occurs in the onset source channel. -/
theorem pulseLayer_liftSecond_horizon (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (t : ℝ) :
    2 * radialLiftSecond (physicalRate q branch) 0 amp 1 t =
      (Real.exp (2 * t) : ℂ) *
        pulseLayerLiftSecondProfile q branch amp (radialUnit t) := by
  let s := physicalRate q branch
  let u : ℂ := radialUnit t
  have he : 1 - u = (Real.exp (2 * t) : ℂ) * (1 + u) := by
    exact_mod_cast radialUnit_one_sub t
  have hminus : u - 1 = -(Real.exp (2 * t) : ℂ) * (1 + u) := by
    linear_combination -he
  have hsq : u ^ 2 - 1 = -(Real.exp (2 * t) : ℂ) * (1 + u) ^ 2 := by
    calc
      u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
      _ = _ := by rw [hminus]; ring
  unfold radialLiftSecond sourceAmplitude amplitudeRate liftSecondPolynomial
    pulseLayerLiftSecondProfile
  dsimp only [s, u]
  simp only [zero_mul, Complex.exp_zero, one_mul, mul_one]
  rw [he, hminus, hsq]
  ring

/-- At the horizon, each second radial coefficient is exactly twice its first
coefficient's compact profile.  This is the source-side origin of the factor
two in the pulse normal trace. -/
theorem pulseLayer_secondProfiles_at_horizon (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) :
    pulseLayerSeedSecondProfile q branch amp 1 =
      2 * seedHorizonProfile q branch amp 1 ∧
    pulseLayerLiftSecondProfile q branch amp 1 =
      2 * sourceHorizonProfile (physicalRate q branch) amp 1 1 := by
  constructor <;> unfold pulseLayerSeedSecondProfile pulseLayerLiftSecondProfile
    seedHorizonProfile sourceHorizonProfile sourceSeedPolynomial sourceSeedFirst sourceSeedSecond
    reducedHorizonPolynomial <;>
      simp only [Complex.ofReal_one, one_pow, one_mul, sub_self, mul_zero, zero_mul,
        add_zero, ↓reduceIte] <;>
      rw [parameter_physicalRate q branch] <;>
      ring

private theorem pulseLayerSeedSecondProfile_continuousAt_one (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) :
    ContinuousAt (pulseLayerSeedSecondProfile q branch amp) 1 := by
  unfold pulseLayerSeedSecondProfile
  have hp : ContinuousAt (fun u : ℝ => power (2 * physicalRate q branch) (1 + u)) 1 :=
    (power_derivatives (2 * physicalRate q branch) (by norm_num : (0 : ℝ) < 1 + 1)).1
      .continuousAt.comp (continuous_const.add continuous_id).continuousAt
  fun_prop

private theorem pulseLayerLiftSecondProfile_continuousAt_one (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) :
    ContinuousAt (pulseLayerLiftSecondProfile q branch amp) 1 := by
  unfold pulseLayerLiftSecondProfile
  have hp : ContinuousAt (fun u : ℝ => power (2 * physicalRate q branch) (1 + u)) 1 :=
    (power_derivatives (2 * physicalRate q branch) (by norm_num : (0 : ℝ) < 1 + 1)).1
      .continuousAt.comp (continuous_const.add continuous_id).continuousAt
  fun_prop

private theorem pulseLayerSeedSecondProfile_continuousOn (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) :
    ContinuousOn (pulseLayerSeedSecondProfile q branch amp) (Set.Icc 0 1) := by
  intro u hu
  have hp : ContinuousAt (fun u : ℝ => power (2 * physicalRate q branch) (1 + u)) u :=
    (power_derivatives (2 * physicalRate q branch) (by linarith [hu.1])).1
      .continuousAt.comp (continuous_const.add continuous_id).continuousAt
  unfold pulseLayerSeedSecondProfile
  fun_prop

private theorem pulseLayerLiftSecondProfile_continuousOn (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) :
    ContinuousOn (pulseLayerLiftSecondProfile q branch amp) (Set.Icc 0 1) := by
  intro u hu
  have hp : ContinuousAt (fun u : ℝ => power (2 * physicalRate q branch) (1 + u)) u :=
    (power_derivatives (2 * physicalRate q branch) (by linarith [hu.1])).1
      .continuousAt.comp (continuous_const.add continuous_id).continuousAt
  unfold pulseLayerLiftSecondProfile
  fun_prop

/-- Cap-scale limit of the actual seed coefficient's second radial derivative.
Its limit is twice the first coefficient's literal horizon profile. -/
theorem pulseLayer_seedSecond_scaled_tendsto (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (z : ℝ) :
    Tendsto (fun x : ℝ =>
      sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) (x - z) /
        (capScale x : ℂ)) atBot
      (𝓝 ((Real.exp (-2 * z) : ℂ) * seedHorizonProfile q branch amp 1)) := by
  rw [show (fun x : ℝ =>
      sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) (x - z) /
        (capScale x : ℂ)) =
      fun x : ℝ => ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
        pulseLayerSeedSecondProfile q branch amp (radialUnit (x - z)) by
        funext x
        rw [pulseLayer_seedSecond_horizon]
        ring]
  have hscale := pulseLayer_direct_scale_tendsto z
  have hprofile := (pulseLayerSeedSecondProfile_continuousAt_one q branch amp).tendsto.comp
    (radialUnit_shift_tendsto_atBot_one z)
  have hproduct := hscale.mul hprofile
  rw [(pulseLayer_secondProfiles_at_horizon q branch amp).1] at hproduct
  convert hproduct using 1 <;> ring

/-- Cap-scale limit of twice the actual lift coefficient's second radial
derivative, again retaining exactly twice the first horizon profile. -/
theorem pulseLayer_liftSecond_scaled_tendsto (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (z : ℝ) :
    Tendsto (fun x : ℝ =>
      (2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)) /
        (capScale x : ℂ)) atBot
      (𝓝 ((Real.exp (-2 * z) : ℂ) *
        sourceHorizonProfile (physicalRate q branch) amp 1 1)) := by
  rw [show (fun x : ℝ =>
      (2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)) /
        (capScale x : ℂ)) =
      fun x : ℝ => ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
        pulseLayerLiftSecondProfile q branch amp (radialUnit (x - z)) by
        funext x
        rw [pulseLayer_liftSecond_horizon]
        ring]
  have hscale := pulseLayer_direct_scale_tendsto z
  have hprofile := (pulseLayerLiftSecondProfile_continuousAt_one q branch amp).tendsto.comp
    (radialUnit_shift_tendsto_atBot_one z)
  have hproduct := hscale.mul hprofile
  rw [(pulseLayer_secondProfiles_at_horizon q branch amp).2] at hproduct
  convert hproduct using 1 <;> ring

/-- Both literal second radial jets retain the same exact horizon order on
the complete incoming source ray.  This is the tail input for differentiating
the direct Peierls density, not a first-jet surrogate. -/
theorem pulseLayer_secondRadialPair_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y < 0 →
      ‖sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) y‖ +
        ‖2 * radialLiftSecond (physicalRate q branch) 0 amp 1 y‖ ≤
          C * Real.exp (2 * y) := by
  obtain ⟨C0, h0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (pulseLayerSeedSecondProfile_continuousOn q branch amp)
  obtain ⟨C1, h1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (pulseLayerLiftSecondProfile_continuousOn q branch amp)
  refine ⟨max C0 0 + max C1 0,
    add_nonneg (le_max_right _ _) (le_max_right _ _), fun y hy => ?_⟩
  have hu : radialUnit y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(radialUnit_bounds y hy).1.le, (radialUnit_bounds y hy).2.le⟩
  have hb0 := (h0 _ hu).trans (le_max_left C0 0)
  have hb1 := (h1 _ hu).trans (le_max_left C1 0)
  rw [pulseLayer_seedSecond_horizon, pulseLayer_liftSecond_horizon, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith [mul_le_mul_of_nonneg_left hb0 (Real.exp_pos (2 * y)).le,
    mul_le_mul_of_nonneg_left hb1 (Real.exp_pos (2 * y)).le]

/-- The two literal second source jets remain uniformly cap-scaled along an
incoming direct ray.  This is the source-jet half of the normal DCT envelope. -/
private theorem pulseLayer_secondRadialPair_div_capScale_bound (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : ℝ, x ≤ 0 → x - z < 0 →
      ‖sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch)
          (x - z) / (capScale x : ℂ)‖ +
        ‖(2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)) /
          (capScale x : ℂ)‖ ≤ C * Real.exp (-2 * z) := by
  obtain ⟨C, hC, hpair⟩ := pulseLayer_secondRadialPair_bound q branch amp
  refine ⟨C, hC, ?_⟩
  intro x z hx hy
  have hcap : 0 < capScale x := by
    unfold capScale
    positivity
  have hscale : Real.exp (2 * x) / capScale x ≤ 1 := by
    rw [exp_two_div_capScale_eq]
    exact pulseLayer_direct_scale_correction_le_one x hx
  have hsource := hpair (x - z) hy
  have hexp : Real.exp (2 * (x - z)) =
      Real.exp (-2 * z) * Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_div, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hcap, abs_of_pos hcap]
  calc
    ‖sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch)
        (x - z)‖ / capScale x +
        ‖2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)‖ /
          capScale x =
        (‖sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch)
          (x - z)‖ + ‖2 * radialLiftSecond (physicalRate q branch) 0 amp 1
            (x - z)‖) / capScale x := by ring
    _ ≤ (C * Real.exp (2 * (x - z))) / capScale x :=
      div_le_div_of_nonneg_right hsource hcap.le
    _ = C * Real.exp (-2 * z) * (Real.exp (2 * x) / capScale x) := by
      rw [hexp]
      field_simp [hcap.ne']
      ring
    _ ≤ C * Real.exp (-2 * z) := by
      rw [← mul_one (C * Real.exp (-2 * z))]
      exact mul_le_mul_of_nonneg_left hscale (by positivity)

private theorem pulseLayer_secondRadialPair_direct_decay_bound (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h u : ℝ, x ≤ 0 →
      x - (v + h - u) < 0 → u ∈ Set.Icc (0 : ℝ) 1 →
      ‖sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch)
          (x - (v + h - u)) / (capScale x : ℂ)‖ +
        ‖(2 * radialLiftSecond (physicalRate q branch) 0 amp 1
          (x - (v + h - u))) / (capScale x : ℂ)‖ ≤
          C * Real.exp (-2 * h) := by
  obtain ⟨C0, hC0, hpair⟩ := pulseLayer_secondRadialPair_div_capScale_bound q branch amp
  let C := C0 * Real.exp (2 - 2 * v)
  refine ⟨C, mul_nonneg hC0 (Real.exp_nonneg _), ?_⟩
  intro x h u hx hy hu
  have hsource := hpair x (v + h - u) hx hy
  have hexp : Real.exp (-2 * (v + h - u)) ≤
      Real.exp ((2 - 2 * v) + (-2 * h)) :=
    Real.exp_le_exp.mpr (by linarith [hu.2])
  calc
    _ ≤ C0 * Real.exp (-2 * (v + h - u)) := hsource
    _ ≤ C0 * Real.exp ((2 - 2 * v) + (-2 * h)) :=
      mul_le_mul_of_nonneg_left hexp hC0
    _ = C * Real.exp (-2 * h) := by
      dsimp only [C]
      rw [Real.exp_add]
      ring

/-- Actual ingoing derivative of the full-response onset coefficient.  The
original clock remains frozen at `v+h-z`; only the literal source radial jet
is differentiated. -/
theorem pulseLayer_onsetResponse_ingoing_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z : ℝ) :
    HasDerivAt (fun r : ℝ =>
      onsetResponseCoefficient q branch amp (v - r + h) (r - z))
      (-2 * sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
        (parameter q branch) (x - z) * pulseLayerClock q branch (v + h - z)) x := by
  have hfun : (fun r : ℝ =>
      onsetResponseCoefficient q branch amp (v - r + h) (r - z)) =
      fun r : ℝ => -2 * sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
        (parameter q branch) (r - z) * pulseLayerClock q branch (v + h - z) := by
    funext r
    rw [(onsetCoefficients_layerClock q branch amp (v - r + h) (r - z)).1,
      show (v - r + h) + (r - z) = v + h - z by ring]
  rw [hfun]
  have hsource := (sourceSeedFieldFirst_hasDerivAt (physicalRate q branch) 0 amp 1
    (parameter q branch) (x - z)).scomp x ((hasDerivAt_id x).sub_const z)
  convert! (hsource.const_mul (-2 : ℂ)).mul_const
    (pulseLayerClock q branch (v + h - z)) using 1
  ring

/-- Actual ingoing derivative of the native-source onset coefficient, with
the same frozen original clock and its literal lift second jet. -/
theorem pulseLayer_onsetSource_ingoing_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z : ℝ) :
    HasDerivAt (fun r : ℝ =>
      onsetSourceCoefficient q branch amp (v - r + h) (r - z))
      (parameter q branch * (2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)) *
        pulseLayerClock q branch (v + h - z)) x := by
  have hfun : (fun r : ℝ =>
      onsetSourceCoefficient q branch amp (v - r + h) (r - z)) =
      fun r : ℝ => parameter q branch *
        (2 * radialLiftFirst (physicalRate q branch) 0 amp 1 (r - z)) *
          pulseLayerClock q branch (v + h - z) := by
    funext r
    rw [(onsetCoefficients_layerClock q branch amp (v - r + h) (r - z)).2,
      show (v - r + h) + (r - z) = v + h - z by ring]
  rw [hfun]
  have hlift := (radialLiftFirst_hasDerivAt (physicalRate q branch) 0 amp 1 (x - z)).scomp x
    ((hasDerivAt_id x).sub_const z)
  convert! ((hlift.const_mul (2 : ℂ)).const_mul (parameter q branch)).mul_const
    (pulseLayerClock q branch (v + h - z)) using 1
  ring

/-- The literal response coefficient has its complete ingoing cap-normal
limit.  This is an actual derivative of the moving source coordinate, with
the fixed original clock retained; it is twice the corresponding value-layer
coefficient. -/
theorem pulseLayer_onsetResponse_ingoing_normal_div_capScale_tendsto
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z : ℝ) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => onsetResponseCoefficient q branch amp (v - r + h) (r - z)) x /
        (capScale x : ℂ)) atBot
      (𝓝 (-2 * (Real.exp (-2 * z) : ℂ) * seedHorizonProfile q branch amp 1 *
        pulseLayerClock q branch (v + h - z))) := by
  rw [show (fun x : ℝ =>
      deriv (fun r : ℝ => onsetResponseCoefficient q branch amp (v - r + h) (r - z)) x /
        (capScale x : ℂ)) =
      fun x : ℝ =>
        (-2 * sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
          (parameter q branch) (x - z) / (capScale x : ℂ)) *
          pulseLayerClock q branch (v + h - z) by
        funext x
        rw [(pulseLayer_onsetResponse_ingoing_hasDerivAt q branch amp v x h z).deriv]
        ring]
  have hnormal :=
    ((pulseLayer_seedSecond_scaled_tendsto q branch amp z).const_mul (-2 : ℂ)).mul_const
      (pulseLayerClock q branch (v + h - z))
  convert hnormal using 1 <;> ring

/-- The literal native-source coefficient has its complete ingoing cap-normal
limit.  Together with the response theorem, this fixes both non-angular
source channels in the direct Peierls normal trace without changing clocks,
sources, or circle faces. -/
theorem pulseLayer_onsetSource_ingoing_normal_div_capScale_tendsto
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z : ℝ) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => onsetSourceCoefficient q branch amp (v - r + h) (r - z)) x /
        (capScale x : ℂ)) atBot
      (𝓝 (parameter q branch * (Real.exp (-2 * z) : ℂ) *
        sourceHorizonProfile (physicalRate q branch) amp 1 1 *
        pulseLayerClock q branch (v + h - z))) := by
  rw [show (fun x : ℝ =>
      deriv (fun r : ℝ => onsetSourceCoefficient q branch amp (v - r + h) (r - z)) x /
        (capScale x : ℂ)) =
      fun x : ℝ =>
        (parameter q branch *
          ((2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)) /
            (capScale x : ℂ))) *
          pulseLayerClock q branch (v + h - z) by
        funext x
        rw [(pulseLayer_onsetSource_ingoing_hasDerivAt q branch amp v x h z).deriv]
        ring]
  have hnormal :=
    ((pulseLayer_liftSecond_scaled_tendsto q branch amp z).const_mul
      (parameter q branch)).mul_const (pulseLayerClock q branch (v + h - z))
  convert hnormal using 1 <;> ring

/-- Both literal radial coefficients have their exact common horizon order on
the complete incoming source ray.  This is the radial ingredient missing from
the generic future-pulse admission bound at cap scale. -/
theorem pulseLayer_radialPair_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y < 0 →
      ‖sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y‖ +
        ‖2 * radialLiftFirst (physicalRate q branch) 0 amp 1 y‖ ≤
          C * Real.exp (2 * y) := by
  obtain ⟨C0, h0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (seedHorizonProfile_continuousOn q branch amp)
  obtain ⟨C1, h1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (sourceHorizonProfile_continuousOn (physicalRate q branch) amp 1)
  refine ⟨max C0 0 + max C1 0,
    add_nonneg (le_max_right _ _) (le_max_right _ _), fun y hy => ?_⟩
  have hu : radialUnit y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(radialUnit_bounds y hy).1.le, (radialUnit_bounds y hy).2.le⟩
  have hb0 := (h0 _ hu).trans (le_max_left C0 0)
  have hb1 := (h1 _ hu).trans (le_max_left C1 0)
  rw [seedFirst_horizon, radialLiftFirst_horizon, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith [mul_le_mul_of_nonneg_left hb0 (Real.exp_pos (2 * y)).le,
    mul_le_mul_of_nonneg_left hb1 (Real.exp_pos (2 * y)).le]

/-- On the fixed original clock strip, the two undifferentiated source
coefficients carry a common `exp (-2h)` direct-layer decay.  Their current
and normal-geometry factors are handled separately. -/
private theorem pulseLayer_radialPair_direct_decay_bound (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h u : ℝ, x ≤ 0 → x - (v + h - u) < 0 →
      u ∈ Set.Icc (0 : ℝ) 1 →
      ‖sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch)
          (x - (v + h - u))‖ +
        ‖2 * radialLiftFirst (physicalRate q branch) 0 amp 1
          (x - (v + h - u))‖ ≤ C * Real.exp (-2 * h) := by
  obtain ⟨C0, hC0, hpair⟩ := pulseLayer_radialPair_bound q branch amp
  let C := C0 * Real.exp (2 - 2 * v)
  refine ⟨C, mul_nonneg hC0 (Real.exp_nonneg _), ?_⟩
  intro x h u hx hy hu
  have hsource := hpair (x - (v + h - u)) hy
  have hexp : Real.exp (2 * (x - (v + h - u))) ≤
      Real.exp ((2 - 2 * v) + (-2 * h)) :=
    Real.exp_le_exp.mpr (by linarith [hu.2])
  calc
    _ ≤ C0 * Real.exp (2 * (x - (v + h - u))) := hsource
    _ ≤ C0 * Real.exp ((2 - 2 * v) + (-2 * h)) :=
      mul_le_mul_of_nonneg_left hexp hC0
    _ = C * Real.exp (-2 * h) := by
      dsimp only [C]
      rw [Real.exp_add]
      ring

/-- Scaled direct-layer response coefficient with every horizon factor
retained. -/
theorem pulseLayer_onsetResponse_scaled (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z : ℝ) :
    onsetResponseCoefficient q branch amp (v - x + h) (x - z) /
        (capScale x : ℂ) =
      ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
        (-2 * seedHorizonProfile q branch amp (radialUnit (x - z)) *
          pulseLayerClock q branch (v + h - z)) := by
  rw [(onsetCoefficients_layerClock q branch amp (v - x + h) (x - z)).1,
    seedFirst_horizon]
  have hclock : (v - x + h) + (x - z) = v + h - z := by ring
  rw [hclock]
  ring

/-- Scaled direct-layer native-source coefficient with every horizon factor
retained. -/
theorem pulseLayer_onsetSource_scaled (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z : ℝ) :
    onsetSourceCoefficient q branch amp (v - x + h) (x - z) /
        (capScale x : ℂ) =
      ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
        (parameter q branch * sourceHorizonProfile (physicalRate q branch) amp 1
          (radialUnit (x - z)) * pulseLayerClock q branch (v + h - z)) := by
  rw [(onsetCoefficients_layerClock q branch amp (v - x + h) (x - z)).2]
  have hclock : (v - x + h) + (x - z) = v + h - z := by ring
  rw [hclock, radialLiftFirst_horizon]
  ring

/-- Cap-scale limit of the literal response onset coefficient on a moving
direct ray.  This is the value-layer coefficient to which its normal jet is
compared; the original transition clock is unchanged. -/
theorem pulseLayer_onsetResponse_scaled_tendsto (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v h z : ℝ) :
    Tendsto (fun x : ℝ =>
      onsetResponseCoefficient q branch amp (v - x + h) (x - z) /
        (capScale x : ℂ)) atBot
      (𝓝 (-(Real.exp (-2 * z) : ℂ) * seedHorizonProfile q branch amp 1 *
        pulseLayerClock q branch (v + h - z))) := by
  rw [show (fun x : ℝ =>
      onsetResponseCoefficient q branch amp (v - x + h) (x - z) /
        (capScale x : ℂ)) =
      fun x : ℝ => ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
        (-2 * seedHorizonProfile q branch amp (radialUnit (x - z)) *
          pulseLayerClock q branch (v + h - z)) by
        funext x
        exact pulseLayer_onsetResponse_scaled q branch amp v x h z]
  have hscale := pulseLayer_direct_scale_tendsto z
  have hprofile := (seedHorizonProfile_continuousAt_one q branch amp).tendsto.comp
    (radialUnit_shift_tendsto_atBot_one z)
  have hwhole := hscale.mul
    ((hprofile.const_mul (-2 : ℂ)).mul_const (pulseLayerClock q branch (v + h - z)))
  convert hwhole using 1 <;> ring

/-- Cap-scale limit of the literal native-source onset coefficient on a
moving direct ray.  This supplies the second value-layer factor needed for
the full direct circle normal trace. -/
theorem pulseLayer_onsetSource_scaled_tendsto (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v h z : ℝ) :
    Tendsto (fun x : ℝ =>
      onsetSourceCoefficient q branch amp (v - x + h) (x - z) /
        (capScale x : ℂ)) atBot
      (𝓝 ((Real.exp (-2 * z) : ℂ) / 2 * parameter q branch *
        sourceHorizonProfile (physicalRate q branch) amp 1 1 *
        pulseLayerClock q branch (v + h - z))) := by
  rw [show (fun x : ℝ =>
      onsetSourceCoefficient q branch amp (v - x + h) (x - z) /
        (capScale x : ℂ)) =
      fun x : ℝ => ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
        (parameter q branch * sourceHorizonProfile (physicalRate q branch) amp 1
          (radialUnit (x - z)) * pulseLayerClock q branch (v + h - z)) by
        funext x
        exact pulseLayer_onsetSource_scaled q branch amp v x h z]
  have hscale := pulseLayer_direct_scale_tendsto z
  have hprofile := (sourceHorizonProfile_continuousAt_one q branch amp).tendsto.comp
    (radialUnit_shift_tendsto_atBot_one z)
  have hwhole := hscale.mul
    ((hprofile.const_mul (parameter q branch)).mul_const
      (pulseLayerClock q branch (v + h - z)))
  convert hwhole using 1 <;> ring

/-- The moving full-circle radius contributes only at second cap order to the
response channel.  This is proved from the actual circle derivative quotient,
not by freezing the circle at radius zero before differentiating. -/
theorem pulseLayer_responseAngular_normal_div_capScale_tendsto_zero
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z X k : ℝ) (hz : |z| < h) :
    Tendsto (fun x : ℝ =>
      onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
        (deriv (fun d : ℝ => angularMean q branch d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) /
          (capScale x : ℂ)) atBot (𝓝 0) := by
  rw [show (fun x : ℝ =>
      onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
        (deriv (fun d : ℝ => angularMean q branch d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) /
          (capScale x : ℂ)) =
      fun x : ℝ =>
        (onsetResponseCoefficient q branch amp (v - x + h) (x - z) /
          (capScale x : ℂ)) *
        (deriv (fun d : ℝ => angularMean q branch d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) by
        funext x
        have hcap : (capScale x : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold capScale; positivity))
        field_simp [hcap]
        ring]
  simpa using
    ((pulseLayer_onsetResponse_scaled_tendsto q branch amp v h z).mul
      (pulseLayer_fullAngular_direct_sinh_ratio_tendsto q branch h z X k hz)).mul
      (pulseLayer_directInvariant_normal_complex_tendsto_zero h z)

/-- The same second-cap-order cancellation holds for the native circle
channel, with its independently constructed literal radial mean retained. -/
theorem pulseLayer_sourceAngular_normal_div_capScale_tendsto_zero
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z X k : ℝ) (hz : |z| < h) :
    Tendsto (fun x : ℝ =>
      onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
        (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) /
          (capScale x : ℂ)) atBot (𝓝 0) := by
  rw [show (fun x : ℝ =>
      onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
        (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) /
          (capScale x : ℂ)) =
      fun x : ℝ =>
        (onsetSourceCoefficient q branch amp (v - x + h) (x - z) /
          (capScale x : ℂ)) *
        (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
        (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) by
        funext x
        have hcap : (capScale x : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold capScale; positivity))
        field_simp [hcap]
        ring]
  simpa using
    ((pulseLayer_onsetSource_scaled_tendsto q branch amp v h z).mul
      (pulseLayer_nativeAngular_direct_sinh_ratio_tendsto q h z X k hz)).mul
      (pulseLayer_directInvariant_normal_complex_tendsto_zero h z)

/-- Exact derivative of the literal undecomposed direct circle face at every
strict cone point.  All four Leibniz terms remain: two moving source jets and
two moving-radius circle jets. -/
theorem pulseLayerDirectCircleKernel_ingoing_hasDerivAt_strict
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x h z X k : ℝ) (hz : |z| < h) :
    HasDerivAt (fun r : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v r h z X k)
      (((-2 * sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
          (parameter q branch) (x - z) * pulseLayerClock q branch (v + h - z)) *
          angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
        onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
          ((deriv (fun d : ℝ => angularMean q branch d X k)
            (Real.arcosh (invariant h x (x - z))) /
            (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
            (-(Real.tanh x + Real.tanh (x - z)) * (invariant h x (x - z) - 1))) +
        (parameter q branch * (2 * radialLiftSecond (physicalRate q branch) 0 amp 1
          (x - z)) * pulseLayerClock q branch (v + h - z)) *
          D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k +
        onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
          ((deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
            (Real.arcosh (invariant h x (x - z))) /
            (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
            (-(Real.tanh x + Real.tanh (x - z)) * (invariant h x (x - z) - 1)))) / 2) x := by
  have hresponse := pulseLayer_onsetResponse_ingoing_hasDerivAt q branch amp v x h z
  have hsource := pulseLayer_onsetSource_ingoing_hasDerivAt q branch amp v x h z
  have hangular := pulseLayer_fullAngular_directInvariant_hasDerivAt q branch h x z X k hz
  have hnative := pulseLayer_nativeAngular_directInvariant_hasDerivAt q h x z X k hz
  unfold pulseLayerDirectCircleKernel
  rw [if_pos hz.le]
  convert! ((hresponse.mul hangular).add (hsource.mul hnative)).div_const (2 : ℂ) using 1
  ring

/-- Closed-direct-cone derivative formula for the literal circle face.  The
characteristic quotients are totalized only at the physical edge, where the
invariant derivative vanishes identically; this is an exact equality, not an
extension of the kernel into the off-cone chart. -/
theorem pulseLayerDirectCircleKernel_ingoing_hasDerivAt_closed
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x h z X k : ℝ) (hz : |z| ≤ h) :
    HasDerivAt (fun r : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v r h z X k)
      (((-2 * sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
          (parameter q branch) (x - z) * pulseLayerClock q branch (v + h - z)) *
          angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
        onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
          (deriv (fun d : ℝ => angularMean q branch d X k)
            (Real.arcosh (invariant h x (x - z))) /
            (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
          (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) +
        (parameter q branch * (2 * radialLiftSecond (physicalRate q branch) 0 amp 1
          (x - z)) * pulseLayerClock q branch (v + h - z)) *
          D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k +
        onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
          (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
            (Real.arcosh (invariant h x (x - z))) /
            (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
          (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ)) / 2) x := by
  rcases lt_or_eq_of_le hz with hstrict | hboundary
  · have h := pulseLayerDirectCircleKernel_ingoing_hasDerivAt_strict
      q branch amp v x h z X k hstrict
    convert h using 1
    rw [(pulseLayer_directInvariant_ingoing_hasDerivAt h x z).deriv]
    ring
  · have hinvariant (r : ℝ) : invariant h r (r - z) = 1 :=
      pulseLayer_directInvariant_eq_one_of_abs_eq h r z hboundary
    have hfun : (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) =
        fun r : ℝ =>
          (onsetResponseCoefficient q branch amp (v - r + h) (r - z) *
              fullAngularField q branch ![X, Real.exp k] +
            onsetSourceCoefficient q branch amp (v - r + h) (r - z) *
              fullSquarePotential q ![X, Real.exp k]) / 2 := by
      funext r
      unfold pulseLayerDirectCircleKernel
      rw [if_pos hboundary.le, hinvariant r, Real.arcosh_one, angularMean_zero,
        D4BMNativeCircle.mean_zero]
    rw [hfun]
    have hresponse := pulseLayer_onsetResponse_ingoing_hasDerivAt q branch amp v x h z
    have hsource := pulseLayer_onsetSource_ingoing_hasDerivAt q branch amp v x h z
    have hbase : HasDerivAt (fun r : ℝ =>
        pulseLayerDirectCircleKernel q branch amp v r h z X k)
        ((deriv (fun r : ℝ => onsetResponseCoefficient q branch amp (v - r + h)
            (r - z)) x * fullAngularField q branch ![X, Real.exp k] +
          deriv (fun r : ℝ => onsetSourceCoefficient q branch amp (v - r + h)
            (r - z)) x * fullSquarePotential q ![X, Real.exp k]) / 2) x := by
      rw [hfun]
      simpa only [hresponse.deriv, hsource.deriv] using
        ((hresponse.mul_const (fullAngularField q branch ![X, Real.exp k])).add
          (hsource.mul_const (fullSquarePotential q ![X, Real.exp k]))).div_const (2 : ℂ)
    have hbase' : HasDerivAt (fun r : ℝ =>
        (onsetResponseCoefficient q branch amp (v - r + h) (r - z) *
            fullAngularField q branch ![X, Real.exp k] +
          onsetSourceCoefficient q branch amp (v - r + h) (r - z) *
            fullSquarePotential q ![X, Real.exp k]) / 2)
        ((deriv (fun r : ℝ => onsetResponseCoefficient q branch amp (v - r + h)
            (r - z)) x * fullAngularField q branch ![X, Real.exp k] +
          deriv (fun r : ℝ => onsetSourceCoefficient q branch amp (v - r + h)
            (r - z)) x * fullSquarePotential q ![X, Real.exp k]) / 2) x := by
      rw [← hfun]
      exact hbase
    convert hbase' using 1
    rw [hresponse.deriv, hsource.deriv, hinvariant x, Real.arcosh_one,
      angularMean_zero, D4BMNativeCircle.mean_zero,
      (pulseLayer_directInvariant_ingoing_hasDerivAt h x z).deriv]
    norm_num
    ring

/-- Literal pointwise cap coefficient of the direct circle face.  This is a
definition of the full/source endpoint expression, not an assumed boundary
condition. -/
def pulseLayerDirectCapLimitDensity (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v h z X k : ℝ) : ℂ :=
  if |z| ≤ h then
    ((Real.exp (-2 * z) : ℂ) / 2) * pulseLayerClock q branch (v + h - z) *
      (-2 * seedHorizonProfile q branch amp 1 * fullAngularField q branch ![X, Real.exp k] +
        parameter q branch * sourceHorizonProfile (physicalRate q branch) amp 1 1 *
          fullSquarePotential q ![X, Real.exp k]) / 2
  else 0

/-- **Strict-cone literal direct normal trace.**  The normal derivative of
the full undecomposed direct circle face is exactly twice its displayed
value-layer cap density.  The proof retains the angular Leibniz terms and
proves their first-scale limit is zero from the actual even circle germs. -/
theorem pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_strict
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z X k : ℝ) (hz : |z| < h) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 (2 * pulseLayerDirectCapLimitDensity q branch amp v h z X k)) := by
  have hradius := pulseLayer_directRadius_tendsto h z hz.le
  have hangular := ((angularMean_smooth q branch X k).continuous.continuousAt.tendsto.comp
    hradius)
  rw [angularMean_zero] at hangular
  have hnative :=
    ((D4BMNativeCircle.mean_radial_smooth q X k).continuous.continuousAt.tendsto.comp hradius)
  rw [D4BMNativeCircle.mean_zero] at hnative
  have hresponse := (pulseLayer_onsetResponse_ingoing_normal_div_capScale_tendsto
    q branch amp v h z).mul hangular
  have hsource := (pulseLayer_onsetSource_ingoing_normal_div_capScale_tendsto
    q branch amp v h z).mul hnative
  have hresponseAngular := pulseLayer_responseAngular_normal_div_capScale_tendsto_zero
    q branch amp v h z X k hz
  have hsourceAngular := pulseLayer_sourceAngular_normal_div_capScale_tendsto_zero
    q branch amp v h z X k hz
  rw [show (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) =
      fun x : ℝ =>
        ((deriv (fun r : ℝ =>
          onsetResponseCoefficient q branch amp (v - r + h) (r - z)) x /
            (capScale x : ℂ)) *
          angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
        onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
          (deriv (fun d : ℝ => angularMean q branch d X k)
            (Real.arcosh (invariant h x (x - z))) /
            (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
          (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) /
            (capScale x : ℂ) +
        (deriv (fun r : ℝ =>
          onsetSourceCoefficient q branch amp (v - r + h) (r - z)) x /
            (capScale x : ℂ)) *
          D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k +
        onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
          (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
            (Real.arcosh (invariant h x (x - z))) /
            (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)) *
          (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) /
            (capScale x : ℂ)) / 2 by
        funext x
        rw [(pulseLayerDirectCircleKernel_ingoing_hasDerivAt_strict
          q branch amp v x h z X k hz).deriv]
        have hcap : (capScale x : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold capScale; positivity))
        field_simp [hcap]
        ring]
  have hwhole := (((hresponse.add hresponseAngular).add hsource).add
    hsourceAngular).div_const (2 : ℂ)
  convert hwhole using 1 <;> simp only [pulseLayerDirectCapLimitDensity, if_pos hz.le] <;>
    ring

/-- **Boundary-cone literal direct normal trace.**  On either characteristic
edge the actual invariant is identically one, so the circle means are
constant and the two retained source jets give the same doubled cap density. -/
theorem pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_boundary
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z X k : ℝ) (hz : |z| = h) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 (2 * pulseLayerDirectCapLimitDensity q branch amp v h z X k)) := by
  have hinvariant (r : ℝ) : invariant h r (r - z) = 1 :=
    pulseLayer_directInvariant_eq_one_of_abs_eq h r z hz
  have hcone : |z| ≤ h := hz.le
  have hfun : (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) =
      fun r : ℝ =>
        (onsetResponseCoefficient q branch amp (v - r + h) (r - z) *
            fullAngularField q branch ![X, Real.exp k] +
          onsetSourceCoefficient q branch amp (v - r + h) (r - z) *
            fullSquarePotential q ![X, Real.exp k]) / 2 := by
    funext r
    unfold pulseLayerDirectCircleKernel
    rw [if_pos hcone, hinvariant r, Real.arcosh_one, angularMean_zero,
      D4BMNativeCircle.mean_zero]
  have hderiv (x : ℝ) : HasDerivAt
      (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k)
      ((deriv (fun r : ℝ =>
          onsetResponseCoefficient q branch amp (v - r + h) (r - z)) x *
          fullAngularField q branch ![X, Real.exp k] +
        deriv (fun r : ℝ =>
          onsetSourceCoefficient q branch amp (v - r + h) (r - z)) x *
          fullSquarePotential q ![X, Real.exp k]) / 2) x := by
    rw [hfun]
    have hresponse := pulseLayer_onsetResponse_ingoing_hasDerivAt q branch amp v x h z
    have hsource := pulseLayer_onsetSource_ingoing_hasDerivAt q branch amp v x h z
    simpa only [hresponse.deriv, hsource.deriv] using
      ((hresponse.mul_const (fullAngularField q branch ![X, Real.exp k])).add
        (hsource.mul_const (fullSquarePotential q ![X, Real.exp k]))).div_const (2 : ℂ)
  rw [show (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) =
      fun x : ℝ =>
        ((deriv (fun r : ℝ =>
          onsetResponseCoefficient q branch amp (v - r + h) (r - z)) x /
          (capScale x : ℂ)) * fullAngularField q branch ![X, Real.exp k] +
        (deriv (fun r : ℝ =>
          onsetSourceCoefficient q branch amp (v - r + h) (r - z)) x /
          (capScale x : ℂ)) * fullSquarePotential q ![X, Real.exp k]) / 2 by
        funext x
        rw [(hderiv x).deriv]
        have hcap : (capScale x : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold capScale; positivity))
        field_simp [hcap]
        ring]
  have hresponse := (pulseLayer_onsetResponse_ingoing_normal_div_capScale_tendsto
    q branch amp v h z).mul_const (fullAngularField q branch ![X, Real.exp k])
  have hsource := (pulseLayer_onsetSource_ingoing_normal_div_capScale_tendsto
    q branch amp v h z).mul_const (fullSquarePotential q ![X, Real.exp k])
  have hwhole := (hresponse.add hsource).div_const (2 : ℂ)
  convert hwhole using 1 <;> simp only [pulseLayerDirectCapLimitDensity, if_pos hcone] <;>
    ring

/-- The literal direct circle face has its doubled cap normal density on the
entire closed direct cone, including both physical characteristic edges. -/
theorem pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z X k : ℝ) (hz : |z| ≤ h) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 (2 * pulseLayerDirectCapLimitDensity q branch amp v h z X k)) := by
  rcases lt_or_eq_of_le hz with hstrict | hboundary
  · exact pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_strict
      q branch amp v h z X k hstrict
  · exact pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_boundary
      q branch amp v h z X k hboundary

/-- Outside the literal direct cone both the face and its normal derivative
are identically zero; this is the complementary pointwise branch of the
closed-cone normal trace. -/
theorem pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_offCone
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z X k : ℝ) (hz : ¬ |z| ≤ h) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 (2 * pulseLayerDirectCapLimitDensity q branch amp v h z X k)) := by
  have hzero : (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) =
      fun _ : ℝ => 0 := by
    funext r
    simp only [pulseLayerDirectCircleKernel, if_neg hz, zero_div]
  rw [show (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) = fun _ : ℝ => 0 by
        funext x
        rw [hzero]
        simp]
  simpa only [pulseLayerDirectCapLimitDensity, if_neg hz, mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atBot (𝓝 0))

/-- Pointwise literal direct-circle normal trace on every co-moving layer
point.  This is the completed local normal calculation needed before the
remaining noncompact action/interchange problem. -/
theorem pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_all
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v h z X k : ℝ) :
    Tendsto (fun x : ℝ =>
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 (2 * pulseLayerDirectCapLimitDensity q branch amp v h z X k)) := by
  by_cases hz : |z| ≤ h
  · exact pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto
      q branch amp v h z X k hz
  · exact pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_offCone
      q branch amp v h z X k hz

/-- Exact cap-scale realization of the undecomposed full direct circle face.
The bracket retains both the actual full angular mean and the native
half-square mean; no Goursat term, image term, or horizon profile is replaced
by a model value. -/
theorem pulseLayerDirectCircleKernel_scaled (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x h z X k : ℝ) :
    pulseLayerDirectCircleKernel q branch amp v x h z X k / (capScale x : ℂ) =
      (if |z| ≤ h then
        ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
          pulseLayerClock q branch (v + h - z) *
          (-2 * seedHorizonProfile q branch amp (radialUnit (x - z)) *
              angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
            parameter q branch * sourceHorizonProfile (physicalRate q branch) amp 1
              (radialUnit (x - z)) *
              D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k) / 2
        else 0) := by
  have hcap : (capScale x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by
      unfold capScale
      positivity))
  by_cases hz : |z| ≤ h
  · simp only [pulseLayerDirectCircleKernel, if_pos hz]
    rw [onsetAngularMean_eq]
    calc
      (onsetResponseCoefficient q branch amp (v - x + h) (x - z) *
          angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
        onsetSourceCoefficient q branch amp (v - x + h) (x - z) *
          D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k) / 2 /
          (capScale x : ℂ) =
          ((onsetResponseCoefficient q branch amp (v - x + h) (x - z) /
              (capScale x : ℂ)) *
              angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
            (onsetSourceCoefficient q branch amp (v - x + h) (x - z) /
              (capScale x : ℂ)) *
              D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k) / 2 := by
            field_simp [hcap]
            ring
      _ = ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
          pulseLayerClock q branch (v + h - z) *
          (-2 * seedHorizonProfile q branch amp (radialUnit (x - z)) *
              angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
            parameter q branch * sourceHorizonProfile (physicalRate q branch) amp 1
              (radialUnit (x - z)) *
              D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k) / 2 := by
            rw [pulseLayer_onsetResponse_scaled, pulseLayer_onsetSource_scaled]
            ring
  · simp only [pulseLayerDirectCircleKernel, if_neg hz, zero_div]

/-- The actual direct full-circle density on the fixed original clock strip.
It is only a coordinate packaging of the literal face, introduced so the
action-level DCT has a single two-variable integrand. -/
def pulseLayerDirectFixedClockDensity (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  pulseLayerDirectCircleKernel q branch amp v x p.1 (v + p.1 - p.2) X k

/-- Actual normal derivative of the fixed-clock literal direct density.  This
is a coordinate packaging only; no derivative is passed through an integral
in this definition. -/
def pulseLayerDirectFixedClockNormalDensity (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun r : ℝ =>
    pulseLayerDirectFixedClockDensity q branch amp v r X k p) x

/-- The corresponding literal cap-limit density on the same fixed clock
domain. -/
def pulseLayerDirectCapLimitFixedClockDensity (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  pulseLayerDirectCapLimitDensity q branch amp v p.1 (v + p.1 - p.2) X k

/-- Above the fixed onset transition, the exact direct fixed-clock density
already vanishes at every finite ingoing depth. -/
theorem pulseLayerDirectFixedClockDensity_eq_zero_of_one_lt
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) (p : ℝ × ℝ)
    (hv : 1 < v) (hu : p.2 ∈ Set.Icc (0 : ℝ) 1) :
    pulseLayerDirectFixedClockDensity q branch amp v x X k p = 0 := by
  unfold pulseLayerDirectFixedClockDensity
  exact pulseLayerDirectCircleKernel_fixedClock_eq_zero_of_one_lt
    q branch amp v x p.1 p.2 X k hv hu

/-- The direct normal density vanishes identically at late fixed clock,
before the cap scaling or integration. -/
theorem pulseLayerDirectFixedClockNormalDensity_eq_zero_of_one_lt
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) (p : ℝ × ℝ)
    (hv : 1 < v) (hu : p.2 ∈ Set.Icc (0 : ℝ) 1) :
    pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p = 0 := by
  unfold pulseLayerDirectFixedClockNormalDensity
  have hzero : (fun r : ℝ =>
      pulseLayerDirectFixedClockDensity q branch amp v r X k p) = fun _ => 0 := by
    funext r
    exact pulseLayerDirectFixedClockDensity_eq_zero_of_one_lt
      q branch amp v r X k p hv hu
  rw [hzero]
  simp

/-- Both finite-depth direct actions are exactly absent after the original
clock leaves its unit onset strip.  This removes the direct-pulse premise from
the literal B2 cap/contact comparison before any noncompact limit. -/
theorem pulseLayerDirectFixedClockActions_eq_zero_of_one_lt
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) (hv : 1 < v) :
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
      pulseLayerDirectFixedClockDensity q branch amp v x X k p) = 0 ∧
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
      pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p) = 0 := by
  constructor
  · calc
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectFixedClockDensity q branch amp v x X k p) =
          ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1, 0 := by
        apply MeasureTheory.setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Icc)
        intro p hp
        exact pulseLayerDirectFixedClockDensity_eq_zero_of_one_lt
          q branch amp v x X k p hv hp.2
      _ = 0 := by simp
  · calc
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p) =
          ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1, 0 := by
        apply MeasureTheory.setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Icc)
        intro p hp
        exact pulseLayerDirectFixedClockNormalDensity_eq_zero_of_one_lt
          q branch amp v x X k p hv hp.2
      _ = 0 := by simp

/-- Late-time support extinction for the literal direct cap coefficient.
The proof-chain consequence is sharp: the full fixed-clock direct normal
action contributes nothing once `v > 1`; HB B2 then reduces from a
noncompact direct-plus-cap comparison to the literal combined-cap/QNM-contact
comparison.  This is an exact incompatibility of the retained direct cone
with the original clock strip, not a decay estimate or a limiting exchange. -/
theorem pulseLayerDirectCapLimitFixedClockDensity_eq_zero_of_one_lt
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (p : ℝ × ℝ)
    (hv : 1 < v) (hu : p.2 ∈ Set.Icc (0 : ℝ) 1) :
    pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p = 0 := by
  unfold pulseLayerDirectCapLimitFixedClockDensity pulseLayerDirectCapLimitDensity
  have hcone : ¬ |v + p.1 - p.2| ≤ p.1 := by
    intro h
    have hright := (abs_le.mp h).2
    linarith [hu.2]
  simp only [hcone, if_false]

/-- The late literal direct normal action vanishes before any QNM comparison.
It packages the pointwise direct-cone/clock incompatibility over the exact
two-dimensional action domain used by the cyclic Peierls realization. -/
theorem pulseLayerDirectCapLimitFixedClockNormalAction_eq_zero_of_one_lt
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (hv : 1 < v) :
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
      2 * pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p) = 0 := by
  calc
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        2 * pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p) =
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1, 0 := by
      apply MeasureTheory.setIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Icc)
      intro p hp
      change 2 * pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p = 0
      rw [pulseLayerDirectCapLimitFixedClockDensity_eq_zero_of_one_lt
        q branch amp v X k p hv hp.2]
      ring
    _ = 0 := by simp

/-- The literal fixed-clock normal density is measurable.  Its formula is
the closed-cone four-term derivative: the quotient terms are totalized at the
characteristic edge, where their invariant-derivative multiplier is exactly
zero. -/
theorem pulseLayerDirectFixedClockNormalDensity_measurable (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x X k : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p) := by
  let z : ℝ × ℝ → ℝ := fun p => v + p.1 - p.2
  let y : ℝ × ℝ → ℝ := fun p => x - z p
  have hz : Continuous z := by
    dsimp only [z]
    fun_prop
  have hy : Continuous y := by
    dsimp only [y]
    exact continuous_const.sub hz
  have hcone : MeasurableSet {p : ℝ × ℝ | |z p| ≤ p.1} :=
    (isClosed_le hz.abs continuous_fst).measurableSet
  have hinvariant : Continuous (fun p : ℝ × ℝ => invariant p.1 x (y p)) := by
    unfold invariant
    exact ((Real.continuous_cosh.comp continuous_fst).add
      ((Real.continuous_sinh.comp hy).const_mul (Real.sinh x))).div
      ((Real.continuous_cosh.comp hy).const_mul (Real.cosh x))
      (fun p => mul_ne_zero (Real.cosh_pos x).ne' (Real.cosh_pos (y p)).ne')
  have hradius : Continuous (fun p : ℝ × ℝ =>
      Real.arcosh (max 1 (invariant p.1 x (y p)))) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max hinvariant)
      (fun p => le_max_left 1 (invariant p.1 x (y p)))
  have hseed1 : Continuous (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
      (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (sourceSeedFieldFirst_hasDerivAt (physicalRate q branch) 0 amp 1
        (parameter q branch) t).continuousAt)
  have hlift1 : Continuous (radialLiftFirst (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (radialLiftFirst_hasDerivAt (physicalRate q branch) 0 amp 1 t).continuousAt)
  have hseed2 : Continuous (sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
      (parameter q branch)) :=
    pulseLayer_sourceSeedSecond_continuous (physicalRate q branch) 0 amp 1
      (parameter q branch)
  have hlift2 : Continuous (radialLiftSecond (physicalRate q branch) 0 amp 1) :=
    pulseLayer_radialLiftSecond_continuous (physicalRate q branch) 0 amp 1
  have hclock : Continuous (fun p : ℝ × ℝ => pulseLayerClock q branch p.2) :=
    (pulseLayerClock_continuous q branch).comp continuous_snd
  have hfull : Continuous (fun p : ℝ × ℝ =>
      angularMean q branch (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k) :=
    (angularMean_smooth q branch X k).continuous.comp hradius
  have hnative : Continuous (fun p : ℝ × ℝ =>
      D4BMNativeCircle.mean q (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k) :=
    (D4BMNativeCircle.mean_radial_smooth q X k).continuous.comp hradius
  have hfullJet : Continuous (deriv (fun d : ℝ => angularMean q branch d X k)) :=
    (contDiff_infty_iff_deriv.mp (angularMean_smooth q branch X k)).2.continuous
  have hnativeJet : Continuous (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)) :=
    (contDiff_infty_iff_deriv.mp (D4BMNativeCircle.mean_radial_smooth q X k)).2.continuous
  have hsinh : Continuous (fun p : ℝ × ℝ =>
      (Real.sinh (Real.arcosh (max 1 (invariant p.1 x (y p)))) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sinh.comp hradius)
  have hfullQuot : Measurable (fun p : ℝ × ℝ =>
      deriv (fun d : ℝ => angularMean q branch d X k)
        (Real.arcosh (max 1 (invariant p.1 x (y p)))) /
        (Real.sinh (Real.arcosh (max 1 (invariant p.1 x (y p)))) : ℂ)) :=
    ((hfullJet.comp hradius).measurable).div hsinh.measurable
  have hnativeQuot : Measurable (fun p : ℝ × ℝ =>
      deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
        (Real.arcosh (max 1 (invariant p.1 x (y p)))) /
        (Real.sinh (Real.arcosh (max 1 (invariant p.1 x (y p)))) : ℂ)) :=
    ((hnativeJet.comp hradius).measurable).div hsinh.measurable
  have hnormalReal : Continuous (fun p : ℝ × ℝ =>
      -(Real.tanh x + Real.tanh (y p)) * (invariant p.1 x (y p) - 1)) := by
    exact ((continuous_const.add (Real.continuous_tanh.comp hy)).neg.mul
      (hinvariant.sub continuous_const))
  have hnormal : Continuous (fun p : ℝ × ℝ =>
      (-(Real.tanh x + Real.tanh (y p)) * (invariant p.1 x (y p) - 1) : ℂ)) :=
    Complex.continuous_ofReal.comp hnormalReal
  have hresponseSecond : Continuous (fun p : ℝ × ℝ =>
      -2 * sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
        (parameter q branch) (y p) * pulseLayerClock q branch p.2) :=
    (continuous_const.mul (hseed2.comp hy)).mul hclock
  have hsourceSecond : Continuous (fun p : ℝ × ℝ =>
      parameter q branch * (2 * radialLiftSecond (physicalRate q branch) 0 amp 1
        (y p)) * pulseLayerClock q branch p.2) :=
    (continuous_const.mul ((hlift2.comp hy).const_mul 2)).mul hclock
  have hresponseFirst : Continuous (fun p : ℝ × ℝ =>
      -2 * sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
        (parameter q branch) (y p) * pulseLayerClock q branch p.2) :=
    (continuous_const.mul (hseed1.comp hy)).mul hclock
  have hsourceFirst : Continuous (fun p : ℝ × ℝ =>
      parameter q branch * (2 * radialLiftFirst (physicalRate q branch) 0 amp 1
        (y p)) * pulseLayerClock q branch p.2) :=
    (continuous_const.mul ((hlift1.comp hy).const_mul 2)).mul hclock
  have hvalue : Measurable (fun p : ℝ × ℝ =>
      ((hresponseSecond p *
          angularMean q branch (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k +
        hresponseFirst p *
          (deriv (fun d : ℝ => angularMean q branch d X k)
            (Real.arcosh (max 1 (invariant p.1 x (y p)))) /
            (Real.sinh (Real.arcosh (max 1 (invariant p.1 x (y p)))) : ℂ)) *
          (-(Real.tanh x + Real.tanh (y p)) * (invariant p.1 x (y p) - 1) : ℂ) +
        hsourceSecond p *
          D4BMNativeCircle.mean q (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k +
        hsourceFirst p *
          (deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
            (Real.arcosh (max 1 (invariant p.1 x (y p)))) /
            (Real.sinh (Real.arcosh (max 1 (invariant p.1 x (y p)))) : ℂ)) *
          (-(Real.tanh x + Real.tanh (y p)) * (invariant p.1 x (y p) - 1) : ℂ)) / 2) :=
    (((hresponseSecond.mul hfull).measurable.add
      ((hresponseFirst.measurable.mul hfullQuot).mul hnormal.measurable)).add
        (hsourceSecond.mul hnative).measurable).add
          ((hsourceFirst.measurable.mul hnativeQuot).mul hnormal.measurable) |>.div_const 2
  have hite := Measurable.ite hcone hvalue measurable_const
  convert hite using 1
  funext p
  by_cases hp : |z p| ≤ p.1
  · have hcausal : 1 ≤ invariant p.1 x (y p) := by
      apply invariant_causal
      refine ⟨p.1, x, y p, ?_⟩
      dsimp only [y]
      have hxy : x - (x - z p) = z p := by ring
      rwa [hxy]
    have hderiv := pulseLayerDirectCircleKernel_ingoing_hasDerivAt_closed
      q branch amp v x p.1 (z p) X k hp
    unfold pulseLayerDirectFixedClockNormalDensity pulseLayerDirectFixedClockDensity
    rw [hderiv.deriv, if_pos hp,
      (onsetCoefficients_layerClock q branch amp (v - x + p.1) (x - z p)).1,
      (onsetCoefficients_layerClock q branch amp (v - x + p.1) (x - z p)).2,
      (pulseLayer_directInvariant_ingoing_hasDerivAt p.1 x (z p)).deriv,
      max_eq_right hcausal]
    have hclock' : (v - x + p.1) + (x - z p) = p.2 := by
      dsimp only [z]
      ring
    rw [hclock']
    dsimp only [z, y]
    ring
  · have hzero : (fun r : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v r p.1 (z p) X k) =
        fun _ : ℝ => 0 := by
      funext r
      simp only [pulseLayerDirectCircleKernel, if_neg hp, zero_div]
    unfold pulseLayerDirectFixedClockNormalDensity pulseLayerDirectFixedClockDensity
    rw [hzero]
    simp only [deriv_const, if_neg hp]

/-- Pointwise fixed-clock normal density realization.  The literal direct
normal density converges to twice the full direct cap density everywhere on
the integration domain, before any noncompact integral interchange. -/
theorem pulseLayerDirectFixedClockNormalDensity_scaled_tendsto
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (p : ℝ × ℝ) :
    Tendsto (fun x : ℝ =>
      pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p /
        (capScale x : ℂ)) atBot
      (𝓝 (2 * pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p)) := by
  simpa only [pulseLayerDirectFixedClockNormalDensity, pulseLayerDirectFixedClockDensity,
    pulseLayerDirectCapLimitFixedClockDensity] using
    pulseLayerDirectCircleKernel_ingoing_normal_div_capScale_tendsto_all
      q branch amp v p.1 (v + p.1 - p.2) X k

/-- The actual scaled direct face has the displayed literal pointwise cap
coefficient.  Both compact radial profiles and both actual circle means are
carried to their proved endpoints; no source or angular proxy is used. -/
theorem pulseLayerDirectCircleKernel_scaled_tendsto (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v h z X k : ℝ) :
    Tendsto (fun x : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v x h z X k / (capScale x : ℂ)) atBot
      (𝓝 (pulseLayerDirectCapLimitDensity q branch amp v h z X k)) := by
  by_cases hz : |z| ≤ h
  · have hscale := pulseLayer_direct_scale_tendsto z
    have hunit := radialUnit_shift_tendsto_atBot_one z
    have hseed := (seedHorizonProfile_continuousAt_one q branch amp).tendsto.comp hunit
    have hsource := (sourceHorizonProfile_continuousAt_one q branch amp).tendsto.comp hunit
    have hradius := pulseLayer_directRadius_tendsto h z hz
    have hangular :=
      ((angularMean_smooth q branch X k).continuous.continuousAt.tendsto.comp hradius)
    have hnative :=
      ((D4BMNativeCircle.mean_radial_smooth q X k).continuous.continuousAt.tendsto.comp hradius)
    rw [angularMean_zero] at hangular
    rw [D4BMNativeCircle.mean_zero] at hnative
    have hfirst := ((hseed.const_mul (-2 : ℂ)).mul hangular)
    have hsecond := ((hsource.const_mul (parameter q branch)).mul hnative)
    have hbracket := hfirst.add hsecond
    have hwhole := ((hscale.mul (tendsto_const_nhds (x :=
      pulseLayerClock q branch (v + h - z)))).mul hbracket).div_const (2 : ℂ)
    rw [show (fun x : ℝ =>
        pulseLayerDirectCircleKernel q branch amp v x h z X k / (capScale x : ℂ)) =
        fun x : ℝ => ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
          pulseLayerClock q branch (v + h - z) *
          (-2 * seedHorizonProfile q branch amp (radialUnit (x - z)) *
              angularMean q branch (Real.arcosh (invariant h x (x - z))) X k +
            parameter q branch * sourceHorizonProfile (physicalRate q branch) amp 1
              (radialUnit (x - z)) *
              D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k) / 2 by
          funext x
          rw [pulseLayerDirectCircleKernel_scaled, if_pos hz]]
    simpa [pulseLayerDirectCapLimitDensity, hz] using hwhole
  · rw [show (fun x : ℝ =>
        pulseLayerDirectCircleKernel q branch amp v x h z X k / (capScale x : ℂ)) =
        fun _ : ℝ => 0 by
          funext x
          rw [pulseLayerDirectCircleKernel, if_neg hz]
          simp]
    simpa [pulseLayerDirectCapLimitDensity, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atBot (𝓝 0))

/-- **Direct fixed-clock action DCT.**  After finite-depth image elimination,
the complete literal direct circle action has its cap-scale limit under the
actual two-dimensional integral.  The limiting integrand retains both horizon
profiles, full angular field, and native square field.  This closes the
value-level noncompact pulse premise; differentiating this action remains a
separate normal-trace problem. -/
theorem pulseLayerDirectFixedClockAction_scaled_tendsto (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x : ℝ =>
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectFixedClockDensity q branch amp v x X k p / (capScale x : ℂ)) atBot
      (𝓝 (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p)) := by
  obtain ⟨B, hB, hmajorant⟩ :=
    pulseLayerDirectCircleKernel_scaled_majorant q branch amp v X k
  let S : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1
  let F : ℝ → ℝ × ℝ → ℂ := fun x p =>
    pulseLayerDirectFixedClockDensity q branch amp v x X k p / (capScale x : ℂ)
  let L : ℝ × ℝ → ℂ := pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k
  let G : ℝ × ℝ → ℝ := fun p => B * Real.exp ((decayExponent q - 2) * p.1)
  have hmeas : ∀ᶠ x : ℝ in atBot,
      AEStronglyMeasurable (F x) (volume.restrict S) :=
    Eventually.of_forall (fun x =>
      ((pulseLayerDirectCircleKernel_fixedClock_measurable q branch amp v x X k).div
        measurable_const).aestronglyMeasurable)
  have hbound : ∀ᶠ x : ℝ in atBot, ∀ᵐ p ∂volume.restrict S,
      ‖F x p‖ ≤ G p := by
    filter_upwards [eventually_lt_atBot (0 : ℝ), eventually_lt_atBot (v - 1),
      eventually_lt_atBot ((v - 1) / 2)] with x hx0 hxsource himage
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Icc)] with p hp
    exact hmajorant x p.1 p.2 hx0.le hxsource himage hp.1 hp.2
  have hG : Integrable G (volume.restrict S) := by
    dsimp only [G, S]
    exact pulseLayerDirectCapMajorant_integrable q B
  have hpoint : ∀ᵐ p ∂volume.restrict S,
      Tendsto (fun x : ℝ => F x p) atBot (𝓝 (L p)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Icc)] with p hp
    simpa only [F, L, pulseLayerDirectFixedClockDensity,
      pulseLayerDirectCapLimitFixedClockDensity] using
      pulseLayerDirectCircleKernel_scaled_tendsto q branch amp v p.1 (v + p.1 - p.2) X k
  have hlimit := tendsto_integral_filter_of_dominated_convergence G hmeas hbound hG hpoint
  simpa only [F, L, S] using hlimit

/-- The direct layer samples its fixed original onset clock at `v + h - z`.
This is an exact identity, keeping the radial source coordinate `x-z`. -/
theorem pulseLayerKernel_direct_clock (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) :
    fullSourceOnsetPulse q branch amp (v - x + h) (x - z) ![X, Real.exp k] =
      -2 * sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
        (parameter q branch) (x - z) *
        pulseLayerClock q branch (v + h - z) * fullAngularField q branch ![X, Real.exp k] +
      2 * parameter q branch * radialLiftFirst (physicalRate q branch) 0 amp 1
        (x - z) *
        pulseLayerClock q branch (v + h - z) * fullSquarePotential q ![X, Real.exp k] := by
  have hclock : (v - x + h) + (x - z) = v + h - z := by ring
  unfold fullSourceOnsetPulse originalSourceOnsetPulse pulseLayerClock
  rw [hclock]
  ring

/-- Exact cap-scale factorization of the direct pulse source.  The displayed
`exp (2 * (x-z)) / capScale x` is why this layer survives the cap scale. -/
theorem pulseLayer_direct_scaled_factor (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v x h z X k : ℝ) :
    fullSourceOnsetPulse q branch amp (v - x + h) (x - z) ![X, Real.exp k] /
        (capScale x : ℂ) =
      ((Real.exp (2 * (x - z)) : ℂ) / (capScale x : ℂ)) *
        pulseLayerClock q branch (v + h - z) *
        (-2 * seedHorizonProfile q branch amp (radialUnit (x - z)) *
            fullAngularField q branch ![X, Real.exp k] +
          parameter q branch * sourceHorizonProfile (physicalRate q branch) amp 1
            (radialUnit (x - z)) * fullSquarePotential q ![X, Real.exp k]) := by
  rw [pulseLayerKernel_direct_clock, seedFirst_horizon]
  rw [show 2 * parameter q branch * radialLiftFirst (physicalRate q branch) 0 amp 1
      (x - z) * pulseLayerClock q branch (v + h - z) *
      fullSquarePotential q ![X, Real.exp k] =
      parameter q branch * (2 * radialLiftFirst (physicalRate q branch) 0 amp 1 (x - z)) *
        pulseLayerClock q branch (v + h - z) * fullSquarePotential q ![X, Real.exp k] by ring,
    radialLiftFirst_horizon]
  ring

/-- The literal direct-face native radial current has a strict decay-compatible
growth rate.  This is the noncompact input required for the normal derivative
majorant; it comes from the original source Laplacian and its Volterra current,
not from a modal replacement of the pulse face. -/
theorem pulseLayer_argumentFirst_strict_growth (q : XiZeroCopy) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Ioi (1 : ℝ),
      ‖D4BMNativeCircle.argumentFirst q z X k‖ ≤
        C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q *
          Real.arcosh z.val) := by
  exact D4BMNativeCircle.argumentFirst_global_growth_at q X k
    (D4BMFullAngularGrowth.strictGrowthExponent q)
    (D4BMFullAngularGrowth.strictGrowthExponent_bounds q).1

/-- The literal direct-face full-response radial current has the same strict
decay-compatible rate.  Its characteristic edge is retained through the
actual circle mean's parity, while its tail is the constructed response tail. -/
theorem pulseLayer_fullArgumentFirst_strict_growth (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Ioi (1 : ℝ),
      ‖deriv (fun d : ℝ => angularMean q branch d X k) (Real.arcosh z.val) /
        (Real.sinh (Real.arcosh z.val) : ℂ)‖ ≤
        C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q *
          Real.arcosh z.val) := by
  obtain ⟨C, hC, hbound⟩ :=
    D4BMFullAngularCurrent.angularMean_sinh_ratio_strict_growth q branch X k
  refine ⟨C, hC, ?_⟩
  intro z
  exact hbound (Real.arcosh z.val) (Real.arcosh_pos z.property)

private theorem pulseLayer_directRadius_le_time (h x z : ℝ) (hz : |z| ≤ h) :
    Real.arcosh (invariant h x (x - z)) ≤ h := by
  have hh : 0 ≤ h := (abs_nonneg z).trans hz
  have hcausal : 1 ≤ invariant h x (x - z) := by
    apply invariant_causal
    refine ⟨h, x, x - z, ?_⟩
    simpa only [sub_sub_cancel_left] using hz
  let d := Real.arcosh (invariant h x (x - z))
  have hd : 0 ≤ d := by
    dsimp only [d]
    exact Real.arcosh_nonneg hcausal
  have he : Real.cosh d = invariant h x (x - z) := by
    dsimp only [d]
    exact Real.cosh_arcosh hcausal
  have hc : Real.cosh d ≤ Real.cosh h := by
    rw [he]
    exact D4BMNativeCircle.invariant_le_cosh_time h x (x - z)
  have ha := Real.cosh_le_cosh.mp hc
  simpa only [abs_of_nonneg hd, abs_of_nonneg hh] using ha

/-- The two actual circle values have one strict direct-cone envelope. -/
private theorem pulseLayer_directCircleMeans_strict_growth (q : XiZeroCopy)
    (branch : Bool) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h x z : ℝ, |z| ≤ h →
      ‖angularMean q branch (Real.arcosh (invariant h x (x - z))) X k‖ +
        ‖D4BMNativeCircle.mean q (Real.arcosh (invariant h x (x - z))) X k‖ ≤
          C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h) := by
  obtain ⟨A, hA, hfull⟩ :=
    D4BMFullAngularGrowth.angularMean_strict_growth q branch X k
  obtain ⟨B, hB, hnative⟩ :=
    D4BMFullAngularCurrent.nativeMean_strict_growth q X k
  let C := A + B
  have hC : 0 ≤ C := add_nonneg hA hB
  refine ⟨C, hC, ?_⟩
  intro h x z hz
  let d := Real.arcosh (invariant h x (x - z))
  have hd : 0 ≤ d := by
    dsimp only [d]
    have hcausal : 1 ≤ invariant h x (x - z) := by
      apply invariant_causal
      refine ⟨h, x, x - z, ?_⟩
      simpa only [sub_sub_cancel_left] using hz
    exact Real.arcosh_nonneg hcausal
  have hdh : d ≤ h := by
    dsimp only [d]
    exact pulseLayer_directRadius_le_time h x z hz
  have hstrict0 : 0 ≤ D4BMFullAngularGrowth.strictGrowthExponent q := by
    have hsource := (D4BMNativeCircle.sourceGrowthExponent_bounds q).1
    have hstrict := (D4BMFullAngularGrowth.strictGrowthExponent_bounds q).1
    linarith
  have hfull' : ‖angularMean q branch d X k‖ ≤
      A * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * d) :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hfull d hd)
  have hnative' : ‖D4BMNativeCircle.mean q d X k‖ ≤
      B * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * d) :=
    hnative d hd
  calc
    ‖angularMean q branch d X k‖ + ‖D4BMNativeCircle.mean q d X k‖ ≤
        A * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * d) +
          B * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * d) :=
      add_le_add hfull' hnative'
    _ = C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * d) := by
      dsimp only [C]
      ring
    _ ≤ C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdh hstrict0)) hC

/-- The two actual characteristic quotients have one strict envelope on the
strict direct cone.  This joins the full even-edge current with the native
Volterra current only after each has been independently controlled. -/
private theorem pulseLayer_directCircleCurrents_strict_growth (q : XiZeroCopy)
    (branch : Bool) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h x z : ℝ, |z| < h →
      ‖deriv (fun d : ℝ => angularMean q branch d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)‖ +
        ‖deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k)
          (Real.arcosh (invariant h x (x - z))) /
          (Real.sinh (Real.arcosh (invariant h x (x - z))) : ℂ)‖ ≤
          C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h) := by
  obtain ⟨A, hA, hfull⟩ := pulseLayer_fullArgumentFirst_strict_growth q branch X k
  obtain ⟨B, hB, hnative⟩ := pulseLayer_argumentFirst_strict_growth q X k
  let C := A + B
  have hC : 0 ≤ C := add_nonneg hA hB
  refine ⟨C, hC, ?_⟩
  intro h x z hz
  let I : ℝ := invariant h x (x - z)
  have hI : 1 < I := by
    dsimp only [I]
    exact pulseLayer_directInvariant_one_lt h x z hz
  have hd : 0 ≤ Real.arcosh I := Real.arcosh_nonneg hI.le
  have hdh : Real.arcosh I ≤ h := by
    dsimp only [I]
    exact pulseLayer_directRadius_le_time h x z hz.le
  have hstrict0 : 0 ≤ D4BMFullAngularGrowth.strictGrowthExponent q := by
    have hsource := (D4BMNativeCircle.sourceGrowthExponent_bounds q).1
    have hstrict := (D4BMFullAngularGrowth.strictGrowthExponent_bounds q).1
    linarith
  let zI : Ioi (1 : ℝ) := ⟨I, hI⟩
  have hfull' := hfull zI
  have hnative' := hnative zI
  change
    ‖deriv (fun d : ℝ => angularMean q branch d X k) (Real.arcosh I) /
        (Real.sinh (Real.arcosh I) : ℂ)‖ +
      ‖deriv (fun d : ℝ => D4BMNativeCircle.mean q d X k) (Real.arcosh I) /
        (Real.sinh (Real.arcosh I) : ℂ)‖ ≤ _
  calc
    _ ≤ A * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q *
          Real.arcosh I) +
        B * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q *
          Real.arcosh I) := add_le_add hfull' hnative'
    _ = C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q *
          Real.arcosh I) := by
      dsimp only [C]
      ring
    _ ≤ C * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdh hstrict0)) hC

/-- Strict-cone integrable envelope for the literal direct normal density.
All four Leibniz channels remain present: two second source jets and two
moving-radius currents.  This is the analytic majorant needed before the
fixed-clock normal DCT; characteristic edges are handled separately. -/
private theorem pulseLayerDirectCircleKernel_ingoing_normal_scaled_majorant_strict
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x h u : ℝ, x ≤ 0 → x < v - 1 → 0 < h →
      u ∈ Set.Icc (0 : ℝ) 1 → |v + h - u| < h →
      ‖deriv (fun r : ℝ =>
        pulseLayerDirectCircleKernel q branch amp v r h (v + h - u) X k) x /
          (capScale x : ℂ)‖ ≤
        B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
  obtain ⟨C2, hC2, hsecond⟩ :=
    pulseLayer_secondRadialPair_direct_decay_bound q branch amp v
  obtain ⟨C1, hC1, hfirst⟩ :=
    pulseLayer_radialPair_direct_decay_bound q branch amp v
  obtain ⟨CM, hCM, hmeans⟩ :=
    pulseLayer_directCircleMeans_strict_growth q branch X k
  obtain ⟨CJ, hCJ, hcurrents⟩ :=
    pulseLayer_directCircleCurrents_strict_growth q branch X k
  obtain ⟨CK, hCK, hclock⟩ := pulseLayerClock_bounded q branch
  let P := ‖parameter q branch‖
  let G := 2 * Real.exp (1 - v)
  let B2 := (2 + P) * CK * C2 * CM
  let B1 := (2 + P) * CK * G * C1 * CJ
  let B := B2 + B1
  have hP : 0 ≤ P := norm_nonneg _
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hB2 : 0 ≤ B2 := by dsimp only [B2]; positivity
  have hB1 : 0 ≤ B1 := by dsimp only [B1]; positivity
  have hB : 0 ≤ B := add_nonneg hB2 hB1
  refine ⟨B, hB, ?_⟩
  intro x h u hx hxsource hh hu hz
  let z := v + h - u
  let d := Real.arcosh (invariant h x (x - z))
  let S2 := sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
    (parameter q branch) (x - z)
  let L2 := 2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)
  let S1 := sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
    (parameter q branch) (x - z)
  let L1 := 2 * radialLiftFirst (physicalRate q branch) 0 amp 1 (x - z)
  let M := angularMean q branch d X k
  let N := D4BMNativeCircle.mean q d X k
  let J := deriv (fun r : ℝ => angularMean q branch r X k) d / (Real.sinh d : ℂ)
  let K := deriv (fun r : ℝ => D4BMNativeCircle.mean q r X k) d / (Real.sinh d : ℂ)
  let R : ℂ := (deriv (fun r : ℝ => invariant h r (r - z)) x : ℂ) /
    (capScale x : ℂ)
  let c := ‖pulseLayerClock q branch u‖
  let a2 := ‖S2 / (capScale x : ℂ)‖
  let b2 := ‖L2 / (capScale x : ℂ)‖
  let a1 := ‖S1‖
  let b1 := ‖L1‖
  let m := ‖M‖
  let n := ‖N‖
  let j := ‖J‖
  let l := ‖K‖
  let r := ‖R‖
  have hy : x - z < 0 := by
    dsimp only [z]
    linarith [hu.2]
  have hz' : |z| < h := by simpa only [z] using hz
  have hsecond' : a2 + b2 ≤ C2 * Real.exp (-2 * h) := by
    simpa only [a2, b2, S2, L2, z] using hsecond x h u hx hy hu
  have hfirst' : a1 + b1 ≤ C1 * Real.exp (-2 * h) := by
    simpa only [a1, b1, S1, L1, z] using hfirst x h u hx hy hu
  have hmeans' : m + n ≤ CM *
      Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h) := by
    simpa only [m, n, M, N, d] using hmeans h x z hz'.le
  have hcurrents' : j + l ≤ CJ *
      Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h) := by
    simpa only [j, l, J, K, d] using hcurrents h x z hz'
  have hc : c ≤ CK := by
    simpa only [c] using hclock u hu
  have hRreal := pulseLayer_directInvariant_normal_div_capScale_bound v x h u hu hz'.le
  have hR : r ≤ G := by
    dsimp only [r, R, G]
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by unfold capScale; positivity)]
    simpa only [abs_div, abs_of_pos (by unfold capScale; positivity)] using hRreal
  have hcr : c * r ≤ CK * G := by gcongr
  have hcap : (capScale x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold capScale; positivity))
  let T2 : ℂ := -2 * (S2 / (capScale x : ℂ)) * pulseLayerClock q branch u * M
  let T1 : ℂ := -2 * S1 * pulseLayerClock q branch u * J * R
  let T4 : ℂ := parameter q branch * (L2 / (capScale x : ℂ)) *
    pulseLayerClock q branch u * N
  let T3 : ℂ := parameter q branch * L1 * pulseLayerClock q branch u * K * R
  have hrewrite :
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
          (capScale x : ℂ) = (T2 + T1 + T4 + T3) / 2 := by
    rw [(pulseLayerDirectCircleKernel_ingoing_hasDerivAt_strict
      q branch amp v x h z X k hz').deriv]
    rw [(onsetCoefficients_layerClock q branch amp (v - x + h) (x - z)).1,
      (onsetCoefficients_layerClock q branch amp (v - x + h) (x - z)).2]
    have hclock' : (v - x + h) + (x - z) = u := by
      dsimp only [z]
      ring
    rw [hclock']
    rw [← (pulseLayer_directInvariant_ingoing_hasDerivAt h x z).deriv]
    dsimp only [T2, T1, T4, T3, R]
    field_simp [hcap]
    ring
  rw [show (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h
      (v + h - u) X k) = fun r : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v r h z X k by
        funext r
        rfl, hrewrite]
  have hT2 : ‖T2‖ = 2 * a2 * c * m := by
    dsimp only [T2, a2, c, m]
    rw [norm_mul, norm_mul, norm_mul, norm_neg]
    norm_num
    ring
  have hT4 : ‖T4‖ = P * b2 * c * n := by
    dsimp only [T4, P, b2, c, n]
    rw [norm_mul, norm_mul, norm_mul]
    ring
  have hT1 : ‖T1‖ = 2 * a1 * (c * r) * j := by
    dsimp only [T1, a1, c, r, j]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg]
    norm_num
    ring
  have hT3 : ‖T3‖ = P * b1 * (c * r) * l := by
    dsimp only [T3, P, b1, c, r, l]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    ring
  have hsecond_weighted : ‖T2‖ + ‖T4‖ ≤
      (2 + P) * c * (a2 + b2) * (m + n) := by
    rw [hT2, hT4]
    exact pulseLayer_weighted_pair_pair_bound a2 b2 m n c P
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hP
  have hcurrent_weighted : ‖T1‖ + ‖T3‖ ≤
      (2 + P) * (c * r) * (a1 + b1) * (j + l) := by
    rw [hT1, hT3]
    exact pulseLayer_weighted_pair_pair_bound a1 b1 j l (c * r) P
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hP
  have hsecond_final : ‖T2‖ + ‖T4‖ ≤ B2 *
      Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
    calc
      _ ≤ (2 + P) * CK * (C2 * Real.exp (-2 * h)) *
          (CM * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h)) := by
        calc
          _ ≤ (2 + P) * c * (a2 + b2) * (m + n) := hsecond_weighted
          _ ≤ _ := by gcongr
      _ = B2 * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
        dsimp only [B2]
        rw [← Real.exp_add]
        congr 1
        ring
  have hcurrent_final : ‖T1‖ + ‖T3‖ ≤ B1 *
      Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
    calc
      _ ≤ (2 + P) * (CK * G) * (C1 * Real.exp (-2 * h)) *
          (CJ * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h)) := by
        calc
          _ ≤ (2 + P) * (c * r) * (a1 + b1) * (j + l) := hcurrent_weighted
          _ ≤ _ := by gcongr
      _ = B1 * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
        dsimp only [B1]
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    ‖(T2 + T1 + T4 + T3) / 2‖ ≤ ‖T2 + T1 + T4 + T3‖ := by
      rw [norm_div, Complex.norm_ofNat]
      norm_num
      exact div_le_self (norm_nonneg _) (by norm_num)
    _ ≤ ‖T2‖ + ‖T1‖ + ‖T4‖ + ‖T3‖ := by
      calc
        _ ≤ ‖T2 + T1 + T4‖ + ‖T3‖ := norm_add_le _ _
        _ ≤ (‖T2 + T1‖ + ‖T4‖) + ‖T3‖ := by gcongr; exact norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ = (‖T2‖ + ‖T4‖) + (‖T1‖ + ‖T3‖) := by ring
    _ ≤ (B2 + B1) *
        Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
      rw [add_mul]
      exact add_le_add hsecond_final hcurrent_final
    _ = B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := rfl

private theorem pulseLayerDirectNormalMajorant_integrable (q : XiZeroCopy) (B : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ =>
      B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * p.1))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hh := integrableOn_exp_mul_Ioi
    (show D4BMFullAngularGrowth.strictGrowthExponent q - 2 < 0 by
      have hstrict := (D4BMFullAngularGrowth.strictGrowthExponent_bounds q).2
      have hdecay := (D4BMFullSourceAdvanced.decayExponent_bounds q).2
      linarith) 0
  have hu : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (0 : ℝ) 1) := by
    rw [integrableOn_const_iff]
    right
    rw [Real.volume_Icc]
    norm_num
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa only [mul_one] using (hh.mul_prod hu).const_mul B

/-- Boundary-cone companion to the strict normal envelope.  Here the
invariant is identically characteristic, so both moving-radius terms vanish
as identities and only the two actual second source jets remain. -/
private theorem pulseLayerDirectCircleKernel_ingoing_normal_scaled_majorant_boundary
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x h u : ℝ, x ≤ 0 → x < v - 1 → 0 < h →
      u ∈ Set.Icc (0 : ℝ) 1 → |v + h - u| = h →
      ‖deriv (fun r : ℝ =>
        pulseLayerDirectCircleKernel q branch amp v r h (v + h - u) X k) x /
          (capScale x : ℂ)‖ ≤
        B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
  obtain ⟨C2, hC2, hsecond⟩ :=
    pulseLayer_secondRadialPair_direct_decay_bound q branch amp v
  obtain ⟨CM, hCM, hmeans⟩ :=
    pulseLayer_directCircleMeans_strict_growth q branch X k
  obtain ⟨CK, hCK, hclock⟩ := pulseLayerClock_bounded q branch
  let P := ‖parameter q branch‖
  let B := (2 + P) * CK * C2 * CM
  have hP : 0 ≤ P := norm_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro x h u hx hxsource hh hu hz
  let z := v + h - u
  let S2 := sourceSeedFieldSecond (physicalRate q branch) 0 amp 1
    (parameter q branch) (x - z)
  let L2 := 2 * radialLiftSecond (physicalRate q branch) 0 amp 1 (x - z)
  let H := fullAngularField q branch ![X, Real.exp k]
  let Q := fullSquarePotential q ![X, Real.exp k]
  let a := ‖S2 / (capScale x : ℂ)‖
  let b := ‖L2 / (capScale x : ℂ)‖
  let c := ‖pulseLayerClock q branch u‖
  let m := ‖H‖
  let n := ‖Q‖
  have hy : x - z < 0 := by
    dsimp only [z]
    linarith [hu.2]
  have hz' : |z| = h := by simpa only [z] using hz
  have hsecond' : a + b ≤ C2 * Real.exp (-2 * h) := by
    simpa only [a, b, S2, L2, z] using hsecond x h u hx hy hu
  have hmeans' : m + n ≤ CM *
      Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h) := by
    have hinvariant (r : ℝ) : invariant h r (r - z) = 1 :=
      pulseLayer_directInvariant_eq_one_of_abs_eq h r z hz'
    simpa only [m, n, H, Q, hinvariant x, Real.arcosh_one,
      angularMean_zero, D4BMNativeCircle.mean_zero] using hmeans h x z hz'.le
  have hc : c ≤ CK := by simpa only [c] using hclock u hu
  have hcap : (capScale x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold capScale; positivity))
  let T2 : ℂ := -2 * (S2 / (capScale x : ℂ)) * pulseLayerClock q branch u * H
  let T4 : ℂ := parameter q branch * (L2 / (capScale x : ℂ)) *
    pulseLayerClock q branch u * Q
  have hinvariant (r : ℝ) : invariant h r (r - z) = 1 :=
    pulseLayer_directInvariant_eq_one_of_abs_eq h r z hz'
  have hfun : (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) =
      fun r : ℝ =>
        (onsetResponseCoefficient q branch amp (v - r + h) (r - z) * H +
          onsetSourceCoefficient q branch amp (v - r + h) (r - z) * Q) / 2 := by
    funext r
    unfold pulseLayerDirectCircleKernel
    rw [if_pos hz'.le, hinvariant r, Real.arcosh_one, angularMean_zero,
      D4BMNativeCircle.mean_zero]
  have hderiv :
      HasDerivAt (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k)
        ((-2 * S2 * pulseLayerClock q branch u * H +
          parameter q branch * L2 * pulseLayerClock q branch u * Q) / 2) x := by
    rw [hfun]
    have hresponse := pulseLayer_onsetResponse_ingoing_hasDerivAt q branch amp v x h z
    have hsource := pulseLayer_onsetSource_ingoing_hasDerivAt q branch amp v x h z
    have hclock' : v + h - z = u := by
      dsimp only [z]
      ring
    rw [hclock'] at hresponse hsource
    dsimp only [S2, L2]
    convert! ((hresponse.mul_const H).add (hsource.mul_const Q)).div_const (2 : ℂ) using 1
    ring
  have hrewrite :
      deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
          (capScale x : ℂ) = (T2 + T4) / 2 := by
    rw [hderiv.deriv]
    dsimp only [T2, T4]
    field_simp [hcap]
    ring
  rw [show (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h
      (v + h - u) X k) = fun r : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v r h z X k by
        funext r
        rfl, hrewrite]
  have hT2 : ‖T2‖ = 2 * a * c * m := by
    dsimp only [T2, a, c, m]
    rw [norm_mul, norm_mul, norm_mul, norm_neg]
    norm_num
    ring
  have hT4 : ‖T4‖ = P * b * c * n := by
    dsimp only [T4, P, b, c, n]
    rw [norm_mul, norm_mul, norm_mul]
    ring
  have hweighted : ‖T2‖ + ‖T4‖ ≤ (2 + P) * c * (a + b) * (m + n) := by
    rw [hT2, hT4]
    exact pulseLayer_weighted_pair_pair_bound a b m n c P
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hP
  have hfinal : ‖T2‖ + ‖T4‖ ≤ B *
      Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
    calc
      _ ≤ (2 + P) * CK * (C2 * Real.exp (-2 * h)) *
          (CM * Real.exp (D4BMFullAngularGrowth.strictGrowthExponent q * h)) := by
        calc
          _ ≤ (2 + P) * c * (a + b) * (m + n) := hweighted
          _ ≤ _ := by gcongr
      _ = B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
        dsimp only [B]
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    ‖(T2 + T4) / 2‖ ≤ ‖T2 + T4‖ := by
      rw [norm_div, Complex.norm_ofNat]
      norm_num
      exact div_le_self (norm_nonneg _) (by norm_num)
    _ ≤ ‖T2‖ + ‖T4‖ := norm_add_le _ _
    _ ≤ _ := hfinal

/-- Global literal direct normal envelope, including both characteristic
edges and the off-cone zero branch.  It is therefore suitable for DCT without
discarding any physical part of the closed direct cone. -/
private theorem pulseLayerDirectCircleKernel_ingoing_normal_scaled_majorant
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x h u : ℝ, x ≤ 0 → x < v - 1 → 0 < h →
      u ∈ Set.Icc (0 : ℝ) 1 →
      ‖deriv (fun r : ℝ =>
        pulseLayerDirectCircleKernel q branch amp v r h (v + h - u) X k) x /
          (capScale x : ℂ)‖ ≤
        B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
  obtain ⟨BS, hBS, hstrict⟩ :=
    pulseLayerDirectCircleKernel_ingoing_normal_scaled_majorant_strict q branch amp v X k
  obtain ⟨BE, hBE, hboundary⟩ :=
    pulseLayerDirectCircleKernel_ingoing_normal_scaled_majorant_boundary q branch amp v X k
  let B := BS + BE
  have hB : 0 ≤ B := add_nonneg hBS hBE
  refine ⟨B, hB, ?_⟩
  intro x h u hx hxsource hh hu
  let z := v + h - u
  by_cases hcone : |z| ≤ h
  · rcases lt_or_eq_of_le hcone with hstrictcone | hboundarycone
    · have h := hstrict x h u hx hxsource hh hu (by simpa only [z] using hstrictcone)
      calc
        ‖deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
            (capScale x : ℂ)‖ ≤
            BS * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := h
        _ ≤ B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right hBE) (Real.exp_pos _).le
    · have h := hboundary x h u hx hxsource hh hu (by simpa only [z] using hboundarycone)
      calc
        ‖deriv (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) x /
            (capScale x : ℂ)‖ ≤
            BE * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := h
        _ ≤ B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * h) := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left hBS) (Real.exp_pos _).le
  · have hzero : (fun r : ℝ => pulseLayerDirectCircleKernel q branch amp v r h z X k) =
      fun _ : ℝ => 0 := by
      funext r
      simp only [pulseLayerDirectCircleKernel, if_neg hcone, zero_div]
    rw [hzero]
    simp only [deriv_const, norm_zero]
    exact mul_nonneg hB (Real.exp_nonneg _)

/-- **Literal fixed-clock normal DCT.**  The complete direct circle normal
action reaches twice its cap density under the original two-dimensional
integral.  The majorant is the actual four-channel normal derivative; neither
the full response, native source, cone edge, nor fixed clock is replaced. -/
theorem pulseLayerDirectFixedClockNormalAction_scaled_tendsto (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x : ℝ =>
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p /
          (capScale x : ℂ)) atBot
      (𝓝 (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        2 * pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p)) := by
  obtain ⟨B, hB, hmajorant⟩ :=
    pulseLayerDirectCircleKernel_ingoing_normal_scaled_majorant q branch amp v X k
  let S : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1
  let F : ℝ → ℝ × ℝ → ℂ := fun x p =>
    pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p /
      (capScale x : ℂ)
  let L : ℝ × ℝ → ℂ := fun p =>
    2 * pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p
  let G : ℝ × ℝ → ℝ := fun p =>
    B * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * p.1)
  have hmeas : ∀ᶠ x : ℝ in atBot,
      AEStronglyMeasurable (F x) (volume.restrict S) :=
    Eventually.of_forall (fun x =>
      ((pulseLayerDirectFixedClockNormalDensity_measurable q branch amp v x X k).div
        measurable_const).aestronglyMeasurable)
  have hbound : ∀ᶠ x : ℝ in atBot, ∀ᵐ p ∂volume.restrict S,
      ‖F x p‖ ≤ G p := by
    filter_upwards [eventually_lt_atBot (0 : ℝ), eventually_lt_atBot (v - 1)] with
      x hx0 hxsource
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Icc)] with p hp
    exact hmajorant x p.1 p.2 hx0.le hxsource hp.1 hp.2
  have hG : Integrable G (volume.restrict S) := by
    dsimp only [G, S]
    exact pulseLayerDirectNormalMajorant_integrable q B
  have hpoint : ∀ᵐ p ∂volume.restrict S,
      Tendsto (fun x : ℝ => F x p) atBot (𝓝 (L p)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Icc)] with p hp
    simpa only [F, L] using
      pulseLayerDirectFixedClockNormalDensity_scaled_tendsto q branch amp v X k p
  have hlimit := tendsto_integral_filter_of_dominated_convergence G hmeas hbound hG hpoint
  simpa only [F, L, S] using hlimit

/-- On the ingoing half-line, removing the positive cap scale cannot enlarge
a norm.  This is the exact conversion from the cap-scale majorants to the
local raw bounds required for differentiation of the literal action. -/
private theorem capScale_le_one_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    capScale x ≤ 1 := by
  rw [capScale_exp_form]
  apply (div_le_iff₀ (by positivity)).mpr
  have hexp : Real.exp (2 * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

private theorem norm_le_of_norm_div_capScale_le (x : ℝ) (hx : x ≤ 0)
    {w : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hw : ‖w / (capScale x : ℂ)‖ ≤ B) : ‖w‖ ≤ B := by
  have hcap : 0 < capScale x := by
    unfold capScale
    positivity
  have hcap' : capScale x ≤ 1 := capScale_le_one_of_nonpos x hx
  have hcap_ne : (capScale x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcap.ne'
  have hrewrite : w = (w / (capScale x : ℂ)) * (capScale x : ℂ) := by
    field_simp [hcap_ne]
  calc
    ‖w‖ = ‖(w / (capScale x : ℂ)) * (capScale x : ℂ)‖ := congrArg norm hrewrite
    _ = ‖w / (capScale x : ℂ)‖ * capScale x := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcap]
    _ ≤ B * capScale x := mul_le_mul_of_nonneg_right hw hcap.le
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left hcap' hB
    _ = B := by ring

/-- The literal fixed-clock direct density is integrable at each finite cap
depth where the exact image-elimination identity applies.  This is the
unscaled form of the already constructed literal value envelope. -/
private theorem pulseLayerDirectFixedClockDensity_integrable (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x X k : ℝ) (hx : x ≤ 0)
    (hsource : x < v - 1) (himage : x < (v - 1) / 2) :
    Integrable (fun p : ℝ × ℝ =>
      pulseLayerDirectFixedClockDensity q branch amp v x X k p)
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨B, hB, hmajorant⟩ :=
    pulseLayerDirectCircleKernel_scaled_majorant q branch amp v X k
  let S : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1
  let F : ℝ × ℝ → ℂ := fun p =>
    pulseLayerDirectFixedClockDensity q branch amp v x X k p
  let G : ℝ × ℝ → ℝ := fun p =>
    B * Real.exp ((decayExponent q - 2) * p.1)
  have hG : Integrable G (volume.restrict S) := by
    dsimp only [G, S]
    exact pulseLayerDirectCapMajorant_integrable q B
  have hG_nonneg (p : ℝ × ℝ) : 0 ≤ G p := by
    dsimp only [G]
    exact mul_nonneg hB (Real.exp_pos _).le
  apply hG.mono'
    ((pulseLayerDirectCircleKernel_fixedClock_measurable q branch amp v x X k)
      .aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Icc)] with p hp
  have hscaled := hmajorant x p.1 p.2 hx hsource himage hp.1 hp.2
  exact norm_le_of_norm_div_capScale_le x hx (hG_nonneg p) (by
    simpa only [F, G, pulseLayerDirectFixedClockDensity] using hscaled)

/-- Exact Fubini identification of the product-measure direct action with
the literal iterated pulse integral.  It changes no contour, clock, source,
or cone: only the already-integrable fixed rectangular action is reassociated. -/
private theorem pulseLayerDirectFixedClockAction_eq_iterated (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x X k : ℝ) (hx : x ≤ 0)
    (hsource : x < v - 1) (himage : x < (v - 1) / 2) :
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
      pulseLayerDirectFixedClockDensity q branch amp v x X k p) =
      ∫ h in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1,
        pulseLayerDirectCircleKernel q branch amp v x h (v + h - u) X k := by
  let F : ℝ × ℝ → ℂ := fun p =>
    pulseLayerDirectFixedClockDensity q branch amp v x X k p
  have hF : Integrable F
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1)) := by
    dsimp only [F]
    exact pulseLayerDirectFixedClockDensity_integrable q branch amp v x X k hx hsource himage
  have hF' : IntegrableOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1)
      (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.volume_eq_prod ℝ ℝ]
    exact hF
  have hprod := MeasureTheory.setIntegral_prod F hF'
  convert hprod using 1
  rw [Measure.volume_eq_prod ℝ ℝ]

/-- The coordinate-packaged normal density is the genuine normal derivative
of the literal fixed-clock face, including the two characteristic edges and
the off-cone zero branch. -/
theorem pulseLayerDirectFixedClockDensity_hasDerivAt (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x X k : ℝ) (p : ℝ × ℝ) :
    HasDerivAt (fun r : ℝ =>
      pulseLayerDirectFixedClockDensity q branch amp v r X k p)
      (pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p) x := by
  let z : ℝ := v + p.1 - p.2
  change HasDerivAt (fun r : ℝ =>
    pulseLayerDirectCircleKernel q branch amp v r p.1 z X k)
    (deriv (fun r : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v r p.1 z X k) x) x
  by_cases hcone : |z| ≤ p.1
  · have hderiv := pulseLayerDirectCircleKernel_ingoing_hasDerivAt_closed
      q branch amp v x p.1 z X k hcone
    rw [hderiv.deriv]
    exact hderiv
  · have hzero : (fun r : ℝ =>
      pulseLayerDirectCircleKernel q branch amp v r p.1 z X k) = fun _ : ℝ => 0 := by
      funext r
      simp only [pulseLayerDirectCircleKernel, if_neg hcone, zero_div]
    rw [hzero]
    simpa using (hasDerivAt_const x (0 : ℂ))

/-- **Literal cyclic Peierls realization.**  At every sufficiently deep
ingoing cap point, the normal derivative of the actual fixed-clock direct
action is the integral of its actual four-channel normal density.  The local
dominator is obtained from the literal cap-scale envelope by the exact bound
`capScale ≤ 1`; no source, current, or cone branch is replaced. -/
theorem pulseLayerDirectFixedClockAction_hasDerivAt (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (v x X k : ℝ) (hx : x < 0)
    (hsource : x < v - 1) (himage : x < (v - 1) / 2) :
    HasDerivAt (fun r : ℝ =>
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectFixedClockDensity q branch amp v r X k p)
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p) x := by
  obtain ⟨BN, hBN, hnormal⟩ :=
    pulseLayerDirectCircleKernel_ingoing_normal_scaled_majorant q branch amp v X k
  let S : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1
  let F : ℝ → ℝ × ℝ → ℂ := fun r p =>
    pulseLayerDirectFixedClockDensity q branch amp v r X k p
  let F' : ℝ → ℝ × ℝ → ℂ := fun r p =>
    pulseLayerDirectFixedClockNormalDensity q branch amp v r X k p
  let GN : ℝ × ℝ → ℝ := fun p =>
    BN * Real.exp ((D4BMFullAngularGrowth.strictGrowthExponent q - 2) * p.1)
  have hGN_nonneg (p : ℝ × ℝ) : 0 ≤ GN p := by
    dsimp only [GN]
    exact mul_nonneg hBN (Real.exp_pos _).le
  have hGN_int : Integrable GN (volume.restrict S) := by
    dsimp only [GN, S]
    exact pulseLayerDirectNormalMajorant_integrable q BN
  have hF_meas (r : ℝ) : AEStronglyMeasurable (F r) (volume.restrict S) := by
    dsimp only [F]
    exact (pulseLayerDirectCircleKernel_fixedClock_measurable q branch amp v r X k)
      .aestronglyMeasurable
  have hF'_meas (r : ℝ) : AEStronglyMeasurable (F' r) (volume.restrict S) := by
    dsimp only [F']
    exact (pulseLayerDirectFixedClockNormalDensity_measurable q branch amp v r X k)
      .aestronglyMeasurable
  have hF_int : Integrable (F x) (volume.restrict S) := by
    dsimp only [F, S]
    exact pulseLayerDirectFixedClockDensity_integrable q branch amp v x X k hx.le hsource himage
  let δ : ℝ := min (-x) (min (v - 1 - x) ((v - 1) / 2 - x))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hx (lt_min (by linarith) (by linarith))
  have hlocal : ∀ᵐ p ∂volume.restrict S, ∀ r : ℝ,
      r ∈ Metric.ball x δ → ‖F' r p‖ ≤ GN p := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Icc)] with p hp
    intro r hr
    have hdist : |r - x| < δ := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have hr0 : r < 0 := by
      have hupper := (abs_lt.mp hdist).2
      have hδ0 : δ ≤ -x := by
        dsimp only [δ]
        exact min_le_left _ _
      linarith
    have hrsource : r < v - 1 := by
      have hupper := (abs_lt.mp hdist).2
      have hδsource : δ ≤ v - 1 - x := by
        dsimp only [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hscaled := hnormal r p.1 p.2 hr0.le hrsource hp.1 hp.2
    exact norm_le_of_norm_div_capScale_le r hr0.le (hGN_nonneg p) (by
      simpa only [F', GN, pulseLayerDirectFixedClockNormalDensity] using hscaled)
  have hderiv : ∀ᵐ p ∂volume.restrict S, ∀ r : ℝ,
      r ∈ Metric.ball x δ → HasDerivAt (fun t : ℝ => F t p) (F' r p) r := by
    filter_upwards with p
    intro r _
    exact pulseLayerDirectFixedClockDensity_hasDerivAt q branch amp v r X k p
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict S) (x₀ := x) (F := F) (F' := F') (bound := GN)
    (s := Metric.ball x δ) (Metric.ball_mem_nhds x hδ)
    (Eventually.of_forall hF_meas) hF_int (hF'_meas x) hlocal hGN_int hderiv
  exact hmain.2

/-- The corrected-future residual has its literal cyclic Peierls normal
derivative: the actual direct pulse normal action plus the actual two-arm
combined-cap normal derivative.  This transfers the finite-depth
corrected-future equality through local Fubini and dominated differentiation;
it does not take a cap limit or suppress either cap arm. -/
theorem correctedFutureCapResidual_ingoing_hasDerivAt_literalDirect
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) (hx : x < 0)
    (hsource : x < v - 1) (himage : x < (v - 1) / 2) :
    HasDerivAt (fun y : ℝ =>
      correctedFutureCapResidual q branch amp (v - y) y X k)
      ((∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
        pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p) +
        deriv (fun y : ℝ =>
          D4BMFutureSeedHorizon.seedCapField q branch amp (v - y) y X k -
            parameter q branch * D4BMFutureHorizon.capBoundaryField q branch amp
              (v - y) y X k) x) x := by
  have haction := pulseLayerDirectFixedClockAction_hasDerivAt
    q branch amp v x X k hx hsource himage
  have hseed := D4BMFullSeedCapRadialMemory.seedCapField_ingoing_normal_hasDerivAt
    q branch amp v x X k
  have hboundary := D4BMCapNormalTrace.capBoundaryField_ingoing_normal_hasDerivAt
    q branch amp v x X k
  have hcapRaw := hseed.sub (hboundary.const_mul (parameter q branch))
  have hcap : HasDerivAt (fun y : ℝ =>
      D4BMFutureSeedHorizon.seedCapField q branch amp (v - y) y X k -
        parameter q branch * D4BMFutureHorizon.capBoundaryField q branch amp
          (v - y) y X k)
      (deriv (fun y : ℝ =>
        D4BMFutureSeedHorizon.seedCapField q branch amp (v - y) y X k -
          parameter q branch * D4BMFutureHorizon.capBoundaryField q branch amp
            (v - y) y X k) x) x := by
    rw [hcapRaw.deriv]
    exact hcapRaw
  apply (haction.add hcap).congr_of_eventuallyEq
  let δ : ℝ := min (-x) (min (v - 1 - x) ((v - 1) / 2 - x))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hx (lt_min (by linarith) (by linarith))
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hdist : |y - x| < δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hy
  have hy0 : y ≤ 0 := by
    have hupper := (abs_lt.mp hdist).2
    have hδ0 : δ ≤ -x := by
      dsimp only [δ]
      exact min_le_left _ _
    linarith
  have hysource : y < v - 1 := by
    have hupper := (abs_lt.mp hdist).2
    have hδsource : δ ≤ v - 1 - x := by
      dsimp only [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hyimage : y < (v - 1) / 2 := by
    have hupper := (abs_lt.mp hdist).2
    have hδimage : δ ≤ (v - 1) / 2 - x := by
      dsimp only [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  rw [correctedFutureCapResidual_ingoing_fixedClock_directCircle
    q branch amp v y X k hy0 hysource hyimage,
    ← pulseLayerDirectFixedClockAction_eq_iterated
      q branch amp v y X k hy0 hysource hyimage]

/-- At late original clock, the actual corrected-future derivative is already
the two-arm cap derivative at every finite ingoing depth.  This removes the
direct face before the cap limit, so no direct-action DCT enters this branch
of HB B2. -/
theorem correctedFutureCapResidual_ingoing_hasDerivAt_late
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) (hv : 1 < v)
    (hx : x < 0) (hsource : x < v - 1) (himage : x < (v - 1) / 2) :
    HasDerivAt (fun y : ℝ =>
      correctedFutureCapResidual q branch amp (v - y) y X k)
      (deriv (fun y : ℝ =>
        D4BMFutureSeedHorizon.seedCapField q branch amp (v - y) y X k -
          parameter q branch * D4BMFutureHorizon.capBoundaryField q branch amp
            (v - y) y X k) x) x := by
  have h := correctedFutureCapResidual_ingoing_hasDerivAt_literalDirect
    q branch amp v x X k hx hsource himage
  rw [(pulseLayerDirectFixedClockActions_eq_zero_of_one_lt
    q branch amp v x X k hv).2, zero_add] at h
  exact h

/-- Late cap normal transport with the direct action eliminated at finite
depth.  Only the complete two-arm cap limit remains for the QNM contact
comparison. -/
theorem correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_late_exact
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (hv : 1 < v) :
    Tendsto (fun x : ℝ =>
      deriv (fun y : ℝ => correctedFutureCapResidual q branch amp (v - y) y X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 ((2 * D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp *
          (parameter q branch *
            (fullAngularField q branch ![X, Real.exp k] +
              fullSquarePotential q ![X, Real.exp k]) / 2) *
            D4BMCapRadialMemory.sourceMemory q branch v) -
          parameter q branch * (D4BMFutureHorizon.liftTraceCoefficient q branch amp *
            D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X, Real.exp k] *
              D4BMCapRadialMemory.sourceMemory q branch v))) := by
  have hcap := D4BMFullSeedCapRadialMemory.combinedCap_ingoing_normal_div_scale
    q branch amp v X k
  apply hcap.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ), eventually_lt_atBot (v - 1),
    eventually_lt_atBot ((v - 1) / 2)] with x hx hsource himage
  rw [(correctedFutureCapResidual_ingoing_hasDerivAt_late
    q branch amp v x X k hv hx hsource himage).deriv]

/-- **Literal cyclic Peierls cap-normal realization.**  The normal trace of
the actual corrected-future residual is the doubled literal direct pulse
coefficient plus the complete two-arm cyclic Peierls cap coefficient.  This
is the full pre-QNM HB-B2 normal-trace chain: no image, direct face, seed arm,
or source-cap arm is omitted. -/
theorem correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_literalDirect
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x : ℝ =>
      deriv (fun y : ℝ => correctedFutureCapResidual q branch amp (v - y) y X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 ((∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
          2 * pulseLayerDirectCapLimitFixedClockDensity q branch amp v X k p) +
        ((2 * D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp *
          (parameter q branch *
            (fullAngularField q branch ![X, Real.exp k] +
              fullSquarePotential q ![X, Real.exp k]) / 2) *
            D4BMCapRadialMemory.sourceMemory q branch v) -
          parameter q branch * (D4BMFutureHorizon.liftTraceCoefficient q branch amp *
            D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X, Real.exp k] *
              D4BMCapRadialMemory.sourceMemory q branch v)))) := by
  have hdirect := pulseLayerDirectFixedClockNormalAction_scaled_tendsto
    q branch amp v X k
  have hcap := D4BMFullSeedCapRadialMemory.combinedCap_ingoing_normal_div_scale
    q branch amp v X k
  have hsum := hdirect.add hcap
  have heq : (fun x : ℝ =>
      deriv (fun y : ℝ => correctedFutureCapResidual q branch amp (v - y) y X k) x /
        (capScale x : ℂ)) =ᶠ[atBot]
      fun x : ℝ =>
        (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1,
          pulseLayerDirectFixedClockNormalDensity q branch amp v x X k p) /
            (capScale x : ℂ) +
          deriv (fun y : ℝ =>
            D4BMFutureSeedHorizon.seedCapField q branch amp (v - y) y X k -
              parameter q branch * D4BMFutureHorizon.capBoundaryField q branch amp
                (v - y) y X k) x /
            (capScale x : ℂ) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ), eventually_lt_atBot (v - 1),
      eventually_lt_atBot ((v - 1) / 2)] with x hx hsource himage
    rw [(correctedFutureCapResidual_ingoing_hasDerivAt_literalDirect
      q branch amp v x X k hx hsource himage).deriv]
    have hscale : (capScale x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold capScale; positivity))
    field_simp [hscale]
    ring
  exact hsum.congr' heq.symm

/-- **Late literal cyclic Peierls reduction.**  Once the retained original
clock has passed its unit transition strip, the direct normal action is
identically absent.  Thus the complete literal corrected-future normal trace
is exactly the two-arm combined cap coefficient.  This discharges the
noncompact direct-action premise of HB B2 and leaves only its actual
left-QNM-contact identification. -/
theorem correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_late
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (hv : 1 < v) :
    Tendsto (fun x : ℝ =>
      deriv (fun y : ℝ => correctedFutureCapResidual q branch amp (v - y) y X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 ((2 * D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp *
          (parameter q branch *
            (fullAngularField q branch ![X, Real.exp k] +
              fullSquarePotential q ![X, Real.exp k]) / 2) *
            D4BMCapRadialMemory.sourceMemory q branch v) -
          parameter q branch * (D4BMFutureHorizon.liftTraceCoefficient q branch amp *
            D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X, Real.exp k] *
              D4BMCapRadialMemory.sourceMemory q branch v))) := by
  exact correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_late_exact
    q branch amp v X k hv

end

end RHTower.D4BMLiteralCyclicPeierlsPulseLayer
