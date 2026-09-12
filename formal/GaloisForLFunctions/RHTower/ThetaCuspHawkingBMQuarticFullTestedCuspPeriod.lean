import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResponseCuspFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspFieldIntegral

/-!
# Complete physical scalar-tested response cusp period

Native absolute admission of the original scalar/source remainder passes through
its exact hyperbolic chart to the high-cusp horizontal integral. The full physical
pairing is restored by the original three weighted response counterterms. Its
finite part retains the native signed remainder integral, all source moments,
and the actual lower-boundary response jet on both quadratic branches.

These are source-derived identities with the original physical frequencies.
They do not assign the finite part a zero value or assert cancellation with
the remaining physical angular currents, boundaries and independent channels.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMQuarticFullTestedCuspPeriod
open D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource D4BMCuspResponse
open D4BMQuarticResponseCuspPair D4BMQuarticResponseMellinTransport
open D4BMQuarticResponseCuspFinitePart D4BMCuspProjection D4BMAngularSeries
noncomputable section
set_option autoImplicit false

private def rectangle (L : ℝ) : Set ℂ := {z | z.re ∈ Icc (-1/2) (1/2) ∧ L < z.im}

private theorem rectangle_subset (L : ℝ) (hL : 1 ≤ L) : rectangle L ⊆ cellChart := by
  intro z hz
  have hy : 0 < z.im := lt_trans (by linarith : 0 < L) hz.2
  refine ⟨⟨z,hy⟩,?_,rfl⟩
  constructor
  · rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re,hz.2]
  · change |z.re| ≤ 1/2
    exact abs_le.mpr (by simpa only [mem_Icc,neg_div] using hz.1)

private theorem cusp_mean_integrable (L : ℝ) (hL : 1 ≤ L) (F : ℂ → ℂ)
    (hi : Integrable (fun z : UpperHalfPlane => F z) measure) :
    IntegrableOn (fun y : ℝ => D4BMCuspProjection.mean
      (fun x => F (Complex.measurableEquivRealProd.symm (x,y)))/(y:ℂ)^2) (Ioi L) := by
  have hden (z : ℂ) (hp : 0 < z.im) : chartDensity z • F z = F z/(z.im:ℂ)^2 := by
    simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
      coe_nnnorm,Real.norm_eq_abs,abs_of_pos hp,Complex.real_smul,
      Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
    ring
  have hmap : Integrable F (Measure.map UpperHalfPlane.coe measure) :=
    UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mpr hi
  rw [map_measure_eq] at hmap
  have hd : IntegrableOn (fun z => chartDensity z • F z) cellChart :=
    (integrable_withDensity_iff_integrable_smul (show Measurable chartDensity by
      unfold chartDensity; fun_prop)).mp hmap
  have hrect : IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^2) (rectangle L) := by
    apply (hd.mono_set (rectangle_subset L hL)).congr_fun
    · intro z hz
      exact hden z (lt_trans (by linarith : 0 < L) hz.2)
    · exact (isClosed_Icc.preimage Complex.continuous_re).measurableSet.inter
        (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  let G : ℝ × ℝ → ℂ := fun xy => F (Complex.measurableEquivRealProd.symm xy)/(xy.2:ℂ)^2
  have hG : IntegrableOn G (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi L)
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    apply (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mp
    change IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^2) (rectangle L)
    exact hrect
  have hf : Integrable G
      ((volume.restrict (Icc (-1/2:ℝ) (1/2))).prod (volume.restrict (Ioi L))) := by
    simpa only [Measure.prod_restrict,IntegrableOn] using hG
  have he : (fun y : ℝ => ∫ x in Icc (-1/2:ℝ) (1/2), G (x,y)) =
      fun y => D4BMCuspProjection.mean
        (fun x => F (Complex.measurableEquivRealProd.symm (x,y)))/(y:ℂ)^2 := by
    funext y
    dsimp only [G]
    simp only [div_eq_mul_inv]
    rw [integral_mul_const,integral_Icc_eq_integral_Ioc]
    rfl
  exact he ▸ hf.integral_prod_right

/-- Complete original test remainder with the hyperbolic metric weight. -/
def testedTailCuspDensity (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  D4BMCuspProjection.mean (fun x =>
    testedResponseTail q b (physicalAngularParameter q) ![x,y])/(y:ℂ)^2

/-- Native admission gives absolute integrability of the actual high-cusp remainder. -/
theorem testedTailCuspDensity_integrable (q : XiZeroCopy) (b : Bool) :
    IntegrableOn (testedTailCuspDensity q b) (Ioi (3:ℝ)) := by
  exact cusp_mean_integrable 3 (by norm_num)
    (fun z => testedResponseTail q b (physicalAngularParameter q) (angularCoordinates z))
    (testedResponseTail_integrable q b (physicalAngularParameter q))

/-- The signed period of the complete original remainder on the native high cusp. -/
def nativeTestedTailPeriod (q : XiZeroCopy) (b : Bool) (a : Ioi (3:ℝ)) : ℂ :=
  ∫ z : UpperHalfPlane in {z | (a:ℝ) < z.im},
    testedResponseTail q b (physicalAngularParameter q) (coordinates z) ∂measure

/-- Exact chart identification; no source-contact remainder is removed. -/
theorem nativeTestedTailPeriod_eq (q : XiZeroCopy) (b : Bool) (a : Ioi (3:ℝ)) :
    nativeTestedTailPeriod q b a = ∫ y in Ioi (a:ℝ), testedTailCuspDensity q b y := by
  let F : ℂ → ℂ := fun z => if (a:ℝ) < z.im then
    testedResponseTail q b (physicalAngularParameter q) (angularCoordinates z) else 0
  have hm : MeasurableSet {z : UpperHalfPlane | (a:ℝ) < z.im} :=
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  have hi : Integrable (fun z : UpperHalfPlane => F z) measure :=
    (testedResponseTail_integrable q b (physicalAngularParameter q)).indicator hm
  have ha : 1 ≤ (a:ℝ) := by have := a.2; change 3 < (a:ℝ) at this; linarith
  have he := integral_cusp_field_from (a:ℝ) ha F hi (by
    intro z hz
    simp only [F,if_neg (not_lt.mpr hz)])
  change (∫ z : UpperHalfPlane, ({z | (a:ℝ) < z.im}.indicator
    (fun z => testedResponseTail q b (physicalAngularParameter q) (coordinates z))) z ∂measure) = _ at he
  rw [integral_indicator hm] at he
  exact he.trans (setIntegral_congr_fun measurableSet_Ioi (fun y hy => by
    change D4BMCuspProjection.mean (fun x => if (a:ℝ) < y then
      testedResponseTail q b (physicalAngularParameter q) ![x,y] else 0)/(y:ℂ)^2 = _
    exact congrArg (fun f : ℝ → ℂ => D4BMCuspProjection.mean f/(y:ℂ)^2)
      (funext (fun x : ℝ => if_pos (show (a:ℝ) < y from hy)))))

/-- Actual full physical scalar test against the complete quadratic response and source. -/
def fullTestedCuspDensity (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  D4BMCuspProjection.mean (fun x => scalar (physicalAngularParameter q) ![x,y]*
    fullSquarePotential q ![x,y]*fullAngularField q b ![x,y])/(y:ℂ)^2

private theorem power_step (v : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^v=(y:ℂ)^(v-2)*(y:ℂ)^2 := by
  have he : (y:ℂ)^(2:ℂ)=(y:ℂ)^2 := by norm_cast
  rw [← he,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  congr 1
  ring

/-- All three original physical weights and the complete admitted remainder occur in the density. -/
theorem fullTestedCuspDensity_eq (q : XiZeroCopy) (b : Bool) (y : Ioi (3:ℝ)) :
    fullTestedCuspDensity q b y = testedTailCuspDensity q b y+
      reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
        ((y:ℂ)^(physicalWeight q i-2)*fullMean q b y) := by
  have hy : 0 < (y:ℝ) := lt_trans (by norm_num : (0:ℝ)<3) y.2
  have h := tested_square_response_cusp_mean q b (physicalAngularParameter q) y
  rw [← fullMean_eq_cusp_data q b y,physical_principal_square_expansion q ⟨y,hy⟩] at h
  unfold fullTestedCuspDensity testedTailCuspDensity
  rw [h,add_div,add_comm]
  congr 1
  rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [power_step (physicalWeight q i) hy]
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne']

private theorem moment_intervalIntegrable (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    (a c : Ioi (3:ℝ)) :
    IntervalIntegrable (fun y : ℝ => (y:ℂ)^(physicalWeight q i-2)*fullMean q b y)
      volume (a:ℝ) c := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hp : 0 < y := lt_trans (by norm_num : (0:ℝ)<3)
    ((lt_min a.2 c.2).trans_le hy.1)
  have hm : ContinuousAt (fullMean q b) y :=
    (average_hasDerivAt (fullAngular q b ∘ ofComplex)
      (fullAngular_smooth q b).planar_contDiffOn hp).continuousAt
  exact ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal
    (w := physicalWeight q i-2) hp).continuousAt.mul hm).continuousWithinAt

private theorem testedTail_intervalIntegrable (q : XiZeroCopy) (b : Bool)
    (a c : Ioi (3:ℝ)) :
    IntervalIntegrable (testedTailCuspDensity q b) volume (a:ℝ) c :=
  ⟨(testedTailCuspDensity_integrable q b).mono_set (fun _ hy => a.2.trans hy.1),
    (testedTailCuspDensity_integrable q b).mono_set (fun _ hy => c.2.trans hy.1)⟩

private theorem fullTestedCusp_segment (q : XiZeroCopy) (b : Bool) (a c : Ioi (3:ℝ)) :
    (∫ y in (a:ℝ)..c, fullTestedCuspDensity q b y) =
      (∫ y in (a:ℝ)..c, testedTailCuspDensity q b y)+
        reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
          (∫ y in (a:ℝ)..c, (y:ℂ)^(physicalWeight q i-2)*fullMean q b y) := by
  have hi (i : Fin 3) := (moment_intervalIntegrable q b i a c).const_mul (principalAmplitude q i)
  have hs : IntervalIntegrable (fun y : ℝ => ∑ i : Fin 3,
      principalAmplitude q i*((y:ℂ)^(physicalWeight q i-2)*fullMean q b y)) volume (a:ℝ) c := by
    exact ⟨integrable_finsetSum Finset.univ (fun i _ => (hi i).1),
      integrable_finsetSum Finset.univ (fun i _ => (hi i).2)⟩
  calc
    _ = ∫ y in (a:ℝ)..c, testedTailCuspDensity q b y+
        reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
          ((y:ℂ)^(physicalWeight q i-2)*fullMean q b y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact fullTestedCuspDensity_eq q b ⟨y,(lt_min a.2 c.2).trans_le hy.1⟩
    _ = _ := by
      rw [intervalIntegral.integral_add (testedTail_intervalIntegrable q b a c) (hs.const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun i _ => hi i)]
      simp only [intervalIntegral.integral_const_mul]

/-- The endpoint subtraction prescribed by the original physical test and source powers. -/
def fullTestedCuspCounterterm (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3,
    principalAmplitude q i*responseCounterterm q b i y

/-- Full response finite part: native signed remainder plus all source-determined periods. -/
def fullTestedCuspFinitePart (q : XiZeroCopy) (b : Bool) (a : Ioi (3:ℝ)) : ℂ :=
  nativeTestedTailPeriod q b a+reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3,
    principalAmplitude q i*sourceDeterminedPeriod q b i a

private theorem fullTestedCusp_moment_restoration (q : XiZeroCopy) (b : Bool)
    (a c : Ioi (3:ℝ)) :
    (∫ y in (a:ℝ)..c, fullTestedCuspDensity q b y)-fullTestedCuspCounterterm q b c =
      (∫ y in (a:ℝ)..c, testedTailCuspDensity q b y)+
        reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
          ((∫ y in (a:ℝ)..c, (y:ℂ)^(physicalWeight q i-2)*fullMean q b y)-
            responseCounterterm q b i c) := by
  rw [fullTestedCusp_segment,fullTestedCuspCounterterm]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Exact finite-cutoff identity for the full physical scalar-tested response. -/
theorem fullTestedCusp_restoration (q : XiZeroCopy) (b : Bool) (a c : Ioi (3:ℝ)) :
    (∫ y in (a:ℝ)..c, fullTestedCuspDensity q b y)-fullTestedCuspCounterterm q b c =
      (∫ y in (a:ℝ)..c, testedTailCuspDensity q b y)+
        reflectedCompletedLambda ((q.1:ℂ)-1)*∑ i : Fin 3, principalAmplitude q i*
          ((physicalFlux q b i c-D4BMQuarticCuspFluxDecay.particularPhysicalFlux q b i c-
              D4BMQuarticCuspFluxDecay.nativePhysicalFlux q b i c-
              physicalFlux q b i a+sourceCounterterm q b i a-
              ∫ y in (a:ℝ)..c, sourceTailDensity q b i y)/physicalGap q b i) := by
  rw [fullTestedCusp_moment_restoration]
  simp_rw [response_period_restoration q b _ a c]

/-- Source-derived finite part of the complete physical scalar-tested response on either branch. -/
theorem fullTestedCusp_period_tendsto (q : XiZeroCopy) (b : Bool) (a : Ioi (3:ℝ)) :
    Tendsto (fun c : ℝ => (∫ y in (a:ℝ)..c, fullTestedCuspDensity q b y)-
      fullTestedCuspCounterterm q b c) atTop (𝓝 (fullTestedCuspFinitePart q b a)) := by
  have hi : IntegrableOn (testedTailCuspDensity q b) (Ioi (a:ℝ)) := by
    apply (testedTailCuspDensity_integrable q b).mono_set
    intro y hy
    change 3 < y
    exact lt_trans a.2 hy
  have hF := intervalIntegral_tendsto_integral_Ioi (a:ℝ) hi tendsto_id
  have hs := tendsto_finsetSum Finset.univ (fun i _ =>
    (response_period_tendsto q b i a).const_mul (principalAmplitude q i))
  have ht := hF.add (hs.const_mul (reflectedCompletedLambda ((q.1:ℂ)-1)))
  rw [fullTestedCuspFinitePart,nativeTestedTailPeriod_eq]
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with c hc
  exact (fullTestedCusp_moment_restoration q b a ⟨c,hc⟩).symm



end
end RHTower.D4BMQuarticFullTestedCuspPeriod
