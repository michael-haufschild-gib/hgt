import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCanonicalRestoration

open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalCanonicalMetricCutoff
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalHorizonGreenMatch
open D4BMOriginalMetricHorizon D4BMOriginalMetricRadial D4BMOriginalCanonicalHorizon
noncomputable section
set_option autoImplicit false

/-- The original Green endpoint is independent of every sufficiently small
auxiliary interface, throughout one actual frequency neighborhood. -/
theorem original_green_endpoint_below (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      AnalyticAt ℂ (fun u => incomingSourcePrimitive s chi amp J K u b) w ∧
      ∀ u∈ball w R,connection u chi≠0 →
        greenHorizonAmplitude s chi amp J K u=incomingResponseEndpoint s chi amp J K u b := by
  obtain ⟨R,B,C,M,hR,hB,hBh,_,_,hd⟩ :=
    incomingSourcePrimitive_common_data s chi amp J K w hw hwr hs
  refine ⟨R,B,hR,hB,hBh,?_⟩
  intro b hb hbB
  refine ⟨((hd w (mem_ball_self hR)).2.2.2.2 b ⟨hb,hbB⟩).1,?_⟩
  intro u hu hc
  have hP := ((hd u hu).2.2.2.1 0 ⟨le_rfl,hB.le⟩).mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT hB] at hP
  simp only [incomingSourcePrimitive,intervalIntegral.integral_same] at hP
  have hlim := hP.const_add (incomingResponseEndpoint s chi amp J K u B)
  simp only [add_zero] at hlim
  have hactual : Tendsto (fun z => continuedResponse s chi amp J K z u/horizon u chi z)
      (𝓝[>] (0:ℝ)) (𝓝 (incomingResponseEndpoint s chi amp J K u B)) := by
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT hB] with z hz
    exact (((hd u hu).2.2.2.2 z ⟨hz.1,hz.2.le⟩).2.2.2 hc).symm
  have hg : greenHorizonAmplitude s chi amp J K u=incomingResponseEndpoint s chi amp J K u B :=
    hactual.limUnder_eq
  have he := ((hd u hu).2.2.2.2 b ⟨hb,hbB⟩).2.2.2 hc
  rw [hg]
  change incomingResponseEndpoint s chi amp J K u B=
    continuedResponse s chi amp J K b u/horizon u chi b-incomingSourcePrimitive s chi amp J K u b
  rw [he]
  ring

def gradient (q : XiZeroCopy) (br : Bool) : ℂ :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1

/-- The prescribed original Green counterterm, with its actual horizon
coefficient rather than an auxiliary positive-radius representation. -/
def canonicalGreenCounterterm (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (e : ℝ) : ℂ :=
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let E := greenHorizonAmplitude s chi amp 1 (gradient q br) w
  incomingCoefficient q w*((E/2)*(e:ℂ)^w/w+
    ((horizonGaussFirstCoefficient w chi+1/4)*E+incomingResponseSlope s amp 1 (gradient q br) w/2)*
      (e:ℂ)^(w+1)/(w+1))+
    oppositeCoefficient q w*(E/2)*(Real.log e:ℂ)

/-- One cutoff of the original full metric radial density, with all its
source-fixed power/log counterterms and no auxiliary interface parameter. -/
def canonicalMetricCutoff (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (e : ℝ) : ℂ :=
  (∫ x in tortoiseOf e..0,D4BMOriginalMetricOuter.outerDensity q br amp w x)+
    greenCoefficient q w*canonicalGreenCounterterm q br amp w e-
    forcingCoefficient q br w*forcingCounterterm
      (incomingValue q br amp (gradient q br)) (incomingSlope q br amp (gradient q br))
      (oppositeValue q br amp (gradient q br)) w e

/-- The entire original radial cutoff agrees with this one source-defined
family at every small local interface. No matching or endpoint-admission
hypothesis is supplied. -/
theorem original_metric_cutoff_canonical (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      ∀ u∈ball w R,connection u (physicalRadialFrequency q)≠0 → ∀ e : ℝ,
        canonicalMetricCutoff q br amp u e=
          radialCutoff q br amp (incomingValue q br amp (gradient q br))
            (incomingSlope q br amp (gradient q br)) (oppositeValue q br amp (gradient q br)) b u e := by
  have hs : w-2*physicalRate q br≠0 := by
    intro he
    have hre := congrArg Complex.re (sub_eq_zero.mp he)
    have hr := currentRate_re_lt q br
    change (2*physicalRate q br).re < -2 at hr
    linarith
  obtain ⟨R,B,hR,hB,hBh,h⟩ := original_green_endpoint_below
    (physicalRate q br) (physicalRadialFrequency q) amp 1 (gradient q br) w hw hwr hs
  refine ⟨R,B,hR,hB,hBh,?_⟩
  intro b hb hbB u hu hc e
  have hE := (h b hb hbB).2 u hu hc
  have he : canonicalGreenCounterterm q br amp u e=greenCounterterm q br amp b u e := by
    dsimp only [gradient] at hE
    simp only [canonicalGreenCounterterm,greenCounterterm,gradient]
    rw [hE]
  simp only [canonicalMetricCutoff,radialCutoff,he]

end
end RHTower.D4BMOriginalCanonicalMetricCutoff
