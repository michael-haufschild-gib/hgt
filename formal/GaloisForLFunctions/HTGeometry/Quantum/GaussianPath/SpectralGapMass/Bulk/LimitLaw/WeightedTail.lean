import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.MeanGap
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # The size-biased gap selected at a scalar entry -/
open MeasureTheory ProbabilityTheory Filter Finset Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

private def clippedPositive (a : ℝ) (ha : 0 ≤ a) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => min (max 0 x) a,
    (continuous_const.max continuous_id).min continuous_const⟩ a fun x y => by
      rw [Real.dist_eq,abs_le]
      change -a ≤ min (max 0 x) a-min (max 0 y) a ∧ min (max 0 x) a-min (max 0 y) a ≤ a
      have h (z : ℝ) : 0 ≤ min (max 0 z) a := le_min (le_max_left ..) ha
      constructor <;> linarith only [h x,h y,min_le_right (max 0 x) a,min_le_right (max 0 y) a]

private theorem positive_half (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) (hz : (∫ x : ℝ, x ∂(μ : Measure ℝ))=0) :
    (∫ x : ℝ, max 0 x ∂(μ : Measure ℝ))=(∫ x : ℝ, |x| ∂(μ : Measure ℝ))/2 := by
  have he (x : ℝ) : max 0 x=(|x|+x)/2 := by
    rcases le_total 0 x with h|h
    · rw [max_eq_right h,abs_of_nonneg h]; ring
    · rw [max_eq_left h,abs_of_nonpos h]; ring
  simp only [he,integral_div,integral_add hi.abs hi,hz,add_zero]

private theorem weighted_tail_eq (μ : ProbabilityMeasure ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hi : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) :
    (∫ x in Ioi a, x ∂(μ : Measure ℝ)) =
      (∫ x : ℝ, max 0 x ∂(μ : Measure ℝ))-(∫ x, clippedPositive a ha x ∂(μ : Measure ℝ))+
      a*(μ : Measure ℝ).real (Ioi a) := by
  have hpos : Integrable (fun x : ℝ => max 0 x) (μ : Measure ℝ) := by
    apply hi.abs.mono' (continuous_const.max continuous_id).aestronglyMeasurable
    filter_upwards with x
    change |max 0 x| ≤ |x|
    rw [abs_of_nonneg (le_max_left 0 x)]
    exact max_le (abs_nonneg x) (le_abs_self x)
  have hclip := (clippedPositive a ha).integrable (μ:=(μ : Measure ℝ))
  have hE := measurableSet_Ioi (a:=a)
  rw [←integral_indicator hE]
  have he : (Ioi a).indicator (fun x : ℝ => x) = fun x =>
      max 0 x-clippedPositive a ha x+(Ioi a).indicator (fun _ : ℝ => a) x := by
    funext x
    change _=max 0 x-min (max 0 x) a+_
    by_cases h : x∈Ioi a
    · have hx : a < x := h
      rw [indicator_of_mem h,indicator_of_mem h,max_eq_right (ha.trans hx.le),min_eq_right hx.le]
      ring
    · have hx : x ≤ a := le_of_not_gt h
      rw [indicator_of_notMem h,indicator_of_notMem h,min_eq_left (max_le ha hx),sub_self,add_zero]
  have hsub : Integrable (fun x : ℝ => max 0 x-clippedPositive a ha x) (μ : Measure ℝ) :=
    hpos.sub hclip
  rw [he,integral_add hsub ((integrable_const a).indicator hE),
    integral_sub hpos hclip,integral_indicator hE,setIntegral_const,smul_eq_mul,mul_comm _ a]

private theorem signed_gap_center {n : ℕ} (u : PathShell n) :
    (∫ x : ℝ, x ∂(listLaw (scaledGap u) : Measure ℝ))=0 := by
  rw [integral_listLaw,Fintype.sum_prod_type]
  simp only [scaledGap,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum,sub_self,mul_zero]

private theorem gaussian_positive_tail (a : ℝ) :
    (∫ x in Ioi a, x ∂gaussianReal 0 24) = (24/sqrt (48*π))*exp (-(a^2/48)) := by
  let c := (sqrt (48*π))⁻¹
  have he : (fun x => gaussianPDFReal 0 24 x • (Ioi a).indicator (fun y : ℝ => y) x) =
      fun x => c*(Ioi a).indicator (fun y : ℝ => y*exp (-(1/48*y^2))) x := by
    funext x
    by_cases hx : x∈Ioi a
    · simp only [indicator_of_mem hx,gaussianPDFReal,NNReal.coe_ofNat,sub_zero,smul_eq_mul,c]
      rw [show 2*π*24=48*π by ring,show -(x^2)/(2*24)= -(1/48*x^2) by ring]
      ring
    · simp only [indicator_of_notMem hx,smul_zero,mul_zero]
  rw [←integral_indicator measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul (by norm_num : (24:NNReal)≠0),he,integral_const_mul,
    integral_indicator measurableSet_Ioi,integral_Ioi_id_mul_expNegSq (by norm_num : (0:ℝ)<1/48)]
  rw [show 1/48*a^2=a^2/48 by ring]
  dsimp only [c]
  ring

/-- Under entry-flux weighting, the scaled positive gap has limiting tail
exp(−a²/48) for every a ≥ 0. Equivalently its density is g exp(−g²/48)/24. -/
theorem gaussian_size_biased_gap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a ≥ (0:ℝ),
      Tendsto (fun n =>
        let μ := (listLaw (scaledGap (pathPauliDisorderShell ω n)) : Measure ℝ)
        (∫ x in Ioi a, x ∂μ)/(∫ x : ℝ, max 0 x ∂μ)) atTop (𝓝 (exp (-(a^2/48)))) := by
  filter_upwards [gaussian_energy_and_gap_laws,gaussian_mean_absolute_gap] with ω hw hm
  intro a ha
  let μ (n : ℕ) := listLaw (scaledGap (pathPauliDisorderShell ω n))
  let ν : ProbabilityMeasure ℝ := ⟨gaussianReal 0 24,inferInstance⟩
  have hweak : Tendsto μ atTop (𝓝 ν) := hw.2
  have hi (n) : Integrable (fun x : ℝ => x) (μ n : Measure ℝ) := integrable_listLaw _ _
  have hν : Integrable (fun x : ℝ => x) (ν : Measure ℝ) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' (μ:=0) (v:=24) 1 (by simp))
  let M := 24/sqrt (48*π)
  have hnum : (48/sqrt (48*π))/2=M := by dsimp only [M]; ring
  have hmean : Tendsto (fun n => ∫ x : ℝ, max 0 x ∂(μ n : Measure ℝ)) atTop (𝓝 M) := by
    have hh := hm.div_const 2
    rw [hnum] at hh
    exact hh.congr fun n => (positive_half (μ n) (hi n) (signed_gap_center _)).symm
  have hpos : (∫ x : ℝ, max 0 x ∂(ν : Measure ℝ))=M := by
    rw [positive_half ν hν (by exact integral_id_gaussianReal)]
    exact (congrArg (fun z : ℝ => z/2) gaussian_gap_absolute_integral).trans hnum
  have hprob := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak (E:=Ioi a)
    (by change gaussianReal 0 24 (frontier (Ioi a))=0
        rw [frontier_Ioi]
        exact gaussianReal_absolutelyContinuous 0 (by norm_num : (24:NNReal)≠0) (measure_singleton a))
  have hp := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) _)).comp hprob
  change Tendsto (fun n => (μ n : Measure ℝ).real (Ioi a)) atTop (𝓝 ((ν : Measure ℝ).real (Ioi a))) at hp
  have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) (clippedPositive a ha)
  have htail := (hmean.sub hc).add (hp.const_mul a)
  rw [←hpos,←weighted_tail_eq ν ha hν] at htail
  have htail' : Tendsto (fun n => ∫ x in Ioi a, x ∂(μ n : Measure ℝ)) atTop
      (𝓝 (M*exp (-(a^2/48)))) := by
    change Tendsto _ _ (𝓝 ((24/sqrt (48*π))*exp (-(a^2/48))))
    rw [←gaussian_positive_tail]
    exact htail.congr fun n => (weighted_tail_eq (μ n) ha (hi n)).symm
  have hM : 0 < M := by dsimp only [M]; positivity
  have hh := htail'.div hmean hM.ne'
  rw [mul_div_cancel_left₀ _ hM.ne'] at hh
  exact hh.congr fun _ => rfl

#print axioms gaussian_size_biased_gap
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
