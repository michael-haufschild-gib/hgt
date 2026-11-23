import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian

/-! # Concentration of local tests on disjoint coefficient windows -/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Reading disjoint, equally shaped windows of an iid field gives
independent blocks with their original product distribution. -/
theorem disjoint_window_law {I J K : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : J × K → I) (hg : Function.Injective g) :
    MeasurePreserving (fun (ω : I → ℝ) j k => ω (g (j,k)))
      (Measure.infinitePi fun _ => μ)
      (Measure.infinitePi fun _ : J => Measure.infinitePi fun _ : K => μ) := by
  let ν : Measure ((J × K) → ℝ) := Measure.infinitePi fun _ => μ
  have hr : MeasurePreserving (fun ω p => ω (g p)) (Measure.infinitePi fun _ => μ) ν :=
    ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _,Measure.map_infinitePi_infinitePi_of_inj hg⟩
  have hc : MeasurePreserving (MeasurableEquiv.curry J K ℝ) ν
      (Measure.infinitePi fun _ : J => Measure.infinitePi fun _ : K => μ) :=
    ⟨(MeasurableEquiv.curry ..).measurable,Measure.infinitePi_map_curry (fun _ _ => μ)⟩
  exact hc.comp hr

/-- Different windows may use different tests. The upper tail depends
only on the common bound for their failure probabilities. -/
theorem independent_window_failures {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (S : I → Set Ω) (hs : ∀ i, MeasurableSet (S i))
    {p η : ℝ} (hp : ∀ i, ν.real (S i)≤p) (hη : 0≤η) :
    (Measure.infinitePi fun _ : I => ν).real {x | (p+η)*Fintype.card I ≤
      ((Finset.univ.filter fun i => x i∈S i).card:ℝ)} ≤ Real.exp (-2*η^2*Fintype.card I) := by
  classical
  let μ := Measure.infinitePi fun _ : I => ν
  let X (i : I) (x : I → Ω) := (S i).indicator (fun _ => (1:ℝ)) (x i)
  let Y (i : I) (x : I → Ω) := X i x-ν.real (S i)
  have hX (i) : Measurable (X i) :=
    (measurable_const.indicator (hs i)).comp (measurable_pi_apply i)
  have hav (i) : ∫ x, X i x ∂μ = ν.real (S i) := by
    have he := (measurePreserving_eval_infinitePi (fun _ : I => ν) i).map_eq
    change (∫ x, (S i).indicator (fun _ => (1:ℝ)) (Function.eval i x) ∂μ)=_
    rw [←integral_map (measurable_pi_apply i).aemeasurable
      (measurable_const.indicator (hs i)).aestronglyMeasurable,he]
    exact integral_indicator_one (hs i)
  have hsg (i) : HasSubgaussianMGF (Y i) ((1/2:NNReal)^2) μ := by
    have hb : ∀ᵐ x ∂μ, X i x∈Icc (0:ℝ) 1 := Filter.Eventually.of_forall fun x => by
      by_cases h : x i∈S i <;> simp [X,h]
    have h := hasSubgaussianMGF_of_mem_Icc (hX i).aemeasurable hb
    rw [hav] at h
    simpa only [Y,sub_zero,nnnorm_one] using h
  have hind : iIndepFun Y μ := iIndepFun_infinitePi (P:=fun _ : I => ν)
    (fun i => (measurable_const.indicator (hs i)).sub measurable_const)
  let m : ℝ := Fintype.card I
  have hm : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s:=Finset.univ)
    (fun i _ => hsg i) (mul_nonneg hη hm.le)
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hsub : {x | (p+η)*Fintype.card I ≤ ((Finset.univ.filter fun i => x i∈S i).card:ℝ)}
      ⊆ {x | η*m ≤ ∑ i, Y i x} := by
    intro x hx
    change η*m ≤ ∑ i, Y i x
    have hcount : ∑ i, X i x=((Finset.univ.filter fun i => x i∈S i).card:ℝ) := by
      simp only [X,Set.indicator_apply,Finset.sum_boole]
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hp i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
    change (p+η)*m ≤ _ at hx
    simp only [Y,Finset.sum_sub_distrib,hcount]
    change ∑ i, ν.real (S i) ≤ m*p at hsum
    linarith only [hx,hsum]
  apply ((measureReal_mono (μ:=μ) hsub (measure_ne_top _ _)).trans h).trans_eq
  apply congrArg Real.exp
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,NNReal.coe_mul,
    NNReal.coe_natCast,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,m]
  field_simp [show (Fintype.card I:ℝ)≠0 from hm.ne']

#print axioms independent_window_failures
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
