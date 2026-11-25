import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.WindowDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation

/-! # Prescribed dates after conditioning on a block of Gaussian couplings -/

open Set Filter MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Any inverse-homogeneous measurable clock has a conditional probability
bounded by a constant times the width at each prescribed positive date,
after revealing a whole block of Gaussian coefficients. The exceptional
backgrounds may depend on the date. -/
theorem gaussian_conditional_window (F : (I→ℝ)×(J→ℝ)→ℝ) (hF : Measurable F)
    (hscale : ∀ a> (0:ℝ), ∀ x y, a*F (a • x,a • y)=F (x,y)) {T : ℝ} (hT : 0<T) :
    let μ := Measure.pi fun _ : I => gaussianReal 0 1
    let ν := Measure.pi fun _ : J => gaussianReal 0 1
    ∀ᵐ x ∂μ, ∃ C ≥ (0:ℝ), ∀ h> (0:ℝ), ν.real {y | |F (x,y)-T|<h}≤C*h := by
  intro μ ν
  have hm := measurableSet_regular ν hF
  have havg : ∀ᵐ u : ℝ, ∀ᵐ x ∂μ, Regular ν F x u := by
    apply (Measure.ae_ae_comm hm).mp
    apply Filter.Eventually.of_forall
    intro x
    let f (y : J→ℝ) := F (x,y)
    have hf : Measurable f := hF.comp (measurable_const.prodMk measurable_id)
    let ρ := ν.map f
    letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hf.aemeasurable
    filter_upwards [ae_window_bound ρ] with t ht
    obtain ⟨C,_,hc⟩ := ht
    apply regular_of_bound ν F x t C
    intro r hr
    have h := hc r hr
    have he : MeasurableSet {u : ℝ | |u-t|<r} :=
      measurableSet_lt (measurable_id.sub_const t).abs measurable_const
    change (ν.map f {u : ℝ | |u-t|<r}).toReal ≤ C*r at h
    rw [Measure.map_apply hf he] at h
    exact h
  obtain ⟨u,hu,hregular⟩ : ∃ u∈Ioo T (T+1), ∀ᵐ x ∂μ, Regular ν F x u := by
    by_contra hh
    have hz : volume (Ioo T (T+1))=0 := measure_eq_zero_iff_ae_notMem.mpr
      (havg.mono fun v hv hmem => hh ⟨v,hmem,hv⟩)
    simp only [Real.volume_Ioo,add_sub_cancel_left,ENNReal.ofReal_one,one_ne_zero] at hz
  let a := u/T
  have ha : 1≤a := (one_le_div hT).mpr hu.1.le
  have ha₀ : 0<a := zero_lt_one.trans_le ha
  have haT : a*T=u := div_mul_cancel₀ _ hT.ne'
  have hreg : ∀ᵐ x ∂μ, Regular ν F (a • x) T := by
    filter_upwards [hregular] with x hx
    obtain ⟨K,hK,hbound⟩ := bound_of_regular ν F hx
    apply regular_of_bound ν F (a • x) T (a^(Fintype.card J)*K*a)
    intro r hr
    let B := {y | |F (a • x,y)-T|<r}
    have hB : MeasurableSet B := measurableSet_lt
      ((hF.comp (measurable_const.prodMk measurable_id)).sub_const T).abs measurable_const
    have hsub : (fun y : J→ℝ => a • y) ⁻¹' B ⊆ {y | |F (x,y)-u|<a*r} := by
      intro y hy
      change |F (a • x,a • y)-T|<r at hy
      change |F (x,y)-u|<a*r
      rw [←hscale a ha₀ x y,←haT,←mul_sub,abs_mul,abs_of_pos ha₀]
      exact mul_lt_mul_of_pos_left hy ha₀
    apply (gaussian_dilation_comparison ha B hB).trans
    exact (mul_le_mul_of_nonneg_left ((measureReal_mono (μ:=ν) hsub (measure_ne_top _ _)).trans (hbound _ (mul_pos ha₀ hr)))
      (pow_nonneg ha₀.le _)).trans_eq (by ring)
  let E := {x | ¬ Regular ν F x T}
  have hE : MeasurableSet E := (hm.preimage (measurable_id.prodMk measurable_const)).compl
  have hz : μ ((fun x : I→ℝ => a • x) ⁻¹' E)=0 := ae_iff.mp hreg
  have hbound := gaussian_dilation_comparison ha E hE
  change μ.real E ≤ a^Fintype.card I * (μ ((fun x : I→ℝ => a • x) ⁻¹' E)).toReal at hbound
  have hzero : μ.real E=0 := le_antisymm (by simpa only [Measure.real,hz,ENNReal.toReal_zero,mul_zero] using hbound)
    measureReal_nonneg
  have hfinal : ∀ᵐ x ∂μ, Regular ν F x T := ae_iff.mpr
    ((measureReal_eq_zero_iff (measure_ne_top μ E)).mp hzero)
  exact hfinal.mono fun _ hx => bound_of_regular ν F hx

#print axioms gaussian_conditional_window
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
