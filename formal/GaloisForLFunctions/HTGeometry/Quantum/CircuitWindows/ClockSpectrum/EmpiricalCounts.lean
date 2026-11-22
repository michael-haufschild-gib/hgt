import GaloisForLFunctions.HTGeometry.BoundedSumConcentration
import GaloisForLFunctions.HTGeometry.GaussianStableRankLowerTail

/-! # Simultaneous concentration of phase counts at a finite set of cuts -/
open MeasureTheory ProbabilityTheory Filter Set Finset
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
noncomputable section

/-- Count the phase configurations in a specified measurable region. -/
def sampleCount {I Ω : Type*} [Fintype I] (x : I→Ω) (S : Set Ω) : ℝ :=
  ∑ i, S.indicator (fun _ => (1:ℝ)) (x i)

/-- A finite family of tests costs one union bound. The samples have
an arbitrary common probability law, including Haar on the phase circle. -/
theorem empirical_count_tail {I J Ω : Type*} [Fintype I] [Fintype J] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : J→Set Ω) (hm : ∀ j, MeasurableSet (S j))
    (a : ℝ) (ha : 0 ≤ a) :
    let ν := Measure.pi (fun _ : I => μ)
    let n := (Fintype.card I:ℝ)
    ν.real {x : I→Ω | ∃ j, a ≤ |sampleCount x (S j)-n*μ.real (S j)|} ≤
      Fintype.card J*(2*Real.exp (-a^2/(2*n))) := by
  classical
  intro ν n
  let F (j : J) := {x : I→Ω | a ≤ |sampleCount x (S j)-n*μ.real (S j)|}
  have h (j : J) : ν.real (F j) ≤ 2*Real.exp (-a^2/(2*n)) := by
    let p := μ.real (S j)
    let f (y : Ω) := (S j).indicator (fun _ => (1:ℝ)) y-p
    have hf : Measurable f := ((measurable_const.indicator (hm j)).sub measurable_const)
    have hI : Integrable ((S j).indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator (hm j)
    have hz : ∫ y, f y ∂μ=0 := by
      dsimp only [f]
      rw [integral_sub hI (integrable_const _),integral_indicator_one (hm j),integral_const]
      simp [p]
    have hp : p ≤ 1 := (measureReal_mono (subset_univ (S j))).trans_eq probReal_univ
    have hbound (y : Ω) : f y∈Icc (-1) 1 := by
      have hnon : 0 ≤ p := ENNReal.toReal_nonneg
      by_cases hy : y∈S j
      · simp only [f,indicator_of_mem hy,mem_Icc]
        constructor <;> linarith only [hp,hnon]
      · simp only [f,indicator_of_notMem hy,zero_sub,mem_Icc]
        constructor <;> linarith only [hp,hnon]
    let X (i : I) (x : I→Ω) := f (x i)
    have hi : iIndepFun X ν := iIndepFun_pi fun _ => hf.aemeasurable
    have hx (i : I) : AEMeasurable (X i) ν := (hf.comp (measurable_pi_apply i)).aemeasurable
    have hμ (i : I) : ∫ x, X i x ∂ν=0 := by
      exact (integral_comp_eval (i:=i) hf.aestronglyMeasurable).trans hz
    have hh := measure_abs_sum_ge_le hi hx (fun i => Eventually.of_forall fun x => hbound (x i)) hμ ha
    have he (x : I→Ω) : ∑ i, X i x=sampleCount x (S j)-n*p := by
      simp only [X,f,sampleCount,n,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simpa only [he,F,p,n] using hh
  rw [show {x : I→Ω | ∃ j, a ≤ |sampleCount x (S j)-n*μ.real (S j)|}=⋃ j, F j from setOf_exists _]
  apply (measureReal_iUnion_fintype_le F).trans
  calc _ ≤ ∑ _j : J, 2*Real.exp (-a^2/(2*n)) := Finset.sum_le_sum (fun j _ => h j)
       _ = _ := by simp [nsmul_eq_mul]

#print axioms empirical_count_tail
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
