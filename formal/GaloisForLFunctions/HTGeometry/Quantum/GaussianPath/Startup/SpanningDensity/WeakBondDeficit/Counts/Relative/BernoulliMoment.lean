import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exponential moments for counts in finite independent samples -/

open MeasureTheory Finset Real Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.Counts
noncomputable section
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]

open scoped Classical in
/-- Number of sample coordinates falling in a measurable box. -/
def sampleCount (B : Set Ω) (x : I→Ω) : ℕ := (Finset.univ.filter fun i => x i∈B).card

/-- The Markov bound for a signed exponential tilt of the count. Both
tails use the same product moment and remain informative for rare boxes. -/
theorem count_exponential_tilt (ν : Measure Ω) [IsProbabilityMeasure ν] (B : Set Ω)
    (hB : MeasurableSet B) (θ v : ℝ) :
    let μ := Measure.pi fun _ : I => ν
    exp v*μ.real {x | v≤θ*(sampleCount B x:ℝ)}≤(1+(exp θ-1)*ν.real B)^Fintype.card I := by
  classical
  intro μ
  let J := B.indicator (fun _ => (1:ℝ))
  let f (x : Ω) := 1+(exp θ-1)*J x
  let E := {x : I→Ω | v≤θ*(sampleCount B x:ℝ)}
  have hj : Integrable J ν := (integrable_const 1).indicator hB
  have hf : Integrable f ν := (integrable_const 1).add (hj.const_mul _)
  have counts (x : I→Ω) : (∑ i, J (x i))=(sampleCount B x:ℝ) := by
    simp only [J,Set.indicator_apply,sampleCount,sum_boole]
  have hcnt : Measurable (fun x : I→Ω => (sampleCount B x:ℝ)) := by
    simp_rw [←counts]
    exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hB).comp (measurable_pi_apply i)
  have hE : MeasurableSet E := measurableSet_le measurable_const (measurable_const.mul hcnt)
  have hpoint (x : Ω) : f x=exp (θ*J x) := by
    by_cases hx : x∈B <;> simp [f,J,hx]
  have hprod (x : I→Ω) : (∏ i, f (x i))=exp (θ*(sampleCount B x:ℝ)) := by
    simp_rw [hpoint]
    rw [←Real.exp_sum,←mul_sum,counts]
  have hbound (x : I→Ω) : E.indicator (fun _ => exp v) x≤∏ i, f (x i) := by
    rw [hprod]
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx]
      exact exp_le_exp.mpr hx
    · rw [Set.indicator_of_notMem hx]
      exact (exp_pos _).le
  have hmean : (∫ z, f z ∂ν)=1+(exp θ-1)*ν.real B := by
    dsimp only [f]
    rw [integral_add (integrable_const ..) (hj.const_mul _),integral_const_mul]
    have hJ : (∫ z, J z ∂ν)=ν.real B := integral_indicator_one hB
    simp only [integral_const,probReal_univ,one_smul,hJ]
  have hm := integral_mono ((integrable_const (μ:=μ) (exp v)).indicator hE)
    (Integrable.fintype_prod (fun _ : I => hf)) hbound
  rw [integral_indicator_const _ hE,integral_fintype_prod_eq_prod] at hm
  simpa only [hmean,prod_const,card_univ,Measure.real,smul_eq_mul,mul_comm (exp v)] using hm

#print axioms count_exponential_tilt
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.Counts
