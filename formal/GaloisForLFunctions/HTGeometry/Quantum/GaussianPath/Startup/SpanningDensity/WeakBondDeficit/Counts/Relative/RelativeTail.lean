import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Relative.BernoulliMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Relative count tails at the mean occupancy of a small box -/

open MeasureTheory Real Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.Counts
noncomputable section
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]

private theorem tilt_tail (ν : Measure Ω) [IsProbabilityMeasure ν] (B : Set Ω)
    (hB : MeasurableSet B) (θ v : ℝ) :
    let μ := Measure.pi fun _ : I => ν
    μ.real {x | v≤θ*(sampleCount B x:ℝ)}≤exp ((exp θ-1)*(ν.real B*Fintype.card I)-v) := by
  intro μ
  let p := ν.real B
  let m := Fintype.card I
  have hp : 0≤p := measureReal_nonneg
  have hp' : p≤1 := measureReal_le_one
  let y := (exp θ-1)*p
  have hy : 0≤1+y := by
    change 0≤1+(exp θ-1)*p
    nlinarith only [hp',mul_nonneg (exp_pos θ).le hp]
  have hh : 1+y≤exp y := by linarith only [add_one_le_exp y]
  have hpow := pow_le_pow_left₀ hy hh m
  rw [←exp_nat_mul] at hpow
  have hm := (count_exponential_tilt (I:=I) ν B hB θ v).trans hpow
  rw [exp_sub,le_div_iff₀ (exp_pos _),mul_comm _ (exp v)]
  exact hm.trans_eq (by congr 1; dsimp only [m,y,p]; ring)

/-- With mean occupancy M, missing three quarters of M or reaching four
times M has probability at most 2 exp(-M/4), uniformly in the box mass. -/
theorem relative_sample_tail (ν : Measure Ω) [IsProbabilityMeasure ν] (B : Set Ω)
    (hB : MeasurableSet B) :
    let μ := Measure.pi fun _ : I => ν
    let M := ν.real B*Fintype.card I
    μ.real {x | (sampleCount B x:ℝ)≤M/4 ∨ 4*M≤(sampleCount B x:ℝ)}≤2*exp (-M/4) := by
  intro μ M
  have hM : 0≤M := mul_nonneg measureReal_nonneg (Nat.cast_nonneg _)
  have hnegExp : exp (-1)≤1/2 := by
    rw [exp_neg,inv_eq_one_div]
    apply one_div_le_one_div_of_le zero_lt_two
    linarith only [add_one_le_exp (1:ℝ)]
  let A := {x : I→Ω | -(M/4)≤(-1:ℝ)*(sampleCount B x:ℝ)}
  let B' := {x : I→Ω | 4*M≤(1:ℝ)*(sampleCount B x:ℝ)}
  have ha : μ.real A≤exp (-M/4) := (tilt_tail ν B hB (-1) (-(M/4))).trans (exp_le_exp.mpr (by
    change (exp (-1)-1)*M- -(M/4)≤ -M/4
    linarith only [mul_le_mul_of_nonneg_right hnegExp hM]))
  have hb : μ.real B'≤exp (-M/4) := (tilt_tail ν B hB 1 (4*M)).trans (exp_le_exp.mpr (by
    change (exp 1-1)*M-4*M≤ -M/4
    linarith only [mul_le_mul_of_nonneg_right exp_one_lt_three.le hM,hM]))
  have hs : {x : I→Ω | (sampleCount B x:ℝ)≤M/4 ∨ 4*M≤(sampleCount B x:ℝ)}⊆A∪B' := by
    intro x hx
    rcases hx with h|h
    · exact Or.inl (by change -(M/4)≤(-1:ℝ)*_; simpa only [neg_one_mul,neg_le_neg_iff] using h)
    · exact Or.inr (by change 4*M≤(1:ℝ)*_; simpa only [one_mul] using h)
  exact (((measureReal_mono (μ:=μ) hs).trans (measureReal_union_le ..)).trans (add_le_add ha hb)).trans_eq (two_mul _).symm

#print axioms relative_sample_tail
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.Counts
