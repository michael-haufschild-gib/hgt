import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Lower tail for the number of independent visits to a coefficient box -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Among m independent draws, the chance of seeing a measurable set fewer
than half as often as its mean is at most four divided by the mean. -/
theorem iid_box_count_lower_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {B : Set α} (hB : MeasurableSet B) (m : ℕ)
    (hmean : 0 < (m:ℝ)*μ.real B) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ω | (((Finset.range m).filter (fun i => ω i ∈ B)).card : ℝ) < m*μ.real B/2} ≤
        ENNReal.ofReal (4/((m:ℝ)*μ.real B)) := by
  classical
  let ν := Measure.infinitePi fun _ : ℕ => μ
  let f := B.indicator (fun _ : α => (1:ℝ))
  let X (j : ℕ) (ω : ℕ → α) := f (ω j)
  let S := ∑ j ∈ Finset.range m, X j
  have hf : Measurable f := measurable_const.indicator hB
  have hX (j : ℕ) : MemLp (X j) 2 ν :=
    ((memLp_const (1:ℝ)).indicator hB).comp_measurePreserving
      (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) j)
  have hE (j : ℕ) : (∫ ω, X j ω ∂ν) = μ.real B := by
    have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) j
    change (∫ ω, f (Function.eval j ω) ∂ν) = _
    rw [← integral_map hm.measurable.aemeasurable hf.aestronglyMeasurable,hm.map_eq]
    simp [f,integral_indicator hB,Measure.real]
  have hV (j : ℕ) : variance (X j) ν ≤ μ.real B := by
    have hid : X j ^ 2 = X j := by
      funext ω
      by_cases h : ω j ∈ B <;> simp [Pi.pow_apply,X,f,h]
    simpa only [hid,hE] using variance_le_expectation_sq (hX j).1
  have hind : iIndepFun X ν := iIndepFun_infinitePi (P := fun _ => μ) (fun _ => hf)
  have hmem : MemLp S 2 ν := memLp_finsetSum' _ (fun i _ => hX i)
  have hsum (ω) : S ω = ∑ j ∈ Finset.range m, X j ω := by simp [S,Finset.sum_apply]
  have hexp : (∫ ω, S ω ∂ν) = (m:ℝ)*μ.real B := by
    simp only [hsum,integral_finsetSum _ (fun i _ => (hX i).integrable (by norm_num)),hE,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hvar : variance S ν ≤ (m:ℝ)*μ.real B := by
    rw [show variance S ν = _ from IndepFun.variance_sum (fun i _ => hX i)
      (fun _ _ _ _ h => hind.indepFun h)]
    simpa using (Finset.sum_le_sum (s := Finset.range m) (fun j _ => hV j))
  have hbad := meas_ge_le_variance_div_sq hmem (half_pos hmean)
  rw [hexp] at hbad
  apply le_trans (measure_mono (t := {ω | (m:ℝ)*μ.real B/2 ≤ |S ω-(m:ℝ)*μ.real B|}) ?_)
  · refine hbad.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ ((m:ℝ)*μ.real B)/((m:ℝ)*μ.real B/2)^2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
      _ = _ := by field_simp [hmean.ne']; ring
  · intro ω hω
    change (m:ℝ)*μ.real B/2 ≤ |S ω-(m:ℝ)*μ.real B|
    have hs : S ω = (((Finset.range m).filter (fun j => ω j ∈ B)).card : ℝ) := by
      simp only [hsum,X,f,Set.indicator_apply,Finset.sum_boole]
    refine le_trans ?_ (neg_le_abs _)
    rw [hs]
    change (((Finset.range m).filter (fun i => ω i ∈ B)).card : ℝ) < m*μ.real B/2 at hω
    linarith only [hω]

end
end GaloisForLFunctions.HTGeometry
