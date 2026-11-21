import Mathlib.Probability.Moments.Variance

/-! # A missed-event bound with explicit pairwise excess -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FirstClockIndex
noncomputable section

/-- A block of R tests with marginal p and off-diagonal joint probability
at most p²b misses with probability at most 1/(Rp)+b−1. -/
theorem missed_block {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : ℕ} (hR : 0 < R) (A : Fin R → Set Ω) (hm : ∀ i, MeasurableSet (A i))
    {p b : ℝ} (hp : 0 < p) (hb : 1 ≤ b) (hvol : ∀ i, μ.real (A i) = p)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ p^2*b) :
    μ.real (⋃ i, A i)ᶜ ≤ 1/((R:ℝ)*p)+(b-1) := by
  classical
  let f (i : Fin R) := (A i).indicator (fun _ : Ω => (1:ℝ))
  let Z := ∑ i, f i
  let E := (R:ℝ)*p
  have hE : 0 < E := mul_pos (Nat.cast_pos.mpr hR) hp
  have hf (i) : MemLp (f i) 2 μ := (memLp_const _).indicator (hm i)
  have hz : MemLp Z 2 μ := memLp_finsetSum' _ (fun i _ => hf i)
  have hmu (i) : ∫ x, f i x ∂μ = p := (integral_indicator_one (hm i)).trans (hvol i)
  have eval (x : Ω) : Z x = ∑ i, f i x := Finset.sum_apply _ _ _
  have mean : ∫ x, Z x ∂μ = E := by
    simp only [eval]
    rw [integral_finsetSum _ (fun i _ => (hf i).integrable (by norm_num))]
    simp [hmu,E]
  have cov (i j : Fin R) : covariance (f i) (f j) μ = μ.real (A i ∩ A j)-p^2 := by
    rw [covariance_eq_sub (hf i) (hf j),hmu,hmu,←sq]
    congr 1
    have eqf : (fun x => f i x*f j x) = (A i ∩ A j).indicator (fun _ => 1) := by
      funext x
      by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;> simp [f,hi,hj]
    change (∫ x, f i x*f j x ∂μ) = _
    rw [eqf]
    exact integral_indicator_one ((hm i).inter (hm j))
  have hvar : variance Z μ ≤ E+E^2*(b-1) := by
    rw [show Z = ∑ i, f i from rfl,variance_sum hf]
    calc
      _ ≤ ∑ i : Fin R, ∑ j : Fin R, (p^2*(b-1) + if i=j then p else 0) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [cov]
        by_cases h : i=j
        · subst j; rw [inter_self,hvol,if_pos rfl]
          linarith only [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hb),sq_nonneg p]
        · rw [if_neg h,add_zero]
          linarith only [hpair i j h]
      _ = _ := by simp [E,Finset.sum_add_distrib]; ring
  have inc : (⋃ i, A i)ᶜ ⊆ {x | E ≤ |Z x-(∫ y, Z y ∂μ)|} := by
    intro x hx
    have hn (i : Fin R) : x ∉ A i := fun hh => hx (mem_iUnion.mpr ⟨i,hh⟩)
    change E ≤ |Z x-(∫ y, Z y ∂μ)|
    rw [mean,eval]
    simp [f,hn,abs_of_pos hE]
  have h := (measure_mono inc).trans (meas_ge_le_variance_div_sq hz hE)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at ht
  apply (ht.trans (div_le_div_of_nonneg_right hvar (sq_nonneg E))).trans_eq
  field_simp [hE.ne']
  ring

#print axioms missed_block
end
end GaloisForLFunctions.HTGeometry.FirstClockIndex
