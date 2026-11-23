import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.FirstScale

/-! # Total forecast length for any finite list of budgets and first-return dates -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
noncomputable section

/-- Truncation at B charges only the total forecast length, regardless
of the positions, overlaps, or different return budgets. -/
theorem late_forecast_union (n j b : ℕ) {I : Type*} [Fintype I]
    (s : I→ℕ) (t w : I→ℝ) (hs : ∀ i, s i ≤ b) (hw : ∀ i, 0 ≤ w i) {B : ℝ} (hB : 0 < B) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let m := Fintype.card (ChainLabel (n+2))
    μ.real {x | B < crossingWait n j b x ∧ ∃ i, crossingWait n j (s i) x ∈ Ioc (t i) (t i+w i)} ≤
      1024*sqrt m*(∑ i, w i)/B := by
  classical
  intro μ m
  let L (i : I) := max B (t i)
  let A (i : I) := {x | crossingWait n j (s i) x ∈ Ioc (L i) (L i+w i)}
  have hsub : {x | B < crossingWait n j b x ∧ ∃ i, crossingWait n j (s i) x ∈ Ioc (t i) (t i+w i)}
      ⊆ ⋃ i, A i := by
    rintro x ⟨h,i,hi⟩
    have hx := h.trans_le (crossingWait_antitone (hs i) x)
    exact mem_iUnion.mpr ⟨i,max_lt hx hi.1,hi.2.trans (add_le_add (le_max_right ..) le_rfl)⟩
  have price (i : I) : μ.real (A i) ≤ 1024*sqrt m*w i/B := by
    have hl : 0 < L i := hB.trans_le (le_max_left ..)
    exact (first_wait_window n j (s i) hl (hw i)).trans
      (div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (hw i)) hB (le_max_left ..))
  calc _ ≤ ∑ i, μ.real (A i) := (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le A)
       _ ≤ ∑ i, 1024*sqrt m*w i/B := Finset.sum_le_sum fun i _ => price i
       _ = _ := by rw [←Finset.sum_div,←Finset.mul_sum]

/-- The cost of the early tail is paid just once even if every forecast
uses a different return budget and all its intervals overlap. -/
theorem first_wait_forecast_union (n j b : ℕ) {I : Type*} [Fintype I]
    (s : I→ℕ) (t w : I→ℝ) (hs : ∀ i, s i ≤ b) (hw : ∀ i, 0 ≤ w i) {B : ℝ} (hB : 0 < B) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let m := Fintype.card (ChainLabel (n+2))
    μ.real {x | ∃ i, crossingWait n j (s i) x ∈ Ioc (t i) (t i+w i)} ≤
      μ.real {x | crossingWait n j b x ≤ B}+1024*sqrt m*(∑ i, w i)/B := by
  intro μ m
  let F := {x | ∃ i, crossingWait n j (s i) x ∈ Ioc (t i) (t i+w i)}
  let A := {x | B < crossingWait n j b x ∧ x∈F}
  let E := {x | crossingWait n j b x ≤ B}
  have hsub : F ⊆ E∪A := fun x hx => (le_or_gt (crossingWait n j b x) B).imp_right (fun h => ⟨h,hx⟩)
  exact ((measureReal_mono (μ:=μ) hsub).trans (measureReal_union_le _ _)).trans
    (add_le_add le_rfl (late_forecast_union n j b s t w hs hw hB))

end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
