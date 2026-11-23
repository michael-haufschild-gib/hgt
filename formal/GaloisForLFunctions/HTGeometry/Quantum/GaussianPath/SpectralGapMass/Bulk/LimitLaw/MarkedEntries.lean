import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows

/-! # Entry counts with a prescribed subset of closing spectral pairs -/
open MeasureTheory Filter Finset Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
open EmptyVisitFlux
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Physical entries whose defining closed face has one of the specified pairs.
An entry with several such pairs counts once. -/
def selectedDates (E : I→ℝ) (S : Finset (I×I)) (r T : ℝ) : Finset ℝ := by
  classical
  exact S.biUnion fun p => markedDates E p.1 p.2 r (forwardUnitArc r) T

/-- Contribution of these pairs to the entry flux before the angular factor. -/
def selectedRate (E : I→ℝ) (S : Finset (I×I)) : ℝ :=
  ∑ p ∈ S, max 0 (E p.1-E p.2)/(2*π)

theorem selected_dates_rate (E : I→ℝ) (hi : MaximallyProjectiveEnergy E) (S : Finset (I×I))
    {r : ℝ} (hr : 0 < r) (hs : r < 1/2) :
    Tendsto (fun T : ℝ => ((selectedDates E S r T).card:ℝ)/T) atTop
      (𝓝 (r^(Fintype.card I-2)*selectedRate E S)) := by
  classical
  let V (A : Set UnitAddCircle) (T : ℝ) (p : I×I) := markedDates E p.1 p.2 r A T
  let O := openArc r
  let C := forwardUnitArc r
  let count (A : Set UnitAddCircle) (T : ℝ) := ∑ p ∈ S, ((V A T p).card:ℝ)/T
  have hh : r < 1 := by linarith only [hs]
  have hlim (A) (hA : A∈({O,C}:Set (Set UnitAddCircle))) : Tendsto (count A) atTop
      (𝓝 (r^(Fintype.card I-2)*selectedRate E S)) := by
    rw [selectedRate,mul_sum]
    exact tendsto_finsetSum S fun p _ => markedDates_rate E hi p.1 p.2 ⟨r,hr.le,hs.le⟩ A hA
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim O (Or.inl rfl)) (hlim C (Or.inr rfl))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have hdis : (↑S : Set (I×I)).PairwiseDisjoint (V O T) := by
      intro p _ q _ hpq
      refine disjoint_left.mpr fun t hp hq => ?_
      have hf := ((mem_markedDates E p.1 p.2 hr.le hh O t T).mp hp).2.2
      have hg := ((mem_markedDates E q.1 q.2 hr.le hh O t T).mp hq).2.2
      have he := inward_endpoints_unique hr hs hf hg.2.1
      exact hpq (Prod.ext he.1.symm he.2.symm)
    have hsub : S.biUnion (V O T) ⊆ selectedDates E S r T := by
      intro t ht
      obtain ⟨p,hp,h⟩ := mem_biUnion.mp ht
      obtain ⟨h₀,hT',hf⟩ := (mem_markedDates E p.1 p.2 hr.le hh O t T).mp h
      refine mem_biUnion.mpr ⟨p,hp,(mem_markedDates E p.1 p.2 hr.le hh C t T).mpr ⟨h₀,hT',hf.1,hf.2.1,?_⟩⟩
      exact fun i h₁ h₂ => Set.image_mono Set.Ioo_subset_Icc_self (hf.2.2 i h₁ h₂)
    have h := Finset.card_le_card hsub
    rw [card_biUnion hdis] at h
    dsimp only [count]
    rw [←sum_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) hT
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have h : (selectedDates E S r T).card ≤ ∑ p ∈ S, (V C T p).card := card_biUnion_le
    dsimp only [count]
    rw [←sum_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) hT

/-- Restricting to dates after any fixed origin preserves the marked
fraction of actual entries. -/
theorem selected_entry_fraction (E : I→ℝ) (hi : MaximallyProjectiveEnergy E) (S : Finset (I×I))
    {r : ℝ} (hr : 0 < r) (hs : r < 1/2) (a : ℝ) (hp : 0 < pairTurnRate E) :
    Tendsto (fun T : ℝ => (((selectedDates E S r T) \ (entryDates E r a)).card:ℝ)/
      (entriesAfter E r a T).card) atTop (𝓝 (selectedRate E S/pairTurnRate E)) := by
  classical
  have remove (f : ℝ→Finset ℝ) (s : Finset ℝ) {K : ℝ}
      (h : Tendsto (fun T : ℝ => ((f T).card:ℝ)/T) atTop (𝓝 K)) :
      Tendsto (fun T : ℝ => (((f T) \ s).card:ℝ)/T) atTop (𝓝 K) := by
    have hc := (tendsto_id (x:= (atTop : Filter ℝ))).const_div_atTop (s.card:ℝ)
    have hl := h.sub hc
    rw [sub_zero] at hl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl h
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
      have hh := card_sdiff_add_card_inter (f T) s
      have hi := Finset.card_le_card (Finset.inter_subset_right : f T ∩ s ⊆ s)
      rw [id_eq,←sub_div]
      apply div_le_div_of_nonneg_right _ hT
      exact sub_le_iff_le_add.mpr (by exact_mod_cast (show (f T).card ≤ ((f T) \ s).card+s.card by omega))
    · exact (eventually_ge_atTop (0:ℝ)).mono fun T hT => div_le_div_of_nonneg_right
        (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : f T \ s ⊆ f T)) hT
  have hden := remove (entryDates E r) (entryDates E r a) (entry_count_rate E hi hr hs)
  have hnum := remove (selectedDates E S r) (entryDates E r a) (selected_dates_rate E hi S hr hs)
  have hpow := pow_pos hr (Fintype.card I-2)
  have hh := hnum.div hden (mul_pos hpow hp).ne'
  rw [mul_div_mul_left _ _ hpow.ne'] at hh
  exact hh.congr' ((eventually_gt_atTop (0:ℝ)).mono fun T hT =>
    div_div_div_cancel_right₀ hT.ne' _ _)

#print axioms selected_entry_fraction
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
