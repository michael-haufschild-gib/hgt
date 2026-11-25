import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.Averaging

/-! # A finite counting bound on every spectral sampling clock -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- Subtracting the first translated hit injects all hits into the
affordable indices of the same unshifted record. -/
private theorem tick_injection (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ i j, j ≤ i → P i → P j → Q (i-j)) (n : ℕ) :
    ((Finset.range n).filter P).card ≤ ((Finset.range n).filter Q).card := by
  let F := (Finset.range n).filter P
  by_cases hne : F.Nonempty
  · let b := F.min' hne
    have hb := F.min'_mem hne
    apply Finset.card_le_card_of_injOn (fun k => k-b)
    · intro k hk
      have hc := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Nat.sub_le k b).trans_lt (Finset.mem_range.mp hc.1)),
        h k b (F.min'_le _ hk) hc.2 (Finset.mem_filter.mp hb).2⟩
    · intro k hk j hj heq
      have hk' := F.min'_le _ hk
      have hj' := F.min'_le _ hj
      change k-b=j-b at heq
      omega
  · change F.card ≤ _
    simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.zero_le]

/-- The Haar probability of a phase target bounds from below the fraction
of allowed difference indices on each finite record. Sampling periods with
rational relations satisfy the same estimate. -/
theorem translated_tick_floor {I : Type*} [Fintype I] (z : ℕ → I → UnitAddCircle)
    (A : Set (I → UnitAddCircle)) (hm : MeasurableSet A) (Q : ℕ → Prop) [DecidablePred Q]
    (hpair : ∀ y i j, j ≤ i → z i+y ∈ A → z j+y ∈ A → Q (i-j)) (n : ℕ) :
    (n:ℝ)*volume.real A ≤ (((Finset.range n).filter Q).card:ℝ) := by
  classical
  let E (i : ℕ) := (fun y => z i+y) ⁻¹' A
  let f (i : ℕ) := (E i).indicator (fun _ => (1:ℝ))
  have hmE (i) : MeasurableSet (E i) := hm.preimage (continuous_const.add continuous_id).measurable
  have hI (i) : Integrable (f i) volume := (integrable_const _).indicator (hmE i)
  have hmean (i) : ∫ y, f i y = volume.real A :=
    (integral_indicator_one (hmE i)).trans ((measurePreserving_add_left volume (z i)).measureReal_preimage hm.nullMeasurableSet)
  let m := ((Finset.range n).filter Q).card
  have bound (y : I → UnitAddCircle) : ∑ i∈Finset.range n,f i y ≤ (m:ℝ) := by
    have h := tick_injection (fun i => y ∈ E i) Q (hpair y) n
    have heq : (∑ i∈Finset.range n, f i y) = (((Finset.range n).filter (fun i => y ∈ E i)).card:ℝ) := by
      simp only [Finset.card_filter,Nat.cast_sum,Set.indicator_apply,f,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [heq]
    exact_mod_cast h
  calc
    (n:ℝ)*volume.real A = ∫ y, ∑ i∈Finset.range n,f i y := by
      rw [integral_finsetSum _ (fun i _ => hI i)]
      simp only [hmean,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    _ ≤ ∫ _ : I → UnitAddCircle, (m:ℝ) := integral_mono
      (integrable_finsetSum _ (fun i _ => hI i)) (integrable_const _) bound
    _ = _ := by simp only [integral_const,probReal_univ,one_smul,m]

#print axioms translated_tick_floor
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
