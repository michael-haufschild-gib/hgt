import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! # Occupation charged to rising intervals and terminal parts of genuine waits -/

open Set Finset MeasureTheory
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
noncomputable section

/-- On a timeline of full cycles, charge each rising interval and the
last W time units of its wait. These pieces are disjoint even when the
entire wait is shorter than W. -/
theorem charge_windows (v σ : ℕ → ℝ) {W : ℝ} (hW : 0≤W)
    (hr : ∀ i, v i≤σ i) (hw : ∀ i, σ i≤v (i+1)) (A : Set ℝ)
    (hpre : ∀ i, Ico (v i) (σ i) ⊆ A)
    (hpost : ∀ i, Ico (max (σ i) (v (i+1)-W)) (v (i+1)) ⊆ A) (n : ℕ) :
    ∑ i ∈ range n, ((σ i-v i)+min W (v (i+1)-σ i)) ≤ volume.real (A∩Icc (v 0) (v n)) := by
  classical
  let L (i : ℕ) := Ico (v i) (σ i)
  let R (i : ℕ) := Ico (max (σ i) (v (i+1)-W)) (v (i+1))
  let B (i : Fin n) := L i.val ∪ R i.val
  have mono : Monotone v := monotone_nat_of_le_succ fun i => (hr i).trans (hw i)
  have box (i : Fin n) : B i ⊆ Ico (v i.val) (v (i.val+1)) := by
    rintro t (hl|ht)
    · exact ⟨hl.1,hl.2.trans_le (hw _)⟩
    · exact ⟨(hr _).trans ((le_max_left ..).trans ht.1),ht.2⟩
  have dis (i j : Fin n) (hij : i<j) : Disjoint (B i) (B j) := Set.disjoint_left.mpr fun _ hi hj =>
    (box i hi).2.not_ge ((mono (show i.val+1≤j.val from hij)).trans (box j hj).1)
  have hp : Pairwise (fun i j => Disjoint (B i) (B j)) := fun i j h =>
    (lt_or_gt_of_ne h).elim (dis i j) (fun hg => (dis j i hg).symm)
  have hb (i : Fin n) : volume (B i)≠⊤ := measure_ne_top_of_subset (box i) measure_Ico_lt_top.ne
  have hvol (i : Fin n) : volume.real (B i)=(σ i.val-v i.val)+min W (v (i.val+1)-σ i.val) := by
    have hd : Disjoint (L i.val) (R i.val) := Set.disjoint_left.mpr fun t ht h =>
      ht.2.not_ge ((le_max_left ..).trans h.1)
    change volume.real (L i.val ∪ R i.val)=_
    rw [measureReal_union hd measurableSet_Ico measure_Ico_lt_top.ne measure_Ico_lt_top.ne]
    dsimp only [L,R]
    rw [Real.volume_real_Ico_of_le (hr _),Real.volume_real_Ico_of_le (max_le (hw _) (sub_le_self _ hW))]
    congr 1
    rcases le_total (σ i.val) (v (i.val+1)-W) with h|h
    · rw [max_eq_right h,min_eq_left (by linarith only [h])]; ring
    · rw [max_eq_left h,min_eq_right (by linarith only [h])]
  have hsub : (⋃ i, B i) ⊆ A∩Icc (v 0) (v n) := by
    intro t ht
    obtain ⟨j,hj⟩ := mem_iUnion.mp ht
    exact ⟨hj.elim (fun h => hpre j.val h) (fun h => hpost j.val h), (mono (Nat.zero_le _)).trans (box j hj).1,
      (box j hj).2.le.trans (mono j.isLt)⟩
  calc
    _ = ∑ i : Fin n, volume.real (B i) := by
      simp_rw [hvol]
      exact (Fin.sum_univ_eq_sum_range (fun i => (σ i-v i)+min W (v (i+1)-σ i)) n).symm
    _ = volume.real (⋃ i, B i) := (measureReal_iUnion_fintype hp (fun _ => measurableSet_Ico.union measurableSet_Ico) hb).symm
    _ ≤ _ := measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated

