import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms
import GaloisForLFunctions.HTGeometry.ReplicaRationalGate

/-! # Squared-mass bound for overlapping Pauli interactions on a path -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {n : ℕ}

/-- Each path word has one or two nonidentity letters. -/
theorem pathWord_support_card_le_two (l : PathLabel n) : (labelSupport (pathWord l)).card ≤ 2 := by
  rcases l with ⟨s,a⟩ | ⟨e,ab⟩
  · apply (Finset.card_le_card (t := {s}) ?_).trans (by simp)
    intro v hv
    have h := mem_labelSupport.mp hv
    by_contra hn
    exact h (pathWord_none_of_not_incidentSite v _ (by simpa [pathIncident,eq_comm] using hn))
  · apply (Finset.card_le_card (t := {e.castSucc,e.succ}) ?_).trans
      ((Finset.card_insert_le _ _).trans (by simp))
    intro v hv
    by_contra hn
    exact mem_labelSupport.mp hv
      (pathWord_none_of_not_incidentSite v _ (by simpa [pathIncident,eq_comm] using hn))

/-- Labels whose supports meet that of the given interaction. -/
def pathOverlaps (l : PathLabel n) := (labelSupport (pathWord l)).biUnion pathIncidentLabels

theorem mem_pathOverlaps {l q : PathLabel n} :
    q ∈ pathOverlaps l ↔ ¬Disjoint (labelSupport (pathWord l)) (labelSupport (pathWord q)) := by
  classical
  rw [pathOverlaps,Finset.mem_biUnion,Finset.not_disjoint_iff]
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  change _ ∈ Finset.filter _ _ ↔ _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_labelSupport]
  exact ⟨pathWord_ne_none_of_incident,fun h => by
    by_contra hn
    exact h (pathWord_none_of_not_incidentSite v q hn)⟩

theorem pathOverlaps_card_le (l : PathLabel n) : (pathOverlaps l).card ≤ 42 :=
  (pathIncident_union_card _).trans (Nat.mul_le_mul_left 21 (pathWord_support_card_le_two l))

/-- Summing the two squared endpoint weights over all ordered overlaps
costs at most twice the maximum overlap degree times the total squared weight. -/
theorem path_sum_overlap_squares_le (u : PathShell n) :
    (∑ l : PathLabel n, ∑ q ∈ pathOverlaps l, ((u l)^2+(u q)^2)) ≤
      84*‖u‖^2 := by
  classical
  let w (l : PathLabel n) := (u l)^2
  have hsym (l q : PathLabel n) : q ∈ pathOverlaps l ↔ l ∈ pathOverlaps q := by
    rw [mem_pathOverlaps,mem_pathOverlaps,disjoint_comm]
  have hflip : (∑ l : PathLabel n, ∑ q ∈ pathOverlaps l, w q) =
      ∑ l : PathLabel n, ∑ _q ∈ pathOverlaps l, w l := by
    have hr (l : PathLabel n) (f : PathLabel n → ℝ) :
        (∑ q ∈ pathOverlaps l, f q) = ∑ q : PathLabel n, if q ∈ pathOverlaps l then f q else 0 := by
      rw [← Finset.sum_filter]; simp
    simp_rw [hr]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => if_congr (hsym q l) rfl rfl
  have hhalf : (∑ l : PathLabel n, ∑ _q ∈ pathOverlaps l, w l) ≤ 42*‖u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    simp only [Finset.sum_const,nsmul_eq_mul,Real.norm_eq_abs,sq_abs]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast pathOverlaps_card_le l) (sq_nonneg _)
  change (∑ l : PathLabel n, ∑ q ∈ pathOverlaps l, (w l+w q)) ≤ _
  simp_rw [Finset.sum_add_distrib]
  rw [hflip]
  linarith only [hhalf]

end
end GaloisForLFunctions.HTGeometry

