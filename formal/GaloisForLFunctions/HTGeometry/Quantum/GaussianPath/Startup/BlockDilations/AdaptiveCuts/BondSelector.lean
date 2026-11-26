import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SelectedCoordinates

/-! # A measurable weakest-bond selector preserved by one-sided dilations -/

open Finset Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

/-- Break ties in favour of the earliest bond in the buffer. -/
def IsFirstMinimum {I : Type*} [LinearOrder I] (f : I→ℝ) (i : I) : Prop :=
  (∀ j, f i≤f j) ∧ ∀ j < i, f i<f j

theorem existsUnique_firstMinimum {I : Type*} [Fintype I] [Nonempty I] [LinearOrder I] (f : I→ℝ) :
    ∃! i, IsFirstMinimum f i := by
  classical
  obtain ⟨k,_,hk⟩ := exists_min_image univ f univ_nonempty
  let C := univ.filter fun i => f i=f k
  have hC : C.Nonempty := ⟨k,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  let i := C.min' hC
  have hi := (mem_filter.mp (C.min'_mem hC)).2
  have he : IsFirstMinimum f i := by
    refine ⟨fun j => hi.trans_le (hk j (mem_univ _)),?_⟩
    intro j hj
    refine lt_of_le_of_ne (hi.trans_le (hk j (mem_univ _))) ?_
    intro hh
    exact hj.not_ge (min'_le C j (mem_filter.mpr ⟨mem_univ _,hh.symm.trans hi⟩))
  refine ⟨i,he,?_⟩
  intro j hj
  rcases lt_trichotomy j i with h|h|h
  · exact ((he.2 j h).not_ge (hj.1 i)).elim
  · exact h
  · exact ((hj.2 i h).not_ge (he.1 j)).elim

private theorem measurable_firstMinimum {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (f : I→X→ℝ) (hf : ∀ j, Measurable (f j)) (i : I) :
    MeasurableSet {x | IsFirstMinimum (fun j => f j x) i} := by
  have h : {x | IsFirstMinimum (fun j => f j x) i} =
      (⋂ j, {x | f i x≤f j x}) ∩ (⋂ j : {j : I // j < i}, {x | f i x<f j x}) := by
    ext x
    simp [IsFirstMinimum]
  rw [h]
  exact (MeasurableSet.iInter (fun j => measurableSet_le (hf i) (hf j))).inter
    (MeasurableSet.iInter (fun j => measurableSet_lt (hf i) (hf j)))

/-- Sum of squares of the nine Pauli couplings of a candidate bond. -/
def bondSquare {ι : Type*} (labels : Fin 9→ι) (x : ι→ℝ) := ∑ j, (x (labels j))^2

/-- Every weakest-bond ownership region is measurable in the original coordinates. -/
theorem measurable_bond_owner {ι I : Type*} [Fintype I] [LinearOrder I]
    (labels : I→Fin 9→ι) (i : I) :
    MeasurableSet {x : ι→ℝ | IsFirstMinimum (fun j => bondSquare (labels j) x) i} :=
  measurable_firstMinimum _ (fun _ => by unfold bondSquare; fun_prop) i

/-- Expansion away from the chosen bond preserves both minimality and the tie rule. -/
theorem expand_preserves_bond_owner {ι I : Type*} [DecidableEq ι] [LinearOrder I]
    (labels : I→Fin 9→ι) (S : Finset ι) {a : ℝ} (ha : 1≤a) (x : ι→ℝ) (i : I)
    (hi : IsFirstMinimum (fun j => bondSquare (labels j) x) i)
    (hS : ∀ k, labels i k∉S) :
    IsFirstMinimum (fun j => bondSquare (labels j) (expand S a x)) i := by
  have hsame : bondSquare (labels i) (expand S a x)=bondSquare (labels i) x := by
    apply sum_congr rfl
    intro k _
    rw [show expand S a x (labels i k)=x (labels i k) from if_neg (hS k)]
  have hinc (j : I) : bondSquare (labels j) x≤bondSquare (labels j) (expand S a x) := by
    apply sum_le_sum
    intro k _
    by_cases hm : labels j k∈S
    · rw [show expand S a x _=a*x (labels j k) from if_pos hm,mul_pow]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ ha)
    · rw [show expand S a x _=x (labels j k) from if_neg hm]
  exact ⟨fun j => hsame.trans_le ((hi.1 j).trans (hinc j)),
    fun j hj => hsame.trans_lt ((hi.2 j hj).trans_le (hinc j))⟩


/-- If a selectively expanded sample chooses a bond whose nine
coordinates were expanded, its precursor chooses the very same bond. -/
theorem expanded_owner_reflects {ι I : Type*} [DecidableEq ι] [LinearOrder I]
    (labels : I→Fin 9→ι) (S : Finset ι) {a : ℝ} (ha : 1≤a) (x : ι→ℝ) (i : I)
    (hi : IsFirstMinimum (fun j => bondSquare (labels j) (expand S a x)) i)
    (hS : ∀ k, labels i k∈S) :
    IsFirstMinimum (fun j => bondSquare (labels j) x) i := by
  have hp := sq_pos_of_pos (zero_lt_one.trans_le ha)
  have hsame : bondSquare (labels i) (expand S a x)=a^2*bondSquare (labels i) x := by
    unfold bondSquare
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [show expand S a x _=a*x (labels i k) from if_pos (hS k),mul_pow]
  have hle (j : I) : bondSquare (labels j) (expand S a x)≤a^2*bondSquare (labels j) x := by
    unfold bondSquare
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    by_cases hm : labels j k∈S
    · rw [show expand S a x _=a*x (labels j k) from if_pos hm,mul_pow]
    · rw [show expand S a x _=x (labels j k) from if_neg hm]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ ha)
  exact ⟨fun j => (mul_le_mul_iff_right₀ hp).mp (hsame.symm.trans_le ((hi.1 j).trans (hle j))),
    fun j hj => (mul_lt_mul_iff_right₀ hp).mp (hsame.symm.trans_lt ((hi.2 j hj).trans_le (hle j)))⟩

#print axioms expanded_owner_reflects
#print axioms existsUnique_firstMinimum
#print axioms measurable_bond_owner
#print axioms expand_preserves_bond_owner
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
