import GaloisForLFunctions.HTGeometry.ChronologicalTensor.GapTransfer
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Activation

/-!
# Cost-preserving monotone merges

An adjacent merge of absolute gaps remains nonnegative and preserves total
variation. If both entries were active, either merge strictly decreases
the number of active gaps. Endpoint affinity and the triangle inequality
show that one of the two merges never lowers absolute pairing response.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def mergeAdjacent {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1)) (side : Bool) : Fin n → ℝ :=
  if side then mergeAdjacentLeft g a else mergeAdjacentRight g a

theorem mergeAdjacent_apply {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1))
    (side : Bool) (q : Fin n) :
    mergeAdjacent g a side q =
      if q=adjacentLower a then (if side then 0 else g (adjacentLower a)+g (adjacentUpper a))
      else if q=adjacentUpper a then (if side then g (adjacentLower a)+g (adjacentUpper a) else 0)
      else g q := by
  have hne := ne_of_lt (adjacentLower_lt_upper a)
  by_cases hl : q=adjacentLower a
  · subst q
    cases side <;> simp [mergeAdjacent,mergeAdjacentLeft,mergeAdjacentRight,gapTransfer,hne]
  · by_cases hu : q=adjacentUpper a
    · subst q
      cases side <;>
        simp only [mergeAdjacent,mergeAdjacentLeft,mergeAdjacentRight,gapTransfer,
          Bool.false_eq_true,if_false,if_true,if_neg hne.symm,add_zero,sub_self,
          sub_neg_eq_add]
      ring
    · cases side <;> simp [mergeAdjacent,mergeAdjacentLeft,mergeAdjacentRight,gapTransfer,hl,hu]

theorem mergeAdjacent_nonneg {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1))
    (side : Bool) (q : Fin n) :
    0 ≤ mergeAdjacent (fun i => |g i|) a side q := by
  rw [mergeAdjacent_apply]
  split_ifs <;> positivity

theorem mergeAdjacent_variation {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1))
    (side : Bool) : variation (mergeAdjacent (fun i => |g i|) a side) = variation g := by
  unfold variation
  simp only [abs_of_nonneg (mergeAdjacent_nonneg g a side _)]
  cases side <;> simp only [mergeAdjacent,Bool.false_eq_true,if_false,if_true,
    mergeAdjacentRight_sum,mergeAdjacentLeft_sum]

theorem mergeAdjacent_support_decreases {n : ℕ} (g : Fin n → ℝ)
    (a : Fin (n-1)) (side : Bool) :
    g (adjacentLower a)=0 ∨ g (adjacentUpper a)=0 ∨
      activeGapCount (mergeAdjacent g a side) < activeGapCount g := by
  classical
  by_cases hl : g (adjacentLower a)=0
  · exact Or.inl hl
  by_cases hu : g (adjacentUpper a)=0
  · exact Or.inr (Or.inl hu)
  right; right
  unfold activeGapCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro q hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hv := (Finset.mem_filter.mp hq).2
    by_cases hqlo : q=adjacentLower a
    · simpa [hqlo] using hl
    by_cases hqup : q=adjacentUpper a
    · simpa [hqup] using hu
    simpa only [mergeAdjacent_apply,if_neg hqlo,if_neg hqup] using hv
  · intro heq
    cases side
    · have hmem : adjacentUpper a ∈ Finset.univ.filter (fun q => g q ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩
      rw [← heq] at hmem
      have hv := (Finset.mem_filter.mp hmem).2
      exact hv (mergeAdjacentRight_upper g a)
    · have hmem : adjacentLower a ∈ Finset.univ.filter (fun q => g q ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩
      rw [← heq] at hmem
      have hv := (Finset.mem_filter.mp hmem).2
      exact hv (mergeAdjacentLeft_lower g a)

theorem enumeratedFamily_merge_bound {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (g : Fin (2*d) → ℝ) (a : Fin (2*d-1)) :
    |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) (fun q => |g q|)| ≤
      max (|familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
        (mergeAdjacentLeft (fun q => |g q|) a)|)
        (|familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
        (mergeAdjacentRight (fun q => |g q|) a)|) := by
  let p : Fin (2*d) → ℝ := fun q => |g q|
  let F := familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
  change |F p| ≤ max (|F (mergeAdjacentLeft p a)|) (|F (mergeAdjacentRight p a)|)
  have hl : 0 ≤ p (adjacentLower a) := abs_nonneg _
  have hu : 0 ≤ p (adjacentUpper a) := abs_nonneg _
  by_cases hz : p (adjacentLower a)+p (adjacentUpper a)=0
  · have hlz : p (adjacentLower a)=0 := by linarith only [hl,hu,hz]
    have hmerge : mergeAdjacentLeft p a=p := by
      rw [mergeAdjacentLeft,hlz,neg_zero,gapTransfer_zero]
    rw [hmerge]
    exact le_max_left _ _
  · have hpos : 0 < p (adjacentLower a)+p (adjacentUpper a) :=
      lt_of_le_of_ne (add_nonneg hl hu) (Ne.symm hz)
    let u := p (adjacentLower a)/(p (adjacentLower a)+p (adjacentUpper a))
    have hu0 : 0 ≤ u := div_nonneg hl hpos.le
    have hu1 : u ≤ 1 := (div_le_one hpos).mpr (by linarith only [hu])
    have hmix : (1-u)*(-p (adjacentLower a))+u*p (adjacentUpper a)=0 := by
      dsimp only [u]
      field_simp
      ring
    have h := enumeratedFamily_adjacent_affine E c p a
      (-p (adjacentLower a)) (p (adjacentUpper a)) u
    rw [hmix,gapTransfer_zero] at h
    change F p=(1-u)*F (mergeAdjacentLeft p a)+u*F (mergeAdjacentRight p a) at h
    rw [h]
    calc
      _ ≤ |(1-u)*F (mergeAdjacentLeft p a)|+|u*F (mergeAdjacentRight p a)| := abs_add_le _ _
      _ = (1-u)*|F (mergeAdjacentLeft p a)|+u*|F (mergeAdjacentRight p a)| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hu1),abs_of_nonneg hu0]
      _ ≤ (1-u)*max (|F (mergeAdjacentLeft p a)|) (|F (mergeAdjacentRight p a)|)+
          u*max (|F (mergeAdjacentLeft p a)|) (|F (mergeAdjacentRight p a)|) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hu1))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hu0)
      _ = _ := by ring

theorem enumeratedFamily_merge_choice {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (g : Fin (2*d) → ℝ) (a : Fin (2*d-1)) :
    ∃ side : Bool,
      |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) (fun q => |g q|)| ≤
        |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
          (mergeAdjacent (fun q => |g q|) a side)| := by
  let p : Fin (2*d) → ℝ := fun q => |g q|
  let F := familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
  change ∃ side : Bool, |F p| ≤ |F (mergeAdjacent p a side)|
  have h := enumeratedFamily_merge_bound E c g a
  change |F p| ≤ max (|F (mergeAdjacentLeft p a)|) (|F (mergeAdjacentRight p a)|) at h
  rcases le_total (|F (mergeAdjacentLeft p a)|) (|F (mergeAdjacentRight p a)|) with hl | hr
  · exact ⟨false,by simpa only [mergeAdjacent,Bool.false_eq_true,if_false,max_eq_right hl] using h⟩
  · exact ⟨true,by simpa only [mergeAdjacent,if_true,max_eq_left hr] using h⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
