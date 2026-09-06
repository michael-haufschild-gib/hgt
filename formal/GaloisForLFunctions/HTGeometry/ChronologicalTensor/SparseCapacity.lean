import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Coalescence

/-!
# Exact capacity on physical sparse probes

Deleting the terminal unused gap leaves every pairing response unchanged
and cannot increase variation. Coalescence then preserves that zero gap.
The full monotone capacity is exactly the supremum on nonnegative,
nonadjacent physical probes with variation at most one.

This set is a cone. Its unit-variation section, needed for the topological
spectrum, is a separate normalization step for positive-degree pairings.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def terminalFreeProbe {n : ℕ} (g : Fin n → ℝ) : Fin n → ℝ :=
  fun q => if q.val+1=n then 0 else g q

theorem terminalFreeProbe_variation {n : ℕ} (g : Fin n → ℝ) :
    variation (terminalFreeProbe g) ≤ variation g := by
  unfold variation
  apply Finset.sum_le_sum
  intro q hq
  unfold terminalFreeProbe
  split_ifs
  · exact (abs_zero : |(0 : ℝ)|=0).trans_le (abs_nonneg _)
  · exact le_rfl

theorem endpointPositions_terminalFree {n : ℕ} (g : Fin n → ℝ) :
    endpointPositions (terminalFreeProbe g)=endpointPositions g := by
  ext q
  unfold endpointPositions
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i < q
  · have ht : i.val+1 ≠ n := by
      have hq := q.isLt
      change i.val < q.val at h
      omega
    simp only [endpointPulse,if_pos h,terminalFreeProbe,if_neg ht]
  · simp only [endpointPulse,if_neg h]

theorem enumeratedFamily_terminalFree {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (g : Fin (2*d) → ℝ) :
    familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) (terminalFreeProbe g)=
      familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) g := by
  rw [enumeratedFamily_gap_value,enumeratedFamily_gap_value,endpointPositions_terminalFree]

def physicalSparseValues {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) : Set ℝ :=
  {y | ∃ g : Fin (2*d) → ℝ, (∀ q, 0 ≤ g q) ∧ variation g ≤ 1 ∧
    separatedSupport g ∧ (∀ q, q.val+1=2*d → g q=0) ∧
    y=|familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) g|}

theorem physicalSparseValues_nonempty {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) :
    (physicalSparseValues E c).Nonempty := by
  refine ⟨_,(fun _ => 0),fun _ => le_rfl,?_,fun _ => Or.inl rfl,fun _ _ => rfl,rfl⟩
  simp only [variation,abs_zero,Finset.sum_const_zero]
  exact zero_le_one

theorem physicalSparseValues_bddAbove {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) :
    BddAbove (physicalSparseValues E c) := by
  refine ⟨monotoneCapacity (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c),?_⟩
  rintro y ⟨g,hnn,hvar,hsep,hterminal,rfl⟩
  have hfix : monotoneProbe g=g := by
    ext q
    simp only [monotoneProbe,normalizeProbe,max_eq_left hvar,div_one,abs_of_nonneg (hnn q)]
  rw [← hfix]
  exact monotoneCapacity_probe_bound _ _ g

theorem monotoneCapacity_physical_sparse {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) :
    monotoneCapacity (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)=
      sSup (physicalSparseValues E c) := by
  let F := familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨g,rfl⟩
    let p := terminalFreeProbe (monotoneProbe g)
    have hp : ∀ q, 0 ≤ p q := by
      intro q
      dsimp only [p,terminalFreeProbe]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
    have hpvar : variation p ≤ 1 :=
      (terminalFreeProbe_variation (monotoneProbe g)).trans (monotoneProbe_budget g)
    obtain ⟨h,hnn,hvar,hzeros,hdom,hsep,hcount⟩ := enumeratedFamily_monotone_coalescence E c p
    have hpabs : (fun q => |p q|)=p := funext (fun q => abs_of_nonneg (hp q))
    rw [hpabs] at hdom
    have hsame : F p=F (monotoneProbe g) := enumeratedFamily_terminalFree E c _
    change |F p| ≤ |F h| at hdom
    rw [hsame] at hdom
    apply hdom.trans
    apply le_csSup (physicalSparseValues_bddAbove E c)
    refine ⟨h,hnn,hvar.le.trans hpvar,hsep,?_,rfl⟩
    intro q hq
    apply hzeros
    simp only [p,terminalFreeProbe,if_pos hq]
  · apply csSup_le (physicalSparseValues_nonempty E c)
    rintro y ⟨g,hnn,hvar,hsep,hterminal,rfl⟩
    have hfix : monotoneProbe g=g := by
      ext q
      simp only [monotoneProbe,normalizeProbe,max_eq_left hvar,div_one,abs_of_nonneg (hnn q)]
    rw [← hfix]
    exact monotoneCapacity_probe_bound _ _ g

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
