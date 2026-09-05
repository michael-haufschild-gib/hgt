import GaloisForLFunctions.HTGeometry.ChronologicalTensor.EndpointAffinity

/-!
# Adjacent transfer of chronological gaps

Redistributing two neighboring gaps moves only their shared endpoint.
Every genuine pairing family is therefore affine along this transfer,
with no sign or interpolation assumptions. Both endpoint merges preserve
the sum of all gaps and set one specified gap to zero.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def gapTransfer {n : ℕ} (g : Fin n → ℝ) (a b : Fin n) (z : ℝ) : Fin n → ℝ :=
  fun q => g q+(if q=a then z else 0)-(if q=b then z else 0)

def adjacentLower {n : ℕ} (a : Fin (n-1)) : Fin n :=
  ⟨a.val,by have h := a.isLt; omega⟩

def adjacentUpper {n : ℕ} (a : Fin (n-1)) : Fin n :=
  ⟨a.val+1,by have h := a.isLt; omega⟩

theorem adjacentLower_lt_upper {n : ℕ} (a : Fin (n-1)) :
    adjacentLower a < adjacentUpper a := by
  change a.val < a.val+1
  omega

theorem gapTransfer_zero {n : ℕ} (g : Fin n → ℝ) (a b : Fin n) :
    gapTransfer g a b 0 = g := by
  ext q
  simp [gapTransfer]

theorem endpointPositions_add {n : ℕ} (g h : Fin n → ℝ) :
    endpointPositions (fun q => g q+h q) = fun q => endpointPositions g q+endpointPositions h q := by
  ext q
  unfold endpointPositions
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i < q <;> simp [endpointPulse,h]

theorem endpointPositions_sub {n : ℕ} (g h : Fin n → ℝ) :
    endpointPositions (fun q => g q-h q) = fun q => endpointPositions g q-endpointPositions h q := by
  ext q
  unfold endpointPositions
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i < q <;> simp [endpointPulse,h]

theorem endpointPositions_single {n : ℕ} (a : Fin n) (z : ℝ) (q : Fin n) :
    endpointPositions (fun i => if i=a then z else 0) q = endpointPulse a z q := by
  classical
  unfold endpointPositions
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [hba,endpointPulse]
  · simp

theorem endpointPositions_transfer {n : ℕ} (g : Fin n → ℝ) (a b : Fin n) (z : ℝ) (q : Fin n) :
    endpointPositions (gapTransfer g a b z) q =
      endpointPositions g q+endpointPulse a z q-endpointPulse b z q := by
  unfold gapTransfer
  rw [endpointPositions_sub,endpointPositions_add]
  simp only [endpointPositions_single]

theorem endpointPositions_adjacent_transfer {n : ℕ} (g : Fin n → ℝ)
    (a : Fin (n-1)) (z : ℝ) :
    endpointPositions (gapTransfer g (adjacentLower a) (adjacentUpper a) z) =
      Function.update (endpointPositions g) (adjacentUpper a)
        (endpointPositions g (adjacentUpper a)+z) := by
  ext q
  rw [endpointPositions_transfer]
  by_cases hq : q=adjacentUpper a
  · subst q
    simp [endpointPulse,adjacentLower_lt_upper]
  · rw [Function.update_of_ne hq]
    have hnq : q.val ≠ a.val+1 := by
      intro h
      apply hq
      exact Fin.ext h
    by_cases hl : adjacentLower a < q
    · have hu : adjacentUpper a < q := by
        change a.val+1 < q.val
        change a.val < q.val at hl
        omega
      simp [endpointPulse,hl,hu]
    · have hu : ¬adjacentUpper a < q := by
        change ¬a.val+1 < q.val
        change ¬a.val < q.val at hl
        omega
      simp [endpointPulse,hl,hu]

theorem enumeratedFamily_adjacent_affine {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (g : Fin (2*d) → ℝ) (a : Fin (2*d-1)) (s t u : ℝ) :
    familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
        (gapTransfer g (adjacentLower a) (adjacentUpper a) ((1-u)*s+u*t)) =
      (1-u)*familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
        (gapTransfer g (adjacentLower a) (adjacentUpper a) s)+
      u*familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
        (gapTransfer g (adjacentLower a) (adjacentUpper a) t) := by
  simp only [enumeratedFamily_gap_value,endpointPositions_adjacent_transfer]
  rw [show endpointPositions g (adjacentUpper a)+((1-u)*s+u*t) =
    (1-u)*(endpointPositions g (adjacentUpper a)+s)+u*(endpointPositions g (adjacentUpper a)+t) by ring]
  exact enumeratedFamily_endpoint_affine E c (endpointPositions g) (adjacentUpper a) _ _ u

theorem gapTransfer_sum {n : ℕ} (g : Fin n → ℝ) (a b : Fin n) (z : ℝ) :
    (∑ q, gapTransfer g a b z q) = ∑ q, g q := by
  classical
  simp [gapTransfer,Finset.sum_sub_distrib,Finset.sum_add_distrib]

theorem gapTransfer_adjacent_lower {n : ℕ} (g : Fin n → ℝ)
    (a : Fin (n-1)) (z : ℝ) :
    gapTransfer g (adjacentLower a) (adjacentUpper a) z (adjacentLower a) =
      g (adjacentLower a)+z := by
  simp [gapTransfer,ne_of_lt (adjacentLower_lt_upper a)]

theorem gapTransfer_adjacent_upper {n : ℕ} (g : Fin n → ℝ)
    (a : Fin (n-1)) (z : ℝ) :
    gapTransfer g (adjacentLower a) (adjacentUpper a) z (adjacentUpper a) =
      g (adjacentUpper a)-z := by
  simp [gapTransfer,ne_of_gt (adjacentLower_lt_upper a)]

def mergeAdjacentLeft {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1)) : Fin n → ℝ :=
  gapTransfer g (adjacentLower a) (adjacentUpper a) (-g (adjacentLower a))

def mergeAdjacentRight {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1)) : Fin n → ℝ :=
  gapTransfer g (adjacentLower a) (adjacentUpper a) (g (adjacentUpper a))

theorem mergeAdjacentLeft_lower {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1)) :
    mergeAdjacentLeft g a (adjacentLower a) = 0 := by
  simp [mergeAdjacentLeft,gapTransfer_adjacent_lower]

theorem mergeAdjacentRight_upper {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1)) :
    mergeAdjacentRight g a (adjacentUpper a) = 0 := by
  simp [mergeAdjacentRight,gapTransfer_adjacent_upper]

theorem mergeAdjacentLeft_sum {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1)) :
    (∑ q, mergeAdjacentLeft g a q) = ∑ q, g q :=
  gapTransfer_sum g _ _ _

theorem mergeAdjacentRight_sum {n : ℕ} (g : Fin n → ℝ) (a : Fin (n-1)) :
    (∑ q, mergeAdjacentRight g a q) = ∑ q, g q :=
  gapTransfer_sum g _ _ _

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
