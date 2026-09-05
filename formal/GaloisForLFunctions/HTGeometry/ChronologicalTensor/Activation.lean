import GaloisForLFunctions.HTGeometry.ChronologicalTensor.TwoGap
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SealingExamples

/-!
# The sharp activation threshold for pairing reversal

Any probe supported on at most two gaps is represented by a two-gap face.
Thus reversal advantage for a nonempty perfect-pairing family requires at
least three active gaps. An explicit pair of genuine six-endpoint matchings
has monotone capacity one and a three-gap unit probe of magnitude 28/27.
The endpoint enumerations, interval windows, sparsity, and capacity comparison
are all constructed here without incidence or optimization assumptions.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def separatedEndpointPermutation : Equiv.Perm (Fin 6) where
  toFun := ![0,2,4,1,3,5]
  invFun := ![0,3,1,4,2,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def separatedEndpointEnumeration : (Fin 3 ⊕ Fin 3) ≃ Fin 6 :=
  finSumFinEquiv.trans separatedEndpointPermutation

def rainbowEndpointEnumeration : (Fin 3 ⊕ Fin 3) ≃ Fin 6 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3)) Fin.revPerm).trans finSumFinEquiv

def cubicPairingEnumerations : Fin 2 → ((Fin 3 ⊕ Fin 3) ≃ Fin 6) :=
  ![separatedEndpointEnumeration,rainbowEndpointEnumeration]

theorem cubicPairing_windows : enumeratedFamilyWindows cubicPairingEnumerations =
    ![![{0},{2},{4}],![{0,1,2,3,4},{1,2,3},{2}]] := by
  funext j i
  fin_cases j <;> fin_cases i <;> ext q <;> fin_cases q <;>
    simp [enumeratedFamilyWindows,enumeratedPairingWindows,cubicPairingEnumerations,
      separatedEndpointEnumeration,separatedEndpointPermutation,rainbowEndpointEnumeration,
      finSumFinEquiv,Finset.mem_Ico]

theorem cubicPairing_coefficients (A B : ℝ) :
    enumeratedFamilyCoefficients cubicPairingEnumerations ![A,B] = ![A,B] := by
  ext j
  fin_cases j <;>
    simp [enumeratedFamilyCoefficients,enumeratedPairingSign,endpointOrderSign,cubicPairingEnumerations,
      separatedEndpointEnumeration,separatedEndpointPermutation,rainbowEndpointEnumeration,
      finSumFinEquiv,Fin.prod_univ_three]

theorem cubicPairing_reversal_value (g : Fin 6 → ℝ) :
    familyValue (enumeratedFamilyWindows cubicPairingEnumerations)
      (enumeratedFamilyCoefficients cubicPairingEnumerations ![27,-1]) g =
      reversalResponse (g 0) (g 1) (g 2) (g 3) (g 4) := by
  rw [cubicPairing_windows,cubicPairing_coefficients]
  simp [familyValue,diagramValue,windowValue,Fin.sum_univ_two,Fin.prod_univ_three,
    reversalResponse,separatedThree,rainbowThree]
  ring

theorem cubicPairing_monotoneCapacity :
    monotoneCapacity (enumeratedFamilyWindows cubicPairingEnumerations)
      (enumeratedFamilyCoefficients cubicPairingEnumerations ![27,-1]) = 1 := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    rw [cubicPairing_reversal_value]
    let z := normalizeProbe g
    have hv : sixCost (z 0) (z 1) (z 2) (z 3) (z 4) ≤ 1 := by
      have hb := normalizeProbe_budget g
      change variation z ≤ 1 at hb
      rw [variation,Fin.sum_univ_six] at hb
      unfold sixCost
      linarith only [hb,abs_nonneg (z 5)]
    have h := monotone_reversal_bound (z 0) (z 1) (z 2) (z 3) (z 4)
    have h0 : 0 ≤ sixCost (z 0) (z 1) (z 2) (z 3) (z 4) := by unfold sixCost; positivity
    have hp := pow_le_pow_left₀ h0 hv 3
    rw [one_pow] at hp
    exact h.trans hp
  · have h := monotoneCapacity_probe_bound (enumeratedFamilyWindows cubicPairingEnumerations)
      (enumeratedFamilyCoefficients cubicPairingEnumerations (![27,-1] : Fin 2 → ℝ))
      (![0,0,1,0,0,0] : Fin 6 → ℝ)
    rw [cubicPairing_reversal_value] at h
    simpa [monotoneProbe,normalizeProbe,variation,Fin.sum_univ_six,
      reversalResponse,separatedThree,rainbowThree] using h

def cubicSparseProbe : Fin 6 → ℝ := ![1/3,0,-1/3,0,1/3,0]

def activeGapCount {n : ℕ} (g : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => g i ≠ 0)).card

theorem sparseProbe_twoGap_representation (r : ℕ) (g : Fin (2*(r+1)) → ℝ) :
    3 ≤ activeGapCount g ∨ ∃ (a : Fin (2*(r+1))) (offset : Fin (2*(r+1)-a.val-1))
      (u v : ℝ), g = twoGapProbe a (secondCut a offset) u v := by
  classical
  by_cases hlarge : 3 ≤ activeGapCount g
  · exact Or.inl hlarge
  · right
    let S := Finset.univ.filter (fun i => g i ≠ 0)
    have hs : S.card ≤ 2 := by
      change ¬ 3 ≤ S.card at hlarge
      omega
    have hu : 2 ≤ (Finset.univ : Finset (Fin (2*(r+1)))).card := by
      simp only [Finset.card_univ,Fintype.card_fin]
      omega
    obtain ⟨T,hST,_,hT⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hs hu
    obtain ⟨a,b,hne,hTab⟩ := Finset.card_eq_two.mp hT
    have hout (q : Fin (2*(r+1))) (hqa : q≠a) (hqb : q≠b) : g q=0 := by
      by_contra hn
      have hq : q∈S := by simp [S,hn]
      have ht := hST hq
      rw [hTab] at ht
      simp [hqa,hqb] at ht
    have ordered (a b : Fin (2*(r+1))) (hab : a<b)
        (hz : ∀ q, q≠a → q≠b → g q=0) :
        ∃ (a : Fin (2*(r+1))) (offset : Fin (2*(r+1)-a.val-1)) (u v : ℝ),
          g = twoGapProbe a (secondCut a offset) u v := by
      let offset : Fin (2*(r+1)-a.val-1) := ⟨b.val-a.val-1,by
        have hb := b.isLt
        have hh : a.val<b.val := hab
        omega⟩
      have hb : secondCut a offset=b := by
        apply Fin.ext
        change a.val+1+(b.val-a.val-1)=b.val
        have hh : a.val<b.val := hab
        omega
      refine ⟨a,offset,g a,g b,?_⟩
      rw [hb]
      ext q
      by_cases hqa : q=a
      · subst q
        simp [twoGapProbe,ne_of_lt hab]
      · by_cases hqb : q=b
        · subst q
          simp [twoGapProbe,ne_of_gt hab]
        · simp [twoGapProbe,hqa,hqb,hz q hqa hqb]
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact ordered a b hab hout
    · exact ordered b a hba (fun q hqb hqa => hout q hqa hqb)

theorem pairing_reversal_support_bound {r m : ℕ}
    (E : Fin m → ((Fin (r+1) ⊕ Fin (r+1)) ≃ Fin (2*(r+1)))) (c : Fin m → ℝ)
    (g : Fin (2*(r+1)) → ℝ) :
    |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) (normalizeProbe g)| ≤
        monotoneCapacity (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) ∨
      3 ≤ activeGapCount g := by
  rcases sparseProbe_twoGap_representation r g with h | ⟨a,offset,u,v,rfl⟩
  · exact Or.inr h
  · exact Or.inl (enumeratedFamily_twoGap_capacity_bound E c a offset u v)

theorem cubicSparseProbe_budget : variation cubicSparseProbe = 1 := by
  simp [variation,cubicSparseProbe,Fin.sum_univ_six]
  ring

theorem cubicSparseProbe_support : activeGapCount cubicSparseProbe = 3 := by
  classical
  have he : Finset.univ.filter (fun i => cubicSparseProbe i ≠ 0) = ({0,2,4} : Finset (Fin 6)) := by
    ext i
    fin_cases i <;> simp [cubicSparseProbe]
  unfold activeGapCount
  rw [he]
  simp

theorem cubicSparseProbe_value :
    familyValue (enumeratedFamilyWindows cubicPairingEnumerations)
      (enumeratedFamilyCoefficients cubicPairingEnumerations ![27,-1])
      (normalizeProbe cubicSparseProbe) = -28/27 := by
  rw [(normalizeProbe_fixed_iff cubicSparseProbe).mpr cubicSparseProbe_budget.le,
    cubicPairing_reversal_value]
  simp [cubicSparseProbe,reversalResponse,separatedThree,rainbowThree]
  ring

theorem cubicPairing_twoGap_bound (a : Fin 6) (offset : Fin (6-a.val-1)) (u v : ℝ) :
    |familyValue (enumeratedFamilyWindows cubicPairingEnumerations)
      (enumeratedFamilyCoefficients cubicPairingEnumerations ![27,-1])
      (normalizeProbe (twoGapProbe a (secondCut a offset) u v))| ≤ 1 := by
  have h := enumeratedFamily_twoGap_capacity_bound cubicPairingEnumerations
    (![27,-1] : Fin 2 → ℝ) a offset u v
  rwa [cubicPairing_monotoneCapacity] at h

theorem cubicPairing_threeGap_advantage :
    activeGapCount cubicSparseProbe = 3 ∧ variation cubicSparseProbe = 1 ∧
      monotoneCapacity (enumeratedFamilyWindows cubicPairingEnumerations)
        (enumeratedFamilyCoefficients cubicPairingEnumerations ![27,-1]) <
      |familyValue (enumeratedFamilyWindows cubicPairingEnumerations)
        (enumeratedFamilyCoefficients cubicPairingEnumerations ![27,-1])
        (normalizeProbe cubicSparseProbe)| := by
  refine ⟨cubicSparseProbe_support,cubicSparseProbe_budget,?_⟩
  rw [cubicPairing_monotoneCapacity,cubicSparseProbe_value,
    abs_of_neg (show (-28/27 : ℝ) < 0 by
      have h : (0 : ℝ) < 28/27 := by positivity
      linarith only [h])]
  linarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
