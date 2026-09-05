import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SharpDepth

/-!
# Perfect-pairing depth differs from unrestricted polynomial depth

Every linear combination of the three pairings on four ordered endpoints
has enclosure depth zero. The Pluecker relation reduces its capacity to the
two-generator formula. In contrast, a degree-two finite-window Chebyshev
form has depth two. Thus universal polynomial sharpness cannot be assumed
to hold within the perfect-pairing subspace.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem fourWindows_monotoneCapacity (A B : ℝ) :
    monotoneCapacity fourWindows ![A,B] = fourCapacity A B := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    have h := familyCapacity_probe_bound fourWindows (![A,B] : Fin 2 → ℝ) (fun i => |g i|)
    rw [normalizeProbe_abs,fourWindows_capacity] at h
    exact h
  · apply max_le
    · have h := monotoneCapacity_probe_bound fourWindows (![A,B] : Fin 2 → ℝ)
        (![1,0,1] : Fin 3 → ℝ)
      rw [fourWindows_value] at h
      have hg : monotoneProbe (![1,0,1] : Fin 3 → ℝ) = ![1/2,0,1/2] := by
        ext i
        fin_cases i <;> simp [monotoneProbe,normalizeProbe,variation,Fin.sum_univ_three]
          <;> rw [abs_of_pos (by positivity)] <;> ring
      rw [hg] at h
      change |A*(1/2*(1/2))+B*(0*(1/2+0+1/2))| ≤ _ at h
      rw [show A*(1/2*(1/2))+B*(0*(1/2+0+1/2))=A/4 by ring,abs_div] at h
      simpa only [abs_of_pos (show (0 : ℝ) < 4 by positivity)] using h
    · have h := monotoneCapacity_probe_bound fourWindows (![A,B] : Fin 2 → ℝ)
        (![0,1,0] : Fin 3 → ℝ)
      rw [fourWindows_value] at h
      simpa [monotoneProbe,normalizeProbe,variation,Fin.sum_univ_three,
        fourResponse,separated,enclosing] using h

theorem fourWindows_sealedCapacity (A B : ℝ) (k : ℕ) :
    sealedCapacity fourWindows ![A,B] k = fourCapacity A B := by
  apply le_antisymm
  · have h := sealedCapacity_add_depth fourWindows (![A,B] : Fin 2 → ℝ) 0 k
    have h0 : sealedCapacity fourWindows ![A,B] 0 = familyCapacity fourWindows ![A,B] := by
      simp only [sealedCapacity,familyCapacity,pow_zero,one_mul]
    simpa only [Nat.zero_add,h0,fourWindows_capacity] using h
  · simpa only [fourWindows_monotoneCapacity] using
      monotoneCapacity_le_sealed fourWindows (![A,B] : Fin 2 → ℝ) k

theorem fourWindows_depth (A B : ℝ) : enclosureDepth fourWindows ![A,B] = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (enclosureDepth_le_iff fourWindows (![A,B] : Fin 2 → ℝ) 0).mpr
  rw [fourWindows_sealedCapacity,fourWindows_monotoneCapacity]

def fourPairingWindows : Fin 3 → Fin 2 → Finset (Fin 3) :=
  ![![{0},{2}],![{1},Finset.univ],![{0,1},{1,2}]]

theorem fourPairingWindows_value (c : Fin 3 → ℝ) (g : Fin 3 → ℝ) :
    familyValue fourPairingWindows c g =
      familyValue fourWindows ![c 0+c 2,c 1+c 2] g := by
  rw [fourWindows_value]
  simp [familyValue,diagramValue,windowValue,fourPairingWindows,Fin.sum_univ_three,
    Fin.prod_univ_two,fourResponse,separated,enclosing]
  ring

theorem fourPairingWindows_sealedCapacity (c : Fin 3 → ℝ) (k : ℕ) :
    sealedCapacity fourPairingWindows c k = fourCapacity (c 0+c 2) (c 1+c 2) := by
  have he : sealedCapacity fourPairingWindows c k =
      sealedCapacity fourWindows ![c 0+c 2,c 1+c 2] k := by
    simp only [sealedCapacity,fourPairingWindows_value]
  rw [he,fourWindows_sealedCapacity]

theorem fourPairingWindows_monotoneCapacity (c : Fin 3 → ℝ) :
    monotoneCapacity fourPairingWindows c = fourCapacity (c 0+c 2) (c 1+c 2) := by
  have he : monotoneCapacity fourPairingWindows c =
      monotoneCapacity fourWindows ![c 0+c 2,c 1+c 2] := by
    simp only [monotoneCapacity,fourPairingWindows_value]
  rw [he,fourWindows_monotoneCapacity]

theorem fourPairingWindows_depth (c : Fin 3 → ℝ) :
    enclosureDepth fourPairingWindows c = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (enclosureDepth_le_iff fourPairingWindows c 0).mpr
  rw [fourPairingWindows_sealedCapacity,fourPairingWindows_monotoneCapacity]

theorem quadratic_pairing_depth_separation (c : Fin 3 → ℝ) :
    enclosureDepth fourPairingWindows c = 0 ∧
      enclosureDepth (binaryWindows 2) (chebyshevCoefficients 2) = 2 := by
  refine ⟨fourPairingWindows_depth c,?_⟩
  simpa only [Nat.zero_add,Nat.mul_one] using binary_chebyshev_exact_depth 0

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
