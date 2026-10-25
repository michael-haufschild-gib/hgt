import GaloisForLFunctions.ArithmeticDefectRigidity.WienerCovariancesFollowTheCommonCofactorLimit
import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction

/-!
# Common cofactor limits along prescribed horizons

A cofinal observation family admits a strictly increasing refinement whose
actual cofactor covariances all converge simultaneously.
-/

section

noncomputable section
set_option autoImplicit false
open Filter Topology
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A prescribed increasing horizon family still has an actual common cofactor limit. -/
theorem exists_actualCofactorLimit_along (ε : SubcriticalDamping)
    (T : ℕ → ℕ) (hT : StrictMono T) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ L : ActualCofactorLimit ε,
      L.subsequence = T ∘ ns := by
  have hmem (m : ℕ) (jk : ℕ+ × ℕ+) :
      cofactorGram ε (T m) jk.1 jk.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    refine (abs_cofactorGram_le ε (T m) jk.1 jk.2).trans ?_
    exact (mul_le_mul (inv_sqrt_pnat_le_one jk.1) (inv_sqrt_pnat_le_one jk.2)
      (by positivity) zero_le_one).trans_eq (one_mul 1)
  obtain ⟨ns, hns, K, _, hK⟩ := HTGeometry.exists_subseq_tendsto_of_mem_Icc hmem
  let L : ActualCofactorLimit ε :=
    { subsequence := T ∘ ns
      strictMono := hT.comp hns
      kernel := fun j k => K (j, k)
      converges := fun j k => hK (j, k) }
  exact ⟨ns, hns, L, rfl⟩


/-- Every cofinal horizon family contains an actual common cofactor limit. -/
theorem exists_actualCofactorLimit_along_cofinal (ε : SubcriticalDamping)
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ L : ActualCofactorLimit ε,
      L.subsequence = T ∘ ns := by
  obtain ⟨φ, hφ, hTφ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hT
  obtain ⟨ψ, hψ, L, hL⟩ := exists_actualCofactorLimit_along ε (T ∘ φ) hTφ
  exact ⟨φ ∘ ψ, hφ.comp hψ, L, hL⟩

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.exists_actualCofactorLimit_along

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.exists_actualCofactorLimit_along_cofinal
end
end
