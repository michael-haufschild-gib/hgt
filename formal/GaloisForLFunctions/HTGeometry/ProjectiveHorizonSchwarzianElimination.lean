import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianKernel
import GaloisForLFunctions.HTGeometry.FreeCoordinateChainRule

/-!
# The chart currents in the Schwarzian coordinates

Conjugating a current into the Schwarzian coordinates and expanding by the chain rule, the tail
coordinates drop out because the current annihilates every Schwarzian jet.  What is left is a
three-term expression in the derivatives along the first three coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
theorem freeCoordinateField_mono {σ : Type*} {S T : Set σ} (h : S ⊆ T) :
    freeCoordinateField C σ S ≤ freeCoordinateField C σ T := by
  rw [freeCoordinateField, freeCoordinateField, IntermediateField.adjoin_le_iff]
  exact fun _ hx => IntermediateField.subset_adjoin _ _ (Set.image_mono h hx)

omit [CharZero C] in
/-- If the translation and inversion currents annihilate an observable, so does their bracket. -/
theorem jetH_eq_zero_of {f : FreeScalarJetField C}
    (hE : freeCoordinateDerivation C ℕ 0 f = 0) (hF : freeJetFZero C f = 0) :
    jetH C f = 0 := by
  rw [jetH_apply, hE, hF, map_zero, map_zero, sub_zero]

/-- **The chain-rule reduction.**  A current annihilating every Schwarzian jet is determined, on the
pullback, by its values on the first three coordinates. -/
theorem current_chain (D : Derivation C (FreeScalarJetField C) (FreeScalarJetField C))
    (hD : ∀ k : ℕ, D (differentialJet k (freeJetSchwarzian C)) = 0)
    (f : FreeScalarJetField C) :
    (schwarzianBasisEquiv C).symm (D f) =
      ∑ p ∈ ({0, 1, 2} : Finset ℕ),
        (schwarzianBasisEquiv C).symm (D (freeCoordinate C ℕ p)) *
          freeCoordinateDerivation C ℕ p ((schwarzianBasisEquiv C).symm f) := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_mem_freeCoordinateField ((schwarzianBasisEquiv C).symm f)
  have hgS : (schwarzianBasisEquiv C).symm f ∈
      freeCoordinateField C ℕ (↑(T ∪ ({0, 1, 2} : Finset ℕ)) : Set ℕ) :=
    freeCoordinateField_mono (by
      intro x hx
      exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx))) hT
  have hval : ∀ p : ℕ, conjDerivation (schwarzianBasisEquiv C) D (freeCoordinate C ℕ p) =
      (schwarzianBasisEquiv C).symm (D (schwarzianSystem C p)) := by
    intro p
    rw [conjDerivation_apply, schwarzianBasisEquiv_freeCoordinate]
  have hchain := freeCoordinate_chainRule (T ∪ ({0, 1, 2} : Finset ℕ))
    (conjDerivation (schwarzianBasisEquiv C) D) hgS
  have hzero : ∀ p ∈ T ∪ ({0, 1, 2} : Finset ℕ), p ∉ ({0, 1, 2} : Finset ℕ) →
      conjDerivation (schwarzianBasisEquiv C) D (freeCoordinate C ℕ p) *
        freeCoordinateDerivation C ℕ p ((schwarzianBasisEquiv C).symm f) = 0 := by
    intro p _ hp
    have hp3 : 3 ≤ p := by
      by_contra hlt
      have hlt3 : p < 3 := by omega
      interval_cases p <;> simp at hp
    rw [hval p, schwarzianSystem_of_ge hp3, hD, map_zero, zero_mul]
  rw [← Finset.sum_subset Finset.subset_union_right hzero, conjDerivation_apply,
    AlgEquiv.apply_symm_apply] at hchain
  rw [hchain]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hlt : p < 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> omega
  rw [hval p, schwarzianSystem_of_lt hlt]

end

end GaloisForLFunctions.HTGeometry
