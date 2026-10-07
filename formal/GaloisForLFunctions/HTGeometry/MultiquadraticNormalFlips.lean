import GaloisForLFunctions.HTGeometry.QuadraticRootConjugation
import GaloisForLFunctions.HTGeometry.MultiquadraticAdjoinDegree
import Mathlib.FieldTheory.Normal.Basic

/-!
# Independent radical flips inside a normal extension

The square-class kernel keeps an omitted radical nonsquare. Conjugation over
the field of the other radicals then extends to the ambient normal field.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped IntermediateField
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A radical outside a finite independent packet remains nonsquare over that packet. -/
theorem multiquadratic_not_isSquare_adjoin {ι : Type*} (d : ι → F) (r : ι → L)
    (h2 : (2 : L) ≠ 0) (hsq : ∀ i, r i * r i = algebraMap F L (d i))
    (hind : ∀ T : Finset ι, T.Nonempty → ¬ IsSquare (∏ i ∈ T, d i))
    (S : Finset ι) {i : ι} (hi : i ∉ S) :
    ¬ IsSquare (algebraMap F (IntermediateField.adjoin F (r '' (S : Set ι))) (d i)) := by
  classical
  intro h
  obtain ⟨T, hT, hs⟩ := (multiquadratic_degree_and_twists d r h2 hsq hind S).2 (d i) h
  have hiT : i ∉ T := fun hit => hi (hT hit)
  apply hind (insert i T) (Finset.insert_nonempty _ _)
  rwa [Finset.prod_insert hiT]

/-- In a normal ambient extension each independent radical can be flipped alone. -/
theorem exists_normal_independent_radical_flip {ι : Type*} [Normal F L]
    (d : ι → F) (r : ι → L)
    (h2 : (2 : L) ≠ 0) (hsq : ∀ i, r i * r i = algebraMap F L (d i))
    (hind : ∀ T : Finset ι, T.Nonempty → ¬ IsSquare (∏ i ∈ T, d i))
    (S : Finset ι) (i : ι) :
    ∃ σ : L ≃ₐ[F] L, σ (r i) = -r i ∧ ∀ j ∈ S, j ≠ i → σ (r j) = r j := by
  classical
  let E := IntermediateField.adjoin F (r '' ((S.erase i : Finset ι) : Set ι))
  have hns : ¬ IsSquare (algebraMap F E (d i)) :=
    multiquadratic_not_isSquare_adjoin d r h2 hsq hind (S.erase i) (Finset.notMem_erase i S)
  have hsqE : r i * r i = algebraMap E L (algebraMap F E (d i)) := hsq i
  letI : IsScalarTower F E⟮r i⟯ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := quadraticRootConjugation hsqE hns
  let σ := (e.restrictScalars F).liftNormal L
  refine ⟨σ, ?_, ?_⟩
  · have h := (e.restrictScalars F).liftNormal_commutes L
      (⟨r i, IntermediateField.mem_adjoin_simple_self E (r i)⟩ : E⟮r i⟯)
    change σ (r i) = (e ⟨r i, IntermediateField.mem_adjoin_simple_self E (r i)⟩ : L) at h
    rw [show e ⟨r i, IntermediateField.mem_adjoin_simple_self E (r i)⟩ =
      -⟨r i, IntermediateField.mem_adjoin_simple_self E (r i)⟩ from
        quadraticRootConjugation_gen hsqE hns] at h
    exact h
  · intro j hj hji
    have hjE : r j ∈ E := IntermediateField.subset_adjoin F _
      ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, rfl⟩
    have h := (e.restrictScalars F).liftNormal_commutes L
      (algebraMap E E⟮r i⟯ ⟨r j, hjE⟩)
    change σ (r j) = (e (algebraMap E E⟮r i⟯ ⟨r j, hjE⟩) : L) at h
    rw [e.commutes] at h
    exact h

end GaloisForLFunctions.HTGeometry
