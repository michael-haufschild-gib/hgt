import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanMatrixCone

/-!
# Finite-cusp transfer between archimedean cone models

The raw matrix cone is the correct locally convex ambient model for Macbeath's criterion, while the
existing reduction theory is stated for self-adjoint positive forms.  The equivariant homeomorphism
between those models transfers open cusp families, connectedness, covering, and pairwise transition
sets exactly.  Hence future arithmetic reduction theorems can remain on their existing interface.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField Pointwise
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Pull a cusp neighbourhood in the self-adjoint model back to the raw matrix cone. -/
def numberFieldArchimedeanMatrixCuspPullback
    (V : Set (numberFieldArchimedeanPositiveForms K n)) :
    Set (numberFieldArchimedeanMatrixCone K n) :=
  numberFieldArchimedeanMatrixConeHomeomorph ⁻¹' V

omit [NumberField K] in
theorem isOpen_numberFieldArchimedeanMatrixCuspPullback
    {V : Set (numberFieldArchimedeanPositiveForms K n)} (hV : IsOpen V) :
    IsOpen (numberFieldArchimedeanMatrixCuspPullback V) :=
  numberFieldArchimedeanMatrixConeHomeomorph.isOpen_preimage.mpr hV

omit [NumberField K] in
theorem numberFieldArchimedeanMatrixCuspPullback_nonempty
    {V : Set (numberFieldArchimedeanPositiveForms K n)} (hV : V.Nonempty) :
    (numberFieldArchimedeanMatrixCuspPullback V).Nonempty :=
  hV.preimage numberFieldArchimedeanMatrixConeHomeomorph.surjective

omit [NumberField K] in
/-- Pullback commutes with a finite union of cusp neighbourhoods. -/
theorem finiteCuspUnion_numberFieldArchimedeanMatrixCuspPullback
    {C : Type*} (S : Finset C)
    (V : C → Set (numberFieldArchimedeanPositiveForms K n)) :
    finiteCuspUnion S (fun c => numberFieldArchimedeanMatrixCuspPullback (V c)) =
      numberFieldArchimedeanMatrixConeHomeomorph ⁻¹' finiteCuspUnion S V := by
  ext A
  simp [finiteCuspUnion, numberFieldArchimedeanMatrixCuspPullback]

omit [NumberField K] in
/-- Preconnectedness of a finite cusp union transfers to the raw cone. -/
theorem isPreconnected_finiteCuspUnion_numberFieldArchimedeanMatrixCuspPullback
    {C : Type*} (S : Finset C)
    (V : C → Set (numberFieldArchimedeanPositiveForms K n))
    (hV : IsPreconnected (finiteCuspUnion S V)) :
    IsPreconnected
      (finiteCuspUnion S (fun c => numberFieldArchimedeanMatrixCuspPullback (V c))) := by
  rw [finiteCuspUnion_numberFieldArchimedeanMatrixCuspPullback]
  exact numberFieldArchimedeanMatrixConeHomeomorph.isPreconnected_preimage.mpr hV

omit [NumberField K] in
/-- An equivariant cusp cover of self-adjoint positive forms pulls back to an equivariant cover of
the raw cone. -/
theorem numberFieldArchimedeanMatrixCuspPullback_cover
    {C : Type*} (S : Finset C)
    (V : C → Set (numberFieldArchimedeanPositiveForms K n))
    (hcover : ⋃ g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K),
      g • finiteCuspUnion S V = Set.univ) :
    ⋃ g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K),
      g • finiteCuspUnion S
        (fun c => numberFieldArchimedeanMatrixCuspPullback (V c)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro A
  have hmem : numberFieldArchimedeanMatrixConeHomeomorph A ∈
      ⋃ g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K),
        g • finiteCuspUnion S V := by
    rw [hcover]
    trivial
  rcases Set.mem_iUnion.1 hmem with ⟨g, hg⟩
  refine Set.mem_iUnion.2 ⟨g, ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hg ⊢
  rw [finiteCuspUnion_numberFieldArchimedeanMatrixCuspPullback]
  change numberFieldArchimedeanMatrixConeHomeomorph (g⁻¹ • A) ∈ finiteCuspUnion S V
  simpa using hg

omit [NumberField K] in
/-- Pairwise cusp-transition sets are unchanged by the equivariant homeomorphism. -/
theorem numberFieldArchimedeanMatrixCuspPullback_transitionSet
    (V W : Set (numberFieldArchimedeanPositiveForms K n)) :
    {g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) |
      ∃ A ∈ numberFieldArchimedeanMatrixCuspPullback V,
        g • A ∈ numberFieldArchimedeanMatrixCuspPullback W} =
    {g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) |
      ∃ A ∈ V, g • A ∈ W} := by
  ext g
  constructor
  · rintro ⟨A, hAV, hgAW⟩
    change numberFieldArchimedeanMatrixConeHomeomorph (g • A) ∈ W at hgAW
    rw [numberFieldArchimedeanMatrixConeHomeomorph_smul] at hgAW
    exact ⟨numberFieldArchimedeanMatrixConeHomeomorph A, hAV, hgAW⟩
  · rintro ⟨A, hAV, hgAW⟩
    let B := numberFieldArchimedeanMatrixConeHomeomorph.symm A
    refine ⟨B, ?_, ?_⟩
    · simpa [B, numberFieldArchimedeanMatrixCuspPullback] using hAV
    · change numberFieldArchimedeanMatrixConeHomeomorph (g • B) ∈ W
      simpa [B] using hgAW

/-- **Finite-cusp presentation criterion on the established positive-form interface.**  The
correct raw-cone topology is discharged internally, so callers supply only arithmetic cusp data. -/
theorem isFinitelyPresented_specialLinearGroup_of_numberFieldArchimedeanPositiveFiniteCusps
    {C : Type*} (S : Finset C)
    (V : C → Set (numberFieldArchimedeanPositiveForms K n))
    (hVopen : ∀ i ∈ S, IsOpen (V i))
    (hVne : ∃ i ∈ S, (V i).Nonempty)
    (hVconn : IsPreconnected (finiteCuspUnion S V))
    (hcover : ⋃ g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K),
      g • finiteCuspUnion S V = Set.univ)
    (hfinite : ∀ i ∈ S, ∀ j ∈ S,
      {g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) |
        ∃ A ∈ V i, g • A ∈ V j}.Finite) :
    IsFinitelyPresented (Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) := by
  apply isFinitelyPresented_specialLinearGroup_of_numberFieldArchimedeanMatrixFiniteCusps
    S (fun c => numberFieldArchimedeanMatrixCuspPullback (V c))
  · intro i hi
    exact isOpen_numberFieldArchimedeanMatrixCuspPullback (hVopen i hi)
  · rcases hVne with ⟨i, hi, hVi⟩
    exact ⟨i, hi, numberFieldArchimedeanMatrixCuspPullback_nonempty hVi⟩
  · exact isPreconnected_finiteCuspUnion_numberFieldArchimedeanMatrixCuspPullback S V hVconn
  · exact numberFieldArchimedeanMatrixCuspPullback_cover S V hcover
  · intro i hi j hj
    rw [numberFieldArchimedeanMatrixCuspPullback_transitionSet]
    exact hfinite i hi j hj

end

end GaloisForLFunctions.HTGeometry
