import GaloisForLFunctions.HTGeometry.FiniteBuildingVertices
import GaloisForLFunctions.HTGeometry.ProjectiveFlagDimension
import GaloisForLFunctions.HTGeometry.WeightedComplexLink

/-!
# Finite weighted flag complex of a spherical building

For a finite vector space, the nonzero proper subspaces form the vertex set of its spherical
building.  This file packages the already formalized flag dimension theorem and the finite vertex
enumeration as a `WeightedComplex`, the input format used by Garland localization.

The construction records top chains at the maximal possible cardinality.  Identifying every local
link of this complex with its finite spherical-building link is a separate later step.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [Fintype V]

/-- The rank-filtered weighted flag complex on the vertices of a finite spherical building.
Its top faces are precisely the comparable flags with `finrank K V - 1` vertices. -/
noncomputable def finiteSphericalBuildingFlagComplex :
    WeightedComplex (properPart (Submodule K V)) := by
  classical
  letI : Fintype (properPart (Submodule K V)) := properPartSubmoduleFintype
  exact flagComplexOfCard (V := properPart (Submodule K V)) (Module.finrank K V - 1)

/-- Every top face of the finite spherical-building flag complex has the ambient maximal
flag cardinality. -/
theorem finiteSphericalBuildingFlagComplex_pure :
    ∀ s ∈ (finiteSphericalBuildingFlagComplex K V).top, s.card = Module.finrank K V - 1 := by
  classical
  letI : Fintype (properPart (Submodule K V)) := properPartSubmoduleFintype
  exact flagComplexOfCard_pure (V := properPart (Submodule K V)) _

/-- Every face of the finite spherical-building flag complex is a comparable subspace flag. -/
theorem finiteSphericalBuildingFlagComplex_isChain {τ : Finset (properPart (Submodule K V))}
    (hτ : (finiteSphericalBuildingFlagComplex K V).IsFace τ) : IsChainFinset τ := by
  classical
  letI : Fintype (properPart (Submodule K V)) := properPartSubmoduleFintype
  exact flagComplexOfCard_isChain (V := properPart (Submodule K V)) hτ

variable [FiniteDimensional K V]

/-- A nonzero finite-dimensional vector space has a complete proper flag, hence a top face in its
finite spherical-building flag complex. -/
theorem exists_mem_finiteSphericalBuildingFlagComplex_top (hN : 0 < Module.finrank K V) :
    ∃ s : Finset (properPart (Submodule K V)), s ∈ (finiteSphericalBuildingFlagComplex K V).top := by
  classical
  obtain ⟨S, hS, hchain, hbot, htop⟩ := exists_chain_card_eq_finrank_sub_one hN
  let e : {W : Submodule K V // W ∈ S} ↪ properPart (Submodule K V) :=
    ⟨fun W => ⟨W, bot_lt_iff_ne_bot.mpr (hbot W W.2), lt_top_iff_ne_top.mpr (htop W W.2)⟩,
      fun W W' h => Subtype.ext (congrArg (fun U : properPart (Submodule K V) =>
        (U : Submodule K V)) h)⟩
  let s : Finset (properPart (Submodule K V)) := S.attach.map e
  have hscard : s.card = Module.finrank K V - 1 := by
    rw [show s = S.attach.map e by rfl, Finset.card_map, Finset.card_attach, hS]
  have hschain : IsChainFinset s := by
    intro W hW W' hW'
    obtain ⟨U, -, rfl⟩ := Finset.mem_map.1 hW
    obtain ⟨U', -, rfl⟩ := Finset.mem_map.1 hW'
    exact hchain U U.2 U' U'.2
  refine ⟨s, ?_⟩
  letI : Fintype (properPart (Submodule K V)) := properPartSubmoduleFintype
  rw [show finiteSphericalBuildingFlagComplex K V =
      flagComplexOfCard (V := properPart (Submodule K V)) (Module.finrank K V - 1) by rfl]
  rw [flagComplexOfCard, unitComplex_top, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hschain, hscard⟩

/-- Every face in the finite spherical-building flag complex has no more vertices than a complete
proper flag. -/
theorem finiteSphericalBuildingFlagComplex_face_card_le
    {τ : Finset (properPart (Submodule K V))}
    (hτ : (finiteSphericalBuildingFlagComplex K V).IsFace τ) :
    τ.card ≤ Module.finrank K V - 1 := by
  classical
  let T : Finset (Submodule K V) := τ.image (fun W : properPart (Submodule K V) => (W : Submodule K V))
  have hinj : Function.Injective
      (fun W : properPart (Submodule K V) => (W : Submodule K V)) := fun W W' h => Subtype.ext h
  have hcard : T.card = τ.card := by
    rw [show T = τ.image (fun W : properPart (Submodule K V) => (W : Submodule K V)) by rfl,
      Finset.card_image_of_injective _ hinj]
  have hchain : ∀ W ∈ T, ∀ W' ∈ T, W ≤ W' ∨ W' ≤ W := by
    intro W hW W' hW'
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hW
    obtain ⟨U', hU', rfl⟩ := Finset.mem_image.1 hW'
    exact finiteSphericalBuildingFlagComplex_isChain K V hτ U hU U' hU'
  have hbot : ∀ W ∈ T, W ≠ ⊥ := by
    intro W hW
    obtain ⟨U, -, rfl⟩ := Finset.mem_image.1 hW
    exact ne_of_gt U.2.1
  have htop : ∀ W ∈ T, W ≠ ⊤ := by
    intro W hW
    obtain ⟨U, -, rfl⟩ := Finset.mem_image.1 hW
    exact ne_of_lt U.2.2
  rw [← hcard]
  exact card_le_finrank_sub_one T hchain hbot htop

end

end GaloisForLFunctions.HTGeometry
