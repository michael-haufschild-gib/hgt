import GaloisForLFunctions.HTGeometry.ApartmentClassMono
import GaloisForLFunctions.HTGeometry.BuildingNonvanishing
import GaloisForLFunctions.HTGeometry.BuildingConnected

/-!
# The Steinberg module as top cycles, and the homology of the building

Two consequences of the machinery, and the combinatorial shape of a rank-three apartment.

The building has dimension `N - 2`, so a class of its top homology is exactly a normalized cycle
there: the Steinberg module *is* the module of top cycles of the order complex.  Collecting the
computations gives the homological content of "the building is a wedge of `(N-2)`-spheres": one copy
of the coefficients in degree zero, nothing in any other degree but `N - 2`, and there a coproduct of
copies of the coefficients over a nonempty index set.

For a frame of three vectors the apartment is a hexagon: its vertices are the one- and two-element
coordinate sets, and a comparable pair always has one of each — the alternation the card describes.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

section Cycles

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The Steinberg module is the module of top cycles of the building.**  There are no chains above
degree `N - 2`, so a top homology class is exactly a normalized cycle. -/
noncomputable def steinbergIsoCycles (R : C) (h3 : 3 ≤ finrank K V) :
    steinbergModule K V R
      ≅ ((nerve (properPart (Submodule K V))).normalizedChainComplex R).cycles
        (finrank K V - 2) := by
  haveI : SSet.HasDimensionLT (nerve (properPart (Submodule K V)))
      (finrank K V - 2 + 1) := by
    rw [show finrank K V - 2 + 1 = finrank K V - 1 by omega]
    exact properPartSubmoduleHasDimensionLT K V
  exact topHomologyIsoCycles (X := nerve (properPart (Submodule K V))) (R := R)
    (n := finrank K V - 2)

/-- **The homology of the building vanishes off the top degree**, in the presentation by the proper
nonzero subspaces. -/
theorem isZero_homology_properPart_submodule_of_ne [Nontrivial V] (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hne : i ≠ finrank K V - 2) :
    Limits.IsZero ((nerve (properPart (Submodule K V))).homology R i) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hpos : 0 < finrank K V := finrank_pos
    exact isZero_homology_properPart_submodule R i hi (by omega)
  · haveI : SSet.HasDimensionLT (nerve (properPart (Submodule K V))) (finrank K V - 1) :=
      properPartSubmoduleHasDimensionLT K V
    exact SSet.isZero_homology_of_hasDimensionLT _ R i (finrank K V - 1) (by omega)

/-- **The homology of the building is that of a wedge of `(N-2)`-spheres.**  This is the whole
homological content of the card's `(4)`: degree zero is one copy of the coefficients, every other
degree except `N - 2` vanishes, and the top degree is a coproduct of copies of the coefficients over
a nonempty index set. -/
theorem homology_building_wedge (R : C) (h3 : 3 ≤ finrank K V) :
    Nonempty ((nerve (properPart (Submodule K V))).homology R 0 ≅ R)
      ∧ (∀ i : ℕ, 1 ≤ i → i ≠ finrank K V - 2 →
          Limits.IsZero ((nerve (properPart (Submodule K V))).homology R i))
      ∧ ∃ B : Type u, Nonempty B ∧
          Nonempty ((nerve (properPart (Submodule K V))).homology R (finrank K V - 2)
            ≅ ∐ fun _ : B => R) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
  refine ⟨⟨homologyZeroIsoProperPartSubmodule h3 R⟩, fun i hi hne => ?_, ?_⟩
  · exact isZero_homology_properPart_submodule_of_ne R i hi hne
  · exact exists_nonempty_index_steinbergModule R h3

/-- The chambers of the building: its complete flags, i.e. its nondegenerate top simplices. -/
abbrev buildingChamber (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Type u :=
  (nerve (properPart (Submodule K V))).nonDegenerate (finrank K V - 2)

/-- The normalized chains of a simplicial set are the coproduct over its nondegenerate simplices. -/
noncomputable def normalizedChainsIsoSigma (X : SSet.{u}) (R : C) (n : ℕ) :
    (X.normalizedChainComplex R).X n ≅ ∐ fun _ : X.nonDegenerate n => R :=
  (X.isColimitCofanNormalizedChainComplex R n).coconePointUniqueUpToIso
    (coproductIsCoproduct fun _ : X.nonDegenerate n => R)

/-- **The Steinberg module inside the free object on the chambers.**  A top homology class is a
normalized cycle, and normalized top chains are the coproduct of copies of the coefficients over the
complete flags. -/
noncomputable def steinbergToChambers (R : C) (h3 : 3 ≤ finrank K V) :
    steinbergModule K V R ⟶ ∐ fun _ : buildingChamber K V => R :=
  (steinbergIsoCycles R h3).hom
    ≫ ((nerve (properPart (Submodule K V))).normalizedChainComplex R).iCycles (finrank K V - 2)
    ≫ (normalizedChainsIsoSigma _ R (finrank K V - 2)).hom

/-- **The Steinberg module is a subobject of the free object on the chambers.** -/
theorem mono_steinbergToChambers (R : C) (h3 : 3 ≤ finrank K V) :
    Mono (steinbergToChambers R h3) := by
  rw [steinbergToChambers]
  exact mono_comp _ _

omit [FiniteDimensional K V] in
theorem three_le_finrank_of_card {ι : Type u} [Fintype ι] (b : Basis ι K V)
    (h3 : 3 ≤ Nat.card ι) : 3 ≤ finrank K V := by
  rw [← card_eq_finrank b]
  exact h3

/-- **The apartment cycle of a frame, in the flag coordinates.**  This is the class of the frame's
Coxeter sphere, read inside the free object on the complete flags of the building. -/
noncomputable def apartmentChamberCycle {ι : Type u} [Fintype ι] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) : R ⟶ ∐ fun _ : buildingChamber K V => R :=
  apartmentClass b R h3 ≫ steinbergToChambers R (three_le_finrank_of_card b h3)

/-- **The apartment cycle is a monomorphism**, so it is a nonzero cycle on the chambers. -/
theorem mono_apartmentChamberCycle {ι : Type u} [Fintype ι] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) : Mono (apartmentChamberCycle b R h3) := by
  show Mono (apartmentClass b R h3 ≫ steinbergToChambers R (three_le_finrank_of_card b h3))
  exact @mono_comp _ _ _ _ _ _ (mono_apartmentClass b R h3) _
    (mono_steinbergToChambers (K := K) (V := V) R (three_le_finrank_of_card b h3))

end Cycles

section Hexagon

variable {ι : Type u}

/-- Inside an apartment a strict inclusion strictly increases the number of frame vectors. -/
theorem apartment_ncard_lt_of_lt [Finite ι] {s t : properPart (Set ι)} (h : s < t) :
    (s : Set ι).ncard < (t : Set ι).ncard :=
  Set.ncard_lt_ncard h (Set.toFinite _)

/-- **The vertices of a rank-three apartment are the one- and two-element coordinate sets.** -/
theorem apartment_ncard_eq_one_or_two (h3 : Nat.card ι = 3) (s : properPart (Set ι)) :
    (s : Set ι).ncard = 1 ∨ (s : Set ι).ncard = 2 := by
  haveI : Finite ι := (Nat.card_pos_iff.1 (by omega)).2
  have hpos : 0 < (s : Set ι).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.2 (Set.nonempty_iff_ne_empty.2 (ne_of_gt s.2.1))
  have hlt : (s : Set ι).ncard < (Set.univ : Set ι).ncard :=
    Set.ncard_lt_ncard s.2.2 (Set.toFinite _)
  rw [Set.ncard_univ, h3] at hlt
  omega

/-- **A comparable pair of apartment vertices has one vertex of each kind** — the hexagon of a
three-vector frame alternates between single observers and their pairwise fields. -/
theorem apartment_ncard_ne_of_lt (h3 : Nat.card ι = 3) {s t : properPart (Set ι)} (h : s < t) :
    (s : Set ι).ncard = 1 ∧ (t : Set ι).ncard = 2 := by
  haveI : Finite ι := (Nat.card_pos_iff.1 (by omega)).2
  have hlt := apartment_ncard_lt_of_lt h
  rcases apartment_ncard_eq_one_or_two h3 s with hs | hs <;>
    rcases apartment_ncard_eq_one_or_two h3 t with ht | ht <;> omega

end Hexagon

end GaloisForLFunctions.HTGeometry
