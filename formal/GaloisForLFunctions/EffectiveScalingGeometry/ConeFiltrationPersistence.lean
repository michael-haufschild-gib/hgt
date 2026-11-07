import GaloisForLFunctions.EffectiveScalingGeometry.PrimeHeightFiltration

/-!
# Persistence through a conical star

For an inclusion of complexes with conical stars, the induced map between the
sphere bouquets is the identity up to homotopy on a surviving facet sphere and
constant on a facet which enters the larger star. This describes filtration
maps, in addition to the homotopy type of each individual complex.
-/

noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
open GaloisForLFunctions.HodgeTheoryWithoutVarieties
namespace GaloisForLFunctions.EffectiveScalingGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Inclusion of realizations in a fixed ambient simplex. -/
def faceFamilyInclusion {K L : Finset (Finset V)} (hKL : K ⊆ L) :
    C(faceFamilySpace K, faceFamilySpace L) where
  toFun x := ⟨x.val, faceFamilySpace_mono hKL x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

omit [Fintype V] in
theorem faceStar_mono {K L : Finset (Finset V)} (hKL : K ⊆ L) (a : V) :
    faceStar K a ⊆ faceStar L a := by
  intro S hS
  obtain ⟨hS, hi⟩ := mem_faceStar.mp hS
  exact mem_faceStar.mpr ⟨hKL hS, hKL hi⟩

variable {K L : Finset (Finset V)} {a : V}

/-- The filtration map expressed in the explicit sphere-bouquet coordinates. -/
def conePersistenceMap (hKL : K ⊆ L)
    (haK : {a} ∈ K) (haL : {a} ∈ L)
    (hpK : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (hdL : ∀ S ∈ L, ∀ T ⊆ S, T ∈ L)
    (hpL : ∀ S ∈ complementaryFaces L a, ∀ T ⊂ S, T ∈ faceStar L a) :
    C(ConeBouquet haK, ConeBouquet haL) :=
  (coneBouquetForward hdL haL hpL).comp
    ((faceFamilyInclusion hKL).comp (coneBouquetBack haK hpK))

/-- A surviving facet retains its sphere, up to the canonical sphere homotopy. -/
theorem conePersistenceMap_surviving (hKL : K ⊆ L)
    (haK : {a} ∈ K) (haL : {a} ∈ L)
    (hpK : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (hdL : ∀ S ∈ L, ∀ T ⊆ S, T ∈ L)
    (hpL : ∀ S ∈ complementaryFaces L a, ∀ T ⊂ S, T ∈ faceStar L a)
    (S : complementaryFaces K a) (hS : S.val ∈ complementaryFaces L a)
    (p : FacetBoundary a S.val) :
    conePersistenceMap hKL haK haL hpK hdL hpL
        (bouquetInclusion (complementarySpherePoint haK) S p) =
      bouquetInclusion (complementarySpherePoint haL) ⟨S.val, hS⟩
        (complementarySphereHomotopy haL ⟨S.val, hS⟩ (1, p)) := by
  exact coneBouquetForward_boundary hdL haL hpL ⟨S.val, hS⟩ p

/-- A facet which has entered the larger star maps to the bouquet basepoint. -/
theorem conePersistenceMap_dead (hKL : K ⊆ L)
    (haK : {a} ∈ K) (haL : {a} ∈ L)
    (hpK : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (hdL : ∀ S ∈ L, ∀ T ⊆ S, T ∈ L)
    (hpL : ∀ S ∈ complementaryFaces L a, ∀ T ⊂ S, T ∈ faceStar L a)
    (S : complementaryFaces K a) (hS : S.val ∉ complementaryFaces L a)
    (p : FacetBoundary a S.val) :
    conePersistenceMap hKL haK haL hpK hdL hpL
        (bouquetInclusion (complementarySpherePoint haK) S p) =
      bouquetPoint (complementarySpherePoint haL) := by
  have hstar : S.val ∈ faceStar L a := by
    by_contra hn
    exact hS (mem_complementaryFaces.mpr
      ⟨hKL (mem_complementaryFaces.mp S.property).1, hn⟩)
  have hx : facetBoundaryToAmbient a S.val p ∈ faceFamilySpace (faceStar L a) := by
    by_cases hp : facetBoundaryToAmbient a S.val p ∈ faceFamilySpace (faceStar K a)
    · exact faceFamilySpace_mono (faceStar_mono hKL a) hp
    · exact mem_faceFamilySpace.mpr ⟨S.val, hstar,
        facetBoundary_mem_facet_of_not_star hpK S p hp⟩
  exact coneBouquetForward_of_star hdL haL hpL _ hx

/-- The map on a surviving summand is homotopic to its unchanged inclusion. -/
def survivingSummandHomotopy (hKL : K ⊆ L)
    (haK : {a} ∈ K) (haL : {a} ∈ L)
    (hpK : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (hdL : ∀ S ∈ L, ∀ T ⊆ S, T ∈ L)
    (hpL : ∀ S ∈ complementaryFaces L a, ∀ T ⊂ S, T ∈ faceStar L a)
    (S : complementaryFaces K a) (hS : S.val ∈ complementaryFaces L a) :
    (bouquetInclusion (complementarySpherePoint haL) ⟨S.val, hS⟩).Homotopy
      ((conePersistenceMap hKL haK haL hpK hdL hpL).comp
        (bouquetInclusion (complementarySpherePoint haK) S)) where
  toFun z := bouquetInclusion (complementarySpherePoint haL) ⟨S.val, hS⟩
    (complementarySphereHomotopy haL ⟨S.val, hS⟩ z)
  continuous_toFun := (bouquetInclusion (complementarySpherePoint haL) ⟨S.val, hS⟩).continuous.comp
    (complementarySphereHomotopy haL ⟨S.val, hS⟩).continuous
  map_zero_left p := congrArg (bouquetInclusion (complementarySpherePoint haL) ⟨S.val, hS⟩)
    (complementarySphereHomotopy_zero haL ⟨S.val, hS⟩ p)
  map_one_left p := (conePersistenceMap_surviving hKL haK haL hpK hdL hpL S hS p).symm

/-- The surviving-sphere homotopy fixes the bouquet basepoint throughout. -/
theorem survivingSummandHomotopy_base (hKL : K ⊆ L)
    (haK : {a} ∈ K) (haL : {a} ∈ L)
    (hpK : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (hdL : ∀ S ∈ L, ∀ T ⊆ S, T ∈ L)
    (hpL : ∀ S ∈ complementaryFaces L a, ∀ T ⊂ S, T ∈ faceStar L a)
    (S : complementaryFaces K a) (hS : S.val ∈ complementaryFaces L a)
    (t : unitInterval) :
    survivingSummandHomotopy hKL haK haL hpK hdL hpL S hS
        (t, complementarySpherePoint haL ⟨S.val, hS⟩) =
      bouquetPoint (complementarySpherePoint haL) := by
  change bouquetInclusion (complementarySpherePoint haL) ⟨S.val, hS⟩
    (complementarySphereHomotopy haL ⟨S.val, hS⟩
      (t, complementarySpherePoint haL ⟨S.val, hS⟩)) = _
  rw [complementarySphereHomotopy_point, bouquetInclusion_base]

#print axioms conePersistenceMap_surviving
#print axioms conePersistenceMap_dead
#print axioms survivingSummandHomotopy
#print axioms survivingSummandHomotopy_base
end GaloisForLFunctions.EffectiveScalingGeometry
