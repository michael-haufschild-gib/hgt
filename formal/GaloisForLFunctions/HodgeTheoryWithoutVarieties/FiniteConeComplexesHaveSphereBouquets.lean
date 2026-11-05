import GaloisForLFunctions.HodgeTheoryWithoutVarieties.CompatibleSimplexContractions

/-!
# Finite complexes with a conical star

If every face outside a vertex star is a facet whose proper faces lie in
the star, contracting the star leaves one sphere for each such facet.
-/

noncomputable section

open ContinuousMap Set Finset
open DifferentialGeometry.Simplex

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Standard barycentric realization of a finite family of faces. -/
def faceFamilySpace (K : Finset (Finset V)) : Set (stdSimplex ℝ V) :=
  ⋃ S : K, supportFace S.val

omit [DecidableEq V] in
theorem mem_faceFamilySpace {K : Finset (Finset V)} {x : stdSimplex ℝ V} :
    x ∈ faceFamilySpace K ↔ ∃ S ∈ K, x ∈ supportFace S := by
  simp only [faceFamilySpace, mem_iUnion, Subtype.exists, exists_prop]

omit [DecidableEq V] in
theorem isClosed_faceFamilySpace (K : Finset (Finset V)) : IsClosed (faceFamilySpace K) :=
  isClosed_iUnion_of_finite (fun S : K => isClosed_supportFace S.val)

omit [DecidableEq V] in
theorem faceFamilySpace_mono {K L : Finset (Finset V)} (hKL : K ⊆ L) :
    faceFamilySpace K ⊆ faceFamilySpace L := by
  intro x hx
  obtain ⟨S, hS, hxS⟩ := mem_faceFamilySpace.mp hx
  exact mem_faceFamilySpace.mpr ⟨S, hKL hS, hxS⟩

/-- Augmented star of a vertex. -/
def faceStar (K : Finset (Finset V)) (a : V) : Finset (Finset V) :=
  K.filter (fun S => insert a S ∈ K)

omit [Fintype V] in
theorem faceStar_subset (K : Finset (Finset V)) (a : V) : faceStar K a ⊆ K :=
  Finset.filter_subset _ _

omit [Fintype V] in
theorem mem_faceStar {K : Finset (Finset V)} {a : V} {S : Finset V} :
    S ∈ faceStar K a ↔ S ∈ K ∧ insert a S ∈ K := Finset.mem_filter

omit [Fintype V] in
theorem insert_mem_faceStar {K : Finset (Finset V)} {a : V} {S : Finset V}
    (hS : S ∈ faceStar K a) : insert a S ∈ faceStar K a := by
  obtain ⟨_, hi⟩ := mem_faceStar.mp hS
  exact mem_faceStar.mpr ⟨hi, by simpa only [Finset.insert_idem] using hi⟩

theorem vertex_mem_supportFace {a : V} {S : Finset V} (ha : a ∈ S) :
    stdSimplex.vertex (S := ℝ) a ∈ supportFace S := by
  intro i hi
  have hia : i ≠ a := fun h => hi (h ▸ ha)
  simp [stdSimplex.vertex, hia]

theorem vertex_mem_faceStarSpace {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K) :
    stdSimplex.vertex (S := ℝ) a ∈ faceFamilySpace (faceStar K a) := by
  refine mem_faceFamilySpace.mpr ⟨{a}, ?_, vertex_mem_supportFace (Finset.mem_singleton_self a)⟩
  exact mem_faceStar.mpr ⟨ha, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self a)] using ha⟩

theorem vertexContraction_mem_insert_supportFace {a : V} {S : Finset V}
    (t : unitInterval) {x : stdSimplex ℝ V} (hx : x ∈ supportFace S) :
    vertexContraction a (t, x) ∈ supportFace (insert a S) := by
  intro i hi
  have hia : a ≠ i := fun h => hi (h ▸ Finset.mem_insert_self a S)
  have hiS : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
  change (vertexContraction a (t, x)).val i = 0
  have hx0 : x.val i = 0 := hx i hiS
  rw [vertexContraction_apply, hx0, if_neg hia]
  ring

theorem vertexContraction_mem_faceStarSpace (K : Finset (Finset V)) (a : V)
    (t : unitInterval) {x : stdSimplex ℝ V} (hx : x ∈ faceFamilySpace (faceStar K a)) :
    vertexContraction a (t, x) ∈ faceFamilySpace (faceStar K a) := by
  obtain ⟨S, hS, hxS⟩ := mem_faceFamilySpace.mp hx
  exact mem_faceFamilySpace.mpr ⟨insert a S, insert_mem_faceStar hS,
    vertexContraction_mem_insert_supportFace t hxS⟩

/-- The star contracts linearly and remains inside itself at every time. -/
def faceStarContraction (K : Finset (Finset V)) (a : V) :
    C(unitInterval × faceFamilySpace (faceStar K a), faceFamilySpace (faceStar K a)) where
  toFun z := ⟨vertexContraction a (z.1, z.2.val),
    vertexContraction_mem_faceStarSpace K a z.1 z.2.property⟩
  continuous_toFun := ((vertexContraction a).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- Faces outside the star index the sphere summands. -/
def complementaryFaces (K : Finset (Finset V)) (a : V) : Finset (Finset V) := K \ faceStar K a

omit [Fintype V] in
theorem mem_complementaryFaces {K : Finset (Finset V)} {a : V} {S : Finset V} :
    S ∈ complementaryFaces K a ↔ S ∈ K ∧ S ∉ faceStar K a := Finset.mem_sdiff

omit [Fintype V] in
theorem apex_not_mem_complementary {K : Finset (Finset V)} {a : V} {S : Finset V}
    (hS : S ∈ complementaryFaces K a) : a ∉ S := by
  obtain ⟨hSK, hSstar⟩ := mem_complementaryFaces.mp hS
  intro ha
  exact hSstar (mem_faceStar.mpr ⟨hSK, by rwa [Finset.insert_eq_of_mem ha]⟩)

omit [Fintype V] in
theorem complementary_nonempty {K : Finset (Finset V)} {a : V} {S : Finset V}
    (ha : {a} ∈ K) (hS : S ∈ complementaryFaces K a) : S.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  obtain ⟨hSK, hSstar⟩ := mem_complementaryFaces.mp hS
  apply hSstar
  refine mem_faceStar.mpr ⟨hSK, ?_⟩
  simpa [he] using ha

omit [Fintype V] in
theorem faceStar_down_closed {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) {S T : Finset V}
    (hS : S ∈ faceStar K a) (hTS : T ⊆ S) : T ∈ faceStar K a := by
  obtain ⟨hSK, hi⟩ := mem_faceStar.mp hS
  exact mem_faceStar.mpr ⟨hdown S hSK T hTS,
    hdown (insert a S) hi (insert a T) (Finset.insert_subset_insert a hTS)⟩

/-- A complementary face meets the star only on its boundary. -/
theorem exists_zero_coordinate_of_complementary_inter_star {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) {S : Finset V}
    (hS : S ∈ complementaryFaces K a) {x : stdSimplex ℝ V}
    (hstar : x ∈ faceFamilySpace (faceStar K a)) : ∃ j ∈ S, x j = 0 := by
  obtain ⟨T, hT, hxT⟩ := mem_faceFamilySpace.mp hstar
  by_contra h
  push Not at h
  have hST : S ⊆ T := by
    intro j hj
    by_contra hjT
    exact h j hj (hxT j hjT)
  exact (mem_complementaryFaces.mp hS).2 (faceStar_down_closed hdown hT hST)

/-- Different complementary facets intersect inside the star. -/
theorem complementary_inter_subset_star {K : Finset (Finset V)} {a : V}
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    {S T : Finset V} (hS : S ∈ complementaryFaces K a)
    (hT : T ∈ complementaryFaces K a) (hne : S ≠ T) :
    supportFace S ∩ supportFace T ⊆ faceFamilySpace (faceStar K a) := by
  have hproperST : S ∩ T ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro he
    have hST : S ⊆ T := by rw [← he]; exact Finset.inter_subset_right
    exact (mem_complementaryFaces.mp hS).2
      (hproper T hT S (Finset.ssubset_iff_subset_ne.mpr ⟨hST, hne⟩))
  intro x hx
  refine mem_faceFamilySpace.mpr ⟨S ∩ T, hproper S hS _ hproperST, ?_⟩
  rwa [supportFace_inter]

/-- A simplex coordinate that vanishes removes its vertex from the support. -/
theorem map_mem_supportFace_erase (U : Finset V) (p : stdSimplex ℝ U) (i : U)
    (hi : p i = 0) : stdSimplex.map Subtype.val p ∈ supportFace (U.erase i.val) := by
  intro j hj
  by_cases hjU : j ∈ U
  · have hji : j = i.val := by
      by_contra hne
      exact hj (Finset.mem_erase.mpr ⟨hne, hjU⟩)
    subst j
    rw [map_subtype_val_apply_mem U p i, hi]
  · exact map_subtype_val_apply_notMem U p j hjU

/-- The sphere surrounding a complementary facet, with the star vertex adjoined. -/
abbrev FacetBoundary (a : V) (S : Finset V) := boundary ↥(insert a S)

def facetBoundaryToAmbient (a : V) (S : Finset V) : C(FacetBoundary a S, stdSimplex ℝ V) where
  toFun p := stdSimplex.map Subtype.val p.val
  continuous_toFun := (stdSimplex.continuous_map (fun i : ↥(insert a S) => i.val)).comp
    continuous_subtype_val

theorem facetBoundaryToAmbient_injective (a : V) (S : Finset V) :
    Function.Injective (facetBoundaryToAmbient a S) := by
  intro p q hpq
  apply Subtype.ext
  apply (supportFaceHomeomorph (insert a S)).injective
  exact Subtype.ext hpq

def facetBoundaryPoint (a : V) (S : Finset V) (hS : S.Nonempty) (ha : a ∉ S) :
    FacetBoundary a S :=
  ⟨stdSimplex.vertex (S := ℝ) ⟨a, Finset.mem_insert_self a S⟩, by
    obtain ⟨j, hj⟩ := hS
    have hja : j ≠ a := fun h => ha (h ▸ hj)
    refine ⟨⟨j, Finset.mem_insert_of_mem hj⟩, ?_⟩
    simp [Subtype.ext_iff, hja]⟩

theorem facetBoundaryToAmbient_point (a : V) (S : Finset V) (hS : S.Nonempty) (ha : a ∉ S) :
    facetBoundaryToAmbient a S (facetBoundaryPoint a S hS ha) = stdSimplex.vertex (S := ℝ) a := by
  exact stdSimplex.map_vertex Subtype.val ⟨a, Finset.mem_insert_self a S⟩

omit [Fintype V] in
theorem complementary_erase_apex (a : V) {S : Finset V} (ha : a ∉ S) :
    (insert a S).erase a = S := Finset.erase_insert ha

omit [Fintype V] in
theorem erase_apex_insert {a j : V} (hja : j ≠ a) (S : Finset V) :
    (insert a S).erase j = insert a (S.erase j) := by
  ext i
  by_cases hi : i = a
  · subst i
    simp [Ne.symm hja]
  · simp [hi]

theorem facetBoundaryToAmbient_mem {K : Finset (Finset V)} {a : V}
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    {S : Finset V} (hS : S ∈ complementaryFaces K a) (p : FacetBoundary a S) :
    facetBoundaryToAmbient a S p ∈ faceFamilySpace K := by
  obtain ⟨i, hi⟩ := p.property
  refine mem_faceFamilySpace.mpr ⟨(insert a S).erase i.val, ?_,
    map_mem_supportFace_erase _ p.val i hi⟩
  by_cases hia : i.val = a
  · rw [hia, complementary_erase_apex a (apex_not_mem_complementary hS)]
    exact (mem_complementaryFaces.mp hS).1
  · have hiS : i.val ∈ S := (Finset.mem_insert.mp i.property).resolve_left hia
    rw [erase_apex_insert hia]
    exact (mem_faceStar.mp (hproper S hS (S.erase i.val) (Finset.erase_ssubset hiS))).2

def facetBoundaryInComplex {K : Finset (Finset V)} {a : V}
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (S : complementaryFaces K a) : C(FacetBoundary a S.val, faceFamilySpace K) :=
  ⟨fun p => ⟨facetBoundaryToAmbient a S.val p, facetBoundaryToAmbient_mem hproper S.property p⟩,
    (facetBoundaryToAmbient a S.val).continuous.subtype_mk _⟩

/-- The original facet is the face opposite the star vertex. -/
def facetToBoundary (a : V) (S : Finset V) (ha : a ∉ S) : C(supportFace S, FacetBoundary a S) where
  toFun x :=
    ⟨supportFaceRestrict (insert a S)
      ⟨x.val, supportFace_mono (Finset.subset_insert a S) x.property⟩,
      ⟨⟨a, Finset.mem_insert_self a S⟩, x.property a ha⟩⟩
  continuous_toFun := ((supportFaceRestrict (insert a S)).continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

theorem facetBoundaryToAmbient_facetToBoundary (a : V) (S : Finset V) (ha : a ∉ S)
    (x : supportFace S) : facetBoundaryToAmbient a S (facetToBoundary a S ha x) = x.val := by
  exact congrArg Subtype.val (supportFaceInsert_supportFaceRestrict (insert a S)
    ⟨x.val, supportFace_mono (Finset.subset_insert a S) x.property⟩)

theorem facetToBoundary_mem_inactive {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) {S : Finset V}
    (hS : S ∈ complementaryFaces K a) (x : supportFace S)
    (hx : x.val ∈ faceFamilySpace (faceStar K a)) :
    ∃ j : ↥(insert a S), j ≠ ⟨a, Finset.mem_insert_self a S⟩ ∧
      (facetToBoundary a S (apex_not_mem_complementary hS) x).val.val j = 0 := by
  obtain ⟨j, hjS, hj0⟩ := exists_zero_coordinate_of_complementary_inter_star hdown hS hx
  refine ⟨⟨j, Finset.mem_insert_of_mem hjS⟩, ?_, hj0⟩
  intro he
  have hja : j = a := congrArg Subtype.val he
  exact apex_not_mem_complementary hS (hja ▸ hjS)

theorem facetBoundary_inactive_mem_star {K : Finset (Finset V)} {a : V}
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    {S : Finset V} (hS : S ∈ complementaryFaces K a) (p : FacetBoundary a S)
    (hp : ∃ j : ↥(insert a S), j ≠ ⟨a, Finset.mem_insert_self a S⟩ ∧ p.val.val j = 0) :
    facetBoundaryToAmbient a S p ∈ faceFamilySpace (faceStar K a) := by
  obtain ⟨j, hja, hj0⟩ := hp
  have hjna : j.val ≠ a := fun h => hja (Subtype.ext h)
  have hjS : j.val ∈ S := (Finset.mem_insert.mp j.property).resolve_left hjna
  have hT : S.erase j.val ∈ faceStar K a := hproper S hS _ (Finset.erase_ssubset hjS)
  refine mem_faceFamilySpace.mpr ⟨insert a (S.erase j.val), insert_mem_faceStar hT, ?_⟩
  rw [← erase_apex_insert hjna]
  exact map_mem_supportFace_erase _ p.val j hj0

theorem facetBoundary_inactive_of_mem_star {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) {S : Finset V}
    (hS : S ∈ complementaryFaces K a) (p : FacetBoundary a S)
    (hp : facetBoundaryToAmbient a S p ∈ faceFamilySpace (faceStar K a)) :
    ∃ j : ↥(insert a S), j ≠ ⟨a, Finset.mem_insert_self a S⟩ ∧ p.val.val j = 0 := by
  obtain ⟨j, hjS, hj0⟩ := exists_zero_coordinate_of_complementary_inter_star hdown hS hp
  refine ⟨⟨j, Finset.mem_insert_of_mem hjS⟩, ?_, ?_⟩
  · intro he
    have hja : j = a := congrArg Subtype.val he
    exact apex_not_mem_complementary hS (hja ▸ hjS)
  · change (stdSimplex.map Subtype.val p.val) j = 0 at hj0
    change p.val ⟨j, Finset.mem_insert_of_mem hjS⟩ = 0
    simpa only [map_subtype_val_apply_mem (insert a S) p.val ⟨j, Finset.mem_insert_of_mem hjS⟩]
      using hj0

omit [Fintype V] in
private theorem complementary_card_insert {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) : 2 ≤ Fintype.card ↥(insert a S.val) := by
  have hcard : (insert a S.val).card = S.val.card + 1 := by
    simp [apex_not_mem_complementary S.property]
  rw [Fintype.card_coe, hcard]
  have hs := (complementary_nonempty ha S.property).card_pos
  omega

def complementarySphereHomotopy {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) :
    C(unitInterval × FacetBoundary a S.val, FacetBoundary a S.val) :=
  Classical.choose (exists_boundary_contraction_at_vertex
    (⟨a, Finset.mem_insert_self a S.val⟩ : ↥(insert a S.val)) (complementary_card_insert ha S))

omit [Fintype V] in
theorem complementarySphereHomotopy_zero {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) (p : FacetBoundary a S.val) :
    complementarySphereHomotopy ha S (0, p) = p :=
  (Classical.choose_spec (exists_boundary_contraction_at_vertex
    (⟨a, Finset.mem_insert_self a S.val⟩ : ↥(insert a S.val)) (complementary_card_insert ha S))).1 p

omit [Fintype V] in
theorem complementarySphereHomotopy_inactive {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) (t : unitInterval) (p : FacetBoundary a S.val)
    (hp : ∃ j : ↥(insert a S.val), j ≠ ⟨a, Finset.mem_insert_self a S.val⟩ ∧ p.val.val j = 0) :
    (complementarySphereHomotopy ha S (t, p)).val =
      vertexContraction ⟨a, Finset.mem_insert_self a S.val⟩ (t, p.val) :=
  (Classical.choose_spec (exists_boundary_contraction_at_vertex
    (⟨a, Finset.mem_insert_self a S.val⟩ : ↥(insert a S.val)) (complementary_card_insert ha S))).2 t p hp

def complementarySpherePoint {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) : FacetBoundary a S.val :=
  facetBoundaryPoint a S.val (complementary_nonempty ha S.property) (apex_not_mem_complementary S.property)

omit [Fintype V] in
theorem complementarySpherePoint_inactive {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) :
    ∃ j : ↥(insert a S.val), j ≠ ⟨a, Finset.mem_insert_self a S.val⟩ ∧
      (complementarySpherePoint ha S).val.val j = 0 := by
  obtain ⟨j, hj⟩ := (complementarySpherePoint ha S).property
  refine ⟨j, ?_, hj⟩
  intro he
  subst j
  simp [complementarySpherePoint, facetBoundaryPoint, stdSimplex.vertex] at hj

theorem complementarySphereHomotopy_point {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) (t : unitInterval) :
    complementarySphereHomotopy ha S (t, complementarySpherePoint ha S) = complementarySpherePoint ha S := by
  apply Subtype.ext
  rw [complementarySphereHomotopy_inactive ha S t _ (complementarySpherePoint_inactive ha S)]
  exact vertexContraction_vertex _ t

theorem complementarySphereHomotopy_one_of_inactive {K : Finset (Finset V)} {a : V}
    (ha : {a} ∈ K) (S : complementaryFaces K a) (p : FacetBoundary a S.val)
    (hp : ∃ j : ↥(insert a S.val), j ≠ ⟨a, Finset.mem_insert_self a S.val⟩ ∧ p.val.val j = 0) :
    complementarySphereHomotopy ha S (1, p) = complementarySpherePoint ha S := by
  apply Subtype.ext
  rw [complementarySphereHomotopy_inactive ha S 1 p hp, vertexContraction_one]
  rfl

theorem complementarySphereHomotopy_ambient_of_star {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (S : complementaryFaces K a) (t : unitInterval) (p : FacetBoundary a S.val)
    (hp : facetBoundaryToAmbient a S.val p ∈ faceFamilySpace (faceStar K a)) :
    facetBoundaryToAmbient a S.val (complementarySphereHomotopy ha S (t, p)) =
      vertexContraction a (t, facetBoundaryToAmbient a S.val p) := by
  change stdSimplex.map Subtype.val (complementarySphereHomotopy ha S (t, p)).val = _
  rw [complementarySphereHomotopy_inactive ha S t p
    (facetBoundary_inactive_of_mem_star hdown S.property p hp)]
  exact (vertexContraction_map Subtype.val ⟨a, Finset.mem_insert_self a S.val⟩ t p.val).symm

/-- The star and complementary facets form a finite closed cover. -/
def coneCover (K : Finset (Finset V)) (a : V) :
    Option (complementaryFaces K a) → Set (faceFamilySpace K)
  | none => {x | x.val ∈ faceFamilySpace (faceStar K a)}
  | some S => {x | x.val ∈ supportFace S.val}

theorem isClosed_coneCover (K : Finset (Finset V)) (a : V)
    (j : Option (complementaryFaces K a)) : IsClosed (coneCover K a j) := by
  cases j with
  | none => exact (isClosed_faceFamilySpace (faceStar K a)).preimage continuous_subtype_val
  | some S => exact (isClosed_supportFace S.val).preimage continuous_subtype_val

theorem iUnion_coneCover (K : Finset (Finset V)) (a : V) : ⋃ j, coneCover K a j = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨S, hS, hxS⟩ := mem_faceFamilySpace.mp x.property
  by_cases hstar : S ∈ faceStar K a
  · exact Set.mem_iUnion.mpr ⟨none, mem_faceFamilySpace.mpr ⟨S, hstar, hxS⟩⟩
  · exact Set.mem_iUnion.mpr ⟨some ⟨S, mem_complementaryFaces.mpr ⟨hS, hstar⟩⟩, hxS⟩

private def coneCoverFacetChart (K : Finset (Finset V)) (a : V) (S : complementaryFaces K a) :
    C(coneCover K a (some S), supportFace S.val) :=
  ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def coneCoverHomotopy {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a) :
    ∀ j : Option (complementaryFaces K a), C(unitInterval × coneCover K a j, faceFamilySpace K)
  | none =>
    ⟨fun z => ⟨vertexContraction a (z.1, z.2.val.val),
      faceFamilySpace_mono (faceStar_subset K a)
        (faceStarContraction K a (z.1, ⟨z.2.val.val, z.2.property⟩)).property⟩,
      ((vertexContraction a).continuous.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _⟩
  | some S =>
    (facetBoundaryInComplex hproper S).comp ((complementarySphereHomotopy ha S).comp
      (ContinuousMap.prodMap (ContinuousMap.id _) ((facetToBoundary a S.val
        (apex_not_mem_complementary S.property)).comp (coneCoverFacetChart K a S))))

theorem coneCoverHomotopy_ambient_of_star {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (j : Option (complementaryFaces K a)) (t : unitInterval) (x : coneCover K a j)
    (hx : x.val.val ∈ faceFamilySpace (faceStar K a)) :
    (coneCoverHomotopy ha hproper j (t, x)).val = vertexContraction a (t, x.val.val) := by
  cases j with
  | none => rfl
  | some S =>
    change facetBoundaryToAmbient a S.val
      (complementarySphereHomotopy ha S
        (t, facetToBoundary a S.val (apex_not_mem_complementary S.property)
          ⟨x.val.val, x.property⟩)) = _
    rw [complementarySphereHomotopy_ambient_of_star hdown ha S t _ ?_,
      facetBoundaryToAmbient_facetToBoundary]
    rwa [facetBoundaryToAmbient_facetToBoundary]

theorem coneCoverHomotopy_compatible {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (i j : Option (complementaryFaces K a)) (x : faceFamilySpace K)
    (hi : x ∈ coneCover K a i) (hj : x ∈ coneCover K a j) (t : unitInterval) :
    coneCoverHomotopy ha hproper i (t, ⟨x, hi⟩) = coneCoverHomotopy ha hproper j (t, ⟨x, hj⟩) := by
  by_cases hij : i = j
  · subst j
    rfl
  have hx : x.val ∈ faceFamilySpace (faceStar K a) := by
    cases i with
    | none => exact hi
    | some S =>
      cases j with
      | none => exact hj
      | some T =>
        have hne : S.val ≠ T.val := fun h => hij (congrArg some (Subtype.ext h))
        exact complementary_inter_subset_star hproper S.property T.property hne ⟨hi, hj⟩
  apply Subtype.ext
  rw [coneCoverHomotopy_ambient_of_star hdown ha hproper i t _ hx,
    coneCoverHomotopy_ambient_of_star hdown ha hproper j t _ hx]

def coneComplexHomotopy {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a) :
    C(unitInterval × faceFamilySpace K, faceFamilySpace K) :=
  let F j := ((coneCoverHomotopy ha hproper j).comp ContinuousMap.prodSwap).curry
  let hF : ∀ i j x hi hj, F i ⟨x, hi⟩ = F j ⟨x, hj⟩ :=
    fun i j x hi hj => ContinuousMap.ext (coneCoverHomotopy_compatible hdown ha hproper i j x hi hj)
  (finiteClosedCoverMap (coneCover K a) (isClosed_coneCover K a) (iUnion_coneCover K a) F hF).uncurry.comp
    ContinuousMap.prodSwap

theorem coneComplexHomotopy_cover {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (j : Option (complementaryFaces K a)) (t : unitInterval) (x : coneCover K a j) :
    coneComplexHomotopy hdown ha hproper (t, x.val) = coneCoverHomotopy ha hproper j (t, x) := by
  simp only [coneComplexHomotopy, ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply,
    ContinuousMap.uncurry_apply, Function.uncurry_apply_pair, finiteClosedCoverMap_apply,
    ContinuousMap.curry_apply]

def complexApex {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K) : faceFamilySpace K :=
  ⟨stdSimplex.vertex (S := ℝ) a,
    faceFamilySpace_mono (faceStar_subset K a) (vertex_mem_faceStarSpace ha)⟩

theorem exists_mem_coneCover (K : Finset (Finset V)) (a : V) (x : faceFamilySpace K) :
    ∃ j, x ∈ coneCover K a j := by
  apply Set.mem_iUnion.mp
  rw [iUnion_coneCover]
  trivial

theorem coneCoverHomotopy_zero {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (j : Option (complementaryFaces K a)) (x : coneCover K a j) :
    coneCoverHomotopy ha hproper j (0, x) = x.val := by
  apply Subtype.ext
  cases j with
  | none => exact vertexContraction_zero a x.val.val
  | some S =>
    change facetBoundaryToAmbient a S.val
      (complementarySphereHomotopy ha S
        (0, facetToBoundary a S.val (apex_not_mem_complementary S.property)
          ⟨x.val.val, x.property⟩)) = x.val.val
    rw [complementarySphereHomotopy_zero, facetBoundaryToAmbient_facetToBoundary]

theorem coneComplexHomotopy_zero {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (x : faceFamilySpace K) : coneComplexHomotopy hdown ha hproper (0, x) = x := by
  obtain ⟨j, hj⟩ := exists_mem_coneCover K a x
  exact (coneComplexHomotopy_cover hdown ha hproper j 0 ⟨x, hj⟩).trans
    (coneCoverHomotopy_zero ha hproper j ⟨x, hj⟩)

theorem coneComplexHomotopy_ambient_of_star {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (t : unitInterval) (x : faceFamilySpace K) (hx : x.val ∈ faceFamilySpace (faceStar K a)) :
    (coneComplexHomotopy hdown ha hproper (t, x)).val = vertexContraction a (t, x.val) := by
  rw [coneComplexHomotopy_cover hdown ha hproper none t ⟨x, hx⟩]
  rfl

theorem facetBoundary_mem_facet_of_not_star {K : Finset (Finset V)} {a : V}
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (S : complementaryFaces K a) (p : FacetBoundary a S.val)
    (hp : facetBoundaryToAmbient a S.val p ∉ faceFamilySpace (faceStar K a)) :
    facetBoundaryToAmbient a S.val p ∈ supportFace S.val := by
  obtain ⟨j, hj⟩ := p.property
  have hja : j = ⟨a, Finset.mem_insert_self a S.val⟩ := by
    by_contra hne
    exact hp (facetBoundary_inactive_mem_star hproper S.property p ⟨j, hne, hj⟩)
  have he : (insert a S.val).erase j.val = S.val := by
    rw [hja]
    exact complementary_erase_apex a (apex_not_mem_complementary S.property)
  simpa only [he, facetBoundaryToAmbient, ContinuousMap.coe_mk] using
    map_mem_supportFace_erase _ p.val j hj

theorem facetToBoundary_ambient_eq (a : V) (S : Finset V) (ha : a ∉ S)
    (p : FacetBoundary a S) (hp : facetBoundaryToAmbient a S p ∈ supportFace S) :
    facetToBoundary a S ha ⟨facetBoundaryToAmbient a S p, hp⟩ = p :=
  facetBoundaryToAmbient_injective a S (facetBoundaryToAmbient_facetToBoundary a S ha _)

theorem coneComplexHomotopy_boundary {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (S : complementaryFaces K a) (t : unitInterval) (p : FacetBoundary a S.val) :
    coneComplexHomotopy hdown ha hproper (t, facetBoundaryInComplex hproper S p) =
      facetBoundaryInComplex hproper S (complementarySphereHomotopy ha S (t, p)) := by
  by_cases hp : facetBoundaryToAmbient a S.val p ∈ faceFamilySpace (faceStar K a)
  · apply Subtype.ext
    rw [coneComplexHomotopy_ambient_of_star hdown ha hproper t _ hp]
    exact (complementarySphereHomotopy_ambient_of_star hdown ha S t p hp).symm
  · have hx := facetBoundary_mem_facet_of_not_star hproper S p hp
    rw [coneComplexHomotopy_cover hdown ha hproper (some S) t
      ⟨facetBoundaryInComplex hproper S p, hx⟩]
    change facetBoundaryInComplex hproper S
      (complementarySphereHomotopy ha S
        (t, facetToBoundary a S.val (apex_not_mem_complementary S.property)
          ⟨facetBoundaryToAmbient a S.val p, hx⟩)) = _
    rw [facetToBoundary_ambient_eq]

abbrev ConeBouquet {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K) :=
  BasedBouquet (fun S : complementaryFaces K a => FacetBoundary a S.val) (complementarySpherePoint ha)

def coneCoverCollapse {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K) :
    ∀ j : Option (complementaryFaces K a), C(coneCover K a j, ConeBouquet ha)
  | none => ContinuousMap.const _ (bouquetPoint (complementarySpherePoint ha))
  | some S =>
    (bouquetInclusion (complementarySpherePoint ha) S).comp
      ((complementarySphereHomotopy ha S).comp
        ⟨fun x => (1, facetToBoundary a S.val (apex_not_mem_complementary S.property)
          (coneCoverFacetChart K a S x)),
          continuous_const.prodMk ((facetToBoundary a S.val (apex_not_mem_complementary S.property)).continuous.comp
            (coneCoverFacetChart K a S).continuous)⟩)

theorem coneCoverCollapse_of_star {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (j : Option (complementaryFaces K a)) (x : coneCover K a j)
    (hx : x.val.val ∈ faceFamilySpace (faceStar K a)) :
    coneCoverCollapse ha j x = bouquetPoint (complementarySpherePoint ha) := by
  cases j with
  | none => rfl
  | some S =>
    change bouquetInclusion (complementarySpherePoint ha) S
      (complementarySphereHomotopy ha S
        (1, facetToBoundary a S.val (apex_not_mem_complementary S.property)
          ⟨x.val.val, x.property⟩)) = _
    rw [complementarySphereHomotopy_one_of_inactive ha S _
      (facetToBoundary_mem_inactive hdown S.property ⟨x.val.val, x.property⟩ hx)]
    exact bouquetInclusion_base _ S

theorem coneCoverCollapse_compatible {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (i j : Option (complementaryFaces K a)) (x : faceFamilySpace K)
    (hi : x ∈ coneCover K a i) (hj : x ∈ coneCover K a j) :
    coneCoverCollapse ha i ⟨x, hi⟩ = coneCoverCollapse ha j ⟨x, hj⟩ := by
  by_cases hij : i = j
  · subst j
    rfl
  have hx : x.val ∈ faceFamilySpace (faceStar K a) := by
    cases i with
    | none => exact hi
    | some S =>
      cases j with
      | none => exact hj
      | some T =>
        exact complementary_inter_subset_star hproper S.property T.property
          (fun h => hij (congrArg some (Subtype.ext h))) ⟨hi, hj⟩
  rw [coneCoverCollapse_of_star hdown ha i _ hx, coneCoverCollapse_of_star hdown ha j _ hx]

def coneBouquetForward {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a) :
    C(faceFamilySpace K, ConeBouquet ha) :=
  finiteClosedCoverMap (coneCover K a) (isClosed_coneCover K a) (iUnion_coneCover K a)
    (coneCoverCollapse ha) (coneCoverCollapse_compatible hdown ha hproper)

theorem coneBouquetForward_cover {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (j : Option (complementaryFaces K a)) (x : coneCover K a j) :
    coneBouquetForward hdown ha hproper x.val = coneCoverCollapse ha j x :=
  finiteClosedCoverMap_apply _ _ _ _ _ j x

theorem coneBouquetForward_of_star {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (x : faceFamilySpace K) (hx : x.val ∈ faceFamilySpace (faceStar K a)) :
    coneBouquetForward hdown ha hproper x = bouquetPoint (complementarySpherePoint ha) :=
  coneBouquetForward_cover hdown ha hproper none ⟨x, hx⟩

def coneBouquetBack {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a) :
    C(ConeBouquet ha, faceFamilySpace K) :=
  bouquetDesc (complementarySpherePoint ha) (facetBoundaryInComplex hproper) (complexApex ha)
    (fun S => Subtype.ext (facetBoundaryToAmbient_point a S.val
      (complementary_nonempty ha S.property) (apex_not_mem_complementary S.property)))

theorem coneBouquetBack_point {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a) :
    coneBouquetBack ha hproper (bouquetPoint (complementarySpherePoint ha)) = complexApex ha := rfl

theorem coneBouquetBack_inclusion {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (S : complementaryFaces K a) (p : FacetBoundary a S.val) :
    coneBouquetBack ha hproper (bouquetInclusion (complementarySpherePoint ha) S p) =
      facetBoundaryInComplex hproper S p := rfl

theorem coneBouquetForward_boundary {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (S : complementaryFaces K a) (p : FacetBoundary a S.val) :
    coneBouquetForward hdown ha hproper (facetBoundaryInComplex hproper S p) =
      bouquetInclusion (complementarySpherePoint ha) S
        (complementarySphereHomotopy ha S (1, p)) := by
  by_cases hp : facetBoundaryToAmbient a S.val p ∈ faceFamilySpace (faceStar K a)
  · rw [coneBouquetForward_of_star hdown ha hproper _ hp,
      complementarySphereHomotopy_one_of_inactive ha S p
        (facetBoundary_inactive_of_mem_star hdown S.property p hp), bouquetInclusion_base]
  · have hx := facetBoundary_mem_facet_of_not_star hproper S p hp
    rw [coneBouquetForward_cover hdown ha hproper (some S)
      ⟨facetBoundaryInComplex hproper S p, hx⟩]
    change bouquetInclusion (complementarySpherePoint ha) S
      (complementarySphereHomotopy ha S
        (1, facetToBoundary a S.val (apex_not_mem_complementary S.property)
          ⟨facetBoundaryToAmbient a S.val p, hx⟩)) = _
    rw [facetToBoundary_ambient_eq]

theorem coneComplexHomotopy_one {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (x : faceFamilySpace K) : coneComplexHomotopy hdown ha hproper (1, x) =
      coneBouquetBack ha hproper (coneBouquetForward hdown ha hproper x) := by
  obtain ⟨j, hj⟩ := exists_mem_coneCover K a x
  rw [coneComplexHomotopy_cover hdown ha hproper j 1 ⟨x, hj⟩,
    coneBouquetForward_cover hdown ha hproper j ⟨x, hj⟩]
  cases j with
  | none =>
    apply Subtype.ext
    exact vertexContraction_one a x.val
  | some S => rfl

def coneBouquetHomotopy {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K) :
    C(unitInterval × ConeBouquet ha, ConeBouquet ha) :=
  bouquetHomotopyMap (complementarySpherePoint ha)
    (fun S => (bouquetInclusion (complementarySpherePoint ha) S).comp (complementarySphereHomotopy ha S))
    (ContinuousMap.const _ (bouquetPoint (complementarySpherePoint ha)))
    (fun S t => by
      change bouquetInclusion (complementarySpherePoint ha) S
        (complementarySphereHomotopy ha S (t, complementarySpherePoint ha S)) = _
      rw [complementarySphereHomotopy_point, bouquetInclusion_base]
      rfl)

theorem coneBouquetHomotopy_zero {K : Finset (Finset V)} {a : V} (ha : {a} ∈ K)
    (z : ConeBouquet ha) : coneBouquetHomotopy ha (0, z) = z := by
  refine bouquet_induction (complementarySpherePoint ha)
    (P := fun z => coneBouquetHomotopy ha (0, z) = z) ?_ ?_ z
  · rfl
  · intro S p
    change bouquetInclusion (complementarySpherePoint ha) S
      (complementarySphereHomotopy ha S (0, p)) = _
    rw [complementarySphereHomotopy_zero]

theorem coneBouquetHomotopy_one {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a)
    (z : ConeBouquet ha) : coneBouquetHomotopy ha (1, z) =
      coneBouquetForward hdown ha hproper (coneBouquetBack ha hproper z) := by
  refine bouquet_induction (complementarySpherePoint ha)
    (P := fun z => coneBouquetHomotopy ha (1, z) =
      coneBouquetForward hdown ha hproper (coneBouquetBack ha hproper z)) ?_ ?_ z
  · change bouquetPoint (complementarySpherePoint ha) =
      coneBouquetForward hdown ha hproper (complexApex ha)
    exact (coneBouquetForward_of_star hdown ha hproper _ (vertex_mem_faceStarSpace ha)).symm
  · intro S p
    change bouquetInclusion (complementarySpherePoint ha) S
      (complementarySphereHomotopy ha S (1, p)) =
        coneBouquetForward hdown ha hproper (facetBoundaryInComplex hproper S p)
    exact (coneBouquetForward_boundary hdown ha hproper S p).symm

/-- A conical star whose complementary faces have all proper faces in the
star gives a homotopy equivalence to the wedge of their surrounding spheres. -/
def finiteConeComplexHomotopyEquiv {K : Finset (Finset V)} {a : V}
    (hdown : ∀ S ∈ K, ∀ T ⊆ S, T ∈ K) (ha : {a} ∈ K)
    (hproper : ∀ S ∈ complementaryFaces K a, ∀ T ⊂ S, T ∈ faceStar K a) :
    HomotopyEquiv (faceFamilySpace K) (ConeBouquet ha) := by
  let f := coneBouquetForward hdown ha hproper
  let g := coneBouquetBack ha hproper
  refine ⟨f, g, ?_, ?_⟩
  · refine ⟨(show (ContinuousMap.id _).Homotopy (g.comp f) from ?_).symm⟩
    exact ⟨coneComplexHomotopy hdown ha hproper, coneComplexHomotopy_zero hdown ha hproper,
      coneComplexHomotopy_one hdown ha hproper⟩
  · refine ⟨(show (ContinuousMap.id _).Homotopy (f.comp g) from ?_).symm⟩
    exact ⟨coneBouquetHomotopy ha, coneBouquetHomotopy_zero ha,
      coneBouquetHomotopy_one hdown ha hproper⟩

#print axioms finiteConeComplexHomotopyEquiv

/-- Pointed homeomorphisms of the summands induce a homeomorphism of wedges. -/
def bouquetHomeomorph {J : Type*} {X Y : J → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ j, TopologicalSpace (Y j)]
    (b : ∀ j, X j) (c : ∀ j, Y j) (h : ∀ j, X j ≃ₜ Y j)
    (hb : ∀ j, h j (b j) = c j) : BasedBouquet X b ≃ₜ BasedBouquet Y c := by
  let f : C(BasedBouquet X b, BasedBouquet Y c) :=
    bouquetDesc b (fun j => (bouquetInclusion c j).comp ⟨h j, (h j).continuous⟩)
      (bouquetPoint c) (fun j => by
        change bouquetInclusion c j (h j (b j)) = _
        rw [hb j, bouquetInclusion_base])
  let g : C(BasedBouquet Y c, BasedBouquet X b) :=
    bouquetDesc c (fun j => (bouquetInclusion b j).comp ⟨(h j).symm, (h j).symm.continuous⟩)
      (bouquetPoint b) (fun j => by
        change bouquetInclusion b j ((h j).symm (c j)) = _
        rw [← hb j, Homeomorph.symm_apply_apply, bouquetInclusion_base])
  refine ⟨⟨f, g, ?_, ?_⟩, f.continuous, g.continuous⟩
  · exact bouquet_induction b (P := fun x => g (f x) = x) rfl (fun j x => by
      change bouquetInclusion b j ((h j).symm (h j x)) = _
      rw [Homeomorph.symm_apply_apply])
  · exact bouquet_induction c (P := fun y => f (g y) = y) rfl (fun j y => by
      change bouquetInclusion c j (h j ((h j).symm y)) = _
      rw [Homeomorph.apply_symm_apply])

/-- Relabeling the index set preserves the pointed wedge. -/
def bouquetReindex {J K : Type*} (e : J ≃ K) {X : K → Type*}
    [∀ k, TopologicalSpace (X k)] (b : ∀ k, X k) :
    BasedBouquet (fun j => X (e j)) (fun j => b (e j)) ≃ₜ BasedBouquet X b := by
  let b' := fun j => b (e j)
  let f : C(BasedBouquet (fun j => X (e j)) b', BasedBouquet X b) :=
    bouquetDesc b' (fun j => bouquetInclusion b (e j)) (bouquetPoint b)
      (fun j => bouquetInclusion_base b (e j))
  let gk : ∀ k, C(X k, BasedBouquet (fun j => X (e j)) b') :=
    Equiv.piCongrLeft (fun k => C(X k, BasedBouquet (fun j => X (e j)) b')) e
      (fun j => bouquetInclusion b' j)
  have hgk (j : J) : gk (e j) = bouquetInclusion b' j := by
    exact Equiv.piCongrLeft_apply_apply _ _ _ j
  have hbase (k : K) : gk k (b k) = bouquetPoint b' := by
    obtain ⟨j, rfl⟩ := e.surjective k
    rw [hgk]
    exact bouquetInclusion_base b' j
  let g : C(BasedBouquet X b, BasedBouquet (fun j => X (e j)) b') :=
    bouquetDesc b gk (bouquetPoint b') hbase
  refine ⟨⟨f, g, ?_, ?_⟩, f.continuous, g.continuous⟩
  · exact bouquet_induction b' (P := fun x => g (f x) = x) rfl (fun j x => by
      change gk (e j) x = _
      rw [hgk])
  · apply bouquet_induction b (P := fun y => f (g y) = y) rfl
    intro k y
    obtain ⟨j, rfl⟩ := e.surjective k
    change f (gk (e j) y) = _
    rw [hgk]
    rfl

/-- Simultaneous relabeling of summands and pointed homeomorphisms. -/
def bouquetFamilyHomeomorph {J K : Type*} (e : J ≃ K) {X : J → Type*} {Y : K → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ k, TopologicalSpace (Y k)]
    (b : ∀ j, X j) (c : ∀ k, Y k) (h : ∀ j, X j ≃ₜ Y (e j))
    (hb : ∀ j, h j (b j) = c (e j)) : BasedBouquet X b ≃ₜ BasedBouquet Y c :=
  (bouquetHomeomorph b (fun j => c (e j)) h hb).trans (bouquetReindex e c)

#print axioms bouquetFamilyHomeomorph

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
