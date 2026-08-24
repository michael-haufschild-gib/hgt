import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Topological bordered spaces and strict morphisms

This file supplies the first topological layer used by enhanced sheaf theory. A topological
bordered space consists of an interior, an ambient space, and an open embedding of the interior
into the ambient space.

The strict morphisms defined here are continuous maps on interiors equipped with continuous
ambient extensions. They form the ambient-extension subcategory of bordered morphisms. General
bordered morphisms, defined by properness of the closure of the interior graph, are deliberately not
identified with this stricter notion.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

open CategoryTheory TopologicalSpace TopCat Topology

universe u

/-- Topological skeleton of a bordered space: an open embedding of an interior into an ambient
space. Good-space and subanalytic hypotheses belong to later refinements. -/
structure TopologicalBorderedSpace where
  /-- Interior space on which objects and morphisms are evaluated. -/
  interior : TopCat.{u}
  /-- Ambient space controlling behavior at the border. -/
  ambient : TopCat.{u}
  /-- Inclusion of the interior into the ambient space. -/
  inclusion : interior ⟶ ambient
  /-- The interior is an open subspace of the ambient space. -/
  inclusion_isOpenEmbedding : IsOpenEmbedding inclusion

namespace TopologicalBorderedSpace

/-- Inclusion from a closed subtype into any larger subtype is a closed embedding. -/
theorem isClosedEmbedding_subtype_mono {X : Type*} [TopologicalSpace X]
    {C G : Set X} (hC : IsClosed C) (hCG : C ⊆ G) :
    IsClosedEmbedding (fun p : C => (⟨p.1, hCG p.2⟩ : G)) := by
  let i : C → G := fun p => ⟨p.1, hCG p.2⟩
  refine ⟨?_, ?_⟩
  · apply IsEmbedding.subtypeVal.of_comp_iff.mp
    change IsEmbedding (Subtype.val : C → X)
    exact hC.isClosedEmbedding_subtypeVal.isEmbedding
  · have hrange : Set.range i = (Subtype.val : G → X) ⁻¹' C := by
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        exact p.2
      · intro hq
        exact ⟨⟨q.1, hq⟩, Subtype.ext rfl⟩
    rw [hrange]
    exact hC.preimage continuous_subtype_val

/-- Pairing a proper map with any continuous map into a Hausdorff space remains proper. -/
theorem isProperMap_prodMk_of_continuous {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    {f : X → Y} (hf : IsProperMap f) {g : X → Z} (hg : Continuous g) :
    IsProperMap (fun x => (f x, g x)) := by
  have hgraph : IsClosedEmbedding (fun x : X => (x, g x)) := by
    refine ⟨isEmbedding_graph hg, ?_⟩
    have hrange : Set.range (fun x : X => (x, g x)) =
        {p : X × Z | g p.1 = p.2} := by
      ext p
      constructor
      · rintro ⟨x, rfl⟩
        rfl
      · intro hp
        exact ⟨p.1, Prod.ext rfl hp⟩
    rw [hrange]
    exact isClosed_eq (hg.comp continuous_fst) continuous_snd
  have hprod : IsProperMap (Prod.map f (id : Z → Z)) :=
    hf.prodMap isProperMap_id
  have hcomp := hprod.comp hgraph.isProperMap
  simpa [Function.comp_def] using hcomp

/-- Restricting the codomain of a proper map to any subtype containing its range preserves
properness. -/
theorem isProperMap_codRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) {S : Set Y} (hS : ∀ x, f x ∈ S) :
    IsProperMap (fun x => (⟨f x, hS x⟩ : S)) := by
  refine ⟨hf.continuous.subtype_mk _, ?_⟩
  intro ℱ y hy
  have hy' : MapClusterPt y.1 ℱ f := by
    change ClusterPt y.1 (Filter.map f ℱ)
    have hc := ClusterPt.map hy continuousAt_subtype_val Filter.tendsto_map
    simpa only [Filter.map_map, Function.comp_def] using hc
  rcases hf.clusterPt_of_mapClusterPt hy' with ⟨x, hxy, hx⟩
  exact ⟨x, Subtype.ext hxy, hx⟩

/-- A continuous graph is homeomorphic to its source. -/
def graphHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (g : X → Y) (hg : Continuous g) : X ≃ₜ Set.range (fun x => (x, g x)) where
  toFun x := ⟨(x, g x), ⟨x, rfl⟩⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨p, x, rfl⟩
    rfl
  continuous_toFun := continuous_id.prodMk hg |>.subtype_mk _
  continuous_invFun := continuous_subtype_val.fst

/-- Set-theoretic fiber product of two maps to a common topological target. -/
def fiberProduct {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (a : X → Z) (b : Y → Z) : Set (X × Y) :=
  {p | a p.1 = b p.2}

/-- First projection from a fiber product. -/
def fiberProductFst {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (a : X → Z) (b : Y → Z) : fiberProduct a b → X :=
  fun p => p.1.1

/-- Proper maps are stable under base change along a continuous map into a Hausdorff target. -/
theorem isProperMap_fiberProductFst {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    {a : X → Z} (ha : Continuous a) {b : Y → Z} (hb : IsProperMap b) :
    IsProperMap (fiberProductFst a b) := by
  have hclosed : IsClosed (fiberProduct a b) :=
    isClosed_eq (ha.comp continuous_fst) (hb.continuous.comp continuous_snd)
  have hprod : IsProperMap (Prod.map (id : X → X) b) :=
    isProperMap_id.prodMap hb
  have hrestrict : IsProperMap (fun p : fiberProduct a b =>
      Prod.map (id : X → X) b p.1) :=
    hprod.restrict hclosed
  let G : Set (X × Z) := Set.range (fun x : X => (x, a x))
  have hinto : ∀ p : fiberProduct a b, Prod.map (id : X → X) b p.1 ∈ G := by
    intro p
    refine ⟨p.1.1, Prod.ext rfl ?_⟩
    exact p.2
  have hcod : IsProperMap (fun p : fiberProduct a b =>
      (⟨Prod.map (id : X → X) b p.1, hinto p⟩ : G)) :=
    isProperMap_codRestrict hrestrict hinto
  have hcomp := (graphHomeomorph a ha).symm.isClosedEmbedding.isProperMap.comp hcod
  change IsProperMap (fun p : fiberProduct a b => p.1.1)
  simpa [graphHomeomorph, G, Function.comp_def] using hcomp

/-- Properness descends through a surjective proper map. -/
theorem isProperMap_of_comp_surjective {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {q : X → Y} (hq : IsProperMap q) (hqsurj : Function.Surjective q) {g : Y → Z}
    (hcomp : IsProperMap (g ∘ q)) : IsProperMap g := by
  have hquot : IsQuotientMap q :=
    hq.isClosedMap.isQuotientMap hq.continuous hqsurj
  refine ⟨hquot.continuous_iff.mpr hcomp.continuous, ?_⟩
  intro ℱ z hz
  have hz' : MapClusterPt z (Filter.comap q ℱ) (g ∘ q) := by
    change ClusterPt z (Filter.map (g ∘ q) (Filter.comap q ℱ))
    rw [← Filter.map_map, Filter.map_comap_of_surjective hqsurj]
    exact hz
  rcases hcomp.clusterPt_of_mapClusterPt hz' with ⟨x, hxz, hx⟩
  refine ⟨q x, hxz, ?_⟩
  exact hx.map hq.continuous.continuousAt Filter.tendsto_comap

/-- Canonical bordered space attached to an open subset of a topological space. -/
def ofOpen {X : Type u} [TopologicalSpace X] (U : Opens X) : TopologicalBorderedSpace where
  interior := TopCat.of U
  ambient := TopCat.of X
  inclusion := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  inclusion_isOpenEmbedding := U.2.isOpenEmbedding_subtypeVal

/-- Interior graph of a continuous map, embedded in the product of the two ambient spaces. -/
def ambientGraph {M N : TopologicalBorderedSpace} (f : M.interior ⟶ N.interior) :
    Set (M.ambient × N.ambient) :=
  Set.range (fun x : M.interior => (M.inclusion x, N.inclusion (f x)))

/-- Closure of the interior graph in the product of ambient spaces. -/
def ambientGraphClosure {M N : TopologicalBorderedSpace} (f : M.interior ⟶ N.interior) :
    Set (M.ambient × N.ambient) :=
  closure (ambientGraph f)

/-- Projection from the closed ambient graph to the source ambient space. -/
def graphProjection {M N : TopologicalBorderedSpace} (f : M.interior ⟶ N.interior) :
    ambientGraphClosure f → M.ambient :=
  fun p => p.1.1

/-- The closed-graph projection is continuous. -/
theorem continuous_graphProjection {M N : TopologicalBorderedSpace}
    (f : M.interior ⟶ N.interior) : Continuous (graphProjection f) :=
  continuous_subtype_val.fst

/-- D'Agnolo--Kashiwara's topological condition for an interior map to define a bordered
morphism: projection of its closed ambient graph to the source ambient space is proper. -/
def IsBorderedMorphism {M N : TopologicalBorderedSpace} (f : M.interior ⟶ N.interior) : Prop :=
  IsProperMap (graphProjection f)

/-- A strict bordered morphism: an interior map with a continuous ambient extension commuting with
the two open embeddings. This is sufficient, but not necessary, for a general bordered morphism. -/
@[ext]
structure StrictHom (M N : TopologicalBorderedSpace) where
  /-- Map on interiors. -/
  interiorMap : M.interior ⟶ N.interior
  /-- Chosen continuous extension to ambient spaces. -/
  ambientMap : M.ambient ⟶ N.ambient
  /-- The ambient extension restricts to the interior map. -/
  comm : M.inclusion ≫ ambientMap = interiorMap ≫ N.inclusion

namespace StrictHom

/-- Identity strict bordered morphism. -/
def id (M : TopologicalBorderedSpace) : StrictHom M M where
  interiorMap := 𝟙 _
  ambientMap := 𝟙 _
  comm := by simp

/-- Composition of strict bordered morphisms. -/
def comp {M N P : TopologicalBorderedSpace} (f : StrictHom M N) (g : StrictHom N P) :
    StrictHom M P where
  interiorMap := f.interiorMap ≫ g.interiorMap
  ambientMap := f.ambientMap ≫ g.ambientMap
  comm := by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc]

@[simp]
theorem id_comp {M N : TopologicalBorderedSpace} (f : StrictHom M N) :
    comp (id M) f = f := by
  ext <;> simp [comp, id]

@[simp]
theorem comp_id {M N : TopologicalBorderedSpace} (f : StrictHom M N) :
    comp f (id N) = f := by
  ext <;> simp [comp, id]

theorem comp_assoc {M N P Q : TopologicalBorderedSpace} (f : StrictHom M N)
    (g : StrictHom N P) (h : StrictHom P Q) :
    comp (comp f g) h = comp f (comp g h) := by
  ext <;> simp [comp, Category.assoc]

/-- Ambient graph of a strict morphism is homeomorphic to its source ambient space. -/
def ambientExtensionGraphHomeomorph {M N : TopologicalBorderedSpace} (f : StrictHom M N) :
    M.ambient ≃ₜ Set.range (fun x : M.ambient => (x, f.ambientMap x)) where
  toFun x := ⟨(x, f.ambientMap x), ⟨x, rfl⟩⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨p, x, rfl⟩
    rfl
  continuous_toFun :=
    continuous_id.prodMk f.ambientMap.hom.continuous |>.subtype_mk _
  continuous_invFun := continuous_subtype_val.fst

/-- Interior graph of a strict morphism lies in the graph of its ambient extension. -/
theorem ambientGraph_subset_extensionGraph {M N : TopologicalBorderedSpace} (f : StrictHom M N) :
    ambientGraph f.interiorMap ⊆ Set.range (fun x : M.ambient => (x, f.ambientMap x)) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨M.inclusion x, Prod.ext rfl ?_⟩
  exact ConcreteCategory.congr_hom f.comm x

/-- Graph of the ambient extension is closed when the target ambient space is Hausdorff. -/
theorem isClosed_extensionGraph {M N : TopologicalBorderedSpace} [T2Space N.ambient]
    (f : StrictHom M N) :
    IsClosed (Set.range (fun x : M.ambient => (x, f.ambientMap x))) := by
  have hrange : Set.range (fun x : M.ambient => (x, f.ambientMap x)) =
      {p : M.ambient × N.ambient | f.ambientMap p.1 = p.2} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro hp
      exact ⟨p.1, Prod.ext rfl hp⟩
  rw [hrange]
  exact isClosed_eq (f.ambientMap.hom.continuous.comp continuous_fst) continuous_snd

/-- Closed interior graph of a strict morphism remains in its ambient extension graph. -/
theorem ambientGraphClosure_subset_extensionGraph {M N : TopologicalBorderedSpace}
    [T2Space N.ambient] (f : StrictHom M N) :
    ambientGraphClosure f.interiorMap ⊆
      Set.range (fun x : M.ambient => (x, f.ambientMap x)) :=
  closure_minimal (ambientGraph_subset_extensionGraph f) (isClosed_extensionGraph f)

/-- Every strict morphism into a Hausdorff ambient target satisfies the full bordered-morphism
proper-graph condition. -/
theorem isBorderedMorphism {M N : TopologicalBorderedSpace} [T2Space N.ambient]
    (f : StrictHom M N) : IsBorderedMorphism f.interiorMap := by
  let G : Set (M.ambient × N.ambient) :=
    Set.range (fun x : M.ambient => (x, f.ambientMap x))
  let i : ambientGraphClosure f.interiorMap → G := fun p =>
    ⟨p.1, ambientGraphClosure_subset_extensionGraph f p.2⟩
  have hi : IsClosedEmbedding i :=
    isClosedEmbedding_subtype_mono isClosed_closure
      (ambientGraphClosure_subset_extensionGraph f)
  have hproj : graphProjection f.interiorMap =
      (ambientExtensionGraphHomeomorph f).symm ∘ i := by
    rfl
  rw [IsBorderedMorphism, hproj]
  exact ((ambientExtensionGraphHomeomorph f).symm.isClosedEmbedding.comp hi).isProperMap

end StrictHom

/-- General bordered morphisms are closed under composition when intermediate and target ambient
spaces are Hausdorff. The proof composes their closed graph relations through a proper fiber
product, then descends properness to the closed image relation. -/
theorem isBorderedMorphism_comp {M N P : TopologicalBorderedSpace}
    [T2Space N.ambient] [T2Space P.ambient]
    {f : M.interior ⟶ N.interior} {g : N.interior ⟶ P.interior}
    (hf : IsBorderedMorphism f) (hg : IsBorderedMorphism g) :
    IsBorderedMorphism (f ≫ g) := by
  let Cf : Set (M.ambient × N.ambient) := ambientGraphClosure f
  let Cg : Set (N.ambient × P.ambient) := ambientGraphClosure g
  let a : Cf → N.ambient := fun p => p.1.2
  let b : Cg → N.ambient := graphProjection g
  let F : Set (Cf × Cg) := fiberProduct a b
  let qf : F → Cf := fiberProductFst a b
  let source : F → M.ambient := fun p => p.1.1.1.1
  let target : F → P.ambient := fun p => p.1.2.1.2
  let compositeGraph : F → M.ambient × P.ambient := fun p => (source p, target p)
  have ha : Continuous a := continuous_subtype_val.snd
  have hqf : IsProperMap qf := by
    apply isProperMap_fiberProductFst ha
    exact hg
  have hsource : IsProperMap source := by
    have hcomp := hf.comp hqf
    simpa [source, qf, a, b, F, Cf, Cg, fiberProductFst, graphProjection,
      Function.comp_def] using hcomp
  have htarget : Continuous target := by
    fun_prop
  have hcomposite : IsProperMap compositeGraph :=
    isProperMap_prodMk_of_continuous hsource htarget
  let R : Set (M.ambient × P.ambient) := Set.range compositeGraph
  have hRclosed : IsClosed R := by
    have hclosed := hcomposite.isClosedMap Set.univ isClosed_univ
    simpa [R] using hclosed
  have hgraphSub : ambientGraph (f ≫ g) ⊆ R := by
    rintro _ ⟨x, rfl⟩
    have hpf : (M.inclusion x, N.inclusion (f x)) ∈ Cf := by
      apply subset_closure
      exact ⟨x, rfl⟩
    have hpg : (N.inclusion (f x), P.inclusion (g (f x))) ∈ Cg := by
      apply subset_closure
      exact ⟨f x, rfl⟩
    let pf : Cf := ⟨(M.inclusion x, N.inclusion (f x)), hpf⟩
    let pg : Cg := ⟨(N.inclusion (f x), P.inclusion (g (f x))), hpg⟩
    have hmatch : a pf = b pg := rfl
    let w : F := ⟨(pf, pg), hmatch⟩
    exact ⟨w, rfl⟩
  have hclosureSub : ambientGraphClosure (f ≫ g) ⊆ R :=
    closure_minimal hgraphSub hRclosed
  have hintoR : ∀ w : F, compositeGraph w ∈ R := fun w => ⟨w, rfl⟩
  let q : F → R := fun w => ⟨compositeGraph w, hintoR w⟩
  have hq : IsProperMap q :=
    isProperMap_codRestrict hcomposite hintoR
  have hqsurj : Function.Surjective q := by
    rintro ⟨_, w, rfl⟩
    exact ⟨w, rfl⟩
  let π : R → M.ambient := fun p => p.1.1
  have hπcomp : IsProperMap (π ∘ q) := by
    simpa [π, q, compositeGraph, source, Function.comp_def] using hsource
  have hπ : IsProperMap π :=
    isProperMap_of_comp_surjective hq hqsurj hπcomp
  let i : ambientGraphClosure (f ≫ g) → R := fun p => ⟨p.1, hclosureSub p.2⟩
  have hi : IsClosedEmbedding i :=
    isClosedEmbedding_subtype_mono isClosed_closure hclosureSub
  rw [IsBorderedMorphism]
  change IsProperMap (fun p : ambientGraphClosure (f ≫ g) => p.1.1)
  have hfinal := hπ.comp hi.isProperMap
  simpa [π, i, Function.comp_def] using hfinal

/-- Hausdorff topological bordered spaces. This is the object class on which the proper closed-graph
morphisms form a category. -/
structure HausdorffBorderedSpace extends TopologicalBorderedSpace where
  /-- Hausdorff separation of the ambient space. -/
  ambient_t2 : T2Space ambient

namespace HausdorffBorderedSpace

instance (M : HausdorffBorderedSpace) : T2Space M.ambient := M.ambient_t2

/-- Morphism between Hausdorff bordered spaces, carrying exactly the proper closed-graph
condition. -/
@[ext]
structure BorderedHom (M N : HausdorffBorderedSpace) where
  /-- Continuous map on interiors. -/
  interiorMap : M.interior ⟶ N.interior
  /-- Properness of the closed ambient graph over the source ambient space. -/
  isBordered : IsBorderedMorphism interiorMap

/-- Category of Hausdorff topological bordered spaces and proper closed-graph morphisms. -/
instance : Category HausdorffBorderedSpace where
  Hom := BorderedHom
  id M :=
    { interiorMap := 𝟙 _
      isBordered := StrictHom.isBorderedMorphism (StrictHom.id M.toTopologicalBorderedSpace) }
  comp f g :=
    { interiorMap := f.interiorMap ≫ g.interiorMap
      isBordered := isBorderedMorphism_comp f.isBordered g.isBordered }
  id_comp f := by
    ext
    simp
  comp_id f := by
    ext
    simp
  assoc f g h := by
    ext
    simp

@[simp]
theorem id_interiorMap (M : HausdorffBorderedSpace) :
    (𝟙 M : M ⟶ M).interiorMap = 𝟙 M.interior := rfl

@[simp]
theorem comp_interiorMap {M N P : HausdorffBorderedSpace} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).interiorMap = f.interiorMap ≫ g.interiorMap := rfl

end HausdorffBorderedSpace

end TopologicalBorderedSpace
end IrregularStokes
end GaloisForLFunctions
