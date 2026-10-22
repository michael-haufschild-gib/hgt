import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutLength

/-!
# The tree of cosets of an amalgamated free product

A pushout of groups `G = *_H G_i` acts on a graph whose vertices are the cosets of the base group
together with the cosets of each factor, and whose edges are indexed by a factor together with a
coset of the base group: the edge `(i, gC)` joins `gC` to `gA_i`.  This graph is the Bass-Serre
tree of the pushout, and its augmented chain complex

  `k[E] → k[V] → k`

is the source of the Mayer-Vietoris sequence for group homology.

This file constructs the complex, proves it equivariant, and proves it exact at `k` and at `k[V]`
(the graph is connected).

* `deningerTreeBoundary`, `deningerTreeAug` : the two maps.
* `deningerTreeAug_surjective`, `deningerTreeAug_comp_boundary` : the complex.
* `deningerTree_connected` : the kernel of the augmentation is the image of the boundary.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  (φ : ∀ i, H →* G i)

/-- The vertices of the tree of cosets: the cosets of the base group and, for each factor, the
cosets of that factor. -/
inductive DeningerTreeVertex (φ : ∀ i, H →* G i) : Type u
  | ofBase : PushoutI φ ⧸ (PushoutI.base φ).range → DeningerTreeVertex φ
  | ofSummand (i : ι) : PushoutI φ ⧸ (PushoutI.of (φ := φ) i).range → DeningerTreeVertex φ

/-- The edges of the tree of cosets: a factor together with a coset of the base group. -/
@[ext]
structure DeningerTreeEdge (φ : ∀ i, H →* G i) : Type u where
  /-- The factor the edge points to. -/
  idx : ι
  /-- The coset of the base group the edge starts at. -/
  coset : PushoutI φ ⧸ (PushoutI.base φ).range

variable {φ}

namespace DeningerTreeVertex

instance : SMul (PushoutI φ) (DeningerTreeVertex φ) where
  smul g v :=
    match v with
    | ofBase x => ofBase (g • x)
    | ofSummand i x => ofSummand i (g • x)

@[simp] theorem smul_ofBase (g : PushoutI φ) (x : PushoutI φ ⧸ (PushoutI.base φ).range) :
    g • ofBase x = ofBase (g • x) := rfl

@[simp] theorem smul_ofSummand (g : PushoutI φ) (i : ι)
    (x : PushoutI φ ⧸ (PushoutI.of (φ := φ) i).range) :
    g • ofSummand i x = ofSummand i (g • x) := rfl

instance : MulAction (PushoutI φ) (DeningerTreeVertex φ) where
  one_smul v := by cases v <;> simp
  mul_smul g₁ g₂ v := by cases v <;> simp [mul_smul]

end DeningerTreeVertex

namespace DeningerTreeEdge

instance : SMul (PushoutI φ) (DeningerTreeEdge φ) where
  smul g e := ⟨e.idx, g • e.coset⟩

@[simp] theorem smul_idx (g : PushoutI φ) (e : DeningerTreeEdge φ) : (g • e).idx = e.idx := rfl

@[simp] theorem smul_coset (g : PushoutI φ) (e : DeningerTreeEdge φ) :
    (g • e).coset = g • e.coset := rfl

instance : MulAction (PushoutI φ) (DeningerTreeEdge φ) where
  one_smul e := by ext <;> simp
  mul_smul g₁ g₂ e := by ext <;> simp [mul_smul]

end DeningerTreeEdge

section Complex

variable (φ) in
theorem deningerBaseRange_le (i : ι) :
    (PushoutI.base φ).range ≤ (PushoutI.of (φ := φ) i).range := by
  rintro _ ⟨h, rfl⟩
  exact ⟨φ i h, PushoutI.of_apply_eq_base φ i h⟩

/-- A coset of the base group determines a coset of any factor. -/
def deningerEdgeHead (i : ι) :
    PushoutI φ ⧸ (PushoutI.base φ).range → PushoutI φ ⧸ (PushoutI.of (φ := φ) i).range :=
  Quotient.map' id (fun _ _ hab =>
    QuotientGroup.leftRel_apply.2 (deningerBaseRange_le φ i (QuotientGroup.leftRel_apply.1 hab)))

@[simp] theorem deningerEdgeHead_mk (i : ι) (g : PushoutI φ) :
    deningerEdgeHead i (QuotientGroup.mk g) = (QuotientGroup.mk g : _ ⧸ _) := rfl

variable (k : Type u) [CommRing k]

/-- The boundary map of the tree of cosets: the edge `(i, gC)` runs from `gC` to `gA_i`. -/
noncomputable def deningerTreeBoundary :
    MonoidAlgebra k (DeningerTreeEdge φ) →ₗ[k] MonoidAlgebra k (DeningerTreeVertex φ) :=
  Finsupp.lift (MonoidAlgebra k (DeningerTreeVertex φ)) k (DeningerTreeEdge φ) (fun e =>
      MonoidAlgebra.single
        (DeningerTreeVertex.ofSummand e.idx (deningerEdgeHead e.idx e.coset)) (1 : k) -
      MonoidAlgebra.single (DeningerTreeVertex.ofBase e.coset) (1 : k)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

/-- The augmentation of the tree of cosets. -/
noncomputable def deningerTreeAug :
    MonoidAlgebra k (DeningerTreeVertex φ) →ₗ[k] k :=
  Finsupp.lift k k (DeningerTreeVertex φ) (fun _ => (1 : k)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem deningerTreeBoundary_single (e : DeningerTreeEdge φ) (c : k) :
    deningerTreeBoundary k (MonoidAlgebra.single e c) =
      c • (MonoidAlgebra.single
          (DeningerTreeVertex.ofSummand e.idx (deningerEdgeHead e.idx e.coset)) (1 : k) -
        MonoidAlgebra.single (DeningerTreeVertex.ofBase e.coset) (1 : k)) := by
  show Finsupp.lift (MonoidAlgebra k (DeningerTreeVertex φ)) k (DeningerTreeEdge φ) _
    (Finsupp.single e c) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]

theorem deningerTreeAug_single (v : DeningerTreeVertex φ) (c : k) :
    deningerTreeAug k (MonoidAlgebra.single v c) = c := by
  show Finsupp.lift k k (DeningerTreeVertex φ) _ (Finsupp.single v c) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp

theorem deningerTreeAug_surjective : Function.Surjective (deningerTreeAug (φ := φ) k) :=
  fun c => ⟨MonoidAlgebra.single (DeningerTreeVertex.ofBase (QuotientGroup.mk 1)) c,
    deningerTreeAug_single k _ c⟩

theorem deningerTreeAug_comp_boundary :
    deningerTreeAug (φ := φ) k ∘ₗ deningerTreeBoundary k = 0 := by
  refine MonoidAlgebra.lhom_ext' fun e => LinearMap.ext_ring ?_
  show deningerTreeAug k (deningerTreeBoundary k (MonoidAlgebra.single e (1:k))) = 0
  rw [deningerTreeBoundary_single, map_smul, map_sub, deningerTreeAug_single,
    deningerTreeAug_single]
  simp

end Complex

section Connected

variable (k : Type u) [CommRing k]

/-- Every coset of the base group is connected to the base coset itself: the difference of their
classes is a boundary.  The induction is over the generators of the pushout, and the step is that
`gC` and `g·of i x·C` are both endpoints of edges into the same vertex `gA_i`. -/
theorem deningerTree_ofBase_sub_root (g : PushoutI φ) :
    MonoidAlgebra.single
        (DeningerTreeVertex.ofBase (QuotientGroup.mk g : PushoutI φ ⧸ _)) (1 : k) -
      MonoidAlgebra.single
        (DeningerTreeVertex.ofBase (QuotientGroup.mk 1 : PushoutI φ ⧸ _)) (1 : k) ∈
      LinearMap.range (deningerTreeBoundary (φ := φ) k) := by
  have key : ∀ x y : PushoutI φ,
      MonoidAlgebra.single
          (DeningerTreeVertex.ofBase (QuotientGroup.mk (y * x) : PushoutI φ ⧸ _)) (1 : k) -
        MonoidAlgebra.single
          (DeningerTreeVertex.ofBase (QuotientGroup.mk y : PushoutI φ ⧸ _)) (1 : k) ∈
        LinearMap.range (deningerTreeBoundary (φ := φ) k) := by
    intro x
    induction x using PushoutI.induction_on with
    | of i g =>
      intro y
      have heq : (QuotientGroup.mk (y * PushoutI.of i g) :
          PushoutI φ ⧸ (PushoutI.of (φ := φ) i).range) = QuotientGroup.mk y := by
        rw [QuotientGroup.eq]
        simp
      refine ⟨MonoidAlgebra.single (⟨i, QuotientGroup.mk y⟩ : DeningerTreeEdge φ) (1 : k) -
        MonoidAlgebra.single
          (⟨i, QuotientGroup.mk (y * PushoutI.of i g)⟩ : DeningerTreeEdge φ) (1 : k), ?_⟩
      rw [map_sub, deningerTreeBoundary_single, deningerTreeBoundary_single]
      simp only [one_smul, deningerEdgeHead_mk, heq]
      abel
    | base h =>
      intro y
      have heq : (QuotientGroup.mk (y * PushoutI.base φ h) :
          PushoutI φ ⧸ (PushoutI.base φ).range) = QuotientGroup.mk y := by
        rw [QuotientGroup.eq]
        simp
      rw [heq, sub_self]
      exact Submodule.zero_mem _
    | mul x₁ x₂ ih₁ ih₂ =>
      intro y
      have hsum := Submodule.add_mem _ (ih₂ (y * x₁)) (ih₁ y)
      rw [show y * (x₁ * x₂) = y * x₁ * x₂ from (mul_assoc _ _ _).symm]
      convert hsum using 1
      abel
  simpa using key g 1

/-- Every vertex of the tree of cosets is connected to the base coset. -/
theorem deningerTree_vertex_sub_root (v : DeningerTreeVertex φ) :
    MonoidAlgebra.single v (1 : k) -
      MonoidAlgebra.single
        (DeningerTreeVertex.ofBase (QuotientGroup.mk 1 : PushoutI φ ⧸ _)) (1 : k) ∈
      LinearMap.range (deningerTreeBoundary (φ := φ) k) := by
  cases v with
  | ofBase x =>
    induction x using QuotientGroup.induction_on with
    | _ g => exact deningerTree_ofBase_sub_root k g
  | ofSummand i x =>
    induction x using QuotientGroup.induction_on with
    | _ g =>
      have hedge : MonoidAlgebra.single
            (DeningerTreeVertex.ofSummand i (QuotientGroup.mk g : PushoutI φ ⧸ _)) (1 : k) -
          MonoidAlgebra.single
            (DeningerTreeVertex.ofBase (QuotientGroup.mk g : PushoutI φ ⧸ _)) (1 : k) ∈
          LinearMap.range (deningerTreeBoundary (φ := φ) k) := by
        refine ⟨MonoidAlgebra.single (⟨i, QuotientGroup.mk g⟩ : DeningerTreeEdge φ) (1 : k), ?_⟩
        rw [deningerTreeBoundary_single]
        simp
      have := Submodule.add_mem _ hedge (deningerTree_ofBase_sub_root k g)
      convert this using 1
      abel

/-- **The tree of cosets is connected**: the kernel of the augmentation is the image of the
boundary. -/
theorem deningerTree_connected (f : MonoidAlgebra k (DeningerTreeVertex φ))
    (hf : deningerTreeAug k f = 0) :
    f ∈ LinearMap.range (deningerTreeBoundary (φ := φ) k) := by
  have general : ∀ f : MonoidAlgebra k (DeningerTreeVertex φ),
      f - deningerTreeAug k f • MonoidAlgebra.single
          (DeningerTreeVertex.ofBase (QuotientGroup.mk 1 : PushoutI φ ⧸ _)) (1 : k) ∈
        LinearMap.range (deningerTreeBoundary (φ := φ) k) := by
    intro f
    obtain ⟨f', rfl⟩ := (MonoidAlgebra.coeffLinearEquiv k).symm.surjective f
    refine Finsupp.induction_linear f' ?_ ?_ ?_
    · simp
    · intro a b ha hb
      rw [map_add, map_add, add_smul]
      have := Submodule.add_mem _ ha hb
      convert this using 1
      abel
    · intro v c
      rw [show (MonoidAlgebra.coeffLinearEquiv k).symm (Finsupp.single v c) =
        MonoidAlgebra.single v c from rfl, deningerTreeAug_single]
      have := Submodule.smul_mem _ c (deningerTree_vertex_sub_root k v)
      convert this using 1
      simp [smul_sub, MonoidAlgebra.smul_single]
  have := general f
  rwa [hf, zero_smul, sub_zero] at this

end Connected

section Equivariance

variable (k : Type u) [CommRing k]

theorem deningerEdgeHead_smul (i : ι) (g : PushoutI φ)
    (x : PushoutI φ ⧸ (PushoutI.base φ).range) :
    deningerEdgeHead i (g • x) = g • deningerEdgeHead i x := by
  induction x using QuotientGroup.induction_on with
  | _ y => rfl

theorem deningerTreeBoundary_comm (g : PushoutI φ) :
    deningerTreeBoundary (φ := φ) k ∘ₗ
        Representation.ofMulAction k (PushoutI φ) (DeningerTreeEdge φ) g =
      Representation.ofMulAction k (PushoutI φ) (DeningerTreeVertex φ) g ∘ₗ
        deningerTreeBoundary k := by
  refine MonoidAlgebra.lhom_ext' fun e => LinearMap.ext_ring ?_
  show deningerTreeBoundary k
      (Representation.ofMulAction k _ _ g (MonoidAlgebra.single e (1 : k))) =
    Representation.ofMulAction k _ _ g (deningerTreeBoundary k (MonoidAlgebra.single e (1 : k)))
  rw [Representation.ofMulAction_single, deningerTreeBoundary_single,
    deningerTreeBoundary_single, one_smul, one_smul, map_sub,
    Representation.ofMulAction_single, Representation.ofMulAction_single]
  simp [deningerEdgeHead_smul]

theorem deningerTreeAug_comm (g : PushoutI φ) :
    deningerTreeAug (φ := φ) k ∘ₗ
        Representation.ofMulAction k (PushoutI φ) (DeningerTreeVertex φ) g =
      (Rep.trivial k (PushoutI φ) k).ρ g ∘ₗ deningerTreeAug k := by
  refine MonoidAlgebra.lhom_ext' fun v => LinearMap.ext_ring ?_
  show deningerTreeAug k (Representation.ofMulAction k _ _ g (MonoidAlgebra.single v (1 : k))) = _
  rw [Representation.ofMulAction_single, deningerTreeAug_single]
  show (1 : k) = (Rep.trivial k (PushoutI φ) k).ρ g (deningerTreeAug k
    (MonoidAlgebra.single v (1 : k)))
  rw [deningerTreeAug_single]
  rfl

variable (φ) in
/-- The permutation representation on the edges of the tree of cosets. -/
noncomputable abbrev deningerTreeEdgeRep : Rep k (PushoutI φ) :=
  Rep.ofMulAction k (PushoutI φ) (DeningerTreeEdge φ)

variable (φ) in
/-- The permutation representation on the vertices of the tree of cosets. -/
noncomputable abbrev deningerTreeVertexRep : Rep k (PushoutI φ) :=
  Rep.ofMulAction k (PushoutI φ) (DeningerTreeVertex φ)

/-- The boundary map as a morphism of representations. -/
noncomputable def deningerTreeBoundaryHom :
    deningerTreeEdgeRep φ k ⟶ deningerTreeVertexRep φ k :=
  Rep.ofHom ⟨deningerTreeBoundary k, deningerTreeBoundary_comm k⟩

/-- The augmentation as a morphism of representations. -/
noncomputable def deningerTreeAugHom :
    deningerTreeVertexRep φ k ⟶ Rep.trivial k (PushoutI φ) k :=
  Rep.ofHom ⟨deningerTreeAug k, deningerTreeAug_comm k⟩

end Equivariance

end RHTower
