import GaloisForLFunctions.HTGeometry.FamilyCoverBaseComponents

/-!
# Components of order complexes and of disjoint unions

Three computations of `π₀`, all of them needed to turn the Mayer--Vietoris kernel into an explicit
coproduct: a full subcomplex with a cone point is connected; a full subcomplex spanned by an
antichain has one component per vertex, because an edge of a nerve is a comparability; and a
disjoint union over a one-element index is as connected as its single member.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

/-! ## Edges of a nerve are comparabilities -/

section Nerve

variable {P : Type u} [PartialOrder P]

/-- **An edge of a full subcomplex of a nerve joins comparable vertices.** -/
theorem nerveSubcomplex_edge_le {Q : Set P}
    {x₀ x₁ : ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) _⦋0⦌} (e : SSet.Edge x₀ x₁) :
    ((x₀ : (nerve P) _⦋0⦌)).obj 0 ≤ ((x₁ : (nerve P) _⦋0⦌)).obj 0 := by
  have h0 : (e.edge.1).obj 0 = (x₀.1).obj 0 :=
    congrArg (fun z : ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) _⦋0⦌ => (z.1).obj 0)
      e.src_eq
  have h1 : (e.edge.1).obj 1 = (x₁.1).obj 0 :=
    congrArg (fun z : ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) _⦋0⦌ => (z.1).obj 0)
      e.tgt_eq
  rw [← h0, ← h1]
  exact leOfHom ((e.edge.1).map' 0 1)

/-- **A full subcomplex spanned by an antichain has one component for each vertex.** -/
noncomputable def nerveSubcomplexAntichainPi0 {Q : Set P} (hanti : ∀ x ∈ Q, ∀ y ∈ Q, x ≤ y → x = y) :
    SSet.π₀ ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) → Q :=
  SSet.π₀.lift (fun x => ⟨((x.1)).obj 0, x.2 0⟩)
    fun x₀ x₁ e => Subtype.ext (hanti _ (x₀.2 0) _ (x₁.2 0) (nerveSubcomplex_edge_le e))

@[simp] theorem nerveSubcomplexAntichainPi0_mk {Q : Set P}
    (hanti : ∀ x ∈ Q, ∀ y ∈ Q, x ≤ y → x = y)
    (x : ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) _⦋0⦌) :
    nerveSubcomplexAntichainPi0 hanti (SSet.π₀.mk x) = ⟨((x.1)).obj 0, x.2 0⟩ := rfl

/-- **The components of a full subcomplex spanned by an antichain are its vertices.** -/
noncomputable def nerveSubcomplexAntichainPi0Equiv {Q : Set P} (hanti : ∀ x ∈ Q, ∀ y ∈ Q, x ≤ y → x = y) :
    SSet.π₀ ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) ≃ Q where
  toFun := nerveSubcomplexAntichainPi0 hanti
  invFun q := SSet.π₀.mk (nerveSubcomplexVertex (q : P) q.2)
  left_inv z := by
    obtain ⟨x, rfl⟩ := z.mk_surjective
    exact congrArg SSet.π₀.mk (nerveSubcomplexVertex_eq x).symm
  right_inv q := Subtype.ext rfl

/-- Distinct elements of an antichain give distinct components. -/
theorem pi0_nerveSubcomplexVertex_ne {Q : Set P} (hanti : ∀ x ∈ Q, ∀ y ∈ Q, x ≤ y → x = y)
    {a b : P} (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b) :
    SSet.π₀.mk (nerveSubcomplexVertex a ha) ≠ SSet.π₀.mk (nerveSubcomplexVertex b hb) := by
  intro hcon
  exact hab (congrArg Subtype.val (congrArg (nerveSubcomplexAntichainPi0 hanti) hcon))

/-- **A full subcomplex whose subset has a cone point is connected.** -/
theorem isPreconnected_nerveSubcomplex_of_cone {Q : Set P} {v : P} (hv : v ∈ Q)
    (hcone : ∀ q ∈ Q, q ≤ v ∨ v ≤ q) :
    SSet.IsPreconnected ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) := by
  refine ⟨fun z z' => ?_⟩
  obtain ⟨y, rfl⟩ := z.mk_surjective
  obtain ⟨y', rfl⟩ := z'.mk_surjective
  have key : ∀ x : ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) _⦋0⦌,
      SSet.π₀.mk x = SSet.π₀.mk (nerveSubcomplexVertex v hv) := by
    intro x
    rw [nerveSubcomplexVertex_eq x]
    rcases hcone _ (x.2 0) with h | h
    · exact pi0_nerveSubcomplexVertex_eq_of_le (x.2 0) hv h
    · exact (pi0_nerveSubcomplexVertex_eq_of_le hv (x.2 0) h).symm
  rw [key y, key y']

end Nerve

/-! ## Arbitrary subcomplexes of a nerve -/

section Subcomplex

variable {P : Type u} [PartialOrder P] {A : (nerve P).Subcomplex}

/-- **An edge of a subcomplex of a nerve joins comparable vertices.** -/
theorem nerveSub_edge_le {x₀ x₁ : (A : SSet.{u}) _⦋0⦌} (e : SSet.Edge x₀ x₁) :
    (x₀.1).obj 0 ≤ (x₁.1).obj 0 := by
  have h0 : (e.edge.1).obj 0 = (x₀.1).obj 0 :=
    congrArg (fun z : (A : SSet.{u}) _⦋0⦌ => (z.1).obj 0) e.src_eq
  have h1 : (e.edge.1).obj 1 = (x₁.1).obj 0 :=
    congrArg (fun z : (A : SSet.{u}) _⦋0⦌ => (z.1).obj 0) e.tgt_eq
  rw [← h0, ← h1]
  exact leOfHom ((e.edge.1).map' 0 1)

/-- A vertex of a subcomplex of a nerve is the vertex attached to its own element. -/
theorem nerveSub_vertex_eq (y : (A : SSet.{u}) _⦋0⦌)
    (h : ComposableArrows.mk₀ ((y.1).obj 0) ∈ A.obj (op ⦋0⦌)) :
    y = ⟨ComposableArrows.mk₀ ((y.1).obj 0), h⟩ :=
  Subtype.ext (ComposableArrows.ext₀ rfl)

/-- **The element of a component of a subcomplex spanned by an antichain.** -/
noncomputable def nerveSubAntichainPi0
    (hanti : ∀ x₀ x₁ : (A : SSet.{u}) _⦋0⦌, (x₀.1).obj 0 ≤ (x₁.1).obj 0 →
      (x₀.1).obj 0 = (x₁.1).obj 0) :
    SSet.π₀ (A : SSet.{u}) → P :=
  SSet.π₀.lift (fun x => (x.1).obj 0) fun x₀ x₁ e => hanti x₀ x₁ (nerveSub_edge_le e)

@[simp] theorem nerveSubAntichainPi0_mk
    (hanti : ∀ x₀ x₁ : (A : SSet.{u}) _⦋0⦌, (x₀.1).obj 0 ≤ (x₁.1).obj 0 →
      (x₀.1).obj 0 = (x₁.1).obj 0) (x : (A : SSet.{u}) _⦋0⦌) :
    nerveSubAntichainPi0 hanti (SSet.π₀.mk x) = (x.1).obj 0 := rfl

end Subcomplex

/-! ## Components of a disjoint union -/

section Family

variable {X : SSet.{w}} {ι : Type w} (A : ι → X.Subcomplex)

/-- The inclusion of one member of a family into the disjoint union. -/
def famSSetIncl (c : ι) : (A c : SSet.{w}) ⟶ famSSet A where
  app _ := ↾fun x => ⟨c, x⟩
  naturality _ _ _ := rfl

@[simp] theorem mapπ₀_famSSetIncl (c : ι) (y : (A c : SSet.{w}) _⦋0⦌) :
    SSet.mapπ₀ (famSSetIncl A c) (SSet.π₀.mk y) = SSet.π₀.mk (⟨c, y⟩ : (famSSet A) _⦋0⦌) := rfl

/-- The two ends of an edge of a disjoint union lie in the same component of the same member. -/
theorem famSSet_edge_pi0 {x₀ x₁ : (famSSet A) _⦋0⦌} (e : SSet.Edge x₀ x₁) :
    (⟨x₀.1, SSet.π₀.mk x₀.2⟩ : Σ c, SSet.π₀ (A c : SSet.{w}))
      = ⟨x₁.1, SSet.π₀.mk x₁.2⟩ := by
  have h0 : (⟨e.edge.1, (A e.edge.1 : SSet.{w}).δ 1 e.edge.2⟩ : (famSSet A) _⦋0⦌) = x₀ := e.src_eq
  have h1 : (⟨e.edge.1, (A e.edge.1 : SSet.{w}).δ 0 e.edge.2⟩ : (famSSet A) _⦋0⦌) = x₁ := e.tgt_eq
  refine (congrArg (fun v : (famSSet A) _⦋0⦌ =>
    (⟨v.1, SSet.π₀.mk v.2⟩ : Σ c, SSet.π₀ (A c : SSet.{w}))) h0).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun v : (famSSet A) _⦋0⦌ =>
    (⟨v.1, SSet.π₀.mk v.2⟩ : Σ c, SSet.π₀ (A c : SSet.{w}))) h1)
  exact congrArg (Sigma.mk e.edge.1) (SSet.π₀.sound ⟨e.edge.2, rfl, rfl⟩)

/-- **The components of a disjoint union are the disjoint union of the components.** -/
noncomputable def famSSetPi0 : SSet.π₀ (famSSet A) → Σ c, SSet.π₀ (A c : SSet.{w}) :=
  SSet.π₀.lift (fun v => ⟨v.1, SSet.π₀.mk v.2⟩) fun _ _ e => famSSet_edge_pi0 A e

@[simp] theorem famSSetPi0_mk (v : (famSSet A) _⦋0⦌) :
    famSSetPi0 A (SSet.π₀.mk v) = ⟨v.1, SSet.π₀.mk v.2⟩ := rfl

/-- **The components of a disjoint union, as an equivalence.** -/
noncomputable def famSSetPi0Equiv : SSet.π₀ (famSSet A) ≃ Σ c, SSet.π₀ (A c : SSet.{w}) where
  toFun := famSSetPi0 A
  invFun q := SSet.mapπ₀ (famSSetIncl A q.1) q.2
  left_inv z := by
    obtain ⟨v, rfl⟩ := z.mk_surjective
    rfl
  right_inv q := by
    obtain ⟨c, z⟩ := q
    obtain ⟨y, rfl⟩ := z.mk_surjective
    rfl

/-- **A disjoint union over a one-element index is as connected as its single member.** -/
theorem isPreconnected_famSSet_of_subsingleton [Subsingleton ι]
    (hconn : ∀ c, SSet.IsPreconnected (A c : SSet.{w})) : SSet.IsPreconnected (famSSet A) := by
  refine ⟨fun z z' => ?_⟩
  obtain ⟨y, rfl⟩ := z.mk_surjective
  obtain ⟨y', rfl⟩ := z'.mk_surjective
  obtain ⟨c, y⟩ := y
  obtain ⟨c', y'⟩ := y'
  obtain rfl : c = c' := Subsingleton.elim c c'
  haveI := hconn c
  rw [← mapπ₀_famSSetIncl A c y, ← mapπ₀_famSSetIncl A c y',
    Subsingleton.elim (SSet.π₀.mk y) (SSet.π₀.mk y')]

end Family

end GaloisForLFunctions.HTGeometry
