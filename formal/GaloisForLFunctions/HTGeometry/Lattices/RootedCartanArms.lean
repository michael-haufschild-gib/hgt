import GaloisForLFunctions.HTGeometry.Lattices.RootedCartanPath
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Removing the center of a finite Cartan tree

The components after removing a vertex of a tree are indexed by its
neighbors. When every other vertex has degree at most two, each such
component is a path starting at its unique neighbor of the center.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.CartanPath
variable {V : Type*} (G : SimpleGraph V) (r : V)

abbrev Off := {v : V // v≠r}

def punctured := G.induce {v | v≠r}

private def liftNeighbor (j : G.neighborSet r) : Off r := ⟨j.val,j.property.ne.symm⟩

def armComponent (j : G.neighborSet r) := (punctured G r).connectedComponentMk (liftNeighbor G r j)

/-- Two neighbors in one punctured component yield two paths from the
center to the second neighbor. Uniqueness forces the neighbors to agree. -/
private theorem arms_distinct (tree : G.IsAcyclic) : Function.Injective (armComponent G r) := by
  intro j k eq
  let u := liftNeighbor G r j
  let v := liftNeighbor G r k
  have reachable : (punctured G r).Reachable u v := SimpleGraph.ConnectedComponent.eq.mp eq
  obtain ⟨p,hp⟩ := reachable.exists_isPath
  let incl := (SimpleGraph.Embedding.induce (G:=G) {v | v≠r}).toHom
  let t := p.map incl
  have simple : t.IsPath := SimpleGraph.Walk.IsPath.map (f:=incl) Subtype.val_injective hp
  have omitRoot : r∉t.support := by
    rw [show t.support=p.support.map incl from SimpleGraph.Walk.support_map _ _]
    rintro hr
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hr
    exact a.property ha
  let lhs : G.Path r k.val := ⟨.cons j.property t,simple.cons omitRoot⟩
  let rhs : G.Path r k.val := ⟨.cons k.property .nil,by simp [SimpleGraph.Walk.cons_isPath_iff,k.property.ne]⟩
  exact Subtype.ext (by
    have eq := congrArg (fun w : G.Path r k.val => w.val.getVert 1) (tree.path_unique lhs rhs)
    simpa only [lhs,rhs,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero] using eq)

private theorem arms_cover (conn : G.Preconnected) : Function.Surjective (armComponent G r) := by
  classical
  let S : Set V := {v | ∀ h : v≠r, ∃ j, armComponent G r j=(punctured G r).connectedComponentMk ⟨v,h⟩}
  have hr : r∈S := fun h => (h rfl).elim
  have closed {x y : V} (hx : x∈S) (edge : G.Adj x y) : y∈S := by
    intro hy
    by_cases he : x=r
    · subst x
      exact ⟨⟨y,edge⟩,rfl⟩
    · obtain ⟨j,hj⟩ := hx he
      exact ⟨j,hj.trans (SimpleGraph.ConnectedComponent.sound
        (show (punctured G r).Adj ⟨x,he⟩ ⟨y,hy⟩ from edge).reachable)⟩
  have mem {x y : V} (p : G.Walk x y) : x∈S → y∈S := by
    induction p with
    | nil => exact id
    | cons e _ ih => exact fun h => ih (closed h e)
  intro c
  obtain ⟨v,rfl⟩ := c.exists_rep
  obtain ⟨w⟩ := conn r v.val
  exact mem w hr v.property

/-- The degree of any vertex in a tree counts the components formed by
deleting it. This holds also for the singleton tree. -/
def neighborComponentEquiv (tree : G.IsTree) : G.neighborSet r ≃ (punctured G r).ConnectedComponent :=
  Equiv.ofBijective (armComponent G r) ⟨arms_distinct G r tree.isAcyclic,arms_cover G r tree.connected.preconnected⟩

/-- Component cardinality as an exact consequence of the vertex bijection. -/
theorem punctured_count [Fintype V] [DecidableRel G.Adj] (tree : G.IsTree) :
    Nat.card (punctured G r).ConnectedComponent=G.degree r := by
  rw [← Nat.card_congr (neighborComponentEquiv G r tree),Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]

private def armStart (j : G.neighborSet r) : armComponent G r j :=
  ⟨liftNeighbor G r j,rfl⟩

open Classical in
/-- The degree bounds in a punctured component charge the edge leading to
the center separately at its neighbor. -/
private theorem arm_degree [Fintype V] [DecidableRel G.Adj] (j : G.neighborSet r) (x : armComponent G r j) :
    let H := (armComponent G r j).toSimpleGraph
    Nat.card (H.neighborSet x) + (if x=armStart G r j then 1 else 0) ≤ G.degree x.val.val := by
  classical
  let H := (armComponent G r j).toSimpleGraph
  let M := G.neighborFinset x.val.val
  let f (y : H.neighborSet x) : V := y.val.val.val
  have inj : Function.Injective f := fun a b h => Subtype.ext (Subtype.ext (Subtype.ext h))
  have mem (y : H.neighborSet x) : f y∈M := (G.mem_neighborFinset _ _).mpr y.property
  have ne (y : H.neighborSet x) : f y≠r := y.val.val.property
  let emb : H.neighborSet x ↪ V := ⟨f,inj⟩
  have incl : (univ.map emb) ⊆ M.erase r := by
    intro z hz
    obtain ⟨y,_,rfl⟩ := mem_map.mp hz
    exact mem_erase.mpr ⟨ne y,mem y⟩
  have le := card_le_card incl
  rw [card_map,card_univ,← Nat.card_eq_fintype_card] at le
  change Nat.card (H.neighborSet x) + _ ≤ M.card
  by_cases eq : x=armStart G r j
  · have hr : r∈M := (G.mem_neighborFinset _ _).mpr (by subst x; exact j.property.symm)
    rw [card_erase_of_mem hr] at le
    have pos : 0<M.card := card_pos.mpr ⟨r,hr⟩
    rw [if_pos eq]
    omega
  · rw [if_neg eq,add_zero]
    exact le.trans (card_le_card (erase_subset _ _))

/-- A finite tree with a unique possible branching vertex is a collection
of rooted paths, canonically distinguished by their first vertices. -/
theorem arm_numbering [Fintype V] [DecidableRel G.Adj] (bound : ∀ v, v≠r → G.degree v≤2)
    (j : G.neighborSet r) :
    let C := armComponent G r j
    ∃ n, ∃ e : Fin (n+1) ≃ C, (e 0).val.val=j.val ∧
      ∀ i k, C.toSimpleGraph.Adj (e i) (e k) ↔ i.val+1=k.val ∨ k.val+1=i.val := by
  classical
  let C := armComponent G r j
  let H := C.toSimpleGraph
  letI : Fintype C := Fintype.ofFinite _
  letI : DecidableRel H.Adj := Classical.decRel _
  have deg (x : C) : H.degree x+(if x=armStart G r j then 1 else 0)≤2 := by
    have q := (arm_degree G r j x).trans (bound _ x.val.property)
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using q
  have leaf : H.degree (armStart G r j)≤1 := by
    have h := deg (armStart G r j)
    rw [if_pos rfl] at h
    omega
  obtain ⟨n,e,h,edges⟩ := rooted_numbering H (armStart G r j) C.connected_toSimpleGraph.preconnected leaf
    (fun i => by have hh := deg i; omega)
  exact ⟨n,e,congrArg (fun x : C => x.val.val) h,edges⟩

abbrev Radial (J : Type*) (d : J → ℕ) := Option (Σ j, Fin (d j+1))

/-- A numbering of all arms identifies the full vertex set with a center
and a disjoint union of nonempty indexed paths. -/
def radialEquiv (tree : G.IsTree) (d : G.neighborSet r → ℕ)
    (e : ∀ j, Fin (d j+1) ≃ armComponent G r j) : Radial (G.neighborSet r) d ≃ V := by
  classical
  let f : Radial (G.neighborSet r) d → V
    | none => r
    | some ⟨j,i⟩ => (e j i).val.val
  apply Equiv.ofBijective f
  constructor
  · rintro (_|⟨j,i⟩) (_|⟨k,l⟩) he
    · rfl
    · exact ((e k l).val.property he.symm).elim
    · exact ((e j i).val.property he).elim
    · have h : (e j i).val=(e k l).val := Subtype.ext he
      have c : armComponent G r j=armComponent G r k :=
        (e j i).property.symm.trans ((congrArg (punctured G r).connectedComponentMk h).trans (e k l).property)
      obtain rfl := arms_distinct G r tree.isAcyclic c
      obtain rfl := (e j).injective (Subtype.ext h)
      rfl
  · intro v
    by_cases eq : v=r
    · exact ⟨none,eq.symm⟩
    · let u : Off r := ⟨v,eq⟩
      obtain ⟨j,h⟩ := arms_cover G r tree.connected.preconnected ((punctured G r).connectedComponentMk u)
      let z : armComponent G r j := ⟨u,h.symm⟩
      exact ⟨some ⟨j,(e j).symm z⟩,congrArg (fun a : armComponent G r j => a.val.val) ((e j).apply_symm_apply z)⟩

private theorem arm_at_center (tree : G.IsTree) (j : G.neighborSet r) (v : armComponent G r j) :
    G.Adj r v.val.val ↔ v=armStart G r j := by
  constructor
  · intro edge
    let k : G.neighborSet r := ⟨v.val.val,edge⟩
    have equal : armComponent G r k=armComponent G r j := v.property
    have hj : k=j := arms_distinct G r tree.isAcyclic equal
    exact Subtype.ext (Subtype.ext (congrArg (fun a : G.neighborSet r => a.val) hj))
  · rintro rfl
    exact j.property

private theorem different_arms {j k : G.neighborSet r} (tree : G.IsTree)
    (ne : j≠k) (x : armComponent G r j) (y : armComponent G r k) : ¬G.Adj x.val.val y.val.val := by
  intro he
  have h : (punctured G r).Adj x.val y.val := he
  exact ne (arms_distinct G r tree.isAcyclic
    (x.property.symm.trans ((SimpleGraph.ConnectedComponent.sound h.reachable).trans y.property)))

/-- Orient all arms toward the center. The first vertex has the center
as parent, and the center itself has no parent. -/
def radialParent {J : Type*} {d : J → ℕ} : Radial J d → Option (Radial J d)
  | none => none
  | some ⟨j,i⟩ => some (if h : i.val=0 then none else some ⟨j,⟨i.val-1,by omega⟩⟩)

private theorem parent_center {J : Type*} {d : J → ℕ} (j : J) (i : Fin (d j+1)) :
    radialParent (some ⟨j,i⟩ : Radial J d)=some none ↔ i=0 := by
  by_cases eq : i.val=0
  · have h : i=0 := Fin.ext eq
    subst i
    simp [radialParent]
  · have ne : i≠0 := fun h => eq (congrArg Fin.val h)
    simp [radialParent,eq,ne]

private theorem parent_arm {J : Type*} {d : J → ℕ} (j : J) (i l : Fin (d j+1)) :
    radialParent (some ⟨j,i⟩ : Radial J d)=some (some ⟨j,l⟩) ↔ l.val+1=i.val := by
  by_cases eq : i.val=0
  · simp [radialParent,eq]
  · simp only [radialParent,dif_neg eq,Option.some.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and,Fin.ext_iff]
    omega

private theorem parent_other {J : Type*} {d : J → ℕ} {j k : J} (ne : j≠k) (i : Fin (d j+1)) (l : Fin (d k+1)) :
    radialParent (some ⟨j,i⟩ : Radial J d)≠some (some ⟨k,l⟩) := by
  intro h
  by_cases zero : i.val=0
  · simp [radialParent,zero] at h
  · simp only [radialParent,dif_neg zero,Option.some.injEq] at h
    exact ne (congrArg Sigma.fst h)

theorem radial_asymm {J : Type*} {d : J → ℕ} (x y : Radial J d) :
    radialParent x=some y → radialParent y≠some x := by
  rintro h g
  rcases x with _|⟨j,i⟩ <;> rcases y with _|⟨k,l⟩
  · cases h
  · cases h
  · cases g
  · by_cases eq : j=k
    · subst k
      have a := (parent_arm j i l).mp h
      have b := (parent_arm j l i).mp g
      omega
    · exact parent_other eq i l h

/-- The radial chart describes every edge in either orientation. -/
theorem radial_edges (tree : G.IsTree) (d : G.neighborSet r → ℕ)
    (e : ∀ j, Fin (d j+1) ≃ armComponent G r j)
    (start : ∀ j, (e j 0).val.val=j.val)
    (path : ∀ j i k, (armComponent G r j).toSimpleGraph.Adj (e j i) (e j k) ↔
      i.val+1=k.val ∨ k.val+1=i.val) (x y : Radial (G.neighborSet r) d) :
    G.Adj (radialEquiv G r tree d e x) (radialEquiv G r tree d e y) ↔
      radialParent x=some y ∨ radialParent y=some x := by
  have leaf (j : G.neighborSet r) (i : Fin (d j+1)) :
      G.Adj r (e j i).val.val ↔ i=0 := by
    have he : e j 0=armStart G r j := Subtype.ext (Subtype.ext (start j))
    rw [arm_at_center G r tree,← he]
    exact (e j).injective.eq_iff
  rcases x with _|⟨j,i⟩ <;> rcases y with _|⟨k,l⟩
  · change G.Adj r r ↔ _
    simp [radialParent]
  · change G.Adj r (e k l).val.val ↔ _
    rw [leaf,or_iff_right (by intro e; cases e),parent_center]
  · change G.Adj (e j i).val.val r ↔ _
    rw [G.adj_comm,leaf,or_iff_left (by intro e; cases e),parent_center]
  · by_cases eq : j=k
    · subst k
      change (armComponent G r j).toSimpleGraph.Adj (e j i) (e j l) ↔ _
      rw [path,parent_arm,parent_arm,or_comm]
    · change G.Adj (e j i).val.val (e k l).val.val ↔ _
      simp only [different_arms G r tree eq, parent_other eq, parent_other (Ne.symm eq),or_self]

#print axioms radialEquiv
#print axioms radial_edges
#print axioms neighborComponentEquiv
#print axioms punctured_count
#print axioms arm_numbering
end GaloisForLFunctions.HTGeometry.CartanPath
