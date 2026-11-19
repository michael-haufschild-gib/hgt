import GaloisForLFunctions.HTGeometry.Lattices.IntegralCartanSupport
import GaloisForLFunctions.HTGeometry.Lattices.IntegralRootParityFibers

/-!
# Orthogonal component decomposition of an integral unit shell

Each root lies in exactly one connected component of the simple-root
graph. Extension by zero in the simple coordinates gives an equivalence
with the disjoint union of the unit shells of the component forms.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {J : Type*} [Fintype J] (Q : Form J) (hQ : Q.PosDef)

abbrev Component := (cartanGraph Q hQ).ConnectedComponent
abbrev Part (c : Component Q hQ) := {i : Vertex Q hQ // (cartanGraph Q hQ).connectedComponentMk i=c}

private def synthesis : (Vertex Q hQ → ℤ) →ₗ[ℤ] Lattice J where
  toFun := synth Q hQ
  map_add' := synth_add Q hQ
  map_smul' r a := by simp only [synth,Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]

private def extend (c : Component Q hQ) : (Part Q hQ c → ℤ) →ₗ[ℤ] (Vertex Q hQ → ℤ) := by
  classical
  let f := fun (a : Part Q hQ c → ℤ) (i : Vertex Q hQ) =>
    if h : (cartanGraph Q hQ).connectedComponentMk i=c then a ⟨i,h⟩ else 0
  exact { toFun := f
          map_add' := fun a b => funext fun i => by by_cases hi : (cartanGraph Q hQ).connectedComponentMk i=c <;> simp [f,hi]
          map_smul' := fun r a => funext fun i => by by_cases hi : (cartanGraph Q hQ).connectedComponentMk i=c <;> simp [f,hi] }

private theorem inside (c : Component Q hQ) (a : Part Q hQ c → ℤ) (i : Part Q hQ c) :
    extend Q hQ c a i.val=a i := by simp [extend,i.property]

private theorem outside (c : Component Q hQ) (a : Part Q hQ c → ℤ) (i : Vertex Q hQ)
    (hi : (cartanGraph Q hQ).connectedComponentMk i≠c) : extend Q hQ c a i=0 := by simp [extend,hi]

private theorem extend_injective (c : Component Q hQ) : Function.Injective (extend Q hQ c) := by
  intro a b he
  funext i
  simpa only [inside] using congrFun he i.val

/-- Restricting the original integral quadratic form to one simple component. -/
def componentForm (c : Component Q hQ) : Form (Part Q hQ c) :=
  Q.comp ((synthesis Q hQ).comp (extend Q hQ c))

theorem componentForm_posDef (c : Component Q hQ) : (componentForm Q hQ c).PosDef := by
  intro a ha
  apply hQ
  intro hz
  have e : synth Q hQ (extend Q hQ c a)=synth Q hQ 0 := hz.trans (by simp [synth])
  apply ha
  exact extend_injective Q hQ c ((synth_injective Q hQ e).trans (map_zero _).symm)

private theorem same_part (x : Root Q) {i j : Vertex Q hQ} (hi : rootCoordinates Q hQ x i≠0)
    (hj : rootCoordinates Q hQ x j≠0) :
    (cartanGraph Q hQ).connectedComponentMk i=(cartanGraph Q hQ).connectedComponentMk j := by
  let S : Set (Vertex Q hQ) := {v | rootCoordinates Q hQ x v≠0}
  let f := (SimpleGraph.Embedding.induce (G:=cartanGraph Q hQ) S).toHom
  have h := (root_support_connected Q hQ x).preconnected (⟨i,hi⟩ : S) (⟨j,hj⟩ : S)
  exact SimpleGraph.ConnectedComponent.eq.mpr (h.map f)

private def assemble (p : Σ c : Component Q hQ, Root (componentForm Q hQ c)) : Root Q :=
  ⟨synth Q hQ (extend Q hQ p.1 p.2.val),p.2.property⟩

/-- The exact decomposition holds even when the root span is a proper
sublattice of the ambient lattice. -/
def componentRootEquiv : (Σ c : Component Q hQ, Root (componentForm Q hQ c)) ≃ Root Q := by
  classical
  apply Equiv.ofBijective (assemble Q hQ)
  constructor
  · rintro ⟨c,x⟩ ⟨d,y⟩ he
    have e : extend Q hQ c x.val=extend Q hQ d y.val := synth_injective Q hQ (congrArg Subtype.val he)
    have nx : x.val≠0 := fun hz => (zero_ne_one : (0:ℤ)≠1) (by simpa [hz] using x.property)
    obtain ⟨i,hi⟩ := Function.ne_iff.mp nx
    have cd : c=d := by
      by_contra h
      have hd : (cartanGraph Q hQ).connectedComponentMk i.val≠d := fun v => h (i.property.symm.trans v)
      exact hi ((inside Q hQ c x.val i).symm.trans ((congrFun e i.val).trans (outside Q hQ d y.val _ hd)))
    subst d
    exact congrArg (Sigma.mk c) (Subtype.ext (extend_injective Q hQ c e))
  · intro x
    obtain ⟨i,hi⟩ := Function.ne_iff.mp (coordinates_nonzero Q hQ x)
    let c := (cartanGraph Q hQ).connectedComponentMk i
    let a := fun j : Part Q hQ c => rootCoordinates Q hQ x j.val
    have e : extend Q hQ c a=rootCoordinates Q hQ x := by
      funext j
      by_cases h : (cartanGraph Q hQ).connectedComponentMk j=c
      · exact inside Q hQ c a ⟨j,h⟩
      · rw [outside Q hQ c a j h]
        by_contra ne
        exact h (same_part Q hQ x (Ne.symm ne) hi)
    have unit : componentForm Q hQ c a=1 := by
      change Q (synth Q hQ (extend Q hQ c a))=1
      rw [e,synth_rootCoordinates,x.property]
    exact ⟨⟨c,a,unit⟩,Subtype.ext ((congrArg (synth Q hQ) e).trans (synth_rootCoordinates Q hQ x))⟩

noncomputable local instance : Fintype (Component Q hQ) := Fintype.ofFinite _
noncomputable local instance (c : Component Q hQ) : Fintype (Part Q hQ c) := Fintype.ofFinite _

private theorem restrict_sum (c : Component Q hQ) (F : Vertex Q hQ → ℤ)
    (outside : ∀ i, (cartanGraph Q hQ).connectedComponentMk i≠c → F i=0) :
    ∑ i,F i=∑ i : Part Q hQ c,F i.val := by
  classical
  let P := fun i => (cartanGraph Q hQ).connectedComponentMk i=c
  have vanished : (∑ i : {i // ¬P i}, F i.val)=0 := sum_eq_zero fun i _ => outside i.val i.property
  calc
    _ = (∑ i : {i // P i}, F i.val)+(∑ i : {i // ¬P i}, F i.val) := by
      have same : Subtype.fintype P=inferInstanceAs (Fintype (Part Q hQ c)) := Subsingleton.elim _ _
      have split := (Fintype.sum_subtype_add_sum_subtype P F).symm
      rw [same] at split
      exact split
    _ = _ := by rw [vanished,add_zero]

/-- The doubled component form has its own Cartan matrix; the complement
contributes no diagonal or edge terms after extension by zero. -/
theorem component_energy (c : Component Q hQ) (a : Part Q hQ c → ℤ) :
    2*componentForm Q hQ c a =
      ∑ i : Part Q hQ c, ∑ j : Part Q hQ c, a i*a j*cartanEntry Q hQ i.val j.val := by
  change 2*Q (synth Q hQ (extend Q hQ c a))=_
  rw [cartan_energy]
  have outer (i : Vertex Q hQ) (out : (cartanGraph Q hQ).connectedComponentMk i≠c) :
      (∑ j, extend Q hQ c a i*extend Q hQ c a j*cartanEntry Q hQ i j)=0 := by
    simp only [outside Q hQ c a i out,zero_mul,sum_const_zero]
  rw [restrict_sum Q hQ c _ outer]
  apply sum_congr rfl
  intro i _
  rw [restrict_sum Q hQ c _ (fun j out => by rw [outside Q hQ c a j out,mul_zero,zero_mul])]
  simp only [inside]

/-- In an orientation by parents, collect each unoriented edge only once.
The equivalence gives the order in which to evaluate the component form. -/
theorem component_parent_energy {I : Type*} [Fintype I] (c : Component Q hQ)
    (e : I ≃ Part Q hQ c) (parent : I → Option I)
    (edges : ∀ i j, (cartanGraph Q hQ).Adj (e i).val (e j).val ↔ parent i=some j ∨ parent j=some i)
    (asymm : ∀ i j, parent i=some j → parent j≠some i) (a : I → ℤ) :
    componentForm Q hQ c (fun v => a (e.symm v)) =
      (∑ i, (a i)^2) - ∑ i, (parent i).elim 0 (fun j => a i*a j) := by
  classical
  let d := fun i j => if parent i=some j then a i*a j else 0
  have entry (i j : I) : a i*a j*cartanEntry Q hQ (e i).val (e j).val =
      (if i=j then 2*(a i)^2 else 0)-(d i j+d j i) := by
    have same : (e i).val=(e j).val ↔ i=j := Subtype.val_injective.eq_iff.trans e.injective.eq_iff
    simp only [cartanEntry,same,edges,d]
    by_cases h : i=j
    · subst j
      have none : parent i≠some i := fun H => asymm i i H H
      simp [none]; ring
    · by_cases ij : parent i=some j
      · simp [h,ij,asymm _ _ ij]
      · by_cases ji : parent j=some i <;> simp [h,ij,ji,mul_comm]
  have parentRow (i : I) : ∑ j,d i j=(parent i).elim 0 (fun j => a i*a j) := by
    cases h : parent i with
    | none => simp [d,h]
    | some k => simp [d,h]
  have reindex (f : Part Q hQ c → Part Q hQ c → ℤ) :
      (∑ i, ∑ j, f i j)=∑ i,∑ j,f (e i) (e j) := by
    rw [← e.sum_comp (fun i => ∑ j, f i j)]
    exact sum_congr rfl fun i _ => (e.sum_comp (f (e i))).symm
  have energy := component_energy Q hQ c (fun v => a (e.symm v))
  rw [reindex] at energy
  simp only [e.symm_apply_apply,entry,sum_sub_distrib,sum_add_distrib,sum_ite_eq,mem_univ,if_true] at energy
  have symm : (∑ i,∑ j,d j i)=∑ i,∑ j,d i j := sum_comm
  rw [symm] at energy
  simp_rw [parentRow] at energy
  rw [← mul_sum] at energy
  omega

/-- The component ranks add to the number of simple roots, which can be
strictly smaller than the ambient lattice rank. -/
theorem sum_component_ranks :
    (∑ c : Component Q hQ, Nat.card (Part Q hQ c))=Nat.card (Vertex Q hQ) := by
  let e : (Σ c : Component Q hQ, Part Q hQ c) ≃ Vertex Q hQ :=
    { toFun := fun p => p.2.val
      invFun := fun i => ⟨(cartanGraph Q hQ).connectedComponentMk i,i,rfl⟩
      left_inv := by rintro ⟨c,i,rfl⟩; rfl
      right_inv := fun _ => rfl }
  exact Nat.card_sigma.symm.trans (Nat.card_congr e)

theorem component_root_count : Nat.card (Root Q)=∑ c : Component Q hQ, Nat.card (Root (componentForm Q hQ c)) := by
  classical
  letI (c : Component Q hQ) : Fintype (Root (componentForm Q hQ c)) :=
    @Fintype.ofFinite _ (finite_roots (componentForm Q hQ c) (componentForm_posDef Q hQ c))
  exact (Nat.card_congr (componentRootEquiv Q hQ)).symm.trans Nat.card_sigma

/-- Small components pay only for their own cubic feature dimensions. -/
theorem component_cubic_bound : Nat.card (Root Q)≤
    ∑ c : Component Q hQ, 2*(Nat.card (Part Q hQ c)+2).choose 3 := by
  rw [component_root_count]
  apply sum_le_sum
  intro c _
  simpa only [Nat.card_eq_fintype_card] using root_card_le (componentForm Q hQ c) (componentForm_posDef Q hQ c)

#print axioms component_energy
#print axioms component_parent_energy
#print axioms componentRootEquiv
#print axioms sum_component_ranks
#print axioms component_root_count
#print axioms component_cubic_bound
end GaloisForLFunctions.HTGeometry.IntegralRootShell
