import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Connected-graph spanning local witnesses

Every finite connected graph admits a leaf-growth spanning architecture. If one
local dimension is at least three, that vertex is preserved as one-site seed; if
all dimensions are two, growth starts from the explicit two-qubit edge seed.
The resulting physical Hamiltonian is tree-local, maximally projective, has the
exact product Hilbert dimension, and its architecture graph embeds in the supplied
graph. These are the witness and spanning-subspace inputs for arbitrary-graph
polynomial genericity.
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Reinsert one distinguished point after passing to its complement. -/
def complSingletonSumEquiv {V : Type u} [DecidableEq V] (v : V) :
    Sum {x : V // x ≠ v} PUnit ≃ V where
  toFun
    | Sum.inl x => x.1
    | Sum.inr _ => v
  invFun x := if h : x = v then Sum.inr PUnit.unit else Sum.inl ⟨x, h⟩
  left_inv x := by
    cases x with
    | inl x => simp [x.2]
    | inr x => simp
  right_inv x := by
    by_cases h : x = v
    · simp [h]
    · simp [h]

@[simp] theorem complSingletonSumEquiv_inl
    {V : Type u} [DecidableEq V] (v : V) (x : {x : V // x ≠ v}) :
    complSingletonSumEquiv v (Sum.inl x) = x := rfl

@[simp] theorem complSingletonSumEquiv_inr
    {V : Type u} [DecidableEq V] (v : V) (x : PUnit) :
    complSingletonSumEquiv v (Sum.inr x) = v := rfl

theorem SimpleGraph.IsTree.exists_degree_one_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) [Nontrivial V] (root : V) :
    ∃ v : V, v ≠ root ∧ T.degree v = 1 := by
  by_contra h
  push Not at h
  have hpos : ∀ v : V, 1 ≤ T.degree v := by
    intro v
    exact hT.preconnected.degree_pos_of_nontrivial v
  have hlower :
      ∑ v : V, (if v = root then 1 else 2) ≤
        ∑ v : V, T.degree v := by
    apply Finset.sum_le_sum
    intro v _hv
    by_cases hvr : v = root
    · simp [hvr, hpos v]
    · simp only [if_neg hvr]
      have hne : T.degree v ≠ 1 := fun hv => h v hvr hv
      exact (T.degree v).two_le_iff.mpr
        ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hpos v)), hne⟩
  have hleft :
      (∑ v : V, if v = root then 1 else 2) =
        2 * Fintype.card V - 1 := by
    classical
    have herase :
        (∑ v ∈ (Finset.univ.erase root),
          if v = root then 1 else 2) =
          2 * (Fintype.card V - 1) := by
      rw [Finset.sum_congr rfl fun v hv => if_neg (Finset.ne_of_mem_erase hv)]
      simp [Finset.card_erase_of_mem, Nat.mul_comm]
    calc
      (∑ v : V, if v = root then 1 else 2) =
          (∑ v ∈ Finset.univ.erase root,
            if v = root then 1 else 2) +
              (if root = root then 1 else 2) :=
        (Finset.sum_erase_add Finset.univ
          (fun v : V => if v = root then 1 else 2)
          (Finset.mem_univ root)).symm
      _ = 2 * Fintype.card V - 1 := by
        rw [herase]
        have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
        simp
        omega
  have hedge := hT.card_edgeFinset
  have hdegree := T.sum_degrees_eq_twice_card_edges
  rw [hleft, hdegree] at hlower
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
  omega

theorem SimpleGraph.Connected.exists_connected_induce_compl_singleton_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) [Nontrivial V] (root : V) :
    ∃ v : V, v ≠ root ∧ (G.induce ({v}ᶜ)).Connected := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨v, hvr, hvdegree⟩ :=
    SimpleGraph.IsTree.exists_degree_one_ne T hT root
  refine ⟨v, hvr, ?_⟩
  exact (hT.connected.induce_compl_singleton_of_degree_eq_one hvdegree).mono
    (by tauto)

/-- Every connected finite architecture with one local factor of dimension
at least three contains an exact spanning-tree-local maximally projective
physical Hamiltonian. -/
theorem exists_rootedSpanningTreePhysicalSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected)
    (q : V → ℕ) (hq : ∀ v, 2 ≤ q v)
    (root : V) (hroot : 3 ≤ q root) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{u},
    ∃ e : Z.spectral.Observer ≃ V,
      Z.architectureGraph ≤ SimpleGraph.comap e G ∧
      Z.spectral.stateCard = ∏ v, q v ∧
      Z.architectureGraph.Connected := by
  classical
  by_cases hnontrivial : Nontrivial V
  · letI : Nontrivial V := hnontrivial
    obtain ⟨v, hvr, hremaining⟩ :=
      SimpleGraph.Connected.exists_connected_induce_compl_singleton_ne G hG root
    let OldV := {x : V // x ≠ v}
    let oldG : SimpleGraph OldV := G.induce ({v}ᶜ)
    let oldRoot : OldV := ⟨root, hvr.symm⟩
    have holdConnected : oldG.Connected := hremaining
    have hqOld : ∀ x : OldV, 2 ≤ q x := fun x => hq x
    have hrootOld : 3 ≤ q oldRoot := by simpa [oldRoot] using hroot
    obtain ⟨Z, eOld, hOldGraph, hOldState, hOldConnected⟩ :=
      exists_rootedSpanningTreePhysicalSystem oldG holdConnected
        (fun x : OldV => q x) hqOld oldRoot hrootOld
    have hvpos : 0 < G.degree v :=
      hG.preconnected.degree_pos_of_nontrivial v
    obtain ⟨parent, hvparent⟩ :=
      (G.degree_pos_iff_exists_adj v).mp hvpos
    let parentOld : OldV := ⟨parent, hvparent.ne'⟩
    let parentObserver : Z.spectral.Observer := eOld.symm parentOld
    let Local : Type u := ULift.{u} (Fin (q v))
    have hLocalCard : Fintype.card Local = q v := by simp [Local]
    let anchorFin : Fin (q v) :=
      ⟨0, lt_of_lt_of_le (by decide : 0 < 2) (hq v)⟩
    let otherFin : Fin (q v) := ⟨1, hq v⟩
    let anchor : Local := ULift.up anchorFin
    let other : Local := ULift.up otherFin
    have hother : other ≠ anchor := by
      intro h
      have := congrArg (fun x : Local => x.down.val) h
      simp [other, anchor, otherFin, anchorFin] at this
    obtain ⟨W, hWextension, hWstate, _hWobserver, _⟩ :=
      exists_physicallyRealizedTensorTree_leafExtension
        Z parentObserver Local anchor other hother
          (by simpa [hLocalCard] using hq v)
    obtain ⟨eW, hWgraph⟩ := hWextension
    let addEquiv : LeafExtendedObserver Z.spectral.Observer ≃ V :=
      (Equiv.sumCongr eOld (Equiv.refl PUnit)).trans
        (complSingletonSumEquiv v)
    let finalEquiv : W.spectral.Observer ≃ V := eW.trans addEquiv
    have hleaf :
        leafGraphExtension Z.architectureGraph parentObserver ≤
          SimpleGraph.comap addEquiv G := by
      intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b =>
              have hab' : Z.architectureGraph.Adj a b := by
                simp only [leafGraphExtension,
                  SimpleGraph.fromRel_adj] at hab
                exact hab.2.elim id Adj.symm
              have hold := hOldGraph hab'
              change G.Adj (eOld a).1 (eOld b).1 at hold
              dsimp [addEquiv]
              exact hold
          | inr b =>
              have hab' : a = parentObserver := by
                simpa [leafGraphExtension] using hab
              subst a
              dsimp [addEquiv, parentObserver, parentOld]
              simpa [complSingletonSumEquiv, Function.comp_apply]
                using hvparent.symm
      | inr a =>
          cases b with
          | inl b =>
              have hab' : b = parentObserver := by
                simpa [leafGraphExtension] using hab
              subst b
              dsimp [addEquiv, parentObserver, parentOld]
              simpa [complSingletonSumEquiv, Function.comp_apply]
                using hvparent
          | inr b =>
              simp [leafGraphExtension] at hab
    refine ⟨W, finalEquiv, ?_, ?_, ?_⟩
    · rw [hWgraph]
      change SimpleGraph.comap eW
          (leafGraphExtension Z.architectureGraph parentObserver) ≤
        SimpleGraph.comap eW (SimpleGraph.comap addEquiv G)
      exact SimpleGraph.comap_monotone eW.toEmbedding hleaf
    · rw [hWstate, hOldState, hLocalCard]
      rw [Fintype.prod_eq_mul_prod_subtype_ne q v]
      ac_rfl
    · rw [hWgraph]
      exact (SimpleGraph.Iso.comap eW
        (leafGraphExtension Z.architectureGraph parentObserver)).connected_iff.mpr
          (leafGraphExtension_connected Z.architectureGraph
            parentObserver hOldConnected)
  · have hsubsingleton : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton V := hsubsingleton
    letI : Unique V :=
      { default := root
        uniq := fun x => Subsingleton.elim x root }
    let Local : Type u := ULift.{u} (Fin (q root))
    have hLocalCard : Fintype.card Local = q root := by simp [Local]
    obtain ⟨Base, hBaseState, hBaseObserver, hBaseGraph⟩ :=
      exists_physicallyRealizedTensorTree_completeOneSiteSeed Local
        (by simpa [hLocalCard] using hroot)
    letI : Fintype Base.spectral.Observer := Base.spectral.observerFintype
    let e : Base.spectral.Observer ≃ V :=
      Fintype.equivOfCardEq (hBaseObserver.trans Fintype.card_unique.symm)
    refine ⟨Base, e, ?_, ?_, ?_⟩
    · rw [hBaseGraph]
      exact bot_le
    · rw [hBaseState, hLocalCard]
      rw [Fintype.prod_unique]
      exact congrArg q (Subsingleton.elim root default)
    · letI : Nonempty Base.spectral.Observer := ⟨e.symm root⟩
      letI : Subsingleton Base.spectral.Observer :=
        ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
      rw [hBaseGraph]
      exact SimpleGraph.Connected.of_subsingleton
termination_by Fintype.card V
decreasing_by
  rw [show Fintype.card OldV = Fintype.card V - 1 by
    dsimp [OldV]
    rw [Fintype.card_subtype_compl (fun x : V => x = v),
      Fintype.card_subtype_eq]]
  exact Nat.sub_lt (Fintype.card_pos) (by omega)

/-- Every connected finite graph with at least two vertices and binary
local factors contains an exact spanning-tree-local maximally projective
physical Hamiltonian, rooted at the explicit two-qubit edge seed. -/
theorem exists_binarySpanningTreePhysicalSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hcard : 2 ≤ Fintype.card V) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ V,
      Z.architectureGraph ≤ SimpleGraph.comap e G ∧
      Z.spectral.stateCard = 2 ^ Fintype.card V ∧
      Z.architectureGraph.Connected := by
  classical
  by_cases hlarge : 2 < Fintype.card V
  · letI : Nontrivial V :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hremaining⟩ :=
      hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let OldV := {x : V // x ≠ v}
    let oldG : SimpleGraph OldV := G.induce ({v}ᶜ)
    have holdConnected : oldG.Connected := hremaining
    have holdCard : 2 ≤ Fintype.card OldV := by
      rw [show Fintype.card OldV = Fintype.card V - 1 by
        dsimp [OldV]
        rw [Fintype.card_subtype_compl (fun x : V => x = v),
          Fintype.card_subtype_eq]]
      omega
    obtain ⟨Z, eOld, hOldGraph, hOldState, hOldConnected⟩ :=
      exists_binarySpanningTreePhysicalSystem oldG holdConnected holdCard
    have hvpos : 0 < G.degree v :=
      hG.preconnected.degree_pos_of_nontrivial v
    obtain ⟨parent, hvparent⟩ :=
      (G.degree_pos_iff_exists_adj v).mp hvpos
    let parentOld : OldV := ⟨parent, hvparent.ne'⟩
    let parentObserver : Z.spectral.Observer := eOld.symm parentOld
    let Local : Type := Fin 2
    let anchor : Local := 0
    let other : Local := 1
    have hother : other ≠ anchor := by decide
    obtain ⟨W, hWextension, hWstate, _hWobserver, _⟩ :=
      exists_physicallyRealizedTensorTree_leafExtension
        Z parentObserver Local anchor other hother (by decide)
    obtain ⟨eW, hWgraph⟩ := hWextension
    let addEquiv : LeafExtendedObserver Z.spectral.Observer ≃ V :=
      (Equiv.sumCongr eOld (Equiv.refl PUnit)).trans
        (complSingletonSumEquiv v)
    let finalEquiv : W.spectral.Observer ≃ V := eW.trans addEquiv
    have hleaf :
        leafGraphExtension Z.architectureGraph parentObserver ≤
          SimpleGraph.comap addEquiv G := by
      intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b =>
              have hab' : Z.architectureGraph.Adj a b := by
                simp only [leafGraphExtension,
                  SimpleGraph.fromRel_adj] at hab
                exact hab.2.elim id Adj.symm
              have hold := hOldGraph hab'
              change G.Adj (eOld a).1 (eOld b).1 at hold
              dsimp [addEquiv]
              exact hold
          | inr b =>
              have hab' : a = parentObserver := by
                simpa [leafGraphExtension] using hab
              subst a
              dsimp [addEquiv, parentObserver, parentOld]
              simpa [complSingletonSumEquiv, Function.comp_apply]
                using hvparent.symm
      | inr a =>
          cases b with
          | inl b =>
              have hab' : b = parentObserver := by
                simpa [leafGraphExtension] using hab
              subst b
              dsimp [addEquiv, parentObserver, parentOld]
              simpa [complSingletonSumEquiv, Function.comp_apply]
                using hvparent
          | inr b =>
              simp [leafGraphExtension] at hab
    refine ⟨W, finalEquiv, ?_, ?_, ?_⟩
    · rw [hWgraph]
      change SimpleGraph.comap eW
          (leafGraphExtension Z.architectureGraph parentObserver) ≤
        SimpleGraph.comap eW (SimpleGraph.comap addEquiv G)
      exact SimpleGraph.comap_monotone eW.toEmbedding hleaf
    · rw [hWstate, hOldState]
      have hOldCard : Fintype.card OldV = Fintype.card V - 1 := by
        dsimp [OldV]
        rw [Fintype.card_subtype_compl (fun x : V => x = v),
          Fintype.card_subtype_eq]
      rw [show Fintype.card Local = 2 by rfl, hOldCard]
      rw [← pow_succ]
      congr 1
      omega
    · rw [hWgraph]
      exact (SimpleGraph.Iso.comap eW
        (leafGraphExtension Z.architectureGraph parentObserver)).connected_iff.mpr
          (leafGraphExtension_connected Z.architectureGraph
            parentObserver hOldConnected)
  · have hcardEq : Fintype.card V = 2 := by omega
    obtain ⟨Base, hBaseState, hBaseObserver, hBaseGraph, -⟩ :=
      exists_physicallyRealizedTensorTree_twoQubitGraphSeed
    letI : Fintype Base.spectral.Observer := Base.spectral.observerFintype
    let observerBool : Base.spectral.Observer ≃ Bool :=
      Fintype.equivOfCardEq hBaseObserver
    let boolVertex : Bool ≃ V :=
      Fintype.equivOfCardEq hcardEq.symm
    let e : Base.spectral.Observer ≃ V := observerBool.trans boolVertex
    have hendpoint : G.Adj (boolVertex false) (boolVertex true) := by
      haveI : Nontrivial V :=
        Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hpos : 0 < G.degree (boolVertex false) :=
        hG.preconnected.degree_pos_of_nontrivial (boolVertex false)
      obtain ⟨w, hw⟩ :=
        (G.degree_pos_iff_exists_adj (boolVertex false)).mp hpos
      have hwlabel : boolVertex.symm w = true := by
        cases hlabel : boolVertex.symm w with
        | false =>
            exfalso
            have hwEq : w = boolVertex false := by
              calc
              w = boolVertex (boolVertex.symm w) :=
                (boolVertex.apply_symm_apply w).symm
              _ = boolVertex false := by rw [hlabel]
            exact hw.ne hwEq.symm
        | true => rfl
      have hwEq : w = boolVertex true := by
        calc
          w = boolVertex (boolVertex.symm w) :=
            (boolVertex.apply_symm_apply w).symm
          _ = boolVertex true := by rw [hwlabel]
      simpa [hwEq] using hw
    have htop : (⊤ : SimpleGraph Base.spectral.Observer) ≤
        SimpleGraph.comap e G := by
      intro a b hab
      have hne : a ≠ b := by simpa using hab
      have ha : a = observerBool.symm false ∨
          a = observerBool.symm true := by
        have : observerBool a = false ∨ observerBool a = true := by
          cases observerBool a <;> simp
        exact this.imp
          (fun h => observerBool.injective (by simpa using h))
          (fun h => observerBool.injective (by simpa using h))
      have hb : b = observerBool.symm false ∨
          b = observerBool.symm true := by
        have : observerBool b = false ∨ observerBool b = true := by
          cases observerBool b <;> simp
        exact this.imp
          (fun h => observerBool.injective (by simpa using h))
          (fun h => observerBool.injective (by simpa using h))
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (hne (ha.trans hb.symm)).elim
      · subst a; subst b
        simpa [e, Function.comp_apply] using hendpoint
      · subst a; subst b
        simpa [e, Function.comp_apply] using hendpoint.symm
      · exact (hne (ha.trans hb.symm)).elim
    refine ⟨Base, e, ?_, ?_, ?_⟩
    · rw [hBaseGraph]
      exact htop
    · rw [hBaseState, hcardEq]
      norm_num
    · letI : Nonempty Base.spectral.Observer :=
        ⟨observerBool.symm false⟩
      rw [hBaseGraph]
      exact SimpleGraph.connected_top
termination_by Fintype.card V
decreasing_by
  rw [show Fintype.card OldV = Fintype.card V - 1 by
    dsimp [OldV]
    rw [Fintype.card_subtype_compl (fun x : V => x = v),
      Fintype.card_subtype_eq]]
  exact Nat.sub_lt (by omega) (by omega)

end

end GaloisForLFunctions.HTGeometry
