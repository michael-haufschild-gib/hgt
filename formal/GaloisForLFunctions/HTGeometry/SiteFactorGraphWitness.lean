import GaloisForLFunctions.HTGeometry.SiteFactorLeafTransport
import GaloisForLFunctions.HTGeometry.PhysicalRealizationCarrierTransport
import GaloisForLFunctions.HTGeometry.ConnectedGraphSpanningLocalWitnessLaw

/-!
# Site-product charts of physically realized networks

A physically realized tensor-tree system stores its carrier as the nested
product produced by successive leaf attachments.  A *site-product chart*
identifies that carrier with `∀ v, A v` and certifies that, under the
identification, one-site operators are supported on single sites and local
Hamiltonians are spans of interaction terms of the supplied graph.

The chart is what makes every vertex subset a genuine tensor factor, which the
nested product does not.  This file builds the chart along the whole network
induction: the single-site seed carries one trivially, and one leaf attachment
carries one forward.
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Tensor-tree architecture exposed through stored finite instances. -/
@[reducible] def PhysicallyRealizedTensorTreeSystem.tree
    (Z : PhysicallyRealizedTensorTreeSystem.{u}) :
    RootedTensorTree Z.PhysicalState Z.spectral.Observer := by
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  exact Z.locality.tree

/-- An exact identification of a realized carrier with a named site product,
under which one-site operators are site-supported and local Hamiltonians are
spans of interaction terms of the supplied graph. -/
structure SiteFactorChart
    (Z : PhysicallyRealizedTensorTreeSystem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (A : V → Type u) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (G : SimpleGraph V) where
  observerEquiv : Z.spectral.Observer ≃ V
  chart : Z.PhysicalState ≃ (∀ v, A v)
  oneSite : ∀ (s : Z.spectral.Observer)
      (L : Matrix Z.PhysicalState Z.PhysicalState ℂ),
      Z.tree.IsOneSite s L →
      IsSiteSupported {observerEquiv s} (Matrix.reindex chart chart L)
  localHamiltonian : ∀ H : Matrix Z.PhysicalState Z.PhysicalState ℂ,
      Z.tree.IsLocalHamiltonian H →
      Matrix.reindex chart chart H ∈ siteFactorTermSpan A G

/-- A chart transports along an enlargement of the interaction graph. -/
def SiteFactorChart.mono
    {Z : PhysicallyRealizedTensorTreeSystem.{u}}
    {V : Type u} [Fintype V] [DecidableEq V]
    {A : V → Type u} [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    {G G' : SimpleGraph V} (hG : G ≤ G')
    (C : SiteFactorChart Z A G) : SiteFactorChart Z A G' where
  observerEquiv := C.observerEquiv
  chart := C.chart
  oneSite := C.oneSite
  localHamiltonian := fun H hH =>
    Submodule.span_mono
      (fun X hX => by
        rcases hX with ⟨u, hu⟩ | ⟨u, w, huw, hsupp⟩
        · exact Or.inl ⟨u, hu⟩
        · exact Or.inr ⟨u, w, hG huw, hsupp⟩)
      (C.localHamiltonian H hH)

/-- **Single-site seed chart.**  On one site every operator is site-supported,
so the complete one-site seed carries a site-product chart for free. -/
theorem exists_siteFactorChart_oneSiteSeed
    {V : Type u} [Fintype V] [DecidableEq V] [Unique V]
    (A : V → Type u) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card (A default)) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{u},
      Nonempty (SiteFactorChart Z A G) := by
  classical
  obtain ⟨Z, hstate, hobserver, _hgraph⟩ :=
    exists_physicallyRealizedTensorTree_completeOneSiteSeed (A default) hcard
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  letI : Fintype Z.spectral.Observer := Z.spectral.observerFintype
  have hcardPhysical :
      Fintype.card Z.PhysicalState = Fintype.card (∀ v : V, A v) := by
    have h₁ : Fintype.card Z.PhysicalState = Z.spectral.stateCard :=
      Z.realization.physicalCard_eq_stateCard
    have h₂ : Fintype.card (∀ v : V, A v) = Fintype.card (A default) := by
      rw [Fintype.card_pi, Fintype.prod_unique]
    rw [h₁, hstate, h₂]
  have hcardObserver :
      Fintype.card Z.spectral.Observer = Fintype.card V := by
    rw [show Fintype.card Z.spectral.Observer = Z.spectral.observerCard from rfl,
      hobserver, Fintype.card_unique]
  refine ⟨Z, ⟨?_⟩⟩
  refine
    { observerEquiv := Fintype.equivOfCardEq hcardObserver
      chart := Fintype.equivOfCardEq hcardPhysical
      oneSite := ?_
      localHamiltonian := ?_ }
  · intro s L _
    exact IsSiteSupported.of_forall_mem (A := A)
      (fun w => by
        simp only [Finset.mem_singleton]
        exact Subsingleton.elim _ _) _
  · intro H _
    refine Submodule.subset_span (Or.inl ⟨default, ?_⟩)
    exact IsSiteSupported.of_forall_mem (A := A)
      (fun w => by
        simp only [Finset.mem_singleton]
        exact Subsingleton.elim _ _) _

/-- **Leaf attachment carries the chart.**  Attaching one new local factor at a
charted neighbour produces a charted network on the enlarged site set: the
inherited Hamiltonian keeps its site packets, the new onsite term is supported
on the new site, and the parent--leaf interaction is supported on the new
interaction edge. -/
theorem exists_siteFactorChart_leafExtension
    {V : Type u} [Fintype V] [DecidableEq V]
    (A : V → Type u) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (G : SimpleGraph V) (v : V)
    (Z : PhysicallyRealizedTensorTreeSystem.{u})
    (C : SiteFactorChart Z (fun w : {w : V // w ≠ v} => A w.1)
      (G.comap (Function.Embedding.subtype (fun w : V => w ≠ v))))
    (parent : {w : V // w ≠ v}) (hparent : G.Adj parent.1 v)
    (hcard : 2 ≤ Fintype.card (A v)) :
    ∃ W : PhysicallyRealizedTensorTreeSystem.{u},
      Nonempty (SiteFactorChart W A G) ∧
      W.spectral.stateCard =
        Z.spectral.stateCard * Fintype.card (A v) := by
  classical
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  letI : Nontrivial (A v) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨anchor, other, hne⟩ := exists_pair_ne (A v)
  obtain ⟨W, _hstep, hWstate, _hWobserver, hchart⟩ :=
    exists_physicallyRealizedTensorTree_leafExtension Z
      (C.observerEquiv.symm parent) (A v) anchor other hne.symm hcard
  obtain ⟨eObs, eP, honeSite, hlocalShape⟩ := hchart
  refine ⟨W, ⟨?_⟩, hWstate⟩
  set chartW : W.PhysicalState ≃ (∀ w : V, A w) :=
    eP.trans ((C.chart.prodCongr (Equiv.refl (A v))).trans (leafSiteEquiv A v))
    with hchartW
  set observerW : W.spectral.Observer ≃ V :=
    eObs.trans ((Equiv.sumCongr C.observerEquiv (Equiv.refl PUnit)).trans
      (complSingletonSumEquiv v)) with hobserverW
  have hreindex : ∀ M : Matrix W.PhysicalState W.PhysicalState ℂ,
      Matrix.reindex chartW chartW M =
        leafTransport A v
          (Matrix.reindex (C.chart.prodCongr (Equiv.refl (A v)))
            (C.chart.prodCongr (Equiv.refl (A v)))
            (Matrix.reindex eP eP M)) := fun _ => rfl
  have hcouple : ∀ (M : Matrix Z.PhysicalState Z.PhysicalState ℂ)
      (N : Matrix (A v) (A v) ℂ),
      Matrix.reindex (C.chart.prodCongr (Equiv.refl (A v)))
          (C.chart.prodCongr (Equiv.refl (A v)))
          (layerMatrixCoupling M N) =
        layerMatrixCoupling (Matrix.reindex C.chart C.chart M) N :=
    fun _ _ => rfl
  have hone :
      Matrix.reindex C.chart C.chart
        (1 : Matrix Z.PhysicalState Z.PhysicalState ℂ) = 1 :=
    Matrix.submatrix_one_equiv _
  have hcompat : ∀ a b : {w : V // w ≠ v},
      (G.comap (Function.Embedding.subtype (fun w : V => w ≠ v))).Adj a b →
        G.Adj a.1 b.1 := fun _ _ h => h
  refine
    { observerEquiv := observerW
      chart := chartW
      oneSite := ?_
      localHamiltonian := ?_ }
  · intro s L hL
    obtain ⟨hinl, hinr⟩ := honeSite s L hL
    cases hs : eObs s with
    | inl t =>
        obtain ⟨M, hM, hLeq⟩ := hinl t hs
        have hsupp := isSiteSupported_leafTransport_id (A := A)
          (C.oneSite t M hM)
        rw [deletedSiteImage_singleton] at hsupp
        have hobs : observerW s = (C.observerEquiv t).1 := by
          simp [hobserverW, hs]
        rw [hobs, hreindex, hLeq, hcouple]
        exact hsupp
    | inr u =>
        obtain ⟨N, hLeq⟩ := hinr u hs
        have hobs : observerW s = v := by
          simp [hobserverW, hs]
        rw [hobs, hreindex, hLeq, hcouple, hone]
        exact isSiteSupported_leafTransport_newSite (A := A) v N
  · intro H hH
    obtain ⟨oldHamiltonian, parentOperator, shift, edge,
      holdLocal, hparentOne, hHeq⟩ := hlocalShape H hH
    rw [hreindex, hHeq]
    show leafTransport A v
        (Matrix.reindex (C.chart.prodCongr (Equiv.refl (A v)))
          (C.chart.prodCongr (Equiv.refl (A v)))
          (layerMatrixCoupling oldHamiltonian 1 +
            layerMatrixCoupling 1 (Matrix.diagonal shift) +
            layerMatrixCoupling parentOperator edge)) ∈ _
    have hadd : ∀ X Y : Matrix (Z.PhysicalState × A v)
        (Z.PhysicalState × A v) ℂ,
        leafTransport A v
            (Matrix.reindex (C.chart.prodCongr (Equiv.refl (A v)))
              (C.chart.prodCongr (Equiv.refl (A v))) (X + Y)) =
          leafTransport A v
              (Matrix.reindex (C.chart.prodCongr (Equiv.refl (A v)))
                (C.chart.prodCongr (Equiv.refl (A v))) X) +
            leafTransport A v
              (Matrix.reindex (C.chart.prodCongr (Equiv.refl (A v)))
                (C.chart.prodCongr (Equiv.refl (A v))) Y) := by
      intro X Y
      ext x y
      rfl
    rw [hadd, hadd, hcouple, hcouple, hcouple, hone]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact leafTransport_mem_siteFactorTermSpan A v hcompat
        (C.localHamiltonian oldHamiltonian holdLocal)
    · exact Submodule.subset_span
        (isGraphLocalTerm_leafTransport_newSite A v G (Matrix.diagonal shift))
    · have hsupp := C.oneSite (C.observerEquiv.symm parent) parentOperator
        hparentOne
      rw [Equiv.apply_symm_apply] at hsupp
      exact Submodule.subset_span
        (isGraphLocalTerm_leafTransport_edge A v hsupp hparent edge)

/-- **Two-site seed chart.**  The explicit two-qubit graph-state seed carries a
site-product chart for any two named binary factors joined by an interaction
edge. -/
theorem exists_siteFactorChart_twoSiteSeed
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (G : SimpleGraph V) {a b : V} (hab : a ≠ b)
    (huniv : ∀ w : V, w = a ∨ w = b) (hadj : G.Adj a b)
    (hA : ∀ x, Fintype.card (A x) = 2) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
      Nonempty (SiteFactorChart Z A G) := by
  classical
  obtain ⟨Z, -, -, -, eObs, eP, honeSite⟩ :=
    exists_physicallyRealizedTensorTree_twoQubitGraphSeed
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  refine ⟨Z, ⟨?_⟩⟩
  let boolVertex : Bool ≃ V :=
    { toFun := fun t => cond t b a
      invFun := fun w => if w = a then false else true
      left_inv := by
        intro t
        cases t with
        | false => simp
        | true => simp [hab.symm]
      right_inv := by
        intro w
        rcases huniv w with rfl | rfl
        · simp
        · simp [hab.symm] }
  have hcardBool : ∀ t : Bool, Fintype.card Bool =
      Fintype.card (A (boolVertex t)) := fun t => by rw [hA]; rfl
  let factorEquiv : ∀ t : Bool, Bool ≃ A (boolVertex t) :=
    fun t => Fintype.equivOfCardEq (hcardBool t)
  set chartZ : Z.PhysicalState ≃ (∀ w : V, A w) :=
    eP.trans ((Equiv.prodCongr (factorEquiv false) (factorEquiv true)).trans
      (twoSiteEquiv A hab huniv)) with hchartZ
  refine
    { observerEquiv := eObs.trans boolVertex
      chart := chartZ
      oneSite := ?_
      localHamiltonian := ?_ }
  · intro s L hL
    obtain ⟨hfalse, htrue⟩ := honeSite s L hL
    have hone : ∀ t : Bool,
        Matrix.reindex (factorEquiv t) (factorEquiv t)
          (1 : Matrix Bool Bool ℂ) = 1 :=
      fun t => Matrix.submatrix_one_equiv _
    cases hs : eObs s with
    | false =>
        obtain ⟨M, hLeq⟩ := hfalse hs
        have hstep : Matrix.reindex chartZ chartZ L =
            Matrix.reindex (twoSiteEquiv A hab huniv)
              (twoSiteEquiv A hab huniv)
              (layerMatrixCoupling
                (Matrix.reindex (factorEquiv false) (factorEquiv false) M)
                (Matrix.reindex (factorEquiv true) (factorEquiv true)
                  (1 : Matrix Bool Bool ℂ))) := by
          rw [hchartZ]
          show Matrix.reindex (twoSiteEquiv A hab huniv)
              (twoSiteEquiv A hab huniv)
              (Matrix.reindex
                (Equiv.prodCongr (factorEquiv false) (factorEquiv true))
                (Equiv.prodCongr (factorEquiv false) (factorEquiv true))
                (Matrix.reindex eP eP L)) = _
          rw [hLeq]
          rfl
        have hobs : (eObs.trans boolVertex) s = a := by
          simp only [Equiv.trans_apply, hs]
          rfl
        rw [hobs, hstep, hone]
        exact isSiteSupported_twoSiteEquiv_left A hab huniv _
    | true =>
        obtain ⟨N, hLeq⟩ := htrue hs
        have hstep : Matrix.reindex chartZ chartZ L =
            Matrix.reindex (twoSiteEquiv A hab huniv)
              (twoSiteEquiv A hab huniv)
              (layerMatrixCoupling
                (Matrix.reindex (factorEquiv false) (factorEquiv false)
                  (1 : Matrix Bool Bool ℂ))
                (Matrix.reindex (factorEquiv true) (factorEquiv true) N)) := by
          rw [hchartZ]
          show Matrix.reindex (twoSiteEquiv A hab huniv)
              (twoSiteEquiv A hab huniv)
              (Matrix.reindex
                (Equiv.prodCongr (factorEquiv false) (factorEquiv true))
                (Equiv.prodCongr (factorEquiv false) (factorEquiv true))
                (Matrix.reindex eP eP L)) = _
          rw [hLeq]
          rfl
        have hobs : (eObs.trans boolVertex) s = b := by
          simp only [Equiv.trans_apply, hs]
          rfl
        rw [hobs, hstep, hone]
        exact isSiteSupported_twoSiteEquiv_right A hab huniv _
  · intro H _
    refine Submodule.subset_span (Or.inr ⟨a, b, hadj, ?_⟩)
    refine IsSiteSupported.of_forall_mem (A := A) (fun w => ?_) _
    rcases huniv w with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **Charted spanning-tree witness.**  Every connected finite network with one
local factor of dimension at least three carries a maximally projective
realization together with an exact site-product chart. -/
theorem exists_siteFactorChart_rootedSpanningTree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (A : V → Type u) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (hA : ∀ v, 2 ≤ Fintype.card (A v))
    (root : V) (hroot : 3 ≤ Fintype.card (A root)) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{u},
      Nonempty (SiteFactorChart Z A G) := by
  classical
  by_cases hnontrivial : Nontrivial V
  · letI : Nontrivial V := hnontrivial
    obtain ⟨v, hvr, hremaining⟩ :=
      SimpleGraph.Connected.exists_connected_induce_compl_singleton_ne G hG root
    let OldV := {x : V // x ≠ v}
    let oldG : SimpleGraph OldV :=
      G.comap (Function.Embedding.subtype (fun w : V => w ≠ v))
    have holdConnected : oldG.Connected := hremaining
    letI : DecidableRel oldG.Adj := Classical.decRel _
    have hvpos : 0 < G.degree v :=
      hG.preconnected.degree_pos_of_nontrivial v
    obtain ⟨parent, hvparent⟩ :=
      (G.degree_pos_iff_exists_adj v).mp hvpos
    let parentOld : OldV := ⟨parent, hvparent.ne'⟩
    obtain ⟨Z, ⟨C⟩⟩ :=
      exists_siteFactorChart_rootedSpanningTree oldG holdConnected
        (fun w : OldV => A w.1) (fun w => hA w.1)
        (⟨root, hvr.symm⟩ : OldV) hroot
    obtain ⟨W, hW, -⟩ :=
      exists_siteFactorChart_leafExtension A G v Z C parentOld
        hvparent.symm (hA v)
    exact ⟨W, hW⟩
  · have hsubsingleton : Subsingleton V :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton V := hsubsingleton
    letI : Unique V :=
      { default := root
        uniq := fun x => Subsingleton.elim x root }
    exact exists_siteFactorChart_oneSiteSeed A G hroot
termination_by Fintype.card V
decreasing_by
  rw [show Fintype.card OldV = Fintype.card V - 1 by
    dsimp [OldV]
    rw [Fintype.card_subtype_compl (fun x : V => x = v),
      Fintype.card_subtype_eq]]
  exact Nat.sub_lt (Fintype.card_pos) (by omega)

/-- **Charted binary spanning-tree witness.**  Every connected finite network of
at least two binary sites carries a maximally projective realization together
with an exact site-product chart. -/
theorem exists_siteFactorChart_binarySpanningTree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (A : V → Type) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (hA : ∀ x, Fintype.card (A x) = 2) (hcard : 2 ≤ Fintype.card V) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
      Nonempty (SiteFactorChart Z A G) := by
  classical
  by_cases hlarge : 2 < Fintype.card V
  · letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hremaining⟩ :=
      hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let OldV := {x : V // x ≠ v}
    let oldG : SimpleGraph OldV :=
      G.comap (Function.Embedding.subtype (fun w : V => w ≠ v))
    have holdConnected : oldG.Connected := hremaining
    letI : DecidableRel oldG.Adj := Classical.decRel _
    have holdCard : 2 ≤ Fintype.card OldV := by
      rw [show Fintype.card OldV = Fintype.card V - 1 by
        dsimp [OldV]
        rw [Fintype.card_subtype_compl (fun x : V => x = v),
          Fintype.card_subtype_eq]]
      omega
    have hvpos : 0 < G.degree v :=
      hG.preconnected.degree_pos_of_nontrivial v
    obtain ⟨parent, hvparent⟩ :=
      (G.degree_pos_iff_exists_adj v).mp hvpos
    obtain ⟨Z, ⟨C⟩⟩ :=
      exists_siteFactorChart_binarySpanningTree oldG holdConnected
        (fun w : OldV => A w.1) (fun w => hA w.1) holdCard
    obtain ⟨W, hW, -⟩ :=
      exists_siteFactorChart_leafExtension A G v Z C
        (⟨parent, hvparent.ne'⟩ : OldV) hvparent.symm (hA v).ge
    exact ⟨W, hW⟩
  · have hcardEq : Fintype.card V = 2 := by omega
    obtain ⟨a, b, hab⟩ :=
      Fintype.exists_pair_of_one_lt_card (α := V) (by omega)
    have huniv : ∀ w : V, w = a ∨ w = b := by
      intro w
      by_contra hcon
      push Not at hcon
      have hcard3 : ({w, a, b} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            push Not
            exact ⟨hcon.1, hcon.2⟩),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact hab),
          Finset.card_singleton]
      have hle := Finset.card_le_card (Finset.subset_univ ({w, a, b} : Finset V))
      rw [hcard3, Finset.card_univ, hcardEq] at hle
      omega
    have hadj : G.Adj a b := by
      letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hpos : 0 < G.degree a :=
        hG.preconnected.degree_pos_of_nontrivial a
      obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj a).mp hpos
      rcases huniv w with hwa | hwb
      · rw [hwa] at hw
        exact absurd rfl hw.ne
      · rwa [hwb] at hw
    exact exists_siteFactorChart_twoSiteSeed A G hab huniv hadj hA
termination_by Fintype.card V
decreasing_by
  rw [show Fintype.card OldV = Fintype.card V - 1 by
    dsimp [OldV]
    rw [Fintype.card_subtype_compl (fun x : V => x = v),
      Fintype.card_subtype_eq]]
  exact Nat.sub_lt (by omega) (by omega)

/-- **Charted networks realize maximal projective rank locally.**  A site-product
chart turns the maximally projective spectrum of a realized network into a
maximally projective Hermitian element of the exact onsite-plus-edge Hamiltonian
space of the supplied interaction graph. -/
theorem exists_maximallyProjective_mem_siteFactorLocalSubmodule_of_chart
    {V : Type u} [Fintype V] [DecidableEq V]
    {A : V → Type u} [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    {G : SimpleGraph V} {Z : PhysicallyRealizedTensorTreeSystem.{u}}
    (C : SiteFactorChart Z A G) :
    ∃ H : Matrix (∀ v, A v) (∀ v, A v) ℂ, ∃ hH : H.IsHermitian,
      H ∈ siteFactorLocalSubmodule A G ∧
        MaximallyProjectiveEnergy hH.eigenvalues := by
  classical
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  have hbase :=
    GoodObserverSpectralSystem.PhysicalRealization.hamiltonian_isHermitian
      Z.spectral Z.realization
  have hHerm :
      (Matrix.reindex C.chart C.chart Z.hamiltonian).IsHermitian := by
    show (Matrix.reindex C.chart C.chart Z.hamiltonian)ᴴ = _
    show Matrix.reindex C.chart C.chart Z.hamiltonianᴴ = _
    rw [show Z.hamiltonianᴴ = Z.hamiltonian from hbase]
  refine ⟨Matrix.reindex C.chart C.chart Z.hamiltonian, hHerm, ?_, ?_⟩
  · refine mem_siteFactorLocalSubmodule_of_mem_termSpan A G ?_ hHerm
    exact C.localHamiltonian Z.hamiltonian Z.locality.hamiltonian_local
  · exact reindex_hamiltonian_maximallyProjective Z.spectral Z.realization
      C.chart hHerm

/-- **Connected finite networks realize maximal projective rank.**  Every
connected finite interaction graph with local factors of dimension at least two
admits a Hermitian onsite-plus-edge Hamiltonian whose spectrum has maximal
projective rational rank. -/
theorem exists_maximallyProjective_mem_siteFactorLocalSubmodule
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (A : V → Type) [∀ x, Fintype (A x)] [∀ x, DecidableEq (A x)]
    (hA : ∀ x, 2 ≤ Fintype.card (A x)) :
    ∃ H : Matrix (∀ v, A v) (∀ v, A v) ℂ, ∃ hH : H.IsHermitian,
      H ∈ siteFactorLocalSubmodule A G ∧
        MaximallyProjectiveEnergy hH.eigenvalues := by
  classical
  by_cases h3 : ∃ x, 3 ≤ Fintype.card (A x)
  · obtain ⟨root, hroot⟩ := h3
    obtain ⟨Z, ⟨C⟩⟩ :=
      exists_siteFactorChart_rootedSpanningTree G hG A hA root hroot
    exact exists_maximallyProjective_mem_siteFactorLocalSubmodule_of_chart C
  · push Not at h3
    have hA2 : ∀ x, Fintype.card (A x) = 2 := by
      intro x
      have := h3 x
      have := hA x
      omega
    by_cases hV : 2 ≤ Fintype.card V
    · obtain ⟨Z, ⟨C⟩⟩ :=
        exists_siteFactorChart_binarySpanningTree G hG A hA2 hV
      exact exists_maximallyProjective_mem_siteFactorLocalSubmodule_of_chart C
    · have hV1 : Fintype.card V = 1 := by
        have := Fintype.card_pos_iff.mpr ‹Nonempty V›
        omega
      obtain ⟨x₀, hx₀⟩ := Fintype.card_eq_one_iff.mp hV1
      obtain ⟨energy, hmaxEnergy, -⟩ :=
        exists_maximallyProjectiveEnergy_close_fintype
          (fun _ : (∀ v : V, A v) => (0 : ℝ)) 1 (by norm_num)
      have hHerm :
          (Matrix.diagonal (fun i => (energy i : ℂ)) :
            Matrix (∀ v : V, A v) (∀ v : V, A v) ℂ).IsHermitian := by
        rw [Matrix.isHermitian_diagonal_iff]
        intro i
        rw [isSelfAdjoint_iff]
        exact RCLike.conj_ofReal _
      refine ⟨Matrix.diagonal (fun i => (energy i : ℂ)), hHerm, ?_, ?_⟩
      · refine mem_siteFactorLocalSubmodule_of_oneSite A G hHerm x₀ ?_
        refine IsSiteSupported.of_forall_mem (A := A) (fun w => ?_) _
        rw [hx₀ w]
        exact Finset.mem_singleton_self _
      · refine maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket _
          hHerm energy hmaxEnergy ?_
        intro i
        change (Matrix.scalar (∀ v : V, A v) (energy i : ℂ) -
          Matrix.diagonal (fun j => (energy j : ℂ))).det = 0
        rw [← Matrix.eval_charpoly, Matrix.charpoly_diagonal,
          Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

end

end GaloisForLFunctions.HTGeometry
