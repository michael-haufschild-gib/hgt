import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Right cancellation for covering maps

If `q ∘ r` is a covering, `r` is a surjective local homeomorphism, and `q`
separates points in each fiber, then `q` is a covering over a locally connected
base. Connected sheet sections that meet agree everywhere, allowing the sheets
of the composite to descend. Empty fibers are included.
-/

open Topology Set Function Bundle

namespace GaloisForLFunctions.HTGeometry

/-- Right cancellation: an intermediate surjective local homeomorphism of a covering
has a covering as its remaining factor over a locally connected base, provided
the remaining factor separates points in each fiber. -/
theorem isCoveringMap_of_comp_right_of_isSeparatedMap [TopologicalSpace E] [TopologicalSpace Y]
    [TopologicalSpace B] [LocallyConnectedSpace B]
    {r : E → Y} {q : Y → B} (hp : IsCoveringMap (q ∘ r))
    (hr : IsLocalHomeomorph r) (hrsurj : Surjective r)
    (hsep : IsSeparatedMap q) : IsCoveringMap q := by
  classical
  have hq : IsLocalHomeomorph q := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    have h : IsLocalHomeomorphOn q (r '' (univ : Set E)) :=
      hp.isLocalHomeomorph.isLocalHomeomorphOn.of_comp_right hr.isLocalHomeomorphOn
    simpa only [image_univ, hrsurj.range_eq] using h
  haveI hqdisc : ∀ b : B, DiscreteTopology (q ⁻¹' {b}) := by
    intro b
    have hv : ∀ v : q '' (q ⁻¹' {b}), (v : B) = b := by
      rintro ⟨v, ⟨y, hy, rfl⟩⟩
      exact hy
    letI : Subsingleton (q '' (q ⁻¹' {b})) :=
      ⟨fun v w => Subtype.ext ((hv v).trans (hv w).symm)⟩
    exact (hq.isLocalHomeomorphOn.mono (subset_univ _)).discreteTopology_of_image
  intro b
  cases isEmpty_or_nonempty (q ⁻¹' {b}) with
  | inl hI =>
      letI := hI
      letI : IsEmpty ((q ∘ r) ⁻¹' {b}) :=
        ⟨fun e => isEmptyElim (⟨r e, e.property⟩ : q ⁻¹' {b})⟩
      obtain ⟨_, V, hbV, hVo, _, H, _⟩ := hp b
      letI : IsEmpty (q ⁻¹' V) := ⟨fun y => by
        obtain ⟨e, he⟩ := hrsurj y
        have heV : (q ∘ r) e ∈ V := by
          change q (r e) ∈ V
          rw [he]
          exact y.property
        exact isEmptyElim (H ⟨e, heV⟩).2⟩
      exact ⟨inferInstance, V, hbV, hVo, hVo.preimage hq.continuous,
        Homeomorph.empty, fun y => isEmptyElim y⟩
  | inr hI =>
      letI := hI
      choose e he using hrsurj
      let i₀ : q ⁻¹' {b} := Classical.choice hI
      letI : Nonempty Y := ⟨i₀⟩
      letI : Nonempty E := ⟨e i₀⟩
      letI : Nonempty ((q ∘ r) ⁻¹' {b}) :=
        ⟨⟨e i₀, by change q (r (e i₀)) = b; rw [he]; exact i₀.property⟩⟩
      let tp := (hp b).toTrivialization
      have hb : b ∈ tp.baseSet := (hp b).mem_toTrivialization_baseSet
      let W := connectedComponentIn tp.baseSet b
      have hbW : b ∈ W := mem_connectedComponentIn hb
      have hWo : IsOpen W := tp.open_baseSet.connectedComponentIn
      have hWc : IsConnected W := isConnected_connectedComponentIn_iff.mpr hb
      have hWsub : W ⊆ tp.baseSet := connectedComponentIn_subset _ _
      letI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWc
      let σ : ((q ∘ r) ⁻¹' {b}) → W → Y :=
        fun j w => r (tp.toOpenPartialHomeomorph.symm ((w : B), j))
      have hσproj : ∀ j (w : W), q (σ j w) = (w : B) := fun j w =>
        tp.proj_symm_apply' (hWsub w.property)
      have hσcont : ∀ j, Continuous (σ j) := by
        intro j
        apply hr.continuous.comp
        apply tp.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
          (by fun_prop)
        intro w
        rw [tp.mem_target]
        exact hWsub w.property
      have hσopen : ∀ j, IsOpenEmbedding (σ j) := by
        intro j
        apply hq.isOpenEmbedding_of_comp ?_ (hσcont j)
        have hcomp : q ∘ σ j = ((↑) : W → B) := funext (hσproj j)
        rw [hcomp]
        exact hWo.isOpenEmbedding_subtypeVal
      have hσeq : ∀ j k (w : W), σ j w = σ k w → σ j = σ k := by
        intro j k w hw
        apply hsep.eq_of_comp_eq hq.isLocallyInjective
          (hσcont j) (hσcont k) ?_ w hw
        exact funext fun z => (hσproj j z).trans (hσproj k z).symm
      let κ : (q ⁻¹' {b}) → ((q ∘ r) ⁻¹' {b}) := fun i => (tp (e i)).2
      have heproj : ∀ i : q ⁻¹' {b}, (q ∘ r) (e i) = b := by
        intro i
        change q (r (e i)) = b
        rw [he]
        exact i.property
      have hesrc : ∀ i : q ⁻¹' {b}, e i ∈ tp.source := by
        intro i
        rw [tp.mem_source, heproj]
        exact hb
      have hσbase : ∀ i : q ⁻¹' {b}, σ (κ i) ⟨b, hbW⟩ = (i : Y) := by
        intro i
        change r (tp.toOpenPartialHomeomorph.symm (b, (tp (e i)).2)) = (i : Y)
        have hpair : (b, (tp (e i)).2) = ((q ∘ r) (e i), (tp (e i)).2) :=
          Prod.ext (heproj i).symm rfl
        rw [hpair, tp.symm_apply_mk_proj (hesrc i), he]
      let S : (q ⁻¹' {b}) → Set Y := fun i => range (σ (κ i))
      have hSo : ∀ i, IsOpen (S i) := fun i => (hσopen (κ i)).isOpen_range
      have hinj : ∀ i, (S i).InjOn q := by
        intro i y hy z hz heq
        obtain ⟨u, rfl⟩ := hy
        obtain ⟨v, rfl⟩ := hz
        have huv : u = v := Subtype.ext (by simpa only [hσproj] using heq)
        rw [huv]
      have hsurj : ∀ i, (S i).SurjOn q W := by
        intro i w hw
        exact ⟨σ (κ i) ⟨w, hw⟩, mem_range_self _, hσproj _ _⟩
      have hexhaust : q ⁻¹' W ⊆ ⋃ i, S i := by
        intro y hy
        let z := e y
        have hz : r z = y := he y
        have hzbase : (q ∘ r) z ∈ tp.baseSet := by
          change q (r z) ∈ tp.baseSet
          rw [hz]
          exact hWsub hy
        have hzsrc : z ∈ tp.source := tp.mem_source.mpr hzbase
        let j : (q ∘ r) ⁻¹' {b} := (tp z).2
        let i : q ⁻¹' {b} := ⟨σ j ⟨b, hbW⟩, hσproj j ⟨b, hbW⟩⟩
        have hji : σ j = σ (κ i) := hσeq j (κ i) ⟨b, hbW⟩ (hσbase i).symm
        refine mem_iUnion.mpr ⟨i, ⟨⟨q y, hy⟩, ?_⟩⟩
        rw [← hji]
        change r (tp.toOpenPartialHomeomorph.symm (q y, (tp z).2)) = y
        rw [← hz]
        exact congrArg r (tp.symm_apply_mk_proj hzsrc)
      have hdis : Pairwise (Disjoint on S) := by
        intro i j hij
        rw [onFun, disjoint_left]
        rintro y ⟨u, hu⟩ ⟨v, hv⟩
        have huv : u = v := Subtype.ext (by
          have heq := congrArg q (hu.trans hv.symm)
          simpa only [hσproj] using heq)
        have hσij : σ (κ i) = σ (κ j) := hσeq (κ i) (κ j) u (by rw [← huv] at hv; exact hu.trans hv.symm)
        apply hij
        apply Subtype.ext
        rw [← hσbase i, ← hσbase j, hσij]
      have hopen : ∀ i {V}, V ⊆ W → (IsOpen V ↔ IsOpen (q ⁻¹' V ∩ S i)) := by
        intro i V hVW
        constructor
        · intro hV
          exact (hV.preimage hq.continuous).inter (hSo i)
        · intro hV
          have himg : q '' (q ⁻¹' V ∩ S i) = V := by
            apply Subset.antisymm
            · rintro _ ⟨y, hy, rfl⟩
              exact hy.1
            · intro w hw
              obtain ⟨y, hy, hqy⟩ := hsurj i (hVW hw)
              exact ⟨y, ⟨by rw [mem_preimage, hqy]; exact hw, hy⟩, hqy⟩
          rw [← himg]
          exact hq.isOpenMap _ hV
      exact IsEvenlyCovered.of_trivialization
        (t := IsOpen.trivializationDiscrete S W hWo hopen hinj hsurj hdis hexhaust) hbW

/-- A Hausdorff intermediate space automatically supplies the required fiber separation. -/
theorem isCoveringMap_of_comp_right [TopologicalSpace E] [TopologicalSpace Y]
    [TopologicalSpace B] [T2Space Y] [LocallyConnectedSpace B]
    {r : E → Y} {q : Y → B} (hp : IsCoveringMap (q ∘ r))
    (hr : IsLocalHomeomorph r) (hrsurj : Surjective r) : IsCoveringMap q :=
  isCoveringMap_of_comp_right_of_isSeparatedMap hp hr hrsurj (T2Space.isSeparatedMap q)

end GaloisForLFunctions.HTGeometry
