import Mathlib.Topology.Covering.Basic

open Topology Set Function Bundle

namespace Bottcher

variable {E Y B : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace B]

/-- **Left cancellation for covering maps.** If `q ∘ r` and `q` are covering maps, `r` is continuous
and surjective, `Y` is Hausdorff and `B` is locally connected, then `r` is a covering map.

This is the composition-cancellation companion of `isCoveringMap_comp` (which composes covering maps).
Mathlib has the homeomorphism-cancellation forms (`IsCoveringMap.comp_homeomorph` /
`homeomorph_comp`) but not this genuine two-covering cancellation, which is what reduces the tower of
escape-level maps `ρₙ` to a single base covering by induction (`Q ∘ ρₙ₊₁ = ρₙ`).

Construction. `r` is a local homeomorphism by `IsLocalHomeomorph.of_comp`, and each fibre `r⁻¹{y}`
embeds into `(q ∘ r)⁻¹{q y}` hence is discrete. For each `y₀` we build a `Trivialization` of `r`
over the `q`-sheet `V` through `y₀` above the connected component `W` of `tp.baseSet ∩ tq.baseSet`
(where `tp`, `tq` trivialize `q ∘ r`, `q`). The sheet family is indexed by `r⁻¹{y₀}`, one `tp`-sheet
each. The only non-formal step is the **connectivity core** `hsame`: two points on the same
`tp`-sheet over `W` land on the same `tq`-sheet, because `w ↦ (tq (r (tp.symm (w,k)))).2` is a
continuous map from the connected `W` into the discrete `q`-fibre, hence constant. -/
theorem isCoveringMap_of_comp_left [T2Space Y] [LocallyConnectedSpace B]
    {r : E → Y} {q : Y → B}
    (hqr : IsCoveringMap (q ∘ r)) (hq : IsCoveringMap q)
    (hr : Continuous r) (hrsurj : Function.Surjective r) :
    IsCoveringMap r := by
  classical
  have hrloc : IsLocalHomeomorph r :=
    IsLocalHomeomorph.of_comp hqr.isLocalHomeomorph hq.isLocalHomeomorph hr
  have hrange : IsClosed (Set.range r) := by rw [hrsurj.range_eq]; exact isClosed_univ
  -- fiber discreteness as a global instance
  haveI hdisc : ∀ y : Y, DiscreteTopology (r ⁻¹' {y}) := by
    intro y
    have hsub : r ⁻¹' {y} ⊆ (q ∘ r) ⁻¹' {q y} := by
      intro e he
      simp only [mem_preimage, mem_singleton_iff] at he ⊢
      simp [Function.comp, he]
    haveI : DiscreteTopology ((q ∘ r) ⁻¹' {q y}) := (hqr (q y)).discreteTopology_fiber
    exact (IsEmbedding.inclusion hsub).discreteTopology
  refine IsCoveringMap.mk' r (fun y => r ⁻¹' {y}) ?_ hrange
  intro y₀ _
  set e₀ : E := (hrsurj y₀).choose with he₀def
  have he₀ : r e₀ = y₀ := (hrsurj y₀).choose_spec
  set b : B := q y₀ with hbdef
  haveI hpbfib : Nonempty ((q ∘ r) ⁻¹' {b}) :=
    ⟨⟨e₀, by simp only [mem_preimage, mem_singleton_iff, Function.comp_apply, he₀, hbdef]⟩⟩
  haveI hqbfib : Nonempty (q ⁻¹' {b}) := ⟨⟨y₀, by simp only [mem_preimage, mem_singleton_iff, hbdef]⟩⟩
  set tp : Trivialization ((q ∘ r) ⁻¹' {b}) (q ∘ r) := (hqr b).toTrivialization with htpdef
  set tq : Trivialization (q ⁻¹' {b}) q := (hq b).toTrivialization with htqdef
  haveI hdtp : DiscreteTopology ((q ∘ r) ⁻¹' {b}) := (hqr b).discreteTopology_fiber
  haveI hdtq : DiscreteTopology (q ⁻¹' {b}) := (hq b).discreteTopology_fiber
  have hbtp : b ∈ tp.baseSet := (hqr b).mem_toTrivialization_baseSet
  have hbtq : b ∈ tq.baseSet := (hq b).mem_toTrivialization_baseSet
  -- connected base W in B
  set W : Set B := connectedComponentIn (tp.baseSet ∩ tq.baseSet) b with hWdef
  have hbW : b ∈ W := mem_connectedComponentIn ⟨hbtp, hbtq⟩
  have hWopen : IsOpen W := (tp.open_baseSet.inter tq.open_baseSet).connectedComponentIn
  have hWconn : IsConnected W := isConnected_connectedComponentIn_iff.mpr ⟨hbtp, hbtq⟩
  have hWsub : W ⊆ tp.baseSet ∩ tq.baseSet := connectedComponentIn_subset _ _
  -- q-sheet index of y₀
  have hy₀src : y₀ ∈ tq.source := by
    rw [tq.source_eq]; exact hbtq
  set j₀ : q ⁻¹' {b} := (tq y₀).2 with hj₀def
  -- base V : the q-sheet over W through y₀
  set V : Set Y := {y | q y ∈ W ∧ y ∈ tq.source ∧ (tq y).2 = j₀} with hVdef
  -- sheet family for r, indexed by the fiber r⁻¹{y₀}
  set U : (r ⁻¹' {y₀}) → Set E :=
    fun i => {e | (q ∘ r) e ∈ W ∧ e ∈ tp.source ∧ (tp e).2 = (tp (i : E)).2} with hUdef
  haveI : Nonempty E := ⟨e₀⟩
  haveI : Nonempty (r ⁻¹' {y₀}) := ⟨⟨e₀, by simp only [mem_preimage, mem_singleton_iff, he₀]⟩⟩
  have hfibsrc : ∀ i : (r ⁻¹' {y₀}), (i : E) ∈ tp.source := by
    intro i
    rw [tp.mem_source]
    have hi : (q ∘ r) (i : E) = b := by
      have : r (i : E) = y₀ := i.2
      simp only [Function.comp_apply, this, hbdef]
    rw [hi]; exact hbtp
  have hfibfst : ∀ i : (r ⁻¹' {y₀}), (tp (i : E)).1 = b := by
    intro i
    rw [tp.coe_fst (hfibsrc i)]
    have : r (i : E) = y₀ := i.2
    simp only [Function.comp_apply, this, hbdef]
  have hUopen : ∀ i : (r ⁻¹' {y₀}), IsOpen (U i) := by
    intro i
    have hsheq : {e | e ∈ tp.source ∧ (tp e).2 = (tp (i:E)).2}
        = tp.source ∩ (fun e => (tp e).2) ⁻¹' {(tp (i:E)).2} := by ext e; simp [Set.mem_setOf_eq]
    have hsheet : IsOpen {e | e ∈ tp.source ∧ (tp e).2 = (tp (i:E)).2} := by
      rw [hsheq]
      exact (continuous_snd.comp_continuousOn tp.continuousOn_toFun).isOpen_inter_preimage
        tp.open_source (isOpen_discrete _)
    have : U i = ((q ∘ r) ⁻¹' W) ∩ {e | e ∈ tp.source ∧ (tp e).2 = (tp (i:E)).2} := by
      ext e; simp only [hUdef, mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [this]
    exact (hWopen.preimage (hq.continuous.comp hr)).inter hsheet
  -- connectivity core lemmas (before assembling the trivialization)
  have hWbase : W ⊆ tp.baseSet := fun w hw => (hWsub hw).1
  have hWbaseq : W ⊆ tq.baseSet := fun w hw => (hWsub hw).2
  have hy0V : y₀ ∈ V := ⟨by rw [← hbdef]; exact hbW, hy₀src, rfl⟩
  -- KEY: same tp-sheet over W ⟹ same tq-sheet index (continuous map into discrete over connected W)
  have hsame : ∀ e e' : E, e ∈ tp.source → e' ∈ tp.source →
      (q ∘ r) e ∈ W → (q ∘ r) e' ∈ W → (tp e).2 = (tp e').2 →
      (tq (r e)).2 = (tq (r e')).2 := by
    intro e e' hes hes' hew hew' hidx
    set sec : B → E := fun w => tp.toOpenPartialHomeomorph.symm (w, (tp e).2) with hsecdef
    have hsecproj : ∀ w ∈ W, q (r (sec w)) = w := fun w hw => tp.proj_symm_apply' (hWbase hw)
    have hrsecsrc : ∀ w ∈ W, r (sec w) ∈ tq.source := by
      intro w hw; rw [tq.mem_source, hsecproj w hw]; exact hWbaseq hw
    set G : B → (q ⁻¹' {b}) := fun w => (tq (r (sec w))).2 with hGdef
    have hsec_cont : ContinuousOn sec W := by
      apply tp.toOpenPartialHomeomorph.continuousOn_symm.comp (Continuous.continuousOn (by fun_prop))
      intro w hw; rw [tp.mem_target]; exact hWbase hw
    have hGcont : ContinuousOn G W :=
      continuous_snd.comp_continuousOn
        (tq.continuousOn_toFun.comp (hr.comp_continuousOn hsec_cont)
          (fun w hw => hrsecsrc w hw))
    have hesec : sec ((q ∘ r) e) = e := tp.symm_apply_mk_proj hes
    have hesec' : sec ((q ∘ r) e') = e' := by
      show tp.toOpenPartialHomeomorph.symm ((q ∘ r) e', (tp e).2) = e'
      rw [hidx]; exact tp.symm_apply_mk_proj hes'
    have hconst : G ((q ∘ r) e) = G ((q ∘ r) e') :=
      (hWconn.isPreconnected.image G hGcont).subsingleton
        (mem_image_of_mem G hew) (mem_image_of_mem G hew')
    have hGe : G ((q ∘ r) e) = (tq (r e)).2 := by
      show (tq (r (sec ((q ∘ r) e)))).2 = (tq (r e)).2; rw [hesec]
    have hGe' : G ((q ∘ r) e') = (tq (r e')).2 := by
      show (tq (r (sec ((q ∘ r) e')))).2 = (tq (r e')).2; rw [hesec']
    rw [← hGe, ← hGe']; exact hconst
  -- q is injective on the q-sheet V
  have hqinjV : ∀ y ∈ V, ∀ y' ∈ V, q y = q y' → y = y' := by
    intro y hy y' hy' hqyy
    have hf1 : (tq y).1 = (tq y').1 := by rw [tq.coe_fst hy.2.1, tq.coe_fst hy'.2.1, hqyy]
    have hf2 : (tq y).2 = (tq y').2 := by rw [hy.2.2, hy'.2.2]
    exact tq.injOn hy.2.1 hy'.2.1 (Prod.ext hf1 hf2)
  -- each U-sheet maps into V under r
  have hUiV : ∀ (i : r ⁻¹' {y₀}) (e : E), e ∈ U i → r e ∈ V := by
    intro i e he
    have hiy : r (i : E) = y₀ := i.2
    have hiW : (q ∘ r) (i : E) ∈ W := by show q (r (i:E)) ∈ W; rw [hiy, ← hbdef]; exact hbW
    have hsm : (tq (r e)).2 = (tq (r (i:E))).2 := hsame e (i:E) he.2.1 (hfibsrc i) he.1 hiW he.2.2
    have hidxj : (tq (r e)).2 = j₀ := by rw [hsm, hiy]
    have hrsrc : r e ∈ tq.source := by rw [tq.mem_source]; exact hWbaseq he.1
    exact ⟨he.1, hrsrc, hidxj⟩
  -- surjectivity of r from each U-sheet onto V
  have hsurjOn : ∀ i : r ⁻¹' {y₀}, (U i).SurjOn r V := by
    intro i v hv
    have hqvW : q v ∈ W := hv.1
    have hqvbase : q v ∈ tp.baseSet := hWbase hqvW
    set ev : E := tp.toOpenPartialHomeomorph.symm (q v, (tp (i:E)).2) with hevdef
    have hproj : (q ∘ r) ev = q v := tp.proj_symm_apply' hqvbase
    have happ : tp ev = (q v, (tp (i:E)).2) := tp.apply_symm_apply' hqvbase
    have hevU : ev ∈ U i := ⟨by show (q∘r) ev ∈ W; rw [hproj]; exact hqvW,
      by rw [tp.mem_source, hproj]; exact hqvbase, by rw [happ]⟩
    exact ⟨ev, hevU, hqinjV (r ev) (hUiV i ev hevU) v hv hproj⟩
  refine ⟨IsOpen.trivializationDiscrete U V ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · -- V open
    have hsheq : {y | y ∈ tq.source ∧ (tq y).2 = j₀}
        = tq.source ∩ (fun y => (tq y).2) ⁻¹' {j₀} := by ext y; simp [Set.mem_setOf_eq]
    have hsheet : IsOpen {y | y ∈ tq.source ∧ (tq y).2 = j₀} := by
      rw [hsheq]
      exact (continuous_snd.comp_continuousOn tq.continuousOn_toFun).isOpen_inter_preimage
        tq.open_source (isOpen_discrete {j₀})
    have hVeq : V = (q ⁻¹' W) ∩ {y | y ∈ tq.source ∧ (tq y).2 = j₀} := by
      ext y; simp only [hVdef, mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [hVeq]
    exact (hWopen.preimage hq.continuous).inter hsheet
  · -- open_iff
    intro i W' hW'V
    constructor
    · intro hW'open
      exact (hW'open.preimage hr).inter (hUopen i)
    · intro hpre
      have himg : r '' (r ⁻¹' W' ∩ U i) = W' := by
        apply Set.Subset.antisymm
        · rintro y ⟨e, ⟨heW', _⟩, rfl⟩; exact heW'
        · intro y hy
          obtain ⟨e, heU, hre⟩ := hsurjOn i (hW'V hy)
          exact ⟨e, ⟨by rw [Set.mem_preimage, hre]; exact hy, heU⟩, hre⟩
      rw [← himg]
      exact hrloc.isOpenMap _ hpre
  · -- inj on U i
    intro i e he e' he' hree
    have h1 : (tp e).1 = (tp e').1 := by
      rw [tp.coe_fst he.2.1, tp.coe_fst he'.2.1]; simp only [Function.comp_apply, hree]
    have h2 : (tp e).2 = (tp e').2 := by rw [he.2.2, he'.2.2]
    exact tp.injOn he.2.1 he'.2.1 (Prod.ext h1 h2)
  · -- surj U i onto V
    exact hsurjOn
  · -- pairwise disjoint
    intro i i' hii'
    rw [Function.onFun, Set.disjoint_left]
    rintro e ⟨_, _, hei⟩ ⟨_, _, hei'⟩
    apply hii'
    have hidx : (tp (i:E)).2 = (tp (i':E)).2 := by rw [← hei, hei']
    exact Subtype.ext (tp.injOn (hfibsrc i) (hfibsrc i') (Prod.ext ((hfibfst i).trans (hfibfst i').symm) hidx))
  · -- exhaustive
    intro e he
    have hreV : r e ∈ V := he
    have heW : (q ∘ r) e ∈ W := hreV.1
    have hes : e ∈ tp.source := by rw [tp.mem_source]; exact hWbase heW
    set ipt : E := tp.toOpenPartialHomeomorph.symm (b, (tp e).2) with hiptdef
    have hiproj : (q ∘ r) ipt = b := tp.proj_symm_apply' hbtp
    have hiapp : tp ipt = (b, (tp e).2) := tp.apply_symm_apply' hbtp
    have hipts : ipt ∈ tp.source := by rw [tp.mem_source, hiproj]; exact hbtp
    have hidxeq : (tp e).2 = (tp ipt).2 := by rw [hiapp]
    have hiptW : (q ∘ r) ipt ∈ W := by rw [hiproj]; exact hbW
    have hsm : (tq (r e)).2 = (tq (r ipt)).2 := hsame e ipt hes hipts heW hiptW hidxeq
    have hqript : q (r ipt) = b := hiproj
    have hiptidx : (tq (r ipt)).2 = j₀ := by rw [← hsm]; exact hreV.2.2
    have hiptsrc : r ipt ∈ tq.source := by rw [tq.mem_source, hqript]; exact hbtq
    have hriptV : r ipt ∈ V := ⟨by rw [hqript]; exact hbW, hiptsrc, hiptidx⟩
    have hripty0 : r ipt = y₀ := hqinjV (r ipt) hriptV y₀ hy0V (by rw [hqript, hbdef])
    refine Set.mem_iUnion.mpr ⟨⟨ipt, hripty0⟩, ?_⟩
    exact ⟨heW, hes, hidxeq⟩
  · -- y₀ ∈ baseSet (= V)
    show y₀ ∈ V
    exact ⟨by rw [← hbdef]; exact hbW, hy₀src, rfl⟩

end Bottcher
