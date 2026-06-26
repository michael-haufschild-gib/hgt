/-
# A proper local homeomorphism is a covering map

Mathlib has **no** argument principle, **no** winding number, and **no** "proper local
homeomorphism ⟹ covering map" bridge.  The modular-`λ` univalence (and any holomorphic degree
count) rests on exactly this general-topology fact, so we build it here from scratch.

This file establishes the structural inputs:
* `IsLocalHomeomorph.exists_injOn_nhds` — local injectivity;
* `IsLocalHomeomorph.discreteTopology_fibre` — fibres of a local homeo are discrete;
* `fibre_finite` — a proper local homeo has finite fibres (compact + discrete);
* `exists_pairwise_disjoint_nhds` — finitely many points of a T2 space have pairwise-disjoint
  open neighbourhoods (the disjointification used to build the trivialisation).

The trivialisation assembly (`IsEvenlyCovered`) is built on top of these.
-/
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff
import GaloisForLFunctions.Bottcher.ProperCovering

open Topology Set

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- Local injectivity: every point of a local homeomorphism has an open neighbourhood on which
`f` is injective. -/
theorem IsLocalHomeomorph.exists_injOn_nhds {f : E → X} (hloc : IsLocalHomeomorph f) (e : E) :
    ∃ U : Set E, IsOpen U ∧ e ∈ U ∧ Set.InjOn f U := by
  obtain ⟨g, hg, hfg⟩ := hloc e
  refine ⟨g.source, g.open_source, hg, fun a ha b hb hab => ?_⟩
  apply g.injOn ha hb
  rw [← hfg]; exact hab

/-- The fibre of a local homeomorphism is discrete. -/
theorem IsLocalHomeomorph.discreteTopology_fibre {f : E → X} (hloc : IsLocalHomeomorph f) (x : X) :
    DiscreteTopology (f ⁻¹' {x}) := by
  rw [discreteTopology_subtype_iff]
  intro e he
  obtain ⟨U, hU, heU, hinj⟩ := hloc.exists_injOn_nhds e
  rw [Filter.inf_principal_eq_bot]
  have hsub : {e}ᶜ ∩ U ⊆ (f ⁻¹' {x})ᶜ := by
    rintro y ⟨hyne, hyU⟩ hyf
    simp only [mem_preimage, mem_singleton_iff] at hyf he
    exact hyne (hinj hyU heU (hyf.trans he.symm))
  exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (hU.mem_nhds heU)) hsub

/-- A proper local homeomorphism has finite fibres (compact + discrete ⟹ finite). -/
theorem fibre_finite {f : E → X} (hloc : IsLocalHomeomorph f) (hprop : IsProperMap f) (x : X) :
    Finite (f ⁻¹' {x}) := by
  have hc : CompactSpace (f ⁻¹' {x}) :=
    isCompact_iff_compactSpace.mp (hprop.isCompact_preimage isCompact_singleton)
  have hd := hloc.discreteTopology_fibre x
  exact finite_of_compact_of_discrete

/-- Finitely many points of a T2 space have pairwise-disjoint open neighbourhoods. -/
theorem exists_pairwise_disjoint_nhds [T2Space E] (s : Finset E) :
    ∃ D : E → Set E, (∀ e ∈ s, IsOpen (D e) ∧ e ∈ D e) ∧
      (↑s : Set E).Pairwise (fun a b => Disjoint (D a) (D b)) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => univ, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨D, hD, hDpair⟩ := ih
    let P : E → Prop := fun e => ∃ uv : Set E × Set E,
      IsOpen uv.1 ∧ IsOpen uv.2 ∧ a ∈ uv.1 ∧ e ∈ uv.2 ∧ Disjoint uv.1 uv.2
    have hPe : ∀ e ∈ s, P e := fun e he => by
      obtain ⟨u, v, hu, hv, hau, hev, huv⟩ := t2_separation (show a ≠ e from fun h => ha (h ▸ he))
      exact ⟨(u, v), hu, hv, hau, hev, huv⟩
    let sep : E → Set E × Set E := fun e => if h : P e then h.choose else (univ, ∅)
    have hsep : ∀ e ∈ s, IsOpen (sep e).1 ∧ IsOpen (sep e).2 ∧ a ∈ (sep e).1 ∧
        e ∈ (sep e).2 ∧ Disjoint (sep e).1 (sep e).2 := fun e he => by
      have hp : P e := hPe e he
      simp only [sep, dif_pos hp]; exact hp.choose_spec
    refine ⟨fun x => if x = a then (⋂ e ∈ s, (sep e).1) else D x ∩ (sep x).2, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | hes
      · refine ⟨?_, ?_⟩
        · simp only [if_pos rfl]; exact isOpen_biInter_finset (fun i hi => (hsep i hi).1)
        · simp only [if_pos rfl]; exact mem_iInter₂.mpr (fun i hi => (hsep i hi).2.2.1)
      · have hea : e ≠ a := fun h => ha (h ▸ hes)
        simp only [if_neg hea]
        exact ⟨(hD e hes).1.inter (hsep e hes).2.1, (hD e hes).2, (hsep e hes).2.2.2.1⟩
    · have key : ∀ p ∈ s, Disjoint (⋂ e ∈ s, (sep e).1) (D p ∩ (sep p).2) := fun p hp =>
        Disjoint.mono (iInter₂_subset p hp) inter_subset_right (hsep p hp).2.2.2.2
      intro x hx y hy hxy
      simp only [Finset.coe_insert, mem_insert_iff] at hx hy
      rcases hx with hxa | hxs
      · subst hxa
        rcases hy with hya | hys
        · exact absurd hya.symm hxy
        · have hya : y ≠ x := fun h => ha (h ▸ hys)
          simp only [if_pos rfl, if_neg hya]; exact key y hys
      · have hxa : x ≠ a := fun h => ha (h ▸ hxs)
        rcases hy with hya | hys
        · subst hya
          simp only [if_pos rfl, if_neg hxa]; exact (key x hxs).symm
        · have hya : y ≠ a := fun h => ha (h ▸ hys)
          simp only [if_neg hxa, if_neg hya]
          exact Disjoint.mono inter_subset_left inter_subset_left (hDpair hxs hys hxy)

/-- **A proper local homeomorphism with T2 source is a covering map.** -/
theorem isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    {f : E → X} (hloc : IsLocalHomeomorph f) (hprop : IsProperMap f) :
    IsCoveringMap f := by
  intro x
  refine ⟨hloc.discreteTopology_fibre x, ?_⟩
  classical
  -- charts at every point (total via choice)
  set g : E → OpenPartialHomeomorph E X := fun e => (hloc e).choose with hg
  have hg1 : ∀ e, e ∈ (g e).source := fun e => (hloc e).choose_spec.1
  have hg2 : ∀ e, f = (g e) := fun e => (hloc e).choose_spec.2
  -- fibre as a finset
  have hfin : (f ⁻¹' {x}).Finite := Set.finite_coe_iff.mp (fibre_finite hloc hprop x)
  -- pairwise disjoint nbhds of the fibre points
  obtain ⟨D, hD, hDpair⟩ := exists_pairwise_disjoint_nhds hfin.toFinset
  -- "good" open around each fibre point e:  O e = source ∩ D e (open, contains e, f injective)
  set O : E → Set E := fun e => (g e).source ∩ D e with hO
  have hOopen : ∀ e ∈ f ⁻¹' {x}, IsOpen (O e) := fun e he =>
    (g e).open_source.inter (hD e (hfin.mem_toFinset.mpr he)).1
  have hOmem : ∀ e ∈ f ⁻¹' {x}, e ∈ O e := fun e he =>
    ⟨hg1 e, (hD e (hfin.mem_toFinset.mpr he)).2⟩
  -- f maps e to x; the chart inverse sends x back to e
  have hfe : ∀ e ∈ f ⁻¹' {x}, f e = x := fun e he => he
  have hsymm_x : ∀ e ∈ f ⁻¹' {x}, (g e).symm x = e := fun e he => by
    have hx : (g e) e = x := by rw [← hg2 e]; exact hfe e he
    rw [← hx, (g e).left_inv (hg1 e)]
  -- neighbourhood of x on which the section for e maps into O e
  set V : E → Set X := fun e => (g e).target ∩ ↑(g e).symm ⁻¹' (O e) with hV
  have hxtarget : ∀ e ∈ f ⁻¹' {x}, x ∈ (g e).target := fun e he => by
    have hx : (g e) e = x := by rw [← hg2 e]; exact hfe e he
    rw [← hx]; exact (g e).map_source (hg1 e)
  have hVopen : ∀ e ∈ f ⁻¹' {x}, IsOpen (V e) := fun e he =>
    (g e).continuousOn_symm.isOpen_inter_preimage (g e).open_target (hOopen e he)
  have hxV : ∀ e ∈ f ⁻¹' {x}, x ∈ V e := fun e he =>
    ⟨hxtarget e he, by simp only [mem_preimage, hsymm_x e he]; exact hOmem e he⟩
  -- finite intersection W₀
  set W₀ : Set X := ⋂ e ∈ hfin.toFinset, V e with hW₀
  have hW₀open : IsOpen W₀ := isOpen_biInter_finset (fun e he => hVopen e (hfin.mem_toFinset.mp he))
  have hxW₀ : x ∈ W₀ := mem_iInter₂.mpr (fun e he => hxV e (hfin.mem_toFinset.mp he))
  -- shrink so that f⁻¹(W) lands in the union of the good opens
  have hfibsub : f ⁻¹' {x} ⊆ ⋃ e ∈ hfin.toFinset, O e := fun p hp =>
    mem_iUnion₂.mpr ⟨p, hfin.mem_toFinset.mpr hp, hOmem p hp⟩
  obtain ⟨W₁, hW₁nhds, hW₁sub⟩ := Bottcher.exists_nhds_preimage_subset hprop.isClosedMap
    (isOpen_biUnion (fun e he => hOopen e (hfin.mem_toFinset.mp he))) hfibsub
  set W : Set X := W₀ ∩ interior W₁ with hW
  have hWopen : IsOpen W := hW₀open.inter isOpen_interior
  have hxW : x ∈ W := ⟨hxW₀, mem_interior_iff_mem_nhds.mpr hW₁nhds⟩
  have hWsubV : ∀ e ∈ f ⁻¹' {x}, W ⊆ V e := fun e he =>
    (inter_subset_left.trans (biInter_subset_of_mem (hfin.mem_toFinset.mpr he)))
  have hWsubW₁ : W ⊆ W₁ := inter_subset_right.trans interior_subset
  have hpreW : f ⁻¹' W ⊆ ⋃ e ∈ hfin.toFinset, O e :=
    (preimage_mono hWsubW₁).trans hW₁sub
  -- section facts
  have hsec_mem : ∀ e ∈ f ⁻¹' {x}, ∀ w ∈ W, (g e).symm w ∈ O e := fun e he w hw =>
    (hWsubV e he hw).2
  have hsec_f : ∀ e ∈ f ⁻¹' {x}, ∀ w ∈ W, f ((g e).symm w) = w := fun e he w hw => by
    rw [hg2 e]; exact (g e).right_inv (hWsubV e he hw).1
  -- the (unique) sheet label of a preimage point
  have hlabel : ∀ p ∈ f ⁻¹' W, ∃! e : ↥(f ⁻¹' {x}), p ∈ O (e : E) := by
    intro p hp
    obtain ⟨e, hetoF, hpe⟩ := mem_iUnion₂.mp (hpreW hp)
    refine ⟨⟨e, hfin.mem_toFinset.mp hetoF⟩, hpe, ?_⟩
    rintro ⟨e', he'⟩ hpe'
    by_contra hne
    have hee : e' ≠ e := fun h => hne (Subtype.ext h)
    exact (hDpair (Finset.mem_coe.mpr (hfin.mem_toFinset.mpr he'))
      (Finset.mem_coe.mpr hetoF) hee).le_bot ⟨hpe'.2, hpe.2⟩
  set label : ↥(f ⁻¹' W) → ↥(f ⁻¹' {x}) := fun p => (hlabel p p.2).exists.choose with hlab
  have hlabel_mem : ∀ p : ↥(f ⁻¹' W), (p : E) ∈ O (label p : E) := fun p =>
    (hlabel p p.2).exists.choose_spec
  -- the chart-section lands back in f⁻¹W
  have hinvmem : ∀ (w : ↥W) (e : ↥(f ⁻¹' {x})), (g e).symm w ∈ f ⁻¹' W := fun w e => by
    show f ((g (e:E)).symm (w:X)) ∈ W
    rw [hsec_f (e:E) e.2 (w:X) w.2]; exact w.2
  haveI : DiscreteTopology ↥(f ⁻¹' {x}) := hloc.discreteTopology_fibre x
  -- label is continuous (each fibre {e} pulls back to the open chart O e)
  have hlabel_cont : Continuous label := by
    rw [continuous_discrete_rng]
    intro e
    have hpre : label ⁻¹' {e} = Subtype.val ⁻¹' O (e : E) := by
      ext p
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => h ▸ hlabel_mem p, fun h => (hlabel p p.2).unique (hlabel_mem p) h⟩
    rw [hpre]; exact (hOopen (e:E) e.2).preimage continuous_subtype_val
  -- the chart-section is continuous in (w, e) (e ranges over a discrete set)
  have hsec_cont : Continuous (fun q : ↥W × ↥(f ⁻¹' {x}) => ((g (q.2:E)).symm (q.1:X) : E)) := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨w, e⟩
    have hsymmAt : ContinuousAt (fun y : X => ((g (e:E)).symm y : E)) (w : X) :=
      (g (e:E)).continuousOn_symm.continuousAt
        ((g (e:E)).open_target.mem_nhds (hWsubV (e:E) e.2 w.2).1)
    have hfst : ContinuousAt (fun q : ↥W × ↥(f ⁻¹' {x}) => ((q.1 : X))) (w, e) :=
      (continuous_subtype_val.comp continuous_fst).continuousAt
    have hcomp : ContinuousAt (fun q : ↥W × ↥(f ⁻¹' {x}) => ((g (e:E)).symm (q.1:X) : E)) (w, e) :=
      hsymmAt.comp_of_eq hfst rfl
    have hsnd : ∀ᶠ q : ↥W × ↥(f ⁻¹' {x}) in 𝓝 (w, e), q.2 = e :=
      ((isOpen_discrete ({e} : Set ↥(f ⁻¹' {x}))).preimage continuous_snd).mem_nhds rfl
    refine hcomp.congr ?_
    filter_upwards [hsnd] with q hq
    simp only [hq]
  refine ⟨W, hxW, hWopen, hWopen.preimage hloc.continuous, ?_⟩
  refine ⟨{
    toFun := fun p => (⟨f p, p.2⟩, label p)
    invFun := fun q => ⟨(g q.2).symm q.1, hinvmem q.1 q.2⟩
    left_inv := fun p => by
      apply Subtype.ext
      show (g (label p)).symm (f (p:E)) = (p:E)
      rw [congrFun (hg2 (label p)) (p:E), (g (label p)).left_inv (hlabel_mem p).1]
    right_inv := fun q => by
      obtain ⟨w, e⟩ := q
      have hsmem : (g (e:E)).symm (w:X) ∈ O (e:E) := hsec_mem (e:E) e.2 (w:X) w.2
      refine Prod.ext (Subtype.ext (hsec_f (e:E) e.2 (w:X) w.2)) ?_
      exact (hlabel _ (hinvmem w e)).unique (hlabel_mem _) hsmem
    continuous_toFun := by
      apply Continuous.prodMk
      · exact ((hloc.continuous.comp continuous_subtype_val).subtype_mk _)
      · exact hlabel_cont
    continuous_invFun := (hsec_cont).subtype_mk _
  }, ?_⟩
  intro p
  rfl
