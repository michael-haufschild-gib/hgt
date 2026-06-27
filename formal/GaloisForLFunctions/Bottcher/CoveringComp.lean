import Mathlib
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering
open Topology
namespace Bottcher
variable {E Y Z : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace Z]
theorem isCoveringMap_comp {f : E → Y} {g : Y → Z} (hf : IsCoveringMap f) (hg : IsCoveringMap g)
    (hfin : ∀ z, (g ⁻¹' {z}).Finite) : IsCoveringMap (g ∘ f) := by
  intro z
  obtain ⟨hJdisc, U, hzU, hUo, hgUo, Hg, hHg⟩ := hg z
  haveI : Finite (g ⁻¹' {z}) := hfin z
  set yj : (g ⁻¹' {z}) → Y := fun j => (Hg.symm (⟨z, hzU⟩, j) : g ⁻¹' U) with hyj
  have hg_yj : ∀ j, g (yj j) = z := by
    intro j; have := hHg (Hg.symm (⟨z, hzU⟩, j)); rw [Homeomorph.apply_symm_apply] at this; exact this.symm
  choose hKdisc V hyjV hVo hfVo Hf hHf using fun j => hf (yj j)
  set sheet : ↥U → (g ⁻¹' {z}) → Y := fun u j => (Hg.symm (u, j) : g ⁻¹' U) with hsheet
  set W' : Set ↥U := {u | ∀ j, sheet u j ∈ V j} with hW'
  set W : Set Z := Subtype.val '' W' with hW
  have hWU : W ⊆ U := by rintro w ⟨u, _, rfl⟩; exact u.2
  have hzW' : (⟨z, hzU⟩ : ↥U) ∈ W' := fun j => by show (Hg.symm (⟨z,hzU⟩, j) : g⁻¹'U).1 ∈ V j; exact hyjV j
  have hsheet_recover : ∀ (y : Y) (hy : y ∈ g ⁻¹' U), sheet ⟨g y, hy⟩ (Hg ⟨y, hy⟩).2 = y := by
    intro y hy
    have h2 : (Hg ⟨y, hy⟩).1 = (⟨g y, hy⟩ : ↥U) := Subtype.ext (hHg ⟨y, hy⟩)
    show (Hg.symm (⟨g y, hy⟩, (Hg ⟨y, hy⟩).2) : g ⁻¹' U).1 = y
    rw [← h2, Prod.mk.eta, Homeomorph.symm_apply_apply]
  have hW'mem : ∀ (w : Z) (hw : w ∈ W), (⟨w, hWU hw⟩ : ↥U) ∈ W' := by
    rintro w ⟨u, hu, rfl⟩ ; simpa using hu
  -- FORWARD fibre index + coord
  set idx : ↥((g ∘ f) ⁻¹' W) → (g ⁻¹' {z}) := fun e => (Hg ⟨f ↑e, hWU e.2⟩).2 with hidx
  have hmemV : ∀ e : ↥((g ∘ f) ⁻¹' W), f ↑e ∈ V (idx e) := by
    intro e
    have hrec : sheet ⟨g (f ↑e), hWU e.2⟩ (idx e) = f ↑e := hsheet_recover (f ↑e) (hWU e.2)
    have := (hW'mem (g (f ↑e)) e.2) (idx e); rwa [hrec] at this
  set toFibE : ↥((g ∘ f) ⁻¹' W) → E := fun e =>
    ((Hf (idx e)).symm (⟨yj (idx e), hyjV (idx e)⟩, (Hf (idx e) ⟨↑e, hmemV e⟩).2)) with htoFibE
  have htoFib_f : ∀ e, f (toFibE e) = yj (idx e) := by
    intro e
    have := hHf (idx e) ((Hf (idx e)).symm (⟨yj (idx e), hyjV (idx e)⟩, (Hf (idx e) ⟨↑e, hmemV e⟩).2))
    rw [Homeomorph.apply_symm_apply] at this; exact this.symm
  have htoFib_mem : ∀ e, (g ∘ f) (toFibE e) = z := fun e => by
    show g (f (toFibE e)) = z; rw [htoFib_f, hg_yj]
  -- BACKWARD: fibre index of a fibre point + reconstruction over w
  have hfibU : ∀ ef : ↥((g ∘ f) ⁻¹' {z}), f ↑ef ∈ g ⁻¹' U := by
    intro ef; show g (f ↑ef) ∈ U; have : g (f ↑ef) = z := ef.2; rw [this]; exact hzU
  set fibIdx : ↥((g ∘ f) ⁻¹' {z}) → (g ⁻¹' {z}) := fun ef => (Hg ⟨f ↑ef, hfibU ef⟩).2 with hfibIdx
  have hfibMemV : ∀ ef, f ↑ef ∈ V (fibIdx ef) := by
    intro ef
    have hgef : g (f ↑ef) = z := ef.2
    have hrec : sheet ⟨g (f ↑ef), hfibU ef⟩ (fibIdx ef) = f ↑ef := hsheet_recover (f ↑ef) (hfibU ef)
    have hmem : (⟨g (f ↑ef), hfibU ef⟩ : ↥U) = ⟨z, hzU⟩ := Subtype.ext hgef
    have := hzW' (fibIdx ef); rw [← hmem] at this; rwa [hrec] at this
  set invE : ↥W → ↥((g ∘ f) ⁻¹' {z}) → E := fun w ef =>
    ((Hf (fibIdx ef)).symm
      (⟨(Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef) : g ⁻¹' U), by
          have : (Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef) : g ⁻¹' U).1 = sheet ⟨↑w, hWU w.2⟩ (fibIdx ef) := rfl
          rw [this]; exact (hW'mem ↑w w.2) (fibIdx ef)⟩,
       (Hf (fibIdx ef) ⟨↑ef, hfibMemV ef⟩).2)) with hinvE
  have hgen_f : ∀ (j) (X : ↥(V j) × ↥(f ⁻¹' {yj j})), f ↑((Hf j).symm X) = ↑X.1 := fun j X => by
    have := hHf j ((Hf j).symm X); rw [Homeomorph.apply_symm_apply] at this; exact this.symm
  have hinvE_f : ∀ w ef, f (invE w ef) = (Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef) : g ⁻¹' U) := by
    intro w ef; exact hgen_f (fibIdx ef) _
  have hinvE_mem : ∀ w ef, (g ∘ f) (invE w ef) ∈ W := by
    intro w ef
    show g (f (invE w ef)) ∈ W
    rw [hinvE_f]
    have : g ((Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef) : g ⁻¹' U) : Y) = ↑w := by
      have := hHg (Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef)); rw [Homeomorph.apply_symm_apply] at this; exact this.symm
    rw [this]; exact w.2
  -- index matches under the round trip
  have hfibIdx_toFib : ∀ e, fibIdx ⟨toFibE e, htoFib_mem e⟩ = idx e := by
    intro e
    have heq : (⟨f (toFibE e), hfibU ⟨toFibE e, htoFib_mem e⟩⟩ : ↥(g ⁻¹' U))
        = Hg.symm (⟨z, hzU⟩, idx e) := by
      apply Subtype.ext
      show f (toFibE e) = (Hg.symm (⟨z, hzU⟩, idx e) : g ⁻¹' U).1
      rw [htoFib_f]
    show (Hg ⟨f (toFibE e), hfibU ⟨toFibE e, htoFib_mem e⟩⟩).2 = idx e
    rw [heq, Homeomorph.apply_symm_apply]
  -- general symm round-trip projection (val of Hf.symm composed back)
  have hgen_proj : ∀ (j) (X : ↥(V j) × ↥(f ⁻¹' {yj j})), Hf j ((Hf j).symm X) = X :=
    fun j X => Homeomorph.apply_symm_apply _ _
  -- the V-coordinate over w reconstructs f e (key for left-inverse)
  have hPval : ∀ e : ↥((g ∘ f) ⁻¹' W),
      (Hg.symm (⟨g (f ↑e), hWU e.2⟩, fibIdx ⟨toFibE e, htoFib_mem e⟩) : g ⁻¹' U).1 = f ↑e := by
    intro e
    rw [hfibIdx_toFib e]
    exact hsheet_recover (f ↑e) (hWU e.2)
  -- coordinate match at idx e (avoids fibIdx under symm)
  have hcoord : ∀ (e : ↥((g ∘ f) ⁻¹' W)) (h1 : ↑e ∈ f ⁻¹' V (idx e)) (h2 : toFibE e ∈ f ⁻¹' V (idx e)),
      (Hf (idx e) ⟨toFibE e, h2⟩).2 = (Hf (idx e) ⟨↑e, h1⟩).2 := by
    intro e h1 h2
    have key : (⟨toFibE e, h2⟩ : ↥(f ⁻¹' V (idx e)))
        = (Hf (idx e)).symm (⟨yj (idx e), hyjV _⟩, (Hf (idx e) ⟨↑e, hmemV e⟩).2) := Subtype.ext rfl
    rw [key, Homeomorph.apply_symm_apply]
  -- LEFT INVERSE
  have hleft : ∀ e : ↥((g ∘ f) ⁻¹' W),
      invE ⟨g (f ↑e), e.2⟩ ⟨toFibE e, htoFib_mem e⟩ = ↑e := by
    intro e
    set ef : ↥((g ∘ f) ⁻¹' {z}) := ⟨toFibE e, htoFib_mem e⟩ with hef
    have hji : fibIdx ef = idx e := hfibIdx_toFib e
    have hmem2 : ↑e ∈ f ⁻¹' V (fibIdx ef) := by rw [hji]; exact hmemV e
    have hmemV' : ↑e ∈ f ⁻¹' V (idx e) := hmemV e
    have htf' : toFibE e ∈ f ⁻¹' V (idx e) := by have h := hfibMemV ef; rw [hji] at h; exact h
    -- show the symm-argument equals Hf(fibIdx ef)⟨↑e,_⟩
    have hpair : ((⟨(Hg.symm (⟨g (f ↑e), hWU (⟨g (f ↑e), e.2⟩ : ↥W).2⟩, fibIdx ef) : g ⁻¹' U),
          by show (Hg.symm _ : g ⁻¹' U).1 ∈ V (fibIdx ef); rw [hPval e]; rw [hji]; exact hmemV e⟩
          : ↥(V (fibIdx ef))), (Hf (fibIdx ef) ⟨↑ef, hfibMemV ef⟩).2)
        = Hf (fibIdx ef) ⟨↑e, hmem2⟩ := by
      refine Prod.ext ?_ ?_
      · apply Subtype.ext
        show (Hg.symm _ : g ⁻¹' U).1 = ↑(Hf (fibIdx ef) ⟨↑e, hmem2⟩).1
        rw [hPval e, ← hHf (fibIdx ef) ⟨↑e, hmem2⟩]
      · show (Hf (fibIdx ef) ⟨↑ef, hfibMemV ef⟩).2 = (Hf (fibIdx ef) ⟨↑e, hmem2⟩).2
        suffices h : ∀ (j : g ⁻¹' {z}) (_ : j = idx e) (h1 : toFibE e ∈ f ⁻¹' V j)
            (h2 : ↑e ∈ f ⁻¹' V j), (Hf j ⟨toFibE e, h1⟩).2 = (Hf j ⟨↑e, h2⟩).2 by
          exact h (fibIdx ef) hji (hfibMemV ef) hmem2
        intro j hj h1 h2
        subst hj
        have key : (⟨toFibE e, h1⟩ : ↥(f ⁻¹' V (idx e)))
            = (Hf (idx e)).symm (⟨yj (idx e), hyjV _⟩, (Hf (idx e) ⟨↑e, hmemV e⟩).2) :=
          Subtype.ext rfl
        rw [key, Homeomorph.apply_symm_apply]
    simp only [hinvE]
    rw [hpair, Homeomorph.symm_apply_apply]
  -- f of a z-fibre point is the sheet point over z
  have hffef : ∀ ef : ↥((g ∘ f) ⁻¹' {z}), f ↑ef = yj (fibIdx ef) := by
    intro ef
    have hrec := hsheet_recover (f ↑ef) (hfibU ef)
    have hez : (⟨g (f ↑ef), hfibU ef⟩ : ↥U) = ⟨z, hzU⟩ := Subtype.ext ef.2
    rw [hez] at hrec
    exact hrec.symm
  -- index of a reconstructed point
  have hidxe' : ∀ (w : ↥W) (ef : ↥((g ∘ f) ⁻¹' {z})),
      idx ⟨invE w ef, hinvE_mem w ef⟩ = fibIdx ef := by
    intro w ef
    show (Hg ⟨f (invE w ef), hWU (hinvE_mem w ef)⟩).2 = fibIdx ef
    have heq : (⟨f (invE w ef), hWU (hinvE_mem w ef)⟩ : ↥(g ⁻¹' U))
        = Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef) := Subtype.ext (hinvE_f w ef)
    rw [heq, Homeomorph.apply_symm_apply]
  -- RIGHT INVERSE
  have hright : ∀ (w : ↥W) (ef : ↥((g ∘ f) ⁻¹' {z})),
      toFibE ⟨invE w ef, hinvE_mem w ef⟩ = ↑ef := by
    intro w ef
    set e' : ↥((g ∘ f) ⁻¹' W) := ⟨invE w ef, hinvE_mem w ef⟩ with he'
    have hid : idx e' = fibIdx ef := hidxe' w ef
    have hmemef : ↑ef ∈ f ⁻¹' V (fibIdx ef) := by
      show f ↑ef ∈ V (fibIdx ef); rw [hffef ef]; exact hyjV _
    -- the symm-argument equals Hf(idx e')⟨↑ef,_⟩, giving toFibE e' = ↑ef
    have hpair : (⟨yj (idx e'), hyjV _⟩, (Hf (idx e') ⟨↑e', hmemV e'⟩).2)
        = Hf (idx e') ⟨↑ef, hid ▸ hmemef⟩ := by
      refine Prod.ext ?_ ?_
      · apply Subtype.ext
        show yj (idx e') = ↑(Hf (idx e') ⟨↑ef, hid ▸ hmemef⟩).1
        rw [hHf (idx e') ⟨↑ef, hid ▸ hmemef⟩]
        show yj (idx e') = f ↑ef
        rw [hffef ef, hid]
      · -- coordinate: (Hf (idx e')⟨↑e',_⟩).2 = (Hf (idx e')⟨↑ef,_⟩).2
        suffices h : ∀ (j : g ⁻¹' {z}) (_ : j = fibIdx ef) (h1 : invE w ef ∈ f ⁻¹' V j)
            (h2 : ↑ef ∈ f ⁻¹' V j), (Hf j ⟨invE w ef, h1⟩).2 = (Hf j ⟨↑ef, h2⟩).2 by
          exact h (idx e') hid (hmemV e') (hid ▸ hmemef)
        intro j hj h1 h2
        subst hj
        have key : (⟨invE w ef, h1⟩ : ↥(f ⁻¹' V (fibIdx ef)))
            = (Hf (fibIdx ef)).symm (⟨↑(Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef)),
                by show (Hg.symm _ : g ⁻¹' U).1 ∈ V (fibIdx ef)
                   rw [show (Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef) : g ⁻¹' U).1
                       = sheet ⟨↑w, hWU w.2⟩ (fibIdx ef) from rfl]
                   exact (hW'mem ↑w w.2) (fibIdx ef)⟩,
              (Hf (fibIdx ef) ⟨↑ef, h2⟩).2) := Subtype.ext rfl
        rw [key, Homeomorph.apply_symm_apply]
    simp only [htoFibE]
    rw [hpair, Homeomorph.symm_apply_apply]
  have hidx_cont : Continuous idx :=
    continuous_snd.comp (Hg.continuous.comp
      ((hf.continuous.comp continuous_subtype_val).subtype_mk (fun e => hWU e.2)))
  have hDopen : ∀ j, IsOpen (idx ⁻¹' {j}) := fun j => (isOpen_discrete _).preimage hidx_cont
  have hDcover : ⋃ j, idx ⁻¹' {j} = Set.univ :=
    Set.eq_univ_of_forall (fun e => Set.mem_iUnion.mpr ⟨idx e, rfl⟩)
  have htoFibE_cont : Continuous toFibE := by
    apply continuous_of_continuousOn_iUnion_of_isOpen _ hDopen hDcover
    intro j
    rw [continuousOn_iff_continuous_restrict]
    have hmem' : ∀ e' : ↥(idx ⁻¹' {j}), (↑↑e' : E) ∈ f ⁻¹' V j := by
      intro e'
      have hh : idx ↑e' = j := e'.2
      have hx := hmemV ↑e'
      rwa [hh] at hx
    have hsj : Continuous (fun e' : ↥(idx ⁻¹' {j}) =>
        (⟨↑↑e', hmem' e'⟩ : ↥(f ⁻¹' V j))) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hR : Continuous (fun e' : ↥(idx ⁻¹' {j}) =>
        (↑((Hf j).symm (⟨yj j, hyjV j⟩, (Hf j ⟨↑↑e', hmem' e'⟩).2)) : E)) :=
      continuous_subtype_val.comp ((Hf j).symm.continuous.comp
        (continuous_const.prodMk (continuous_snd.comp ((Hf j).continuous.comp hsj))))
    refine hR.congr (fun e' => ?_)
    have hjeq : idx ↑e' = j := e'.2
    have key : toFibE ↑e' = ↑((Hf j).symm (⟨yj j, hyjV j⟩, (Hf j ⟨↑↑e', hmem' e'⟩).2)) := by
      suffices h : ∀ (k : g ⁻¹' {z}) (_ : k = idx ↑e') (h1 : ↑↑e' ∈ f ⁻¹' V k),
          toFibE ↑e' = ↑((Hf k).symm (⟨yj k, hyjV k⟩, (Hf k ⟨↑↑e', h1⟩).2)) by
        exact h j hjeq.symm (hmem' e')
      intro k hk h1
      subst hk
      simp only [htoFibE]
    exact key.symm
  have hfibIdx_cont : Continuous fibIdx :=
    continuous_snd.comp (Hg.continuous.comp
      ((hf.continuous.comp continuous_subtype_val).subtype_mk (fun ef => hfibU ef)))
  have hinvE_cont : Continuous (fun p : ↥W × ↥((g ∘ f) ⁻¹' {z}) => invE p.1 p.2) := by
    set Q : ↥W × ↥((g ∘ f) ⁻¹' {z}) → ↥(g ⁻¹' {z}) := fun p => fibIdx p.2 with hQ
    have hQcont : Continuous Q := hfibIdx_cont.comp continuous_snd
    apply continuous_of_continuousOn_iUnion_of_isOpen (s := fun j => Q ⁻¹' {j}) _
      (fun j => (isOpen_discrete _).preimage hQcont)
      (Set.eq_univ_of_forall (fun p => Set.mem_iUnion.mpr ⟨Q p, rfl⟩))
    intro j
    rw [continuousOn_iff_continuous_restrict]
    have hPmem : ∀ p' : ↥(Q ⁻¹' {j}),
        (↑(Hg.symm (⟨↑p'.1.1, hWU p'.1.1.2⟩, j)) : Y) ∈ V j := fun p' =>
      (hW'mem ↑p'.1.1 p'.1.1.2) j
    have hmem2 : ∀ p' : ↥(Q ⁻¹' {j}), (↑p'.1.2 : E) ∈ f ⁻¹' V j := by
      intro p'
      have hh : fibIdx p'.1.2 = j := p'.2
      have hx := hfibMemV p'.1.2
      rwa [hh] at hx
    have hR : Continuous (fun p' : ↥(Q ⁻¹' {j}) =>
        (↑((Hf j).symm (⟨↑(Hg.symm (⟨↑p'.1.1, hWU p'.1.1.2⟩, j)), hPmem p'⟩,
          (Hf j ⟨↑p'.1.2, hmem2 p'⟩).2)) : E)) := by
      apply continuous_subtype_val.comp
      apply (Hf j).symm.continuous.comp
      refine Continuous.prodMk ?_ ?_
      · apply Continuous.subtype_mk
        apply continuous_subtype_val.comp
        apply Hg.symm.continuous.comp
        refine Continuous.prodMk ?_ continuous_const
        exact (continuous_subtype_val.comp (continuous_fst.comp
          (continuous_subtype_val.comp continuous_id))).subtype_mk _
      · apply continuous_snd.comp
        apply (Hf j).continuous.comp
        exact (continuous_subtype_val.comp (continuous_snd.comp
          (continuous_subtype_val.comp continuous_id))).subtype_mk _
    refine hR.congr (fun p' => ?_)
    have hjeq : fibIdx p'.1.2 = j := p'.2
    have key : invE p'.1.1 p'.1.2
        = ↑((Hf j).symm (⟨↑(Hg.symm (⟨↑p'.1.1, hWU p'.1.1.2⟩, j)), hPmem p'⟩,
          (Hf j ⟨↑p'.1.2, hmem2 p'⟩).2)) := by
      suffices h : ∀ (k : g ⁻¹' {z}) (_ : k = fibIdx p'.1.2)
          (hP : (↑(Hg.symm (⟨↑p'.1.1, hWU p'.1.1.2⟩, k)) : Y) ∈ V k)
          (h1 : (↑p'.1.2 : E) ∈ f ⁻¹' V k),
          invE p'.1.1 p'.1.2
            = ↑((Hf k).symm (⟨↑(Hg.symm (⟨↑p'.1.1, hWU p'.1.1.2⟩, k)), hP⟩,
              (Hf k ⟨↑p'.1.2, h1⟩).2)) by
        exact h j hjeq.symm (hPmem p') (hmem2 p')
      intro k hk hP h1
      subst hk
      simp only [hinvE]
    exact key.symm
  have hW'open : IsOpen W' := by
    rw [hW', Set.setOf_forall]
    refine isOpen_iInter_of_finite (fun j => (hVo j).preimage ?_)
    exact continuous_subtype_val.comp (Hg.symm.continuous.comp (by fun_prop))
  have hWopen : IsOpen W := hUo.isOpenMap_subtype_val _ hW'open
  have hzW : z ∈ W := ⟨⟨z, hzU⟩, hzW', rfl⟩
  have hgfWopen : IsOpen ((g ∘ f) ⁻¹' W) := hWopen.preimage (hg.continuous.comp hf.continuous)
  have hinvE_proj : ∀ (w : ↥W) (ef : ↥((g ∘ f) ⁻¹' {z})), g (f (invE w ef)) = ↑w := by
    intro w ef
    rw [hinvE_f]
    have hh := hHg (Hg.symm (⟨↑w, hWU w.2⟩, fibIdx ef))
    rw [Homeomorph.apply_symm_apply] at hh
    exact hh.symm
  refine ⟨?_, W, hzW, hWopen, hgfWopen, ?_, ?_⟩
  · exact (hg.isLocalHomeomorph.comp hf.isLocalHomeomorph).discreteTopology_fibre z
  · exact
      { toFun := fun e => (⟨g (f ↑e), e.2⟩, ⟨toFibE e, htoFib_mem e⟩)
        invFun := fun p => ⟨invE p.1 p.2, hinvE_mem p.1 p.2⟩
        left_inv := fun e => Subtype.ext (hleft e)
        right_inv := fun p => Prod.ext (Subtype.ext (hinvE_proj p.1 p.2)) (Subtype.ext (hright p.1 p.2))
        continuous_toFun :=
          Continuous.prodMk
            (((hg.continuous.comp hf.continuous).comp continuous_subtype_val).subtype_mk
              (fun e => e.2))
            (htoFibE_cont.subtype_mk (fun e => htoFib_mem e))
        continuous_invFun := hinvE_cont.subtype_mk (fun p => hinvE_mem p.1 p.2) }
  · intro e; rfl

end Bottcher
