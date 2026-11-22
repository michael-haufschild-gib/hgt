import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.RecordCount
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Counts of nested connected visits at arbitrary observation endpoints -/
open Set
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
noncomputable section

/-- Outer entries whose component contains an inner visit. -/
def reached (E F : Set ℝ) (A : Finset ℝ) : Finset ℝ := by
  classical
  exact A.filter fun u => ∃ w≥u, w∈F ∧ Icc u w ⊆ E

/-- An absent date followed by a visit brackets an actual entry. -/
theorem first_after {E : Set ℝ} (hc : IsClosed E) {a w : ℝ}
    (ha : a∉E) (haw : a≤w) (hw : w∈E) : ∃ u ∈ Ioc a w, Entry E u := by
  let S := Icc a w ∩ E
  have hs : w∈S := ⟨⟨haw,le_rfl⟩,hw⟩
  have hm := (isClosed_Icc.inter hc).isLeast_csInf ⟨w,hs⟩ ⟨a,fun _ h => h.1.1⟩
  let u := sInf S
  have hu : u ∈ S := hm.1
  have hau : a<u := lt_of_le_of_ne hu.1.1 (fun h => ha (h ▸ hu.2))
  refine ⟨u,⟨hau,hu.1.2⟩,hu.2,u-a,sub_pos.mpr hau,?_⟩
  intro z hz he
  exact hz.2.not_ge (hm.2 ⟨⟨by linarith only [hz.1],hz.2.le.trans hu.1.2⟩,he⟩)

private theorem same_entry {E : Set ℝ} {u v z : ℝ} (hu : Entry E u) (hv : Entry E v)
    (huz : u≤z) (hvz : v≤z) (hs : Icc u z ⊆ E) (ht : Icc v z ⊆ E) : u=v := by
  have excludes {a b : ℝ} (hab : a<b) (hb : Entry E b) (hbz : b≤z) (h : Icc a z ⊆ E) : False := by
    obtain ⟨d,hd,hout⟩ := hb.2
    obtain ⟨t,hl,hr⟩ := exists_between (max_lt hab (sub_lt_self b hd))
    exact hout t ⟨(le_max_right ..).trans_lt hl,hr⟩
      (h ⟨((le_max_left ..).trans_lt hl).le,hr.le.trans hbz⟩)
  exact le_antisymm (le_of_not_gt (fun h => excludes h hu huz ht))
    (le_of_not_gt (fun h => excludes h hv hvz hs))

/-- With at most one inner entry per outer component, marked outer counts
and inner counts differ by at most one at every date. Only the two visits
cut by the observation endpoints can affect the comparison. -/
theorem component_count_bounds {E F : Set ℝ} (hE : IsClosed E) (hF : IsClosed F) (hsub : F⊆E)
    (hsep : ∀ u∈F, ∀ v, Entry F v → u<v → ∃ z∈Ioo u v, z∉E)
    {a : ℝ} (A B : ℝ → Finset ℝ)
    (hA : ∀ u T, u∈A T ↔ a<u ∧ u≤T ∧ Entry E u)
    (hB : ∀ u T, u∈B T ↔ a<u ∧ u≤T ∧ Entry F u) (T : ℝ) :
    (B T).card ≤ (reached E F (A T)).card+1 ∧ (reached E F (A T)).card ≤ (B T).card+1 := by
  classical
  constructor
  · let M := insert a (reached E F (A T))
    have parent (w : B T) : ∃ u : M, (u:ℝ)≤w ∧ Icc (u:ℝ) w ⊆ E := by
      obtain ⟨haw,hwT,hw⟩ := (hB ..).mp w.property
      let S := insert a (A w)
      have hS : S.Nonempty := ⟨a,Finset.mem_insert_self ..⟩
      let u := S.max' hS
      have hau : a≤u := Finset.le_max' _ _ (Finset.mem_insert_self ..)
      have hu := Finset.mem_insert.mp (Finset.max'_mem S hS)
      have huw : u≤w := hu.elim (fun h => h.trans_le haw.le) (fun h => ((hA ..).mp h).2.1)
      have hseg : Icc u w ⊆ E := by
        intro t ht
        by_contra hn
        obtain ⟨v,hv,hent⟩ := first_after hE hn ht.2 (hsub hw.1)
        have hmem := (hA ..).mpr ⟨(hau.trans ht.1).trans_lt hv.1,hv.2,hent⟩
        exact (ht.1.trans_lt hv.1).not_ge (Finset.le_max' _ _ (Finset.mem_insert_of_mem hmem))
      refine ⟨⟨u,Finset.mem_insert.mpr (hu.imp_right fun hum => ?_)⟩,huw,hseg⟩
      obtain ⟨ha,_,he⟩ := (hA ..).mp hum
      exact Finset.mem_filter.mpr ⟨(hA ..).mpr ⟨ha,huw.trans hwT,he⟩,
        (show ∃ z≥u, z∈F ∧ Icc u z ⊆ E from ⟨w,huw,hw.1,hseg⟩)⟩
    choose f hf using parent
    have inj : Function.Injective f := by
      intro w v he
      apply Subtype.ext
      have same : (f w:ℝ)=(f v:ℝ) := congrArg Subtype.val he
      have exclude (p q : B T) (hh : (f p:ℝ)=(f q:ℝ)) (hlt : (p:ℝ)<q) : False := by
        obtain ⟨z,hz,hn⟩ := hsep p ((hB ..).mp p.property).2.2.1 q ((hB ..).mp q.property).2.2 hlt
        exact hn ((hf q).2 ⟨((hh ▸ (hf p).1).trans hz.1.le),hz.2.le⟩)
      exact le_antisymm (le_of_not_gt (exclude v w same.symm)) (le_of_not_gt (exclude w v same))
    exact (Finset.card_le_card_of_injective inj).trans (Finset.card_insert_le ..)
  · let M := reached E F (A T)
    let S := insert T (B T)
    have child (u : M) : ∃ v : S, (u:ℝ)≤v ∧ Icc (u:ℝ) v ⊆ E := by
      obtain ⟨hum,w,huw,hw,hseg⟩ := Finset.mem_filter.mp u.property
      obtain ⟨ha,huT,hu⟩ := (hA ..).mp hum
      have hit : ∃ v∈Icc (u:ℝ) w, Entry F v := by
        by_cases h : (u:ℝ)∈F
        · obtain ⟨d,hd,hn⟩ := hu.2
          exact ⟨u,⟨le_rfl,huw⟩,h,d,hd,fun z hz hFz => hn z hz (hsub hFz)⟩
        · obtain ⟨v,hv,he⟩ := first_after hF h huw hw
          exact ⟨v,⟨hv.1.le,hv.2⟩,he⟩
      obtain ⟨v,hv,he⟩ := hit
      by_cases h : v≤T
      · exact ⟨⟨v,Finset.mem_insert_of_mem ((hB ..).mpr ⟨ha.trans_le hv.1,h,he⟩)⟩,hv.1,
          fun z hz => hseg ⟨hz.1,hz.2.trans hv.2⟩⟩
      · exact ⟨⟨T,Finset.mem_insert_self ..⟩,huT,
          fun z hz => hseg ⟨hz.1,(hz.2.trans (le_of_not_ge h)).trans hv.2⟩⟩
    choose f hf using child
    have hent (u : M) : Entry E (u:ℝ) := ((hA ..).mp (Finset.mem_filter.mp u.property).1).2.2
    have inj : Function.Injective f := by
      intro x y he
      exact Subtype.ext (same_entry (hent x) (hent y) (hf x).1 (he.symm ▸ (hf y).1)
        (hf x).2 (he.symm ▸ (hf y).2))
    exact (Finset.card_le_card_of_injective inj).trans (Finset.card_insert_le ..)

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
