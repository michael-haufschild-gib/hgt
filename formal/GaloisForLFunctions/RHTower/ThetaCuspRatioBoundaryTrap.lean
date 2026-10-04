import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace HTGeometry.TwoFunctionTrap
open Set Filter Topology


/-- A negative component cannot return to positive values when its boundary forcing is trapped. -/
theorem nonneg_between {f g f' g' w : ℝ → ℝ} {a c : ℝ}
    (hf : ∀ x ∈ Icc a c, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Icc a c, HasDerivAt g (g' x) x)
    (hw : ∀ x ∈ Icc a c, 0<w x)
    (hboundary : ∀ x ∈ Icc a c, f x=0 → f' x=w x*g x)
    (htrap : ∀ x ∈ Icc a c, f x≤0 → g x=0 → g' x<0)
    (hfa : 0<f a) (hfc : 0<f c) : ∀ x ∈ Icc a c, 0≤f x := by
  intro b hb
  by_contra hnb
  have hfb : f b<0 := lt_of_not_ge hnb
  have hab : a<b := lt_of_le_of_ne hb.1 (by intro h; subst b; linarith)
  have hbc : b<c := lt_of_le_of_ne hb.2 (by intro h; subst b; linarith)
  have hcl : ContinuousOn f (Icc a b) := fun x hx =>
    (hf x ⟨hx.1,hx.2.trans hb.2⟩).continuousAt.continuousWithinAt
  have hcr : ContinuousOn f (Icc b c) := fun x hx =>
    (hf x ⟨hb.1.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt
  let L : Set ℝ := Icc a b ∩ f ⁻¹' {0}
  let R : Set ℝ := Icc b c ∩ f ⁻¹' {0}
  have hLc : IsCompact L := isCompact_Icc.of_isClosed_subset
    (hcl.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hRc : IsCompact R := isCompact_Icc.of_isClosed_subset
    (hcr.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hLn : L.Nonempty := by
    obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc' hab.le hcl ⟨hfb.le,hfa.le⟩
    exact ⟨z,hz,hfz⟩
  have hRn : R.Nonempty := by
    obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc hbc.le hcr ⟨hfb.le,hfc.le⟩
    exact ⟨z,hz,hfz⟩
  obtain ⟨l,hl,hlmax⟩ := hLc.exists_isGreatest hLn
  obtain ⟨r,hr,hrmin⟩ := hRc.exists_isLeast hRn
  have hfl : f l=0 := hl.2
  have hfr : f r=0 := hr.2
  have hlb : l<b := lt_of_le_of_ne hl.1.2 (by intro h; subst l; linarith)
  have hbr : b<r := lt_of_le_of_ne hr.1.1 (by intro h; subst r; linarith)
  have hlr : l<r := hlb.trans hbr
  have hin (x : ℝ) (hx : x∈Icc l r) : x∈Icc a c :=
    ⟨hl.1.1.trans hx.1,hx.2.trans hr.1.2⟩
  have hneg (x : ℝ) (hx : x∈Ioo l r) : f x<0 := by
    by_contra hn
    have hfx : 0≤f x := le_of_not_gt hn
    by_cases hxb : x≤b
    · have hc : ContinuousOn f (Icc x b) := fun z hz =>
        (hf z ⟨hl.1.1.trans (hx.1.le.trans hz.1),hz.2.trans hb.2⟩).continuousAt.continuousWithinAt
      obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc' hxb hc ⟨hfb.le,hfx⟩
      have hzL : z∈L := ⟨⟨hl.1.1.trans (hx.1.le.trans hz.1),hz.2⟩,hfz⟩
      have hzle := hlmax hzL
      linarith [hz.1,hx.1]
    · have hbx : b≤x := (lt_of_not_ge hxb).le
      have hc : ContinuousOn f (Icc b x) := fun z hz =>
        (hf z ⟨hb.1.trans hz.1,hz.2.trans (hx.2.le.trans hr.1.2)⟩).continuousAt.continuousWithinAt
      obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc hbx hc ⟨hfb.le,hfx⟩
      have hzR : z∈R := ⟨⟨hz.1,hz.2.trans (hx.2.le.trans hr.1.2)⟩,hfz⟩
      have hzge := hrmin hzR
      linarith [hz.2,hx.2]
  have hnonpos (x : ℝ) (hx : x∈Icc l r) : f x≤0 := by
    rcases hx.1.eq_or_lt with he | he
    · subst x; exact hfl.le
    · rcases hx.2.eq_or_lt with heq | hlt
      · subst x; exact hfr.le
      · exact (hneg x ⟨he,hlt⟩).le
  have hlac := hin l ⟨le_rfl,hlr.le⟩
  have hrac := hin r ⟨hlr.le,le_rfl⟩
  have hfl' : f' l≤0 := by
    apply le_of_tendsto ((hf l hlac).tendsto_slope.mono_left (nhdsGT_le_nhdsNE l))
    have hrn : ∀ᶠ y in 𝓝[>] l, y<r :=
      (eventually_lt_nhds hlr).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hrn] with y hy hyr
    rw [slope_def_field,hfl,sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (hneg y ⟨hy,hyr⟩).le (sub_pos.mpr hy).le
  have hfr' : 0≤f' r := by
    apply ge_of_tendsto ((hf r hrac).tendsto_slope.mono_left (nhdsLT_le_nhdsNE r))
    have hln : ∀ᶠ y in 𝓝[<] r, l<y :=
      (eventually_gt_nhds hlr).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hln] with y hy hly
    rw [slope_def_field,hfr,sub_zero]
    exact div_nonneg_of_nonpos (hneg y ⟨hly,hy⟩).le (sub_neg.mpr hy).le
  have hgl : g l≤0 := by
    rw [hboundary l hlac hfl] at hfl'
    have hw0 := hw l hlac
    nlinarith
  have hgr : 0≤g r := by
    rw [hboundary r hrac hfr] at hfr'
    have hw0 := hw r hrac
    nlinarith
  have hg_le : ∀ x∈Icc l r, g x≤0 := by
    intro x hx
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := g) (f' := g') (a := l) (b := r)
      (fun z hz => (hg z (hin z hz)).continuousAt.continuousWithinAt)
      (fun z hz => (hg z (hin z ⟨hz.1,hz.2.le⟩)).hasDerivWithinAt)
      (B := fun _ => 0) (B' := fun _ => 0) hgl
      (fun z => hasDerivAt_const z (0:ℝ)) ?_ hx
    intro z hz he
    exact htrap z (hin z ⟨hz.1,hz.2.le⟩) (hnonpos z ⟨hz.1,hz.2.le⟩) he
  have hgr0 : g r=0 := le_antisymm (hg_le r ⟨hlr.le,le_rfl⟩) hgr
  have hgr' : 0≤g' r := by
    apply ge_of_tendsto ((hg r hrac).tendsto_slope.mono_left (nhdsLT_le_nhdsNE r))
    have hln : ∀ᶠ y in 𝓝[<] r, l<y :=
      (eventually_gt_nhds hlr).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hln] with y hy hly
    rw [slope_def_field,hgr0,sub_zero]
    exact div_nonneg_of_nonpos (hg_le y ⟨hly.le,hy.le⟩) (sub_neg.mpr hy).le
  exact (not_lt_of_ge hgr') (htrap r hrac hfr.le hgr0)

end HTGeometry.TwoFunctionTrap
