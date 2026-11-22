import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ComponentCounts

/-! # Marking a continuous visit by the deepest tube it reaches -/
open Set
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
noncomputable section

/-- The visit starting at the recorded date reaches the inner set without
leaving the outer set. -/
def marked (E F : Set ℝ) (entries : Finset ℝ) : Finset ℝ := by
  classical
  exact entries.filter (fun u => ∃ w ∈ Icc u (u+1), w∈F ∧ Icc u w ⊆ E)

private theorem segment {E : Set ℝ} (hc : IsClosed E)
    (hg : ∀ v ∈ E, ∀ w, Entry E w → v<w → 1<w-v)
    {u w : ℝ} (hu : u∈E) (hw : w∈E) (hwu : w≤u+1) : Icc u w ⊆ E := by
  intro z hz
  by_contra hn
  obtain ⟨y,hy,he⟩ := first_after hc hn hz.2 hw
  have h := hg u hu y he (hz.1.trans_lt hy.1)
  linarith only [hy.2,hwu,h]

private theorem unique_on_unit {E : Set ℝ} (hg : ∀ v ∈ E, ∀ w, Entry E w → v<w → 1<w-v)
    {a x y : ℝ} (hx : Entry E x) (hy : Entry E y) (h₁ : x∈Icc a (a+1))
    (h₂ : y∈Icc a (a+1)) : x=y := by
  rcases lt_trichotomy x y with h|h|h
  · linarith only [hg x hx.1 y hy h,h₁.1,h₂.2]
  · exact h
  · linarith only [hg y hy.1 x hx h,h₂.1,h₁.2]

/-- The counted outer visits reaching the inner tube differ from the
inner entry count only by a possible terminal visit. -/
theorem count_bounds {E F : Set ℝ} (hE : IsClosed E) (hF : IsClosed F) (hsub : F⊆E)
    {a : ℝ} (ha : a∉E) (hu : ∀ v ∈ E, v+1 ∉ E)
    (hg : ∀ v ∈ E, ∀ w, Entry E w → v<w → 1<w-v)
    (hf : ∀ v ∈ F, ∀ w, Entry F w → v<w → 1<w-v)
    (A B : ℝ → Finset ℝ)
    (hA : ∀ u T, u∈A T ↔ a<u ∧ u≤T ∧ Entry E u)
    (hB : ∀ u T, u∈B T ↔ a<u ∧ u≤T ∧ Entry F u) (T : ℝ) :
    (B T).card ≤ (marked E F (A T)).card ∧ (marked E F (A T)).card ≤ (B (T+1)).card := by
  classical
  constructor
  · have parent (w : B T) : ∃ u : marked E F (A T), (w:ℝ)∈Icc (u:ℝ) (u+1) := by
      obtain ⟨ha',hT,he⟩ := (hB ..).mp w.property
      have hw := hsub he.1
      have hprev : (w:ℝ)-1 ∉ E := fun h => hu _ h (by simpa only [sub_add_cancel] using hw)
      have hleft : max a ((w:ℝ)-1) ∉ E := by
        rcases le_total a ((w:ℝ)-1) with h|h
        · rwa [max_eq_right h]
        · rwa [max_eq_left h]
      obtain ⟨u,huw,hu'⟩ := first_after hE hleft (max_le ha'.le (by linarith)) hw
      have hafter := (le_max_left ..).trans_lt huw.1
      have hnear := (le_max_right ..).trans_lt huw.1
      have hi : (w:ℝ)∈Icc u (u+1) := ⟨huw.2,by linarith only [hnear]⟩
      exact ⟨⟨u,Finset.mem_filter.mpr ⟨(hA ..).mpr ⟨hafter,huw.2.trans hT,hu'⟩,
        (show ∃ z∈Icc u (u+1), z∈F ∧ Icc u z ⊆ E from
          ⟨w,hi,he.1,segment hE hg hu'.1 hw hi.2⟩)⟩⟩,hi⟩
    choose f h using parent
    apply Finset.card_le_card_of_injective (f:=f)
    intro x y heq
    apply Subtype.ext
    exact unique_on_unit hf ((hB ..).mp x.property).2.2 ((hB ..).mp y.property).2.2
      (h x) (heq.symm ▸ h y)
  · have child (u : marked E F (A T)) : ∃ w : B (T+1), (w:ℝ)∈Icc (u:ℝ) (u+1) := by
      obtain ⟨hm,w,hw,hdeep,_⟩ := Finset.mem_filter.mp u.property
      obtain ⟨ha',hT,he⟩ := (hA ..).mp hm
      have lift (v : ℝ) (hi : v∈Icc (u:ℝ) (u+1)) (hv : Entry F v) :
          ∃ w : B (T+1), (w:ℝ)∈Icc (u:ℝ) (u+1) :=
        ⟨⟨v,(hB ..).mpr ⟨ha'.trans_le hi.1,hi.2.trans (add_le_add hT (le_refl 1)),hv⟩⟩,hi⟩
      by_cases h : (u:ℝ)∈F
      · obtain ⟨d,hd,hz⟩ := he.2
        exact lift _ ⟨le_rfl,by linarith⟩ ⟨h,d,hd,fun z hh hf' => hz z hh (hsub hf')⟩
      · obtain ⟨v,hv,hv'⟩ := first_after hF h hw.1 hdeep
        exact lift v ⟨hv.1.le,hv.2.trans hw.2⟩ hv'
    choose f h using child
    apply Finset.card_le_card_of_injective (f:=f)
    intro x y heq
    have inside (u : marked E F (A T)) : (u:ℝ)∈Icc ((f u:ℝ)-1) (((f u:ℝ)-1)+1) := by
      rw [sub_add_cancel]
      exact ⟨by linarith only [(h u).2],(h u).1⟩
    apply Subtype.ext
    exact unique_on_unit hg ((hA ..).mp (Finset.mem_filter.mp x.property).1).2.2
      ((hA ..).mp (Finset.mem_filter.mp y.property).1).2.2 (inside x) (heq.symm ▸ inside y)

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
