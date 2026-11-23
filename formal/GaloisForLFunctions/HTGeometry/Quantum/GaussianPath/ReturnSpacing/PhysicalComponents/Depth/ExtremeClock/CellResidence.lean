import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.ClockCell
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.RecordCount

/-! # Maximal residence intervals and the corresponding physical entry dates -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
open ReturnSpacing.PhysicalComponents
noncomputable section

/-- A filled extreme-gap cell starts a fresh visit at its left edge.
Conversely, every fitted interval of maximum length starts there,
because distinct cells are separated by an open gap. -/
theorem full_residence_iff {F : Set ℝ} {W r : ℝ} (hW : 0 < W) (hr : 0 ≤ r) (hs : r < 1/2)
    (hcell : ∀ (n : ℤ) (z : ℝ), z∈Ico (-(1/2):ℝ) (1/2) →
      ((n:ℝ)+z)/W∈F → z∈Icc (-r) r) (u : ℝ) :
    (Entry F u ∧ Icc u (u+2*r/W) ⊆ F) ↔
    ∃ n : ℤ, u=((n:ℝ)-r)/W ∧ ∀ z∈Icc (-r) r, ((n:ℝ)+z)/W∈F := by
  constructor
  · rintro ⟨hu,hseg⟩
    let n := ⌊u*W+1/2⌋
    let z := u*W-(n:ℝ)
    have hfloor := Int.floor_le (u*W+1/2)
    have hceil := Int.lt_floor_add_one (u*W+1/2)
    have hz : z∈Ico (-(1/2):ℝ) (1/2) := by
      change -(1/2)≤u*W-(⌊u*W+1/2⌋:ℤ) ∧ u*W-(⌊u*W+1/2⌋:ℤ)<1/2
      constructor <;> linarith only [hfloor,hceil]
    have he : u=((n:ℝ)+z)/W := (eq_div_iff hW.ne').mpr (by dsimp only [z]; ring)
    have hb := hcell n z hz (he ▸ hu.1)
    have hz' : z = -r := by
      apply le_antisymm _ hb.1
      by_contra! h
      obtain ⟨v,hv₁,hv₂⟩ := exists_between (lt_min hs (by linarith only [h] : r < z+2*r))
      have hv : ((n:ℝ)+v)/W∈F := hseg ⟨(le_div_iff₀ hW).mpr (by
        linarith only [(eq_div_iff hW.ne').mp he,hb.2,hv₁]),
        (div_le_iff₀ hW).mpr (by rw [add_mul,div_mul_cancel₀ _ hW.ne']
                                 linarith only [(eq_div_iff hW.ne').mp he,hv₂.trans_le (min_le_right ..)])⟩
      exact hv₁.not_ge (hcell n v ⟨by linarith only [hv₁,hr],hv₂.trans_le (min_le_left ..)⟩ hv).2
    have ht : u*W=(n:ℝ)-r := by linarith only [(eq_div_iff hW.ne').mp he,hz']
    refine ⟨n,(eq_div_iff hW.ne').mpr ht,?_⟩
    intro v hv
    exact hseg ⟨(le_div_iff₀ hW).mpr (by linarith only [ht,hv.1]),
      (div_le_iff₀ hW).mpr (by rw [add_mul,div_mul_cancel₀ _ hW.ne']; linarith only [ht,hv.2])⟩
  · rintro ⟨n,he,full⟩
    have ht := (eq_div_iff hW.ne').mp he
    have seg : Icc u (u+2*r/W) ⊆ F := by
      intro v hv
      let z := v*W-(n:ℝ)
      have a := mul_le_mul_of_nonneg_right hv.1 hW.le
      have b := mul_le_mul_of_nonneg_right hv.2 hW.le
      rw [add_mul,div_mul_cancel₀ _ hW.ne'] at b
      have hz : z∈Icc (-r) r := ⟨by dsimp only [z]; linarith only [ht,a],
        by dsimp only [z]; linarith only [ht,b]⟩
      have he' : v=((n:ℝ)+z)/W := (eq_div_iff hW.ne').mpr (by dsimp only [z]; ring)
      exact he' ▸ full z hz
    refine ⟨⟨seg ⟨le_rfl,le_add_of_nonneg_right (div_nonneg (mul_nonneg two_pos.le hr) hW.le)⟩,
      (1/2-r)/W,div_pos (sub_pos.mpr hs) hW,?_⟩,seg⟩
    intro v hv hfit
    have a := mul_lt_mul_of_pos_right hv.1 hW
    have b := mul_lt_mul_of_pos_right hv.2 hW
    rw [sub_mul,div_mul_cancel₀ _ hW.ne'] at a
    let z := v*W-(n:ℝ)
    have hz : z∈Ico (-(1/2):ℝ) (1/2) := ⟨by dsimp only [z]; linarith only [ht,a],
      by dsimp only [z]; linarith only [ht,b,hr]⟩
    have hv' : v=((n:ℝ)+z)/W := (eq_div_iff hW.ne').mpr (by dsimp only [z]; ring)
    have hx := (hcell n z hz (hv' ▸ hfit)).1
    dsimp only [z] at hx
    linarith only [hx,ht,b]

end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
