import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.ReciprocalGrid

/-! # Gaussian bond counts at every physical cutoff in a moving window -/

open Set Finset MeasureTheory Filter Real
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
noncomputable section

/-- Count a box by testing the sampled bonds in the progression. -/
theorem boxCount_as_filter (ω : PathPauliDisorder) (s d m : ℕ) (h : ℝ) :
    boxCount ω s d m h=(Finset.univ.filter fun i : Fin m => bondRow9 ω (s+d*i.val)∈weakBond h).card :=
  rfl

private theorem count_mono (ω : PathPauliDisorder) (s d m : ℕ) {x y : ℝ} (h : x≤y) :
    boxCount ω s d m x≤boxCount ω s d m y := by
  rw [boxCount_as_filter,boxCount_as_filter]
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
  intro k hk
  exact ⟨(neg_le_neg h).trans (hj k hk).1,(hj k hk).2.trans h⟩

/-- All box radii from 2 m^(-1/20) through one have counts comparable
to m h⁹, on the same frozen sample. The constants apply to all fixed
arithmetic progressions at once. -/
theorem gaussian_moving_boxes :
    ∃ c>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s d : ℕ, 0<d → ∀ᶠ m : ℕ in atTop,
      ∀ h : ℝ, 0<h → h≤1 → 2^20≤(m:ℝ)*h^20 →
        c*m*h^9≤boxCount ω s d m h ∧ (boxCount ω s d m h:ℝ)≤C*m*h^9 := by
  let c₀ := (2*gaussianDensityFloor)^9
  have hc : 0<c₀ := pow_pos (mul_pos two_pos gaussianDensityFloor_pos) 9
  refine ⟨c₀/(2*2^9),by positivity,3/2*(4:ℝ)^9*2^9,by positivity,?_⟩
  have hall : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s d : ℕ, ∀ᶠ m : ℕ in atTop, ∀ j : ℕ, 0<j → j^20 ≤ m →
      let p := bondLaw.real (weakBond (1/(j:ℝ)))
      p*m/2<(boxCount ω s (d+1) m (1/(j:ℝ)):ℝ) ∧
        (boxCount ω s (d+1) m (1/(j:ℝ)):ℝ)<3/2*p*m :=
    ae_all_iff.mpr fun s => ae_all_iff.mpr fun d => gaussian_reciprocal_counts s (d+1) (Nat.succ_pos _)
  filter_upwards [hall] with ω hw
  intro s d hd
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  filter_upwards [hw s d] with m hm
  intro h hh h₁ hmass
  let j := ⌊1/h⌋₊
  have hrec : 1≤1/h := (le_div_iff₀ hh).mpr (by simpa only [one_mul] using h₁)
  have hj : 1≤j := Nat.le_floor (by simpa only [Nat.cast_one] using hrec)
  have hJ : 0<(j:ℝ) := Nat.cast_pos.mpr hj
  have hJ₁ : (1:ℝ)≤j := by exact_mod_cast hj
  have hJ' : 0<((j+1:ℕ):ℝ) := by positivity
  have hlo := (le_div_iff₀ hh).mp (Nat.floor_le (one_div_pos.mpr hh).le)
  have hhi := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (1/h))
  change (j:ℝ)*h≤1 at hlo
  change 1<((j:ℝ)+1)*h at hhi
  have hk : ((j+1:ℕ):ℝ)*h≤2 := by push_cast; linarith only [hlo,h₁]
  have hgrid : (j+1)^20 ≤ m := by
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [Nat.cast_pow]
    apply le_of_mul_le_mul_right _ (pow_pos hh 20)
    rw [←mul_pow]
    exact (pow_le_pow_left₀ (mul_nonneg hJ'.le hh.le) hk 20).trans hmass
  let l : ℝ := 1/(j+1:ℕ)
  let r : ℝ := 1/(j:ℝ)
  have hl : l≤h := (div_le_iff₀ hJ').mpr (by push_cast; linarith only [hhi])
  have hr : h ≤ r := (le_div_iff₀ hJ).mpr (by linarith only [hlo])
  have hl' : h/2≤l := (le_div_iff₀ hJ').mpr (by linarith only [hk])
  have hr' : r≤2*h := (div_le_iff₀ hJ).mpr (by
    have hjh := mul_le_mul_of_nonneg_right hJ₁ hh.le
    linarith only [hhi,hjh])
  have hs := (hm (j+1) (Nat.succ_pos _) hgrid).1
  have hb := (hm j hj ((Nat.pow_le_pow_left (Nat.le_succ _) 20).trans hgrid)).2
  have hp := (box_probability (by dsimp only [l]; positivity : 0<l) (hl.trans h₁)).1
  have hq := (box_probability (one_div_pos.mpr hJ) ((div_le_one hJ).mpr hJ₁)).2
  have hM : (0:ℝ) ≤ m := Nat.cast_nonneg _
  constructor
  · calc
      _ = c₀*(h/2)^9*m/2 := by ring
      _ ≤ c₀*l^9*m/2 := by gcongr
      _ ≤ bondLaw.real (weakBond l)*m/2 := by gcongr
      _ ≤ _ := hs.le.trans (Nat.cast_le.mpr (count_mono ω s (d+1) m hl))
  · calc
      _ ≤ _ := (Nat.cast_le.mpr (count_mono ω s (d+1) m hr)).trans hb.le
      _ ≤ 3/2*((4:ℝ)^9*r^9)*m := by gcongr
      _ ≤ 3/2*((4:ℝ)^9*(2*h)^9)*m := by gcongr
      _ = _ := by ring

#print axioms gaussian_moving_boxes
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
