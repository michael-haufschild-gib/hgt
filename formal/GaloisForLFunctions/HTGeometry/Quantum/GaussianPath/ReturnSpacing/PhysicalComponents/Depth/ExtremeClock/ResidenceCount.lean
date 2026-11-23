import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.CellResidence
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.DurationCharge
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.PhysicalClock

/-! # Counting full residence intervals by consecutive extreme-gap ticks -/
open Set
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
open ReturnSpacing.PhysicalComponents ReturnSpacing.PhysicalComponents.Depth
noncomputable section

/-- The number of genuine maximal entries equals the number of successful
ticks whose left edges lie in the physical observation interval. -/
theorem full_residence_count {F : Set ℝ} {W r σ : ℝ} (hW : 0 < W) (hr : 0 ≤ r) (hs : r < 1/2)
    (hcell : ∀ (n : ℤ) (z : ℝ), z∈Ico (-(1/2):ℝ) (1/2) →
      ((n:ℝ)+z)/W∈F → z∈Icc (-r) r) (A : ℝ→Finset ℝ)
    (hA : ∀ u T, u∈A T ↔ σ<u ∧ u≤T ∧ Entry F u)
    (shift : ℕ) (hshift : σ*W+r < shift ∧ (shift:ℝ) ≤ σ*W+r+1) (T : ℝ) :
    let test (k : ℕ) := ∀ z∈Icc (-r) r, (((shift+k:ℕ):ℝ)+z)/W∈F
    (longVisits F (2*r/W) (A T)).card = ((tickIndices (((shift:ℝ)-r)/W) (1/W) T).filter test).card := by
  classical
  intro test
  let date (k : ℕ) := (((shift+k:ℕ):ℝ)-r)/W
  let S := (tickIndices (((shift:ℝ)-r)/W) (1/W) T).filter test
  have hm (k : ℕ) : k∈tickIndices (((shift:ℝ)-r)/W) (1/W) T ↔ date k≤T := by
    rw [mem_tickIndices (one_div_pos.mpr hW)]
    have he : ((shift:ℝ)-r)/W+(k:ℝ)*(1/W)=date k := by
      dsimp only [date]
      rw [Nat.cast_add]
      ring
    rw [he]
  have hinj : Function.Injective date := by
    intro i j he
    have hh := (div_left_inj' hW.ne').mp he
    change (((shift+i:ℕ):ℝ)-r)=(((shift+j:ℕ):ℝ)-r) at hh
    have hj : shift+i=shift+j := by
      exact_mod_cast (show ((shift+i:ℕ):ℝ)=((shift+j:ℕ):ℝ) by linarith only [hh])
    omega
  have hset : longVisits F (2*r/W) (A T) = S.image date := by
    ext u
    constructor
    · intro hu
      obtain ⟨hmem,hseg⟩ := Finset.mem_filter.mp hu
      obtain ⟨ha,ht,hent⟩ := (hA ..).mp hmem
      obtain ⟨n,hn,hfull⟩ := (full_residence_iff hW hr hs hcell u).mp ⟨hent,hseg⟩
      rw [hn] at ha ht
      have hl : (shift:ℤ) ≤ n := by
        by_contra! h
        have hh : (n:ℝ)+1 ≤ shift := by exact_mod_cast (show n+1 ≤ (shift:ℤ) by omega)
        linarith only [(lt_div_iff₀ hW).mp ha,hshift.2,hh]
      let k := (n-(shift:ℤ)).toNat
      have hk : ((shift+k:ℕ):ℤ)=n := by dsimp only [k]; omega
      have hkr : ((shift+k:ℕ):ℝ)=(n:ℝ) := by exact_mod_cast hk
      have hdate : date k=((n:ℝ)-r)/W := congrArg (fun x : ℝ => (x-r)/W) hkr
      refine Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨(hm k).mpr (hdate.trans_le ht),?_⟩,hdate.trans hn.symm⟩
      intro z hz
      simpa only [hkr] using hfull z hz
    · intro hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hkm,ht⟩ := Finset.mem_filter.mp hk
      have hpair := (full_residence_iff hW hr hs hcell (date k)).mpr
        ⟨((shift+k:ℕ):ℤ),by simp only [Int.cast_natCast,date],
         by simpa only [Int.cast_natCast] using ht⟩
      refine Finset.mem_filter.mpr ⟨(hA ..).mpr ⟨?_,(hm k).mp hkm,hpair.1⟩,hpair.2⟩
      apply (lt_div_iff₀ hW).mpr
      rw [Nat.cast_add]
      linarith only [hshift.1,Nat.cast_nonneg (α:=ℝ) k]
  rw [hset,Finset.card_image_of_injective _ hinj]
  rfl

end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
