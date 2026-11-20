import GaloisForLFunctions.RestrictedFactorizationCalculus.DensityOneForRestrictedPrimeExchanges

/-!
# Selecting a prime donor from a word of independent prime pairs

Scan the partial sums of the donor-minus-partner indicators. At a positive
maximum the first arrival is an upward step. Changing it to a downward
step makes its predecessor the last maximum, which identifies the inverse
from the new integer alone.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Step immediately before the first occurrence of a positive maximum. -/
def donorRise (H : ℕ → ℤ) (N i : ℕ) := i<N ∧ (∀ j ≤ i,H j ≤ H i) ∧
  H (i+1)=H i+1 ∧ ∀ j, i<j → j ≤ N → H j ≤ H (i+1)

/-- Step immediately after the last maximum when that maximum precedes the end. -/
def donorFall (H : ℕ → ℤ) (N i : ℕ) := i<N ∧ (∀ j ≤ i,H j ≤ H i) ∧
  H (i+1)=H i-1 ∧ ∀ j, i<j → j ≤ N → H j ≤ H (i+1)

theorem donorRise_unique {H : ℕ → ℤ} {N i j : ℕ} (hi : donorRise H N i) (hj : donorRise H N j) : i=j := by
  have excl {i j : ℕ} (a : donorRise H N i) (b : donorRise H N j) (h : i<j) : False := by
    have h1 := a.2.2.2 (j+1) (by omega) (by have := b.1; omega)
    have h2 := b.2.1 (i+1) (by omega)
    linarith only [h1,h2,b.2.2.1]
  exact le_antisymm (Nat.le_of_not_gt (excl hj hi)) (Nat.le_of_not_gt (excl hi hj))

theorem donorFall_unique {H : ℕ → ℤ} {N i j : ℕ} (hi : donorFall H N i) (hj : donorFall H N j) : i=j := by
  have excl {i j : ℕ} (a : donorFall H N i) (b : donorFall H N j) (h : i<j) : False := by
    have h1 := a.2.2.2 j h b.1.le
    have h2 := b.2.1 i h.le
    linarith only [h1,h2,a.2.2.1]
  exact le_antisymm (Nat.le_of_not_gt (excl hj hi)) (Nat.le_of_not_gt (excl hi hj))

/-- Lowering the path by two after one letter swaps its two canonical
selection rules. This gives a reversible arithmetic switch. -/
theorem donorRise_iff_fall_after_flip {H G : ℕ → ℤ} {N i : ℕ}
    (before : ∀ j ≤ i,G j=H j) (after : ∀ j, i<j → G j=H j-2) :
    donorRise H N i ↔ donorFall G N i := by
  have hb := before i le_rfl
  have ha := after (i+1) (Nat.lt_succ_self _)
  constructor
  · rintro ⟨hi,hpre,hstep,hpost⟩
    refine ⟨hi,fun j hj => by rw [before j hj,hb]; exact hpre j hj,by linarith only [ha,hb,hstep],?_⟩
    intro j hj hN
    rw [after j hj,ha]
    exact sub_le_sub_right (hpost j hj hN) _
  · rintro ⟨hi,hpre,hstep,hpost⟩
    refine ⟨hi,fun j hj => by rw [←before j hj,←hb]; exact hpre j hj,by linarith only [ha,hb,hstep],?_⟩
    intro j hj hN
    have hh := hpost j hj hN
    rw [after j hj,ha] at hh
    linarith only [hh]

/-- A positive total guarantees an eligible donor. The location is
determined by prefix heights, even when a word contains neutral letters. -/
theorem exists_donorRise_of_positive_total (H : ℕ → ℤ) (N : ℕ)
    (hstep : ∀ i<N,H (i+1) ≤ H i+1) (h : H 0<H N) : ∃ i,donorRise H N i := by
  let I := range (N+1)
  have hN : N ∈ I := mem_range.mpr (Nat.lt_succ_self _)
  let S := I.image H
  have hs : S.Nonempty := ⟨H N,mem_image_of_mem _ hN⟩
  let M := S.max' hs
  have peak : ∃ j : ℕ,j ≤ N ∧ H j=M := by
    obtain ⟨j,hj,e⟩ := mem_image.mp (max'_mem S hs)
    exact ⟨j,Nat.le_of_lt_succ (mem_range.mp hj),e⟩
  let k := Nat.find peak
  obtain ⟨hkN,hk⟩ := Nat.find_spec peak
  have hmax (j : ℕ) (hj : j ≤ N) : H j ≤ M := le_max' _ _ (mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_of_le hj)))
  have h0k : 0<k := by
    by_contra! hh
    have he : k=0 := by omega
    have hk' : H k=M := hk
    rw [he] at hk'
    linarith only [hk',h,hmax N le_rfl]
  obtain ⟨i,he⟩ := Nat.exists_eq_succ_of_ne_zero h0k.ne'
  have hi : i<N := by change k ≤ N at hkN; omega
  have hfirst (j : ℕ) (hj : j ≤ i) : H j<M := by
    refine lt_of_le_of_ne (hmax j (hj.trans hi.le)) (fun hh => ?_)
    exact Nat.find_min peak (show j<k by omega) ⟨hj.trans hi.le,hh⟩
  have hii : H (i+1)=M := (congrArg H he).symm.trans hk
  have his := hstep i hi
  have hdiff : H (i+1)=H i+1 := by have := hfirst i le_rfl; omega
  refine ⟨i,hi,fun j hj => ?_,hdiff,fun j _ hj => (hmax j hj).trans_eq hii.symm⟩
  have := hfirst j hj
  omega

end GaloisForLFunctions.RestrictedFactorizationCalculus
