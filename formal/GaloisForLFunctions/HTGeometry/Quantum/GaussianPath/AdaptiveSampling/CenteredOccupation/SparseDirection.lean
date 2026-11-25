import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw

/-! # A transverse direction supported on few coordinates -/

open Finset
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Absolute charge carried by a set of axes. -/
def chargeOn (m : I → ℤ) (s : Finset I) : ℕ := ∑ i ∈ s, (m i).natAbs

/-- If the total charge reaches L, at most L nonzero axes already
carry that much charge. -/
theorem sparse_charge (m : I → ℤ) (L : ℕ) (hL : L≤chargeOn m univ) :
    ∃ s : Finset I, s.card≤L ∧ L≤chargeOn m s := by
  let u := univ.filter fun i => m i≠0
  by_cases h : L≤u.card
  · obtain ⟨s,hs,hc⟩ := exists_subset_card_eq h
    refine ⟨s,hc.le,?_⟩
    calc
      L = ∑ _i ∈ s, 1 := by simp [hc]
      _ ≤ chargeOn m s := sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr
        (Int.natAbs_ne_zero.mpr (mem_filter.mp (hs hi)).2)
  · refine ⟨u,(lt_of_not_ge h).le,?_⟩
    have he : chargeOn m u=chargeOn m univ := by
      apply sum_subset (filter_subset _ _)
      intro i hi hu
      have hz : m i=0 := by
        by_contra hn
        exact hu (mem_filter.mpr ⟨hi,hn⟩)
      rw [hz,Int.natAbs_zero]
    rwa [he]

/-- Signed unit displacement on the selected axes. -/
def signedDirection (m : I → ℤ) (s : Finset I) (i : I) : ℝ :=
  if i∈s then if 0≤m i then 1 else -1 else 0

theorem signed_detuning (m : I → ℤ) (s : Finset I) :
    finiteTorusCharacterDetuning m (signedDirection m s)=chargeOn m s := by
  simp only [finiteTorusCharacterDetuning,chargeOn,Nat.cast_sum]
  have hsum : ∑ i ∈ s, (m i:ℝ)*signedDirection m s i=∑ i, (m i:ℝ)*signedDirection m s i :=
    sum_subset (subset_univ s) fun i _ hi => by rw [signedDirection,if_neg hi,mul_zero]
  rw [←hsum]
  apply sum_congr rfl
  intro i hi
  rw [signedDirection,if_pos hi]
  have hab : ((m i).natAbs:ℝ)=|(m i:ℝ)| := by exact_mod_cast Int.natCast_natAbs (m i)
  rw [hab]
  by_cases h : 0≤m i
  · rw [if_pos h,mul_one,abs_of_nonneg (by exact_mod_cast h : 0≤(m i:ℝ))]
  · rw [if_neg h,mul_neg_one,abs_of_neg (by exact_mod_cast lt_of_not_ge h : (m i:ℝ)<0)]

end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
