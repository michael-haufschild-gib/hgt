import GaloisForLFunctions.HTGeometry.ABHN.ZModReciprocitySupportCongruence
import GaloisForLFunctions.RHTower.DeckChargeCalculus

/-!
# Hasse support laws for conserved deck charges

Interior deck charges form a finite `ZMod n` profile.  Boundary neutrality makes its sum zero, so
one nonzero box charge forces another.  Generator-valued profiles have support divisible by `n`,
and the double-cover case has even support without any generator hypothesis.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry.ABHN

/-- Finite profile of deck charges carried by selected interior boxes. -/
noncomputable def deckInteriorChargeProfile {ι : Type*} (n : ℕ)
    (s : Finset ι) (idx : ι → ℤ) : ι →₀ ZMod n := by
  classical
  exact Finsupp.onFinset s
    (fun i => if i ∈ s then wCharge n (idx i) else 0)
    (by
      intro i hi
      by_contra his
      simp [his] at hi)

@[simp]
theorem deckInteriorChargeProfile_apply {ι : Type*} [DecidableEq ι] (n : ℕ)
    (s : Finset ι) (idx : ι → ℤ) (i : ι) :
    deckInteriorChargeProfile n s idx i =
      if i ∈ s then wCharge n (idx i) else 0 := by
  classical
  simp [deckInteriorChargeProfile]

/-- The profile sum is the sum of the selected interior charges. -/
theorem deckInteriorChargeProfile_sum {ι : Type*} (n : ℕ)
    (s : Finset ι) (idx : ι → ℤ) :
    (deckInteriorChargeProfile n s idx).sum (fun _ z => z) =
      ∑ i ∈ s, wCharge n (idx i) := by
  classical
  rw [deckInteriorChargeProfile, Finsupp.onFinset_sum
    (by
      intro i hi
      by_contra his
      simp [his] at hi)
    (by intros; rfl)]
  simp

/-- Boundary-neutrality is zero-sum reciprocity for the interior charge profile. -/
theorem deckInteriorChargeProfile_sum_eq_zero {ι : Type*} (n : ℕ)
    (s : Finset ι) (idx : ι → ℤ)
    (hbdry : wCharge n (∑ i ∈ s, idx i) = 0) :
    (deckInteriorChargeProfile n s idx).sum (fun _ z => z) = 0 := by
  rw [deckInteriorChargeProfile_sum]
  exact interior_charge_conservation n s idx hbdry

/-- A nonzero interior deck charge has a distinct nonzero interior partner. -/
theorem deckInteriorChargeProfile_exists_other_nonzero_box
    {ι : Type*} [DecidableEq ι] (n : ℕ)
    (s : Finset ι) (idx : ι → ℤ)
    (hbdry : wCharge n (∑ i ∈ s, idx i) = 0)
    {i : ι} (hi : i ∈ s) (hcharge : wCharge n (idx i) ≠ 0) :
    ∃ j, j ∈ s ∧ j ≠ i ∧ wCharge n (idx j) ≠ 0 := by
  obtain ⟨j, hji, hj⟩ := finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (deckInteriorChargeProfile n s idx)
    (deckInteriorChargeProfile_sum_eq_zero n s idx hbdry)
    (i := i) (by simp [hi, hcharge])
  have hjs : j ∈ s := by
    by_contra h
    exact hj (by simp [h])
  exact ⟨j, hjs, hji, by simpa [hjs] using hj⟩

/-- Generator-valued conserved deck charge occupies a multiple of `n` interior boxes. -/
theorem deckInteriorChargeProfile_modulus_dvd_support_card
    {ι : Type*} [DecidableEq ι] (n : ℕ)
    (s : Finset ι) (idx : ι → ℤ)
    (hbdry : wCharge n (∑ i ∈ s, idx i) = 0)
    (hone : ∀ i ∈ (deckInteriorChargeProfile n s idx).support,
      deckInteriorChargeProfile n s idx i = 1) :
    n ∣ (deckInteriorChargeProfile n s idx).support.card := by
  exact (finsuppZMod_sum_eq_zero_iff_dvd_support_card_of_eq_one
    n (deckInteriorChargeProfile n s idx) hone).mp
      (deckInteriorChargeProfile_sum_eq_zero n s idx hbdry)

/-- Conserved double-cover deck charge occupies an even number of boxes. -/
theorem deckInteriorChargeProfile_two_even_support
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (idx : ι → ℤ)
    (hbdry : wCharge 2 (∑ i ∈ s, idx i) = 0) :
    Even (deckInteriorChargeProfile 2 s idx).support.card :=
  (finsuppZModTwo_sum_eq_zero_iff_even_support_card
    (deckInteriorChargeProfile 2 s idx)).mp
      (deckInteriorChargeProfile_sum_eq_zero 2 s idx hbdry)

end RHTower
