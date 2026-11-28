import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslationInvariantCharacterOrbits
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldCharacterOrbits

/-! A regular squaring orbit of length six invariant under translation
by an element of order three is the set of elements of order nine. -/

open Finset

namespace GlobalTheory.EllipticCharacters

open Classical in
theorem squaringOrbit_eq_orderNine {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    (hG : Fintype.card G = 63) (θ τ : G) (hτ : orderOf τ = 3)
    (hθ : ∀ i j : ℕ, i < 6 → j < 6 → θ ^ 2 ^ i = θ ^ 2 ^ j → i = j)
    (hstab : ∀ x ∈ (range 6).image (fun j => θ ^ 2 ^ j), x * τ ∈ (range 6).image (fun j => θ ^ 2 ^ j)) :
    (range 6).image (fun j => θ ^ 2 ^ j) = univ.filter (fun x : G => orderOf x = 9) := by
  let S := (range 6).image (fun j => θ ^ 2 ^ j)
  have hS : #S = 6 := by
    rw [Finset.card_image_of_injOn, card_range]
    intro i hi j hj h
    exact hθ i j (mem_range.mp hi) (mem_range.mp hj) h
  let H := Subgroup.zpowers τ
  let q := QuotientGroup.mk' H
  let B := S.image q
  have hB : #B = 2 := by
    have hcount := card_eq_orderOf_mul_card_image_quotient S τ hstab
    change #S = orderOf τ * #B at hcount
    rw [hS, hτ] at hcount
    omega
  let x := q θ
  have hmem (i : ℕ) (hi : i < 6) : x ^ 2 ^ i ∈ B := by
    rw [← map_pow]
    exact mem_image_of_mem _ (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
  have hx0 : x ∈ B := by simpa only [pow_zero, pow_one] using hmem 0 (by omega)
  have hx1 : x ^ 2 ∈ B := by simpa only [pow_one] using hmem 1 (by omega)
  have hx2 : x ^ 4 ∈ B := hmem 2 (by omega)
  have hx3 : x ^ 3 = 1 := by
    by_cases he : x ^ 2 = x
    · have hx : x = 1 := mul_right_cancel (by simpa only [pow_two, one_mul] using he)
      simp [hx]
    have hpair : ({x ^ 2, x} : Finset (G ⧸ H)) = B := by
      apply Finset.eq_of_subset_of_card_le
      · simp only [insert_subset_iff, singleton_subset_iff, hx0, hx1, and_self]
      · rw [hB, card_insert_of_notMem (by simpa using he), card_singleton]
    rw [← hpair, mem_insert, mem_singleton] at hx2
    rcases hx2 with h | h
    · have hsq : x ^ 2 = 1 := by
        apply mul_right_cancel (b := x ^ 2)
        rw [← pow_add, one_mul]
        exact h
      have hx63 : x ^ 63 = 1 := by
        change q θ ^ 63 = 1
        rw [← hG, ← map_pow, pow_card_eq_one, map_one]
      have hdiv := Nat.dvd_gcd
        (orderOf_dvd_iff_pow_eq_one.mpr hsq) (orderOf_dvd_iff_pow_eq_one.mpr hx63)
      have ho : orderOf x = 1 := Nat.dvd_one.mp hdiv
      simp [orderOf_eq_one_iff.mp ho]
    · apply mul_right_cancel (b := x)
      rw [← pow_succ, one_mul]
      exact h
  have ht : θ ^ 3 ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [← show q (θ ^ 3) = _ from map_pow q θ 3] at hx3
    exact hx3
  have ht9 : θ ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h := orderOf_dvd_of_mem_zpowers ht
    rwa [hτ] at h
  have ht3 : θ ^ 3 ≠ 1 := fun h => by
    have he : θ ^ 2 ^ (0 : ℕ) = θ ^ 2 ^ (2 : ℕ) := by
      change θ ^ 1 = θ ^ 4
      rw [pow_one, pow_succ, h, one_mul]
    have := hθ 0 2 (by omega) (by omega) he
    omega
  have ho : orderOf θ = 9 := by
    obtain ⟨j, hj, h⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (orderOf_dvd_iff_pow_eq_one.mpr ht9 : orderOf θ ∣ 3 ^ 2)
    have hj2 : j = 2 := by
      by_contra hj'
      have hj1 : j ≤ 1 := by omega
      apply ht3
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [h]
      exact pow_dvd_pow 3 hj1
    rw [h, hj2]
    norm_num
  change S = _
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    have hcop : (orderOf θ).Coprime (2 ^ i) := by
      rw [ho]
      exact (show (9 : ℕ).Coprime 2 by norm_num).pow_right i
    simp [hcop.orderOf_pow, ho]
  · rw [IsCyclic.card_orderOf_eq_totient (show 9 ∣ Fintype.card G by rw [hG]; norm_num), hS]
    change Nat.totient (3 ^ 2) ≤ 6
    rw [Nat.totient_prime_pow Nat.prime_three (by omega)]
    norm_num

end GlobalTheory.EllipticCharacters
