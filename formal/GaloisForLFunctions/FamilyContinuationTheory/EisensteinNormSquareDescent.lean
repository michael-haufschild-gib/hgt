import GaloisForLFunctions.FamilyContinuationTheory.TheNormCountOfTheEisensteinIntegers

/-!
# Square-factor descent for Eisenstein norms

Multiplication by a nonzero rational square does not change representability
by `a² - ab + b²`. At split or ramified primes, cancel a prime Eisenstein
factor twice. At inert primes, cancel the rational prime itself.

This supplies the arithmetic obstruction in Kittipassorn--Phetmak--Sriamorn,
*Covering the Triangular Lattice with Non-Overlapping Unit Disks*, Lemma 7.5,
directly from the corpus's norm-factorization lemmas.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm

open _root_.RHTower

local notation "𝔼" => BourgainEisensteinInt
local notation "N" => BourgainEisensteinInt.norm
local notation "cj" => BourgainEisensteinInt.conj

/-- A represented rational prime can be cancelled from any represented norm. -/
theorem normSet_prime_mul_nonempty_iff {p : ℕ} (hp : p.Prime)
    (hrep : (normSet p).Nonempty) (n : ℕ) :
    (normSet (p * n)).Nonempty ↔ (normSet n).Nonempty := by
  obtain ⟨π, hπ⟩ := hrep
  have hnπ : N π = p := mem_normSet.mp hπ
  have hnπc : N (cj π) = p := by rw [norm_conj, hnπ]
  constructor
  · rintro ⟨t, ht⟩
    have hpd : π ∣ (p : 𝔼) := ⟨cj π, by
      rw [BourgainEisensteinInt.mul_conj, hnπ]
      rfl⟩
    have hdiv : π ∣ t * cj t := hpd.trans (natCast_dvd_mul_conj (mem_normSet.mp ht))
    rcases (prime_of_norm_prime hp hnπ).dvd_or_dvd hdiv with h | h
    · obtain ⟨z, rfl⟩ := h
      exact ⟨z, mem_normSet_of_mul hp.pos hnπ ht⟩
    · obtain ⟨z, rfl⟩ := conj_dvd_of_dvd h
      exact ⟨z, mem_normSet_of_mul hp.pos hnπc ht⟩
  · rintro ⟨z, hz⟩
    exact ⟨π * z, mul_mem_normSet hnπ hz⟩

/-- Every rational prime square can be cancelled, including inert primes. -/
theorem normSet_prime_square_nonempty_iff {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (normSet (p * (p * n))).Nonempty ↔ (normSet n).Nonempty := by
  by_cases h2 : p % 3 = 2
  · constructor
    · rintro ⟨t, ht⟩
      obtain ⟨z, rfl⟩ := natCast_dvd_of_two hp h2 ht
      have hz := ((mem_normSet_natCast_mul hp.pos).mp ht).2
      rw [Nat.mul_div_cancel_left n hp.pos] at hz
      exact ⟨z, hz⟩
    · rintro ⟨z, hz⟩
      refine ⟨(p : 𝔼) * z, (mem_normSet_natCast_mul hp.pos).mpr ⟨dvd_mul_right p n, ?_⟩⟩
      simpa only [Nat.mul_div_cancel_left n hp.pos] using hz
  · have hrep : (normSet p).Nonempty := by
      rcases (by omega : p % 3 = 0 ∨ p % 3 = 1) with h0 | h1
      · have hp3 : p = 3 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
            (Nat.dvd_of_mod_eq_zero h0)).symm
        subst p
        exact ⟨lam, mem_normSet.mpr norm_lam⟩
      · obtain ⟨π, hπ⟩ := exists_norm_eq_of_mod_three_eq_one hp h1
        exact ⟨π, mem_normSet.mpr hπ⟩
    rw [normSet_prime_mul_nonempty_iff hp hrep,
      normSet_prime_mul_nonempty_iff hp hrep]

/-- A square factor changes norm representability only when that factor is zero. -/
theorem normSet_square_factor_nonempty_iff (n m : ℕ) :
    (normSet (n * m ^ 2)).Nonempty ↔ m = 0 ∨ (normSet n).Nonempty := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm0 : m = 0
    · subst m
      have hz : (normSet 0).Nonempty := ⟨0, mem_normSet.mpr (by simp)⟩
      simpa only [zero_pow two_ne_zero, mul_zero, true_or, iff_true] using hz
    by_cases hm1 : m = 1
    · subst m
      simp only [one_pow, mul_one, one_ne_zero, false_or]
    let p := m.minFac
    have hp : p.Prime := Nat.minFac_prime hm1
    obtain ⟨q, hq⟩ := Nat.minFac_dvd m
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, mul_zero] at hq
      exact hm0 hq
    have hqm : q < m := by
      rw [hq]
      exact lt_mul_left (Nat.pos_of_ne_zero hq0) hp.one_lt
    have heq : n * m ^ 2 = p * (p * (n * q ^ 2)) := by
      rw [hq]
      ring
    rw [heq, normSet_prime_square_nonempty_iff hp, ih q hqm]
    simp only [hq0, hm0, false_or]

/-- Nonrepresentability persists on every nonzero square multiple. -/
theorem normSet_square_factor_empty_iff (n m : ℕ) :
    normSet (n * m ^ 2) = ∅ ↔ m ≠ 0 ∧ normSet n = ∅ := by
  simpa only [Finset.not_nonempty_iff_eq_empty, not_or] using
    not_congr (normSet_square_factor_nonempty_iff n m)

/-- Positive quadratic-character divisor sums detect nonempty norm shells. -/
theorem normSet_nonempty_iff_divisorChar_pos {n : ℕ} (hn : 0 < n) :
    (normSet n).Nonempty ↔ 0 < divisorChar n := by
  have hcount := card_normSet hn
  rw [← Finset.card_pos]
  constructor
  · intro h
    have hc : (0 : ℤ) < (normSet n).card := by exact_mod_cast h
    linarith only [hc, hcount]
  · intro h
    have hc : (0 : ℤ) < (normSet n).card := by linarith only [h, hcount]
    exact_mod_cast hc

/-- The sign of the cubic norm-count divisor sum is invariant under nonzero squares. -/
theorem divisorChar_square_factor_pos_iff (n m : ℕ) :
    0 < divisorChar (n * m ^ 2) ↔ m ≠ 0 ∧ 0 < divisorChar n := by
  by_cases hn : n = 0
  · subst n
    simp only [zero_mul, divisorChar, Nat.divisors_zero, Finset.sum_empty,
      lt_self_iff_false, and_false]
  by_cases hm : m = 0
  · subst m
    simp only [zero_pow two_ne_zero, mul_zero, divisorChar, Nat.divisors_zero,
      Finset.sum_empty, lt_self_iff_false, ne_eq, not_true_eq_false, false_and]
  rw [← normSet_nonempty_iff_divisorChar_pos (Nat.mul_pos (Nat.pos_of_ne_zero hn)
      (pow_pos (Nat.pos_of_ne_zero hm) 2)),
    normSet_square_factor_nonempty_iff,
    normSet_nonempty_iff_divisorChar_pos (Nat.pos_of_ne_zero hn)]
  simp only [ne_eq, hm, false_or, not_false_eq_true, true_and]

/-- An integer represented over the rational Eisenstein plane is already an integral norm. -/
theorem rational_norm_iff_integral_norm (n : ℕ) :
    (∃ a b : ℚ, a ^ 2 - a * b + b ^ 2 = n) ↔ (normSet n).Nonempty := by
  constructor
  · rintro ⟨a, b, hab⟩
    let m : ℕ := a.den * b.den
    let A : ℤ := a.num * (b.den : ℤ)
    let B : ℤ := b.num * (a.den : ℤ)
    have hm : m ≠ 0 := mul_ne_zero a.den_ne_zero b.den_ne_zero
    have ha : (a.num : ℚ) = a * (a.den : ℚ) :=
      (div_eq_iff (Nat.cast_ne_zero.mpr a.den_ne_zero)).mp (Rat.num_div_den a)
    have hb : (b.num : ℚ) = b * (b.den : ℚ) :=
      (div_eq_iff (Nat.cast_ne_zero.mpr b.den_ne_zero)).mp (Rat.num_div_den b)
    have hA : (A : ℚ) = a * (m : ℚ) := by
      dsimp [A, m]
      push_cast
      rw [ha]
      ring
    have hB : (B : ℚ) = b * (m : ℚ) := by
      dsimp [B, m]
      push_cast
      rw [hb]
      ring
    have hpoly : (A : ℚ) ^ 2 - (A : ℚ) * B + (B : ℚ) ^ 2 = (n * m ^ 2 : ℕ) := by
      rw [hA, hB]
      push_cast
      calc
        (a * m) ^ 2 - (a * m) * (b * m) + (b * m) ^ 2 =
            (a ^ 2 - a * b + b ^ 2) * m ^ 2 := by ring
        _ = _ := by rw [hab]
    have hnorm : N (⟨A, B⟩ : 𝔼) = (n * m ^ 2 : ℕ) := by
      change A ^ 2 - A * B + B ^ 2 = (n * m ^ 2 : ℕ)
      exact_mod_cast hpoly
    exact ((normSet_square_factor_nonempty_iff n m).mp
      ⟨⟨A, B⟩, mem_normSet.mpr hnorm⟩).resolve_left hm
  · rintro ⟨z, hz⟩
    refine ⟨z.re, z.im, ?_⟩
    have h := mem_normSet.mp hz
    rw [BourgainEisensteinInt.norm_def] at h
    exact_mod_cast h

end GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm

#print axioms GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm.normSet_prime_square_nonempty_iff
#print axioms GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm.normSet_square_factor_nonempty_iff
#print axioms GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm.normSet_square_factor_empty_iff
#print axioms GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm.divisorChar_square_factor_pos_iff
#print axioms GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm.rational_norm_iff_integral_norm
