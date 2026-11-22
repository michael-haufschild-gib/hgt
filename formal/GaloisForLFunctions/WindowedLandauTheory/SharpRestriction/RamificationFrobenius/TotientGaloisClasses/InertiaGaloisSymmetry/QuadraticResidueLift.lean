import Mathlib

/-! Lifting a square root modulo prime powers and then a composite modulus. -/

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace WindowedLandauTheory.HC.Der

theorem sq_two_pow {d : ℤ} (hd : d % 8 = 7) (k : ℕ) : ∃ s : ℤ, (2 : ℤ) ^ (k + 3) ∣ s ^ 2 + d := by
  induction k with
  | zero => exact ⟨1, by norm_num; omega⟩
  | succ k ih =>
    obtain ⟨s, t, ht⟩ := ih
    have e3 : (2 : ℤ) ^ (k + 3) = 8 * 2 ^ k := by ring
    rw [e3] at ht
    have hs1 : s % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one s with hs0 | hs1
      · exfalso
        obtain ⟨c, rfl⟩ : ∃ c, s = 2 * c := ⟨s / 2, by omega⟩
        have hd2 : d = 2 * (4 * 2 ^ k * t - 2 * c ^ 2) := by linear_combination ht
        have : d % 2 = 0 := by rw [hd2]; exact Int.mul_emod_right 2 _
        omega
      · exact hs1
    obtain ⟨a, rfl⟩ : ∃ a, s = 2 * a + 1 := ⟨s / 2, by omega⟩
    rcases Int.emod_two_eq_zero_or_one t with ht0 | ht1
    · obtain ⟨b, rfl⟩ : ∃ b, t = 2 * b := ⟨t / 2, by omega⟩
      refine ⟨2 * a + 1, b, ?_⟩
      have e4 : (2 : ℤ) ^ (k + 1 + 3) = 16 * 2 ^ k := by ring
      rw [e4]
      linear_combination ht
    · obtain ⟨b, rfl⟩ : ∃ b, t = 2 * b + 1 := ⟨t / 2, by omega⟩
      refine ⟨2 * a + 1 + 2 ^ (k + 2), a + b + 1 + 2 ^ k, ?_⟩
      have e2 : (2 : ℤ) ^ (k + 2) = 4 * 2 ^ k := by ring
      have e4 : (2 : ℤ) ^ (k + 1 + 3) = 16 * 2 ^ k := by ring
      rw [e2, e4]
      linear_combination ht

theorem sq_odd_pow {d : ℤ} {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hj : jacobiSym (-d) l = 1) (k : ℕ) :
    ∃ s : ℤ, (l : ℤ) ^ (k + 1) ∣ s ^ 2 + d := by
  haveI := Fact.mk hl
  have hl2' : (2 : ZMod l) ≠ 0 := by
    intro h
    have h' : ((2 : ℤ) : ZMod l) = 0 := by exact_mod_cast h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    have h'' : l ∣ 2 := by exact_mod_cast h'
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h'')
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have hd0 : ((-d : ℤ) : ZMod l) ≠ 0 := by
    intro h
    rw [(legendreSym.eq_zero_iff l (-d)).mpr h] at hj
    norm_num at hj
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff l hd0).mp hj
  induction k with
  | zero =>
    refine ⟨(r.val : ℤ), ?_⟩
    rw [zero_add, pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    push_cast at hr
    linear_combination (-1 : ZMod l) * hr
  | succ k ih =>
    obtain ⟨s, t, ht⟩ := ih
    have hs0 : (s : ZMod l) ≠ 0 := by
      intro h
      have h1 : ((s ^ 2 + d : ℤ) : ZMod l) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
        exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero k)) t
      push_cast at h1
      rw [h] at h1
      apply hd0
      push_cast
      linear_combination -h1
    have h2s : (2 * (s : ZMod l)) ≠ 0 := mul_ne_zero hl2' hs0
    obtain ⟨c, hc'⟩ := ZMod.intCast_surjective (n := l) (-(t : ZMod l) * (2 * (s : ZMod l))⁻¹)
    have hc : ((t + 2 * s * c : ℤ) : ZMod l) = 0 := by
      push_cast
      rw [hc']
      have hi : (2 * (s : ZMod l)) * (2 * (s : ZMod l))⁻¹ = 1 := mul_inv_cancel₀ h2s
      linear_combination (-(t : ZMod l)) * hi
    obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp hc
    refine ⟨s + (l : ℤ) ^ (k + 1) * c, w + (l : ℤ) ^ k * c ^ 2, ?_⟩
    linear_combination ht + (l : ℤ) ^ (k + 1) * hw

theorem sq_mod {d : ℤ} (hd : d % 8 = 7) (m : ℕ) (hm0 : m ≠ 0)
    (hm : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ m → jacobiSym (-d) l = 1) : ∃ s : ℤ, (m : ℤ) ∣ s ^ 2 + d := by
  revert hm0 hm
  induction m using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p n hp =>
    intro _ hm
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨s, hs⟩ := sq_two_pow hd n
      exact ⟨s, by push_cast; exact (pow_dvd_pow 2 (by omega)).trans hs⟩
    · rcases n with _ | n
      · exact ⟨0, by simp⟩
      · obtain ⟨s, hs⟩ := sq_odd_pow hp hp2 (hm p hp hp2 (dvd_pow_self p (Nat.succ_ne_zero n))) n
        exact ⟨s, by push_cast; exact hs⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ hm
    obtain ⟨sa, hsa⟩ := iha (by omega) (fun l hl hl2 hla => hm l hl hl2 (Dvd.dvd.mul_right hla b))
    obtain ⟨sb, hsb⟩ := ihb (by omega) (fun l hl hl2 hlb => hm l hl hl2 (Dvd.dvd.mul_left hlb a))
    have hco : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
    obtain ⟨x, y, hxy⟩ := hco
    refine ⟨sa + a * (x * (sb - sa)), ?_⟩
    push_cast
    apply IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr hab)
    · obtain ⟨k, hk⟩ := hsa
      exact ⟨k + 2 * sa * (x * (sb - sa)) + a * (x * (sb - sa)) ^ 2, by linear_combination hk⟩
    · obtain ⟨k, hk⟩ := hsb
      refine ⟨k + 2 * sb * (-y * (sb - sa)) + b * (-y * (sb - sa)) ^ 2, ?_⟩
      linear_combination hk + (sb - sa) * ((sa + a * (x * (sb - sa))) +
        (sb + b * (-y * (sb - sa)))) * hxy

end WindowedLandauTheory.HC.Der

end
