import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeIntervals
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.OmittedResidueMass
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! A uniform upper bound for primes in a short arithmetic progression. -/

open Finset

namespace QH.PrimeProgressions

private theorem exists_dvd_mul_add_of_prime (l q r : ℕ) (hl : l.Prime) (hq : ¬ l ∣ q) : ∃ c : ℕ, l ∣ q * c + r := by
  haveI := Fact.mk hl
  have hq' : (q : ZMod l) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q l).1 h)
  refine ⟨(-(r : ZMod l) * (q : ZMod l)⁻¹).val, (ZMod.natCast_eq_zero_iff _ l).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

private theorem card_large_primes_class_le (q a Q M N : ℕ) (P : Finset ℕ) (hq : 1 ≤ q) (hQ : 2 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≡ a [MOD q] ∧ Q < p ∧ q * M ≤ p ∧ p < q * (M + N)) :
    (P.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1 := by
  classical
  by_cases hPne : P.Nonempty
  · have hdec (p : ℕ) (hp : p ∈ P) : p = q * (p / q) + a % q := by
      have he : p % q = a % q := (hP p hp).2.1
      rw [← he, Nat.div_add_mod]
    have hlo (p : ℕ) (hp : p ∈ P) : M ≤ p / q :=
      (Nat.le_div_iff_mul_le hq).2 (by simpa only [mul_comm M q] using (hP p hp).2.2.2.1)
    let S := P.image (fun p => p / q - M)
    have hS : S ⊆ range N := by
      intro n hn
      obtain ⟨p, hm, rfl⟩ := mem_image.mp hn
      have hi : p / q < M + N :=
        (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [mul_comm (M + N) q] using (hP p hm).2.2.2.2)
      have hM := hlo p hm
      exact mem_range.mpr (by omega)
    have hcard : S.card = P.card := card_image_of_injOn (by
      intro p hp p' hp' h
      change p / q - M = p' / q - M at h
      have h₁ := hlo p hp
      have h₂ := hlo p' hp'
      have hdiv : p / q = p' / q := by omega
      rw [hdec p hp, hdec p' hp', hdiv])
    have hsieve := card_mul_log_le_of_omitted_classes N Q q hQ hq S hS
      (hPne.image _) (by
        intro l hl hlQ hlq
        obtain ⟨c, hc⟩ := exists_dvd_mul_add_of_prime l q (q * M + a % q) hl hlq
        refine ⟨c, fun n hn hnc => ?_⟩
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
        have hmod := (hnc.mul_left q).add_right (q * M + a % q)
        have hleft : q * (p / q - M) + (q * M + a % q) = p := by
          calc
            _ = q * ((p / q - M) + M) + a % q := by ring
            _ = _ := by rw [Nat.sub_add_cancel (hlo p hp)]; exact (hdec p hp).symm
        rw [hleft] at hmod
        have hlp := Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hc))
        have he := (Nat.prime_dvd_prime_iff_eq hl (hP p hp).1).mp hlp
        exact (not_lt_of_ge hlQ) (he ▸ (hP p hp).2.2.1))
    rwa [hcard] at hsieve
  · rw [not_nonempty_iff_eq_empty.mp hPne, card_empty, Nat.cast_zero, zero_mul]
    have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith only [hQ', sq_nonneg ((Q : ℝ) - 2), Nat.cast_nonneg (α := ℝ) N]

/-- The Brun–Titchmarsh upper bound, uniform in the modulus and reduced class. -/
theorem brun_titchmarsh_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  refine ⟨48, by norm_num, fun q a x y hq _ hx hy => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = y / q := ⟨_, rfl⟩
  have hyz : y = q * z := by rw [hz]; field_simp
  have hz2 : 2 ≤ z := by rw [hz, le_div_iff₀ hq0]; exact hy
  rw [← hz]
  have hfl : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz2)
  have hflz : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzfl : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt ⌊z⌋₊ := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hs2 : s * s ≤ ⌊z⌋₊ := hs ▸ Nat.sqrt_le _
  have hs3 : ⌊z⌋₊ < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt _
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = s + 1 := ⟨_, rfl⟩
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast (by omega : 2 ≤ Q)
  have hQz : (Q : ℝ) ^ 2 ≤ 4 * z := by
    have : Q ^ 2 ≤ 4 * ⌊z⌋₊ := by rw [hQ]; nlinarith
    have : (Q : ℝ) ^ 2 ≤ 4 * ⌊z⌋₊ := by exact_mod_cast this
    linarith
  have hzQ : z ≤ (Q : ℝ) ^ 2 := by
    have : ⌊z⌋₊ + 1 ≤ Q ^ 2 := by rw [hQ]; nlinarith
    have : (⌊z⌋₊ : ℝ) + 1 ≤ (Q : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log z ≤ 2 * Real.log Q := by
    have := Real.log_le_log (by linarith) hzQ
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hlQ : Real.log Q ≤ Q := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Q)
    linarith
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set P := (primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q]) with hP
  have hbig := card_large_primes_class_le q a Q (⌊x⌋₊ / q) (⌊z⌋₊ + 2) (P.filter fun p => Q < p) hq (by omega) (by
    intro p hp
    simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    refine ⟨h3, h4, h5, (Nat.mul_div_le _ _).trans h1.le, ?_⟩
    have h6 : (p : ℝ) ≤ x + y := (Nat.le_floor_iff (by nlinarith)).1 h2
    have h7 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h8 : ⌊x⌋₊ + 1 ≤ q * (⌊x⌋₊ / q + 1) := Nat.lt_mul_div_succ _ hq
    have h9 : (⌊x⌋₊ : ℝ) + 1 ≤ q * (((⌊x⌋₊ / q : ℕ) : ℝ) + 1) := by exact_mod_cast h8
    have h10 : (p : ℝ) < q * (((⌊x⌋₊ / q : ℕ) : ℝ) + (⌊z⌋₊ + 2)) := by nlinarith
    exact_mod_cast h10)
  have hsmall : (P.filter fun p => ¬ Q < p).card ≤ Q := by
    calc _ ≤ (Finset.Icc 1 Q).card := Finset.card_le_card fun p hp => by
            simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
            exact Finset.mem_Icc.2 ⟨hp.1.1.2.one_le, by omega⟩
      _ = Q := by simp
  have hsum := Finset.card_filter_add_card_filter_not (s := P) (fun p => Q < p)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((P.filter fun p => Q < p).card : ℝ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ Nat.cast_nonneg _
  have hcard : (P.card : ℝ) ≤ B + Q := by
    rw [hB]; exact_mod_cast (by omega)
  rw [← hB] at hbig
  push_cast at hbig
  have h1 : B * ((q.totient : ℝ) / q * Real.log Q) ≤ 20 * z := by
    linarith only [hbig, hflz, hQz, hz2]
  have h2 : B * (q.totient * Real.log Q) ≤ 20 * y := by
    have := mul_le_mul_of_nonneg_left h1 hq0.le
    rw [hyz]
    calc _ = q * (B * ((q.totient : ℝ) / q * Real.log Q)) := by field_simp
      _ ≤ _ := by linarith
  have h3 : B * (q.totient * Real.log z) ≤ 40 * y := by
    have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB0 hφ0.le)
    nlinarith
  have h4 : (Q : ℝ) * Real.log z ≤ 8 * z := by nlinarith
  have h5 : (Q : ℝ) * (q.totient * Real.log z) ≤ 8 * y := by
    have : (q.totient : ℝ) * (Q * Real.log z) ≤ q * (8 * z) :=
      mul_le_mul hφq h4 (by positivity) hq0.le
    rw [hyz]; nlinarith
  rw [le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ q.totient * Real.log z)
  nlinarith

end QH.PrimeProgressions
