import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLargeSieveForSquarefreeModuli
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.CoprimeTotientMass

/-! The arithmetic large sieve when each prime outside the modulus omits a residue class. -/

open Finset RHTower.Sieve GaloisForLFunctions.BezoutValuationIncidence

namespace QH.PrimeProgressions

private theorem inv_prime_pred_le_occupied_ratio {A : Finset ℕ} (hA : A.Nonempty)
    {p c : ℕ} (hp : p.Prime) (hc : ∀ n ∈ A, ¬ n ≡ c [MOD p]) :
    1 / ((p : ℝ) - 1) ≤
      ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card := by
  have hsub : occupiedClasses p A ⊆ (range p).erase (c % p) := by
    intro r hr
    have hp' := (mem_filter.mp hr).1
    refine mem_erase.mpr ⟨?_, hp'⟩
    intro e
    have h0 : residueCount p A r = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hnA, hnr⟩ := mem_filter.mp hn
      exact hc n hnA (hnr.trans e)
    exact (mem_filter.mp hr).2 h0
  have hle : (occupiedClasses p A).card ≤ p - 1 := by
    have h := card_le_card hsub
    rwa [card_erase_of_mem (mem_range.mpr (Nat.mod_lt c hp.pos)), card_range] at h
  have hcard : 0 < (occupiedClasses p A).card := by
    obtain ⟨n, hn⟩ := hA
    refine card_pos.mpr ⟨n % p, mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp.pos), ?_⟩⟩
    unfold residueCount
    have hpos : 0 < (A.filter fun m => m % p = n % p).card :=
      card_pos.mpr ⟨n, mem_filter.mpr ⟨hn, rfl⟩⟩
    exact hpos.ne'
  have hcard' : (0 : ℝ) < (occupiedClasses p A).card := by exact_mod_cast hcard
  have hle' : ((occupiedClasses p A).card : ℝ) ≤ (p : ℝ) - 1 := by
    rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub hp.one_le]
    exact_mod_cast hle
  have hp₁ : 0 < (p : ℝ) - 1 := by linarith only [hle', hcard']
  apply (le_div_iff₀ hcard').mpr
  rw [one_div_mul_eq_div]
  exact ((div_le_one hp₁).mpr hle').trans (by linarith only [hle'])

private theorem inv_totient_eq_prod {d : ℕ} (hd : Squarefree d) :
    1 / (d.totient : ℝ) = ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd, mul_comm d.totient d] at h
  have hφ := mul_left_cancel₀ hd.ne_zero h
  rw [hφ, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
  refine prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one, one_div]

/-- A modulus's excluded primes reduce the sieve mass by its totient ratio. -/
theorem card_mul_log_le_of_omitted_classes (N Q q : ℕ) (hQ : 2 ≤ Q) (hq : 0 < q)
    (A : Finset ℕ) (hA : A ⊆ range N) (hAne : A.Nonempty)
    (hclasses : ∀ p, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c, ∀ n ∈ A, ¬ n ≡ c [MOD p]) :
    (A.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1 := by
  refine (mul_le_mul_of_nonneg_left
    ((log_le_coprime_reciprocal_totient_mass Q q hq).trans ?_) (Nat.cast_nonneg _)).trans
    (arithmetic_largeSieve_logFree N hQ A hA hAne)
  let weight (p : ℕ) : ℝ := ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card
  refine (sum_le_sum (g := fun d : ℕ => ∏ p ∈ d.primeFactors, weight p) ?_).trans ?_
  · intro d hd
    obtain ⟨hdQ, hds, hcop⟩ := mem_filter.mp hd
    rw [inv_totient_eq_prod hds]
    refine prod_le_prod ?_ ?_
    · intro p hp
      exact one_div_nonneg.mpr (sub_nonneg.mpr
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
    · intro p hp
      have hpP := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hpQ := (Nat.le_of_dvd (mem_Icc.mp hdQ).1 hpd).trans (mem_Icc.mp hdQ).2
      have hpn : ¬ p ∣ q := hpP.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpd hcop)
      obtain ⟨c, hc⟩ := hclasses p hpP hpQ hpn
      exact inv_prime_pred_le_occupied_ratio hAne hpP hc
  · refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => prod_nonneg fun _ _ => occupied_ratio_nonneg A)
    intro d hd
    exact mem_filter.mpr ⟨(mem_filter.mp hd).1, (mem_filter.mp hd).2.1⟩

end QH.PrimeProgressions
