import GaloisForLFunctions.RHTower.Sieve.BrunTitchmarsh
import GaloisForLFunctions.RHTower.NicolasTotientLandau

/-! Harmonic mass of squarefree divisors coprime to the progression modulus. -/

open Finset Nat ArithmeticFunction

namespace QH.PrimeProgressions

private lemma squarefree_prod_of_prime (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hxx
  have hmem : ∀ t ⊆ s, x ∣ ∏ p ∈ t, p → x ∈ t := by
    intro t ht hdvd
    obtain ⟨p, hp, hxp⟩ := (Prime.dvd_finsetProd_iff hx.prime _).1 hdvd
    rw [(Nat.prime_dvd_prime_iff_eq hx (h p (ht hp))).1 hxp]; exact hp
  have hxs : x ∈ s := hmem s subset_rfl (dvd_trans (dvd_mul_right x x) hxx)
  rw [← Finset.mul_prod_erase s (fun p => p) hxs] at hxx
  have := hmem (s.erase x) (Finset.erase_subset _ _) (Nat.dvd_of_mul_dvd_mul_left hx.pos hxx)
  simp at this

private lemma dvd_pow_of_prime_dvd_imp (n k : ℕ) (h : ∀ p, p.Prime → p ∣ n → p ∣ k) (hn : n ≠ 0) (hk : k ≠ 0) :
    n ∣ k ^ n := by
  rw [← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ hk)]
  intro p
  rw [Nat.factorization_pow]
  by_cases hp : p.Prime ∧ p ∣ n
  · have h1 : 1 ≤ k.factorization p := (hp.1.dvd_iff_one_le_factorization hk).1 (h p hp.1 hp.2)
    have h2 : n.factorization p < n := Nat.factorization_lt p hn
    simp only [Finsupp.smul_apply, smul_eq_mul]
    nlinarith
  · have : n.factorization p = 0 := by
      by_cases hp' : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hp ⟨hp', hd⟩)
      · exact Nat.factorization_eq_zero_of_not_prime _ hp'
    rw [this]; exact Nat.zero_le _

private lemma sum_inv_divisors_eq_sigma_div (N : ℕ) (hN : N ≠ 0) :
    ∑ m ∈ N.divisors, (1 : ℝ) / m = (ArithmeticFunction.sigma 1 N : ℝ) / N := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div, ← Nat.sum_div_divisors]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN := Nat.dvd_of_mem_divisors hd
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast hN
  rw [Nat.cast_div hdN hd0]
  field_simp

private theorem sigma_pow_div_le_totient_ratio (K n : ℕ) (hn : 0 < n) :
    ((sigma 1 (n ^ K) : ℕ) : ℝ) / ((n ^ K : ℕ) : ℝ) ≤ (n : ℝ) / n.totient := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp only [pow_zero, (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_one,
      Nat.cast_one, div_one]
    exact (le_div_iff₀ hφ).mpr (by simpa only [one_mul] using
      (show (n.totient : ℝ) ≤ n by exact_mod_cast Nat.totient_le n))
  · refine (RHTower.sigma_div_le_div_totient (pow_ne_zero _ hn.ne')).trans_eq ?_
    rw [RHTower.div_totient_eq_prod (pow_ne_zero _ hn.ne'), Nat.primeFactors_pow _ hK.ne',
      RHTower.div_totient_eq_prod hn.ne']

/-- Group the harmonic sum by its squarefree part after removing the modulus primes. -/
private theorem sum_inv_le_mul_sum_squarefree_inv_totient (Q q : ℕ) (hq : 1 ≤ q) :
    ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n ≤ ((q:ℝ) / q.totient) *
      ∑ f ∈ (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q), (1:ℝ) / f.totient := by
  set D := (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q) with hD
  set g : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), p with hg
  have hgdvd : ∀ n, g n ∣ n := fun n =>
    dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)) (Nat.prod_primeFactors_dvd n)
  have hgD : ∀ n ∈ Finset.Icc 1 Q, g n ∈ D := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [hD, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.pos_of_dvd_of_pos (hgdvd n) (by omega), le_trans (Nat.le_of_dvd (by omega) (hgdvd n)) hn.2⟩,
      squarefree_prod_of_prime _ fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1,
      Nat.Coprime.prod_left fun p hp => (Nat.Prime.coprime_iff_not_dvd
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).2 (Finset.mem_filter.1 hp).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hgD, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  rw [hD, Finset.mem_filter, Finset.mem_Icc] at hf
  have hf0 : 0 < f := hf.1.1
  have hq0 : 0 < q := hq
  set N := (f * q) ^ Q with hN
  have hN0 : N ≠ 0 := pow_ne_zero _ (Nat.mul_pos hf0 hq0).ne'
  have hfib : ∀ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), f ∣ n ∧ n ∣ N := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨hn.2 ▸ hgdvd n, dvd_trans (dvd_pow_of_prime_dvd_imp n (f * q) ?_ (by omega)
      (Nat.mul_pos hf0 hq0).ne') (pow_dvd_pow _ hn.1.2)⟩
    intro p hp hpn
    by_cases hpq : p ∣ q
    · exact dvd_mul_of_dvd_right hpq _
    · apply dvd_mul_of_dvd_left
      rw [← hn.2]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hp.mem_primeFactors hpn (by omega), hpq⟩)
  have hf0' : (f:ℝ) ≠ 0 := by exact_mod_cast hf0.ne'
  calc ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), (1:ℝ) / n
      = ∑ m ∈ ((Finset.Icc 1 Q).filter (fun n => g n = f)).image (· / f), (1:ℝ) / (f * m) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [← Nat.cast_mul, Nat.mul_div_cancel' (hfib n hn).1]
        · intro x hx y hy hxy
          exact (Nat.div_left_inj (hfib x hx).1 (hfib y hy).1).1 hxy
    _ ≤ ∑ m ∈ N.divisors, (1:ℝ) / (f * m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        exact Nat.mem_divisors.2 ⟨dvd_trans (Nat.div_dvd_of_dvd (hfib n hn).1) (hfib n hn).2, hN0⟩
    _ = (1 / f) * ((ArithmeticFunction.sigma 1 N : ℝ) / N) := by
        rw [← sum_inv_divisors_eq_sigma_div N hN0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [one_div_mul_one_div]
    _ ≤ (q:ℝ) / q.totient * (1 / f.totient) := by
        have hcop : Nat.Coprime (f ^ Q) (q ^ Q) := Nat.Coprime.pow Q Q hf.2.2
        rw [hN, mul_pow, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
        have hA := sigma_pow_div_le_totient_ratio Q f hf0
        have hB := sigma_pow_div_le_totient_ratio Q q hq0
        have hφf : (0 : ℝ) < f.totient := by exact_mod_cast Nat.totient_pos.mpr hf0
        calc
          (1 / (f : ℝ)) * ((↑(sigma 1 (f ^ Q) * sigma 1 (q ^ Q)) : ℝ) /
              ((f ^ Q * q ^ Q : ℕ) : ℝ))
              = (1 / (f : ℝ)) * ((sigma 1 (f ^ Q) : ℝ) / ((f ^ Q : ℕ) : ℝ)) *
                ((sigma 1 (q ^ Q) : ℝ) / ((q ^ Q : ℕ) : ℝ)) := by
                  push_cast
                  ring
          _ ≤ (1 / (f : ℝ)) * ((f : ℝ) / f.totient) * ((q : ℝ) / q.totient) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hB
              (by positivity) (by positivity)
          _ = (q : ℝ) / q.totient * (1 / (f.totient : ℝ)) := by
            have hfR : (0 : ℝ) < f := by exact_mod_cast hf0
            field_simp

/-- The reciprocal totient weights retain logarithmic mass after deleting the primes
dividing the modulus, with the expected totient factor. -/
theorem log_le_coprime_reciprocal_totient_mass (Y q : ℕ) (hq : 0 < q) :
    (q.totient : ℝ) / q * Real.log Y ≤
      ∑ f ∈ (Icc 1 Y).filter (fun f => Squarefree f ∧ f.Coprime q), (1 : ℝ) / f.totient := by
  have hlog := (RHTower.Sieve.log_le_sum_inv Y).trans
    (sum_inv_le_mul_sum_squarefree_inv_totient Y q hq)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  have h := mul_le_mul_of_nonneg_left hlog (div_nonneg hφ.le hq₀.le)
  refine h.trans_eq ?_
  have hratio : (q.totient : ℝ) / q * ((q : ℝ) / q.totient) = 1 := by
    field_simp
  rw [← mul_assoc, hratio, one_mul]

end QH.PrimeProgressions
