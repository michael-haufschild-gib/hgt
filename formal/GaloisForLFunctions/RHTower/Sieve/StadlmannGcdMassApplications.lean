import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaNine

/-!
# Stadlmann gcd-sum applications

Lemma 10 of Stadlmann's bounded-gaps paper bounds a positive gcd interval by interval length times
the divisor count.  The Bondarenko--Heap Ramanujan-correlation modulus has exactly this shape.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Positive modulus packaged so Stadlmann Lemma 10 has no external positivity hypothesis. -/
abbrev PositiveModulus := {q : ℕ // q ≠ 0}

/-- Natural-valued gcd interval from Stadlmann Lemma 10. -/
def stadlmannGcdIntervalMass (q : PositiveModulus) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 K, q.1.gcd k

/-- Exact totient expansion of the gcd interval for every positive modulus. -/
theorem stadlmannGcdIntervalMass_eq_totient (q : PositiveModulus) (K : ℕ) :
    stadlmannGcdIntervalMass q K =
      ∑ e ∈ q.1.divisors, Nat.totient e * (K / e) := by
  classical
  unfold stadlmannGcdIntervalMass
  have hqpos : 0 < q.1 := Nat.pos_of_ne_zero q.2
  have hsub : q.1 - 1 + 1 = q.1 := Nat.sub_add_cancel hqpos
  calc
    _ = ∑ k ∈ Finset.Icc 1 K, ∑ e ∈ q.1.divisors,
        if k % e = 0 then Nat.totient e else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hdist : Nat.dist k 0 = k := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.zero_le k), Nat.sub_zero]
      have h := gcd_succ_eq_sum_totient_residueClasses (q.1 - 1) k 0
      rw [hsub, hdist] at h
      simpa using_mod_cast h
    _ = ∑ e ∈ q.1.divisors, Nat.totient e * (K / e) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      have hfilter : (Finset.Icc 1 K).filter (fun k => k % e = 0) =
          (Finset.Icc 1 K).filter (fun k => e ∣ k) := by
        ext k
        simp [Nat.dvd_iff_mod_eq_zero]
      rw [hfilter, Finset.sum_const, nsmul_eq_mul]
      have hIcc : Finset.Icc 1 K = Finset.Ioc 0 K := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
      simp [Nat.mul_comm]

/-- Stadlmann Lemma 10 for every positive natural modulus. -/
theorem stadlmannGcdIntervalMass_le_divisorCount (q : PositiveModulus) (K : ℕ) :
    stadlmannGcdIntervalMass q K ≤ K * q.1.divisors.card := by
  rw [stadlmannGcdIntervalMass_eq_totient]
  calc
    _ ≤ ∑ _e ∈ q.1.divisors, K := by
      apply Finset.sum_le_sum
      intro e he
      calc
        Nat.totient e * (K / e) ≤ e * (K / e) :=
          Nat.mul_le_mul_right (K / e) (Nat.totient_le e)
        _ = (K / e) * e := Nat.mul_comm _ _
        _ ≤ K := Nat.div_mul_le_self K e
    _ = K * q.1.divisors.card := by simp [Nat.mul_comm]

end RHTower

namespace RHTower.OddPrimeFamily

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Stadlmann Lemma 10 applied to the positive Ramanujan/gcd mass already present in the corpus. -/
theorem ramanujanGcdIntervalMass_stadlmannLemmaTen
    (P : OddPrimeFamily I) (K : ℕ) :
    ramanujanGcdIntervalMass P K ≤
      (K : ℝ) * (P.modulus.divisors.card : ℝ) :=
  ramanujanGcdIntervalMass_le_divisorCount P K

omit [DecidableEq I] in
/-- The symmetric correlation range is two applications of Stadlmann Lemma 10. -/
theorem ramanujanGcdSymmetricIntervalMass_stadlmannLemmaTen
    (P : OddPrimeFamily I) (K : ℕ) :
    ramanujanGcdSymmetricIntervalMass P K ≤
      2 * (K : ℝ) * (P.modulus.divisors.card : ℝ) :=
  ramanujanGcdSymmetricIntervalMass_le_two_mul_divisorCount P K

end RHTower.OddPrimeFamily
