import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaNine
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicSecondMoment
import GaloisForLFunctions.RHTower.DirichletCharacterEightOddSecondMoment

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
      simp only [Nat.zero_mod] at h
      exact_mod_cast h
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

/-- Lemma 10 applied to a real divisor/totient coefficient.  Replacing real division by integer
division costs one extra total totient mass, hence the explicit `2q` term. -/
theorem stadlmannDivisorTotientCoefficient_le (q : PositiveModulus) (M : ℕ) :
    ∑ e ∈ q.1.divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1) ≤
      (M : ℝ) * (q.1.divisors.card : ℝ) + 2 * (q.1 : ℝ) := by
  have hmass := stadlmannGcdIntervalMass_le_divisorCount q M
  have hmassReal : (stadlmannGcdIntervalMass q M : ℝ) ≤
      (M : ℝ) * (q.1.divisors.card : ℝ) := by
    exact_mod_cast hmass
  have hmassEq : (stadlmannGcdIntervalMass q M : ℝ) =
      ∑ e ∈ q.1.divisors,
        (Nat.totient e : ℝ) * ((M / e : ℕ) : ℝ) := by
    exact_mod_cast stadlmannGcdIntervalMass_eq_totient q M
  have htot : ∑ e ∈ q.1.divisors, (Nat.totient e : ℝ) = (q.1 : ℝ) := by
    exact_mod_cast Nat.sum_totient q.1
  calc
    ∑ e ∈ q.1.divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1) ≤
        ∑ e ∈ q.1.divisors,
          (Nat.totient e : ℝ) * (((M / e : ℕ) : ℝ) + 2) := by
      apply Finset.sum_le_sum
      intro e he
      have hepos : 0 < e := Nat.pos_of_mem_divisors he
      have heRpos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast hepos
      have hlt : (M : ℝ) < (e : ℝ) * (((M / e : ℕ) : ℝ) + 1) := by
        exact_mod_cast Nat.lt_mul_div_succ M hepos
      have hdiv : (M : ℝ) / (e : ℝ) ≤ ((M / e : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ heRpos]
        linarith
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = (∑ e ∈ q.1.divisors,
          (Nat.totient e : ℝ) * ((M / e : ℕ) : ℝ)) +
          2 * ∑ e ∈ q.1.divisors, (Nat.totient e : ℝ) := by
      calc
        _ = ∑ e ∈ q.1.divisors,
            ((Nat.totient e : ℝ) * ((M / e : ℕ) : ℝ) +
              2 * (Nat.totient e : ℝ)) := by
          apply Finset.sum_congr rfl
          intro e he
          ring
        _ = (∑ e ∈ q.1.divisors,
              (Nat.totient e : ℝ) * ((M / e : ℕ) : ℝ)) +
            ∑ e ∈ q.1.divisors, 2 * (Nat.totient e : ℝ) :=
          Finset.sum_add_distrib
        _ = _ := by rw [Finset.mul_sum]
    _ = (stadlmannGcdIntervalMass q M : ℝ) + 2 * (q.1 : ℝ) := by
      rw [← hmassEq, htot]
    _ ≤ (M : ℝ) * (q.1.divisors.card : ℝ) + 2 * (q.1 : ℝ) := by linarith

end RHTower

namespace RHTower.OddPrimeFamily

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Stadlmann Lemma 10 applied to the positive Ramanujan/gcd mass already present in the corpus. -/
theorem ramanujanGcdIntervalMass_stadlmannLemmaTen
    (P : OddPrimeFamily I) (K : ℕ) :
    ramanujanGcdIntervalMass P K ≤
      (K : ℝ) * (P.modulus.divisors.card : ℝ) := by
  unfold ramanujanGcdIntervalMass
  have h := RHTower.stadlmannGcdIntervalMass_le_divisorCount
    (⟨P.modulus, P.modulus_neZero.out⟩ : RHTower.PositiveModulus) K
  unfold RHTower.stadlmannGcdIntervalMass at h
  exact_mod_cast h

omit [DecidableEq I] in
/-- The symmetric correlation range is two applications of Stadlmann Lemma 10. -/
theorem ramanujanGcdSymmetricIntervalMass_stadlmannLemmaTen
    (P : OddPrimeFamily I) (K : ℕ) :
    ramanujanGcdSymmetricIntervalMass P K ≤
      2 * (K : ℝ) * (P.modulus.divisors.card : ℝ) := by
  rw [ramanujanGcdSymmetricIntervalMass_eq_two_mul]
  nlinarith [ramanujanGcdIntervalMass_stadlmannLemmaTen P K]

/-- Lemma 10 closes the odd quadratic-character interval second moment through its gcd kernel. -/
theorem quadratic_intervalShiftSum_normSq_stadlmannLemmaTen
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x) ≤
      ((M : ℝ) * (P.modulus.divisors.card : ℝ) + 2 * (P.modulus : ℝ)) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
  have henergy : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ (∑ e ∈ P.modulus.divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
      quadratic_intervalShiftSum_normSq_le_divisor P M b
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (RHTower.stadlmannDivisorTotientCoefficient_le
        ⟨P.modulus, P.modulus_neZero.out⟩ M) henergy

/-- Same Lemma 10 route for the conductor-four/odd quadratic character. -/
theorem fourOdd_quadratic_intervalShiftSum_normSq_stadlmannLemmaTen
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (fourOddModulus P),
        Complex.normSq (fourOddQuadraticIntervalShiftSum P M b x) ≤
      ((M : ℝ) * ((fourOddModulus P).divisors.card : ℝ) +
        2 * (fourOddModulus P : ℝ)) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
  have henergy : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ (∑ e ∈ (fourOddModulus P).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
      fourOdd_quadratic_intervalShiftSum_normSq_le_divisor P M b
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (RHTower.stadlmannDivisorTotientCoefficient_le
        ⟨fourOddModulus P, (fourOddModulus_neZero P).out⟩ M) henergy

/-- Same Lemma 10 route for either conductor-eight/odd quadratic character. -/
theorem eightOdd_quadratic_intervalShiftSum_normSq_stadlmannLemmaTen
    (κ : EightQuadraticKind) (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod (eightOddModulus P),
        Complex.normSq (eightOddQuadraticIntervalShiftSum κ P M b x) ≤
      ((M : ℝ) * ((eightOddModulus P).divisors.card : ℝ) +
        2 * (eightOddModulus P : ℝ)) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 := by
  have hmodpos : 0 < eightOddModulus P :=
    Nat.pos_of_ne_zero (eightOddModulus_neZero P).out
  have hmod : eightOddModulus P - 1 + 1 = eightOddModulus P :=
    Nat.sub_add_cancel hmodpos
  have henergy : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ gcdKernelMoment (eightOddModulus P - 1) M b :=
      eightOdd_quadratic_intervalShiftSum_normSq_le_gcdKernel κ P M b
    _ ≤ (∑ e ∈ (eightOddModulus P - 1 + 1).divisors,
        (Nat.totient e : ℝ) * ((M : ℝ) / (e : ℝ) + 1)) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ 2 :=
      gcdKernelMoment_le (eightOddModulus P - 1) M b
    _ ≤ _ := by
      rw [hmod]
      exact mul_le_mul_of_nonneg_right
        (RHTower.stadlmannDivisorTotientCoefficient_le
          ⟨eightOddModulus P, (eightOddModulus_neZero P).out⟩ M) henergy

end RHTower.OddPrimeFamily
