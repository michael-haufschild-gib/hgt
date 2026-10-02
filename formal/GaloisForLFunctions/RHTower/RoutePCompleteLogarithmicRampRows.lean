import GaloisForLFunctions.RHTower.TatuzawaIsekiIdentity
import GaloisForLFunctions.HTGeometry.CenteredModularAbel
import Mathlib.Algebra.DualNumber
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Complete logarithmic ramp rows at their actual square births

Grouping the centered divisor forcing by the product label retains the row
`sum_{d|n} mu(d) * (log(k)-log(d)) * ramp_(n/d)(floor(k/d))`.
At `k=n^2`, every label is active. The exact birth coefficient is a reciprocal
Euler logarithmic jet, with the full `log(k)` coefficient retained.

Two distinct primes give a strictly positive row at birth; such rows occur
arbitrarily late. Thus complete rows cannot individually inherit the unsigned
modular-ramp sign. The finite coefficient formula is the positive survivor.
This does not bound the aggregate forcing or either native Route-P square debt.
-/

noncomputable section
open Finset ArithmeticFunction HTGeometry
open scoped BigOperators
namespace RHTower

private def reciprocalLogJet (n : ℕ) : DualNumber ℝ :=
  ((n : ℝ)⁻¹, Real.log n / n)

private def reciprocalLogArith : ArithmeticFunction (DualNumber ℝ) :=
  ⟨reciprocalLogJet, by ext <;> simp [reciprocalLogJet]⟩

private theorem reciprocalLogArith_multiplicative : reciprocalLogArith.IsMultiplicative := by
  refine ⟨by ext <;> simp [reciprocalLogArith, reciprocalLogJet], ?_⟩
  intro m n _
  change reciprocalLogJet (m * n) = reciprocalLogJet m * reciprocalLogJet n
  rcases eq_or_ne m 0 with rfl | hm
  · ext <;> simp [reciprocalLogJet]
  rcases eq_or_ne n 0 with rfl | hn
  · ext <;> simp [reciprocalLogJet]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  apply TrivSqZeroExt.ext
  · simp [reciprocalLogJet, mul_comm]
  · simp only [reciprocalLogJet, TrivSqZeroExt.snd_mk, DualNumber.snd_mul,
      TrivSqZeroExt.fst_mk, Nat.cast_mul, Real.log_mul hmR hnR]
    field_simp
    ring

private theorem reciprocalLogEuler_sign (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    0 < (∏ p ∈ S, (1 - reciprocalLogJet p)).fst ∧
      (∏ p ∈ S, (1 - reciprocalLogJet p)).snd ≤ 0 ∧
      (S.Nonempty → (∏ p ∈ S, (1 - reciprocalLogJet p)).snd < 0) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hpP := hS p (mem_insert_self p S)
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hpR
    have ha : 0 < (1 - reciprocalLogJet p).fst := by
      change 0 < 1 - (p : ℝ)⁻¹
      have : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).2 hpR
      linarith
    have hb : (1 - reciprocalLogJet p).snd < 0 := by
      change 0 - Real.log p / p < 0
      exact sub_neg.mpr (div_pos (Real.log_pos hpR) hp0)
    obtain ⟨hfst, hsnd, _⟩ := ih (fun q hq => hS q (mem_insert_of_mem hq))
    rw [prod_insert hp]
    have hnegative : ((1 - reciprocalLogJet p) *
        ∏ q ∈ S, (1 - reciprocalLogJet q)).snd < 0 := by
      rw [DualNumber.snd_mul]
      exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le hsnd)
        (mul_neg_of_neg_of_pos hb hfst)
    exact ⟨mul_pos ha hfst, hnegative.le, fun _ => hnegative⟩

/-- Strict sign of the actual logarithmic reciprocal-divisor coefficient. -/
theorem routeP_mobius_log_divisor_strictly_negative {n : ℕ}
    (hn : Squarefree n) (hn1 : n ≠ 1) :
    (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * (Real.log d / d)) < 0 := by
  have he := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    reciprocalLogArith reciprocalLogArith_multiplicative hn
  have hne : n.primeFactors.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    simpa only [ne_eq, Nat.primeFactors_eq_empty, not_or] using ⟨hn.ne_zero, hn1⟩
  have hs := (reciprocalLogEuler_sign n.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)).2.2 hne
  have he' := congrArg TrivSqZeroExt.snd he
  simp only [reciprocalLogArith, ArithmeticFunction.coe_mk, reciprocalLogJet,
    TrivSqZeroExt.snd_sum, DualNumber.snd_mul, TrivSqZeroExt.fst_intCast,
    TrivSqZeroExt.snd_intCast, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
    zero_mul, add_zero] at he'
  rw [← he']
  exact hs

/-- Complete divisor row with the literal logarithmic forcing coefficient. -/
def routePCompleteLogarithmicRampRow (n k : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * (Real.log k - Real.log d) *
    centeredModularRamp (n / d) (k / d)

/-- Exact complete-row value at its common square birth. -/
theorem routeP_complete_logarithmic_ramp_birth {n : ℕ}
    (hn : Squarefree n) (hn1 : n ≠ 1) :
    2 * routePCompleteLogarithmicRampRow n (n * n) =
      ((moebius n : ℤ) : ℝ) *
        (Real.log n * (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) / d) +
          (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * (Real.log d / d)) +
          vonMangoldt n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hsum : (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ)) = 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    simpa only [coe_mul_zeta_apply, one_apply_ne hn1, intCoe_apply] using h
  have hlog : (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * Real.log d) =
      -vonMangoldt n := sum_moebius_mul_log_eq
  unfold routePCompleteLogarithmicRampRow
  rw [← Nat.sum_div_divisors n (fun d =>
    ((moebius d : ℤ) : ℝ) * (Real.log (n * n : ℕ) - Real.log d) *
      centeredModularRamp (n / d) (n * n / d)), Finset.mul_sum]
  have hterm (d : ℕ) (hd : d ∈ n.divisors) :
      2 * (((moebius (n / d) : ℤ) : ℝ) *
          (Real.log (n * n : ℕ) - Real.log (n / d : ℕ)) *
          centeredModularRamp (n / (n / d)) (n * n / (n / d))) =
        ((moebius n : ℤ) : ℝ) *
          (Real.log n * (((moebius d : ℤ) : ℝ) / d) +
            ((moebius d : ℤ) : ℝ) * (Real.log d / d) -
            Real.log n * ((moebius d : ℤ) : ℝ) -
            ((moebius d : ℤ) : ℝ) * Real.log d) := by
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    obtain ⟨j, hj⟩ := hdvd
    have hj0 : 0 < j := by
      by_contra h
      have : j = 0 := by omega
      simp [this] at hj
      exact hn.ne_zero hj
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj0.ne'
    have hs : Squarefree (d * j) := hj ▸ hn
    have hcop := (Nat.squarefree_mul_iff.mp hs).1
    have hsq : (((moebius d : ℤ) : ℝ)) ^ 2 = 1 := by
      exact_mod_cast moebius_sq_eq_one_of_squarefree (Nat.squarefree_mul_iff.mp hs).2.1
    have hmu : ((moebius j : ℤ) : ℝ) =
        ((moebius n : ℤ) : ℝ) * ((moebius d : ℤ) : ℝ) := by
      rw [hj, isMultiplicative_moebius.map_mul_of_coprime hcop]
      push_cast
      linear_combination -(((moebius j : ℤ) : ℝ)) * hsq
    have hnd : n / d = j := by rw [hj, Nat.mul_div_cancel_left j hd0]
    have hnj : n / j = d := by rw [hj, Nat.mul_div_cancel d hj0]
    rw [hnd, hnj, Nat.mul_div_assoc n (show j ∣ n from hj ▸ dvd_mul_left j d), hnj]
    simp only [centeredModularRamp, Nat.mul_mod_left, Nat.cast_zero, zero_div, zero_sub]
    rw [hmu]
    have hl : Real.log (n * n : ℕ) - Real.log j = Real.log n + Real.log d := by
      rw [Nat.cast_mul, Real.log_mul hnR hnR]
      have hnlog : Real.log (n : ℝ) = Real.log d + Real.log j := by
        rw [hj, Nat.cast_mul, Real.log_mul hdR hjR]
      linarith
    rw [hl]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum, hlog]
  ring

/-- Every label of a complete row is present at its common square birth. -/
theorem routeP_complete_logarithmic_ramp_birth_active (n : ℕ) :
    ∀ d ∈ n.divisors, (n / d) * (n / d) ≤ n * n / d := by
  intro d hd
  rw [Nat.mul_div_assoc n (Nat.dvd_of_mem_divisors hd)]
  exact Nat.mul_le_mul_right _ (Nat.div_le_self n d)

/-- The two-prime birth coefficient, retaining the full logarithmic forcing. -/
theorem routeP_complete_logarithmic_ramp_two_prime_birth
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    2 * routePCompleteLogarithmicRampRow (p * q) ((p * q) * (p * q)) =
      Real.log p * (1 - 2 / (p : ℝ)) * (1 - 1 / (q : ℝ)) +
        Real.log q * (1 - 2 / (q : ℝ)) * (1 - 1 / (p : ℝ)) := by
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hs : Squarefree (p * q) := Nat.squarefree_mul_iff.mpr ⟨hc, hp.squarefree, hq.squarefree⟩
  have hn1 : p * q ≠ 1 := by nlinarith [hp.two_le, hq.two_le]
  have hmu : ((moebius (p * q) : ℤ) : ℝ) = 1 := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,
      moebius_apply_prime hp, moebius_apply_prime hq]
    norm_num
  have hΛ : vonMangoldt (p * q) = 0 := by
    apply vonMangoldt_eq_zero_iff.mpr
    intro h
    exact Nat.not_prime_mul hp.ne_one hq.ne_one
      (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hs, h⟩)
  have he := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    reciprocalLogArith reciprocalLogArith_multiplicative hs
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors] at he
  simp only [singleton_union, prod_insert (show p ∉ ({q} : Finset ℕ) by simpa),
    prod_singleton] at he
  have hA := congrArg TrivSqZeroExt.fst he
  have hG := congrArg TrivSqZeroExt.snd he
  simp only [reciprocalLogArith, ArithmeticFunction.coe_mk, reciprocalLogJet,
    TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_intCast, TrivSqZeroExt.fst_mk] at hA
  simp only [reciprocalLogArith, ArithmeticFunction.coe_mk, reciprocalLogJet,
    TrivSqZeroExt.snd_sum, DualNumber.snd_mul, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_one,
    TrivSqZeroExt.fst_intCast, TrivSqZeroExt.snd_intCast, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk, zero_mul, add_zero, zero_sub] at hG
  rw [routeP_complete_logarithmic_ramp_birth hs hn1, hmu, one_mul, hΛ, add_zero,
    hG.symm]
  simp only [div_eq_mul_inv] at hA ⊢
  rw [hA.symm, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  ring

/-- Every ordered two-prime row has a strictly positive forcing value at birth. -/
theorem routeP_complete_logarithmic_ramp_two_prime_positive
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) :
    0 < routePCompleteLogarithmicRampRow (p * q) ((p * q) * (p * q)) := by
  have h := routeP_complete_logarithmic_ramp_two_prime_birth hp hq hpq.ne
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℝ) < q := by exact_mod_cast (lt_of_le_of_lt hp.two_le hpq)
  have hpa : 0 ≤ 1 - 2 / (p : ℝ) := sub_nonneg.mpr ((div_le_one hp0).2 hp2)
  have hqa : 0 < 1 - 2 / (q : ℝ) := sub_pos.mpr ((div_lt_one hq0).2 hq2)
  have hpb : 0 < 1 - 1 / (p : ℝ) := sub_pos.mpr ((div_lt_one hp0).2 hp1)
  have hqb : 0 < 1 - 1 / (q : ℝ) := sub_pos.mpr ((div_lt_one hq0).2 hq1)
  have ha := mul_nonneg (mul_nonneg (Real.log_pos hp1).le hpa) hqb.le
  have hb := mul_pos (mul_pos (Real.log_pos hq1) hqa) hpb
  linarith

/-- Actual complete logarithmic rows have positive births arbitrarily late. -/
theorem routeP_complete_logarithmic_ramp_positive_cofinal (N : ℕ) :
    ∃ n : ℕ, N < n ∧ 0 < routePCompleteLogarithmicRampRow n (n * n) := by
  obtain ⟨p, _, hp⟩ := Nat.exists_infinite_primes 2
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (max (N + 1) (p + 1))
  have hpq : p < q := by have := le_max_right (N + 1) (p + 1); omega
  have hNq : N < q := by have := le_max_left (N + 1) (p + 1); omega
  refine ⟨p * q, ?_, routeP_complete_logarithmic_ramp_two_prime_positive hp hq hpq⟩
  nlinarith [hp.two_le, hq.pos]

/-- No late cutoff makes every complete logarithmic row nonpositive at birth. -/
theorem not_routeP_complete_logarithmic_ramp_eventually_nonpositive :
    ¬ ∃ L : ℕ, ∀ n : ℕ, L ≤ n → routePCompleteLogarithmicRampRow n (n * n) ≤ 0 := by
  rintro ⟨L, hL⟩
  obtain ⟨n, hn, hpos⟩ := routeP_complete_logarithmic_ramp_positive_cofinal L
  exact (not_lt_of_ge (hL n hn.le)) hpos

end RHTower
