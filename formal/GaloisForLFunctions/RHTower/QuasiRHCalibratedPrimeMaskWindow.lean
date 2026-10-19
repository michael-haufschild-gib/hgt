import GaloisForLFunctions.RHTower.QuasiRHCalibratedPrimeMasks
import GaloisForLFunctions.RHTower.Sieve.DivisorSumMeanSquareSmooth
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Uniform finite-prefix bounds for calibrated prime masks

Counting multiples bounds the quadratic divisibility term from above and the
linear term from below. This gives a square error at most `N/A + 4`, where
`A = ∑ (p - 1)`, uniformly over the finite prime set and prefix length.
The principal prefix sum differs from `N` by at most two. The same square
bound controls insertion of the mask against arbitrary complex weights.
-/

open Finset
noncomputable section
namespace RHTower.WeilSingularArithmetic

def primeDivisorWeight (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, if p ∣ n then (p : ℝ) else 0

theorem calibratedPrimeMask_sub_one_eq (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (n : ℕ) :
    calibratedPrimeMask S n - 1 =
      ((S.card : ℝ) - primeDivisorWeight S n) / primeMaskCapacity S := by
  have hA := (primeMaskCapacity_pos S hS hne).ne'
  have hpSum : (∑ p ∈ S, (p : ℝ)) = primeMaskCapacity S + S.card := by
    unfold primeMaskCapacity
    rw [Finset.sum_sub_distrib]
    simp
  have hterm (p : ℕ) (hp : p ∈ S) :
      calibratedPrimeMaskCoefficient S p * coprimeMask p n =
        ((p : ℝ) - (if p ∣ n then (p : ℝ) else 0)) / primeMaskCapacity S := by
    have hc : n.Coprime p ↔ ¬p ∣ n :=
      Nat.coprime_comm.trans (hS p hp).coprime_iff_not_dvd
    by_cases hd : p ∣ n <;>
      simp [calibratedPrimeMaskCoefficient, coprimeMask, hc, hd]
  rw [calibratedPrimeMask, Finset.sum_congr rfl hterm, ← Finset.sum_div,
    Finset.sum_sub_distrib, hpSum]
  change (primeMaskCapacity S + S.card - primeDivisorWeight S n) /
    primeMaskCapacity S - 1 = _
  field_simp
  ring

theorem sum_primeDivisorWeight (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n) =
      ∑ p ∈ S, (p : ℝ) * ((N / p : ℕ) : ℝ) := by
  simp only [primeDivisorWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter, Finset.sum_const,
    Sieve.card_filter_dvd_Icc (hS p hp).pos, nsmul_eq_mul]
  ring

theorem sum_primeDivisorWeight_ge (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (N : ℝ) * S.card - (primeMaskCapacity S + S.card) ≤
      ∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n := by
  rw [sum_primeDivisorWeight S hS N]
  have hterm (p : ℕ) (hp : p ∈ S) :
      (N : ℝ) - p ≤ (p : ℝ) * ((N / p : ℕ) : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    have hfloor := (abs_le.mp (Sieve.abs_natDiv_sub_div_le (N := N) (hS p hp).pos)).1
    have h := mul_le_mul_of_nonneg_left hfloor hp0.le
    have he : (p : ℝ) * ((N : ℝ) / p) = N := by field_simp
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  have hpSum : (∑ p ∈ S, (p : ℝ)) = primeMaskCapacity S + S.card := by
    unfold primeMaskCapacity
    rw [Finset.sum_sub_distrib]
    simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hpSum] at hsum
  nlinarith

private theorem prime_pair_div_lcm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p : ℝ) * q / (Nat.lcm p q : ℝ) =
      1 + (if q = p then (p : ℝ) - 1 else 0) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  by_cases he : p = q
  · subst q
    rw [Nat.lcm_self, if_pos rfl]
    field_simp
    ring
  · rw [(Nat.coprime_primes hp hq).mpr he |>.lcm_eq_mul,
      if_neg (Ne.symm he), Nat.cast_mul]
    field_simp
    ring

theorem sum_sq_primeDivisorWeight_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n ^ 2) ≤
      (N : ℝ) * (primeMaskCapacity S + (S.card : ℝ) ^ 2) := by
  have hexp (n : ℕ) : primeDivisorWeight S n ^ 2 =
      ∑ p ∈ S, ∑ q ∈ S, if Nat.lcm p q ∣ n then (p : ℝ) * q else 0 := by
    rw [primeDivisorWeight, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simp only [Nat.lcm_dvd_iff]
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
  have hswap : (∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n ^ 2) =
      ∑ p ∈ S, ∑ q ∈ S, (p : ℝ) * q * ((N / Nat.lcm p q : ℕ) : ℝ) := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    have hl : 0 < Nat.lcm p q := Nat.pos_of_ne_zero (by
      intro hz
      rcases Nat.lcm_eq_zero_iff.mp hz with hz | hz
      · exact (hS p hp).ne_zero hz
      · exact (hS q hq).ne_zero hz)
    rw [← Finset.sum_filter, Finset.sum_const,
      Sieve.card_filter_dvd_Icc hl, nsmul_eq_mul]
    ring
  rw [hswap]
  calc
    _ ≤ ∑ p ∈ S, ∑ q ∈ S, (N : ℝ) *
        (1 + (if q = p then (p : ℝ) - 1 else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have h : ((N / Nat.lcm p q : ℕ) : ℝ) ≤
          (N : ℝ) / (Nat.lcm p q : ℝ) := Nat.cast_div_le
      have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (p : ℝ) * q by positivity)
      calc
        _ ≤ (p : ℝ) * q * ((N : ℝ) / (Nat.lcm p q : ℝ)) := hm
        _ = (N : ℝ) * ((p : ℝ) * q / (Nat.lcm p q : ℝ)) := by ring
        _ = _ := by rw [prime_pair_div_lcm (hS p hp) (hS q hq)]
    _ = (N : ℝ) * (primeMaskCapacity S + (S.card : ℝ) ^ 2) := by
      simp_rw [← Finset.mul_sum]
      congr 1
      have hinner (p : ℕ) (hp : p ∈ S) :
          (∑ q ∈ S, (1 + (if q = p then (p : ℝ) - 1 else 0))) =
            (S.card : ℝ) + ((p : ℝ) - 1) := by
        rw [Finset.sum_add_distrib]
        simp [hp]
      rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (S.card : ℝ) * S.card + primeMaskCapacity S = _
      ring

/-- The explicit endpoint error is bounded uniformly in the prime set. -/
theorem calibratedPrimeMask_centered_square_prefix_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (calibratedPrimeMask S n - 1) ^ 2) ≤
      (N : ℝ) / primeMaskCapacity S +
        2 * ((S.card : ℝ) / primeMaskCapacity S) *
          (1 + (S.card : ℝ) / primeMaskCapacity S) := by
  have hA := primeMaskCapacity_pos S hS hne
  have hfirst := sum_primeDivisorWeight_ge S hS N
  have hsecond := sum_sq_primeDivisorWeight_le S hS N
  have hscaled := mul_le_mul_of_nonneg_left hfirst
    (show 0 ≤ 2 * (S.card : ℝ) by positivity)
  have hexp : (∑ n ∈ Finset.Icc 1 N, ((S.card : ℝ) - primeDivisorWeight S n) ^ 2) =
      (N : ℝ) * (S.card : ℝ) ^ 2 -
        2 * S.card * (∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n) +
          ∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n ^ 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  have hnum : (∑ n ∈ Finset.Icc 1 N, ((S.card : ℝ) - primeDivisorWeight S n) ^ 2) ≤
      (N : ℝ) * primeMaskCapacity S + 2 * S.card * (primeMaskCapacity S + S.card) := by
    rw [hexp]
    nlinarith
  simp_rw [calibratedPrimeMask_sub_one_eq S hS hne, div_pow]
  rw [← Finset.sum_div]
  calc
    _ ≤ ((N : ℝ) * primeMaskCapacity S +
        2 * S.card * (primeMaskCapacity S + S.card)) / primeMaskCapacity S ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = _ := by field_simp

theorem calibratedPrimeMask_centered_square_prefix_le_four (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (calibratedPrimeMask S n - 1) ^ 2) ≤
      (N : ℝ) / primeMaskCapacity S + 4 := by
  have hA := primeMaskCapacity_pos S hS hne
  have hcard : (S.card : ℝ) ≤ primeMaskCapacity S := by
    have h := primeMaskCapacity_ge_card_mul S 2 (fun p hp => by
      exact_mod_cast (hS p hp).two_le)
    norm_num at h
    exact h
  have hB : 0 ≤ (S.card : ℝ) / primeMaskCapacity S := by positivity
  have hB1 : (S.card : ℝ) / primeMaskCapacity S ≤ 1 :=
    (div_le_iff₀ hA).mpr (by simpa using hcard)
  have hsq := mul_le_mul hB1 hB1 hB (by norm_num : (0 : ℝ) ≤ 1)
  have h := calibratedPrimeMask_centered_square_prefix_le S hS hne N
  nlinarith

/-- The calibrated mask preserves the principal prefix sum with absolute error at most two. -/
theorem calibratedPrimeMask_prefix_bias (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (N : ℕ) :
    0 ≤ (∑ n ∈ Finset.Icc 1 N, calibratedPrimeMask S n) - N ∧
      (∑ n ∈ Finset.Icc 1 N, calibratedPrimeMask S n) - N ≤ 2 := by
  have hA := primeMaskCapacity_pos S hS hne
  have hfirst := sum_primeDivisorWeight_ge S hS N
  have hupper : (∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n) ≤
      (N : ℝ) * S.card := by
    rw [sum_primeDivisorWeight S hS N]
    calc
      _ ≤ ∑ p ∈ S, (N : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).ne_zero
        have h := mul_le_mul_of_nonneg_left (Nat.cast_div_le (m := N) (n := p)
          (α := ℝ)) (show 0 ≤ (p : ℝ) by positivity)
        simpa only [mul_div_cancel₀ _ hp0] using h
      _ = _ := by simp [mul_comm]
  have he : (∑ n ∈ Finset.Icc 1 N, calibratedPrimeMask S n) - N =
      ((N : ℝ) * S.card - ∑ n ∈ Finset.Icc 1 N, primeDivisorWeight S n) /
        primeMaskCapacity S := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 N, (calibratedPrimeMask S n - 1) := by
        simp [Finset.sum_sub_distrib]
      _ = _ := by
        simp_rw [calibratedPrimeMask_sub_one_eq S hS hne]
        rw [← Finset.sum_div, Finset.sum_sub_distrib]
        simp
  have hcard : (S.card : ℝ) ≤ primeMaskCapacity S := by
    have h := primeMaskCapacity_ge_card_mul S 2 (fun p hp => by
      exact_mod_cast (hS p hp).two_le)
    norm_num at h
    exact h
  rw [he]
  refine ⟨div_nonneg (sub_nonneg.mpr hupper) hA.le, ?_⟩
  apply (div_le_iff₀ hA).mpr
  linarith

/-- Squared error under insertion of the mask, with the original complex weights retained. -/
theorem calibratedPrimeMask_weighted_prefix_error_sq (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (N : ℕ) (a : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Icc 1 N, a n * ((calibratedPrimeMask S n - 1 : ℝ) : ℂ)‖ ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * ((N : ℝ) / primeMaskCapacity S + 4) := by
  have ht : ‖∑ n ∈ Finset.Icc 1 N, a n * ((calibratedPrimeMask S n - 1 : ℝ) : ℂ)‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ * |calibratedPrimeMask S n - 1| := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sum_le (Finset.Icc 1 N)
        (fun n => a n * ((calibratedPrimeMask S n - 1 : ℝ) : ℂ))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
    (fun n => ‖a n‖) (fun n => |calibratedPrimeMask S n - 1|)
  simp only [sq_abs] at hcs
  exact ((pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hcs).trans
    (mul_le_mul_of_nonneg_left (calibratedPrimeMask_centered_square_prefix_le_four S hS hne N)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Uniform mask-insertion error for every Dirichlet character and every modulus. -/
theorem calibratedPrimeMask_character_prefix_error_sq (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (N q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ Finset.Icc 1 N, χ n * ((calibratedPrimeMask S n - 1 : ℝ) : ℂ)‖ ^ 2 ≤
      (N : ℝ) * ((N : ℝ) / primeMaskCapacity S + 4) := by
  have hA := primeMaskCapacity_pos S hS hne
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖χ n‖ ^ 2) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        simpa using pow_le_pow_left₀ (norm_nonneg (χ n)) (χ.norm_le_one n) 2
      _ = _ := by simp
  exact (calibratedPrimeMask_weighted_prefix_error_sq S hS hne N (fun n => χ n)).trans
    (mul_le_mul_of_nonneg_right hsum (by positivity))

end RHTower.WeilSingularArithmetic
