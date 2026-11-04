import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeMoments

/-!
# Moments of arbitrarily weighted prime incidences

Distinct-prime divisor counts and diagonal terms give ordinary and
harmonic square bounds in the two reciprocal coefficient masses.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticCouplingTheory
open Finset
open scoped Classical
open GaloisForLFunctions
open CriticalScaleArithmeticRigidity ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
open _root_.RHTower.Sieve

def primeDivisorCoefficientSum (P : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, a p * if p ∣ n then 1 else 0

private theorem indicator_product_le {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then 1 else 0) ≤
      (if p * q ∣ n then 1 else 0) + if p = q then (if p ∣ n then 1 else 0) else 0 := by
  by_cases hpq : p = q
  · subst q
    rw [if_pos (rfl : p = p)]
    split_ifs <;> norm_num
  · simp only [if_neg hpq, add_zero]
    by_cases hpn : p ∣ n
    · by_cases hqn : q ∣ n
      · have hd := ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpn hqn
        simp only [if_pos hpn, if_pos hqn, if_pos hd, one_mul, le_refl]
      · simp only [if_pos hpn, if_neg hqn, mul_zero]
        split_ifs <;> norm_num
    · simp only [if_neg hpn, zero_mul]
      split_ifs <;> norm_num

/-- The diagonal and distinct-prime divisor counts control arbitrary nonnegative prime weights. -/
theorem weighted_count_moment {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 ≤ a p) (N : ℕ) (ν : ℕ → ℝ) (A : ℝ)
    (hν : ∀ n ∈ Icc 1 N, 0 ≤ ν n)
    (hd : ∀ d : ℕ, 0 < d → (∑ n ∈ Icc 1 N, if d ∣ n then ν n else 0) ≤ A / d) :
    (∑ n ∈ Icc 1 N, ν n * primeDivisorCoefficientSum P a n ^ 2) ≤
      A * ((∑ p ∈ P, a p / (p : ℝ)) ^ 2 + ∑ p ∈ P, a p ^ 2 / (p : ℝ)) := by
  have hpairs (n : ℕ) : primeDivisorCoefficientSum P a n ^ 2 ≤
      (∑ p ∈ P, ∑ q ∈ P, a p * a q * if p * q ∣ n then (1 : ℝ) else 0) +
        ∑ p ∈ P, a p ^ 2 * if p ∣ n then (1 : ℝ) else 0 := by
    rw [primeDivisorCoefficientSum, pow_two, sum_mul_sum]
    calc
      _ ≤ ∑ p ∈ P, ∑ q ∈ P, a p * a q *
          ((if p * q ∣ n then (1 : ℝ) else 0) +
            if p = q then (if p ∣ n then 1 else 0) else 0) := by
        apply sum_le_sum
        intro p hp
        apply sum_le_sum
        intro q hq
        have h := mul_le_mul_of_nonneg_left (indicator_product_le (n := n) (hP p hp) (hP q hq))
          (mul_nonneg (ha p hp) (ha q hq))
        convert h using 1
        ring
      _ = _ := by
        simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq]
        congr 1
        apply sum_congr rfl
        intro p hp
        rw [if_pos hp]
        split_ifs <;> ring
  have hpairSum :
      (∑ n ∈ Icc 1 N, ν n *
        (∑ p ∈ P, ∑ q ∈ P, a p * a q * if p * q ∣ n then (1 : ℝ) else 0)) =
      ∑ p ∈ P, ∑ q ∈ P, a p * a q *
        ∑ n ∈ Icc 1 N, if p * q ∣ n then ν n else 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    exact sum_congr rfl fun n _ => by split_ifs <;> ring
  have hdiagSum :
      (∑ n ∈ Icc 1 N, ν n * (∑ p ∈ P, a p ^ 2 * if p ∣ n then (1 : ℝ) else 0)) =
      ∑ p ∈ P, a p ^ 2 * ∑ n ∈ Icc 1 N, if p ∣ n then ν n else 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    exact sum_congr rfl fun n _ => by split_ifs <;> ring
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ν n *
        ((∑ p ∈ P, ∑ q ∈ P, a p * a q * if p * q ∣ n then (1 : ℝ) else 0) +
          ∑ p ∈ P, a p ^ 2 * if p ∣ n then (1 : ℝ) else 0) :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hpairs n) (hν n hn)
    _ = (∑ p ∈ P, ∑ q ∈ P, a p * a q *
          ∑ n ∈ Icc 1 N, if p * q ∣ n then ν n else 0) +
        ∑ p ∈ P, a p ^ 2 * ∑ n ∈ Icc 1 N, if p ∣ n then ν n else 0 := by
      rw [show (∑ n ∈ Icc 1 N, ν n *
          ((∑ p ∈ P, ∑ q ∈ P, a p * a q * if p * q ∣ n then (1 : ℝ) else 0) +
            ∑ p ∈ P, a p ^ 2 * if p ∣ n then (1 : ℝ) else 0)) =
          (∑ n ∈ Icc 1 N, ν n *
            (∑ p ∈ P, ∑ q ∈ P, a p * a q * if p * q ∣ n then (1 : ℝ) else 0)) +
          ∑ n ∈ Icc 1 N, ν n * (∑ p ∈ P, a p ^ 2 * if p ∣ n then (1 : ℝ) else 0) by
        simp only [mul_add, sum_add_distrib], hpairSum, hdiagSum]
    _ ≤ (∑ p ∈ P, ∑ q ∈ P, a p * a q * (A / (p * q : ℕ))) +
        ∑ p ∈ P, a p ^ 2 * (A / p) := by
      apply add_le_add
      · exact sum_le_sum fun p hp => sum_le_sum fun q hq =>
          mul_le_mul_of_nonneg_left (hd (p * q) (Nat.mul_pos (hP p hp).pos (hP q hq).pos))
            (mul_nonneg (ha p hp) (ha q hq))
      · exact sum_le_sum fun p hp =>
          mul_le_mul_of_nonneg_left (hd p (hP p hp).pos) (sq_nonneg _)
    _ = _ := by
      rw [mul_add, pow_two, sum_mul_sum]
      simp only [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro p _
        apply sum_congr rfl
        intro q _
        rw [Nat.cast_mul]
        ring
      · exact sum_congr rfl fun p _ => by ring

/-- A signed incidence packet is controlled by its two reciprocal coefficient masses. -/
theorem weighted_incidence_moment {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (N : ℕ) (ν : ℕ → ℝ) (A : ℝ)
    (hν : ∀ n ∈ Icc 1 N, 0 ≤ ν n) (htotal : (∑ n ∈ Icc 1 N, ν n) ≤ A)
    (hd : ∀ d : ℕ, 0 < d → (∑ n ∈ Icc 1 N, if d ∣ n then ν n else 0) ≤ A / d) :
    (∑ n ∈ Icc 1 N, ν n * incidencePacket P b n ^ 2) ≤
      A * (4 * (∑ p ∈ P, |b p| / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, b p ^ 2 / (p : ℝ)) := by
  let S : ℝ := ∑ p ∈ P, |b p| / (p : ℝ)
  let C : ℕ → ℝ := primeDivisorCoefficientSum P (fun p => |b p|)
  have hpoint (n : ℕ) : incidencePacket P b n ^ 2 ≤ 2 * C n ^ 2 + 2 * S ^ 2 := by
    have hcount : |∑ p ∈ P, b p * if p ∣ n then (1 : ℝ) else 0| ≤ C n := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro p _
      split_ifs <;> simp only [mul_one, mul_zero, abs_zero, le_refl]
    have hmean : |∑ p ∈ P, b p / (p : ℝ)| ≤ S := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro p _
      rw [abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
    have habs : |incidencePacket P b n| ≤ C n + S := by
      simp only [incidencePacket, mul_sub, mul_one_div, sum_sub_distrib]
      exact (abs_sub _ _).trans (add_le_add hcount hmean)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    nlinarith only [hsq, sq_nonneg (C n - S)]
  have hcount := weighted_count_moment hP (fun p => |b p|) (fun p _ => abs_nonneg _)
    N ν A hν hd
  simp only [sq_abs] at hcount
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ν n * (2 * C n ^ 2 + 2 * S ^ 2) :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hpoint n) (hν n hn)
    _ = 2 * (∑ n ∈ Icc 1 N, ν n * C n ^ 2) + 2 * S ^ 2 * ∑ n ∈ Icc 1 N, ν n := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> exact sum_congr rfl fun n _ => by ring
    _ ≤ 2 * (A * (S ^ 2 + ∑ p ∈ P, b p ^ 2 / (p : ℝ))) + 2 * S ^ 2 * A :=
      add_le_add (mul_le_mul_of_nonneg_left hcount zero_le_two)
        (mul_le_mul_of_nonneg_left htotal (by positivity))
    _ = _ := by dsimp only [S]; ring

#print axioms weighted_count_moment
#print axioms weighted_incidence_moment

/-- Divisibility has at most its reciprocal share of the full harmonic mass. -/
theorem harmonic_divisibility (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ Icc 1 N, if d ∣ n then 1 / (n : ℝ) else 0) ≤ harmonicMass N / d := by
  rw [← sum_filter, sum_filter_dvd_eq_sum_scaled hd]
  have hmono : harmonicMass (N / d) ≤ harmonicMass N := by
    apply sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc le_rfl (Nat.div_le_self N d))
    intro n _ _
    exact div_nonneg zero_le_one (Nat.cast_nonneg n)
  calc
    (∑ n ∈ Icc 1 (N / d), 1 / ((d * n : ℕ) : ℝ)) = harmonicMass (N / d) / d := by
      rw [harmonicMass, sum_div]
      exact sum_congr rfl fun n _ => by rw [Nat.cast_mul]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hmono (Nat.cast_nonneg d)

/-- Arbitrary prime coefficients obey a horizon-independent harmonic moment law. -/
theorem weighted_incidence_harmonic_square {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, incidencePacket P b n ^ 2 / (n : ℝ)) ≤
      harmonicMass N *
        (4 * (∑ p ∈ P, |b p| / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, b p ^ 2 / (p : ℝ)) := by
  have h := weighted_incidence_moment hP b N (fun n => 1 / (n : ℝ)) (harmonicMass N)
    (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)) le_rfl
      (fun d hd => harmonic_divisibility N hd)
  simpa only [one_div_mul_eq_div] using h

/-- The ordinary moment has the same two coefficient masses. -/
theorem weighted_incidence_ordinary_square {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, incidencePacket P b n ^ 2) ≤
      (N : ℝ) *
        (4 * (∑ p ∈ P, |b p| / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, b p ^ 2 / (p : ℝ)) := by
  have htotal : (∑ n ∈ Icc 1 N, (1 : ℝ)) ≤ (N : ℝ) := by
    simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, le_refl]
  have h := weighted_incidence_moment hP b N (fun _ => 1) N
    (fun n _ => zero_le_one) htotal
      (fun d _ => by rw [sum_dvdIndicator_Icc]; exact Nat.cast_div_le)
  simpa only [one_mul] using h

#print axioms weighted_incidence_harmonic_square
#print axioms weighted_incidence_ordinary_square

end GaloisForLFunctions.ArithmeticCouplingTheory
