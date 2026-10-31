import GaloisForLFunctions.CriticalScaleArithmeticRigidity.CoherentPrimeTailLowerBound
import GaloisForLFunctions.RHTower.Sieve.PrimePairDivisorMean
import GaloisForLFunctions.HTGeometry.FiniteReversedAbelBounds

/-!
# Harmonic windows retain coherent prime incidence

Centered divisibility has interval discrepancy at most one. Finite Abel
summation therefore controls the coherent tail's first harmonic moment
without a conductor-separation loss. Expanding around its exact constant
coefficient gives a square lower bound with only a prime-mass boundary term.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

/-- The exact centered incidence of multiples of a positive integer. -/
def centeredDivisibility (d n : ℕ) : ℝ := (if d ∣ n then 1 else 0) - 1 / (d : ℝ)

private theorem centeredDivisibility_prefix_eq {d : ℕ} (hd : 0 < d) (X : ℕ) :
    (∑ n ∈ Icc 1 X, centeredDivisibility d n) = -((X % d : ℕ) : ℝ) / d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ((X % d : ℕ) : ℝ) + (d : ℝ) * ((X / d : ℕ) : ℝ) = X := by
    exact_mod_cast Nat.mod_add_div X d
  simp only [centeredDivisibility, sum_sub_distrib, _root_.RHTower.Sieve.sum_dvdIndicator_Icc,
    sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one_div]
  apply (eq_div_iff hdR).mpr
  rw [sub_mul, div_mul_cancel₀ _ hdR]
  linarith only [he]

private theorem centeredDivisibility_prefix_bounds {d : ℕ} (hd : 0 < d) (X : ℕ) :
    -1 ≤ (∑ n ∈ Icc 1 X, centeredDivisibility d n) ∧
      (∑ n ∈ Icc 1 X, centeredDivisibility d n) ≤ 0 := by
  rw [centeredDivisibility_prefix_eq hd]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : (((X % d : ℕ) : ℝ) / d) ≤ 1 := by
    rw [div_le_iff₀ hdR, one_mul]
    exact_mod_cast (Nat.mod_lt X hd).le
  have h0 : 0 ≤ ((X % d : ℕ) : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hdR.le
  constructor <;> linarith only [hr, h0]

/-- Every consecutive interval has at most one unit of centered divisibility error. -/
theorem abs_centeredDivisibility_window_le_one {d : ℕ} (hd : 0 < d) (A K : ℕ) :
    |∑ n ∈ Icc (A + 1) (A + K), centeredDivisibility d n| ≤ 1 := by
  have he := sum_Ico_consecutive (f := centeredDivisibility d)
    (show 1 ≤ A + 1 by omega) (show A + 1 ≤ A + K + 1 by omega)
  simp only [Ico_add_one_right_eq_Icc] at he
  have hA := centeredDivisibility_prefix_bounds hd A
  have hB := centeredDivisibility_prefix_bounds hd (A + K)
  apply abs_le.mpr
  constructor <;> linarith only [he, hA.1, hA.2, hB.1, hB.2]

/-- Harmonic incidence discrepancy costs only the first weight in the window. -/
theorem abs_centeredDivisibility_harmonic_window_le {d : ℕ}
    (hd : 0 < d) (A K : ℕ) :
    |∑ n ∈ Icc (A + 1) (A + K), centeredDivisibility d n / (n : ℝ)| ≤
      1 / ((A : ℝ) + 1) := by
  have hpartial (t : ℕ) (_ : t ≤ K) :
      |∑ j ∈ range t, centeredDivisibility d (A + 1 + j)| ≤ 1 := by
    have h := abs_centeredDivisibility_window_le_one hd A t
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range] at h
    simpa only [show A + t + 1 - (A + 1) = t by omega] using h
  have h := HTGeometry.abs_sum_mul_le_of_finite_partial
    (g := fun i => centeredDivisibility d (A + 1 + i))
    (w := fun i => 1 / ((A + 1 + i : ℕ) : ℝ)) K hpartial
    (fun i => by positivity)
    (fun i => by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simpa only [show A + K + 1 - (A + 1) = K by omega, Nat.add_zero,
    Nat.cast_add, Nat.cast_one, one_mul, div_eq_mul_inv, mul_comm] using h

/-- Reciprocal tower activity of the high-prime source. -/
def highPrimeActivityMass (P Q : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
    if P < p then Real.log p / ((p : ℝ) - 1) else 0

theorem highPrimePoleMass_nonneg (P Q : ℕ) : 0 ≤ highPrimePoleMass P Q := by
  apply sum_nonneg
  intro p _
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  · exact le_rfl

/-- The high-prime receiving mass is exactly the difference of prime Mertens masses. -/
theorem highPrimePoleMass_eq_sub {P Q : ℕ} (hPQ : P ≤ Q) :
    highPrimePoleMass P Q = primePoleScale Q - primePoleScale P := by
  have hset : ((Icc 1 Q).filter Nat.Prime).filter (fun p => p ≤ P) =
      (Icc 1 P).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨hp1, _⟩, hp⟩, hpP⟩
      exact ⟨⟨hp1, hpP⟩, hp⟩
    · rintro ⟨⟨hp1, hpP⟩, hp⟩
      exact ⟨⟨⟨hp1, hpP.trans hPQ⟩, hp⟩, hpP⟩
  have he : primePoleScale P = ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      if p ≤ P then Real.log p / (p : ℝ) else 0 := by
    rw [primePoleScale, ← hset, sum_filter]
  rw [highPrimePoleMass, he, primePoleScale, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  by_cases hP : P < p
  · simp only [if_pos hP, if_neg (not_le.mpr hP), sub_zero]
  · simp only [if_neg hP, if_pos (Nat.le_of_not_lt hP), sub_self]

theorem highPrimePoleMass_le (P Q : ℕ) : highPrimePoleMass P Q ≤ primePoleScale Q := by
  apply sum_le_sum
  intro p _
  by_cases hP : P < p
  · simp only [if_pos hP, le_refl]
  · simp only [if_neg hP]
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem highPrimeActivityMass_le (P Q : ℕ) :
    highPrimeActivityMass P Q ≤ primeActivityMass Q := by
  apply sum_le_sum
  intro p hp
  by_cases hP : P < p
  · simp only [if_pos hP, le_refl]
  · simp only [if_neg hP]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
    exact div_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hp1.le)

/-- The high-prime source splits into its exact mean and centered incidence. -/
theorem highPrimeSource_sub_mean_eq (P Q n : ℕ) :
    highPrimeCoherentSource P Q n - highPrimePoleMass P Q =
      -(∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        if P < p then (Real.log p / ((p : ℝ) - 1)) * centeredDivisibility p n else 0) := by
  rw [highPrimeCoherentSource, highPrimePoleMass, ← sum_sub_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hpm : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp1).ne'
  by_cases hP : P < p
  · simp only [if_pos hP, centeredDivisibility]
    by_cases hn : p ∣ n <;> simp only [hn, if_true, if_false]
    all_goals field_simp [hp0, hpm] <;> ring
  · simp only [if_neg hP, sub_self, neg_zero]

/-- Coherent prime incidence has a source-specific harmonic error independent of `Q²`. -/
theorem abs_highPrimeSource_harmonic_mean_error_le (P Q A K : ℕ) :
    |∑ n ∈ Icc (A + 1) (A + K),
      (highPrimeCoherentSource P Q n - highPrimePoleMass P Q) / (n : ℝ)| ≤
        highPrimeActivityMass P Q / ((A : ℝ) + 1) := by
  simp only [highPrimeSource_sub_mean_eq, neg_div, sum_neg_distrib, abs_neg, sum_div]
  rw [sum_comm]
  calc
    _ ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        |∑ n ∈ Icc (A + 1) (A + K),
          (if P < p then (Real.log p / ((p : ℝ) - 1)) * centeredDivisibility p n else 0) /
            (n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        (if P < p then Real.log p / ((p : ℝ) - 1) else 0) / ((A : ℝ) + 1) := by
      apply sum_le_sum
      intro p hp
      by_cases hP : P < p
      · have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
        have hw : 0 ≤ Real.log p / ((p : ℝ) - 1) :=
          div_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hp1.le)
        simp only [if_pos hP, mul_div_assoc, ← mul_sum, abs_mul, abs_of_nonneg hw]
        exact (mul_le_mul_of_nonneg_left
          (abs_centeredDivisibility_harmonic_window_le (mem_filter.mp hp).2.pos A K) hw).trans_eq
            (by ring)
      · simp only [if_neg hP, zero_div, sum_const_zero, abs_zero, le_refl]
    _ = _ := by rw [← sum_div]; rfl

/-- The coherent source square keeps its mean square with only an incidence boundary cost. -/
theorem highPrimeSource_harmonic_sq_lower (P Q A K : ℕ) :
    (∑ n ∈ Icc (A + 1) (A + K), 1 / (n : ℝ)) * highPrimePoleMass P Q ^ 2 -
        2 * highPrimePoleMass P Q * highPrimeActivityMass P Q / ((A : ℝ) + 1) ≤
      ∑ n ∈ Icc (A + 1) (A + K), highPrimeCoherentSource P Q n ^ 2 / (n : ℝ) := by
  have hmean := (abs_le.mp (abs_highPrimeSource_harmonic_mean_error_le P Q A K)).1
  have hlinear := mul_le_mul_of_nonneg_left hmean
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (highPrimePoleMass_nonneg P Q))
  have hsquare := sum_nonneg (s := Icc (A + 1) (A + K)) fun n _ =>
    div_nonneg (sq_nonneg (highPrimeCoherentSource P Q n - highPrimePoleMass P Q))
      (Nat.cast_nonneg n)
  have he : (∑ n ∈ Icc (A + 1) (A + K), highPrimeCoherentSource P Q n ^ 2 / (n : ℝ)) =
      (∑ n ∈ Icc (A + 1) (A + K), 1 / (n : ℝ)) * highPrimePoleMass P Q ^ 2 +
        2 * highPrimePoleMass P Q *
          (∑ n ∈ Icc (A + 1) (A + K),
            (highPrimeCoherentSource P Q n - highPrimePoleMass P Q) / (n : ℝ)) +
        (∑ n ∈ Icc (A + 1) (A + K),
          (highPrimeCoherentSource P Q n - highPrimePoleMass P Q) ^ 2 / (n : ℝ)) := by
    simp only [sum_mul, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  linarith only [he, hlinear, hsquare]

/-- The actual coherent complementary tail inherits the incidence bound on all high rows. -/
theorem coherentPrimeTail_incidence_lower {P : ℕ} (hP : 0 < P) (Q N : ℕ) :
    (∑ n ∈ Icc (N / P + 1) N, 1 / (n : ℝ)) * highPrimePoleMass P Q ^ 2 -
        2 * highPrimePoleMass P Q * highPrimeActivityMass P Q /
          (((N / P : ℕ) : ℝ) + 1) ≤
      ∑ n ∈ Icc 1 N,
        completedPrimeDilationTail Q (primeOnly primePoleWitness) (N / n) n ^ 2 / (n : ℝ) := by
  have hA : N / P ≤ N := Nat.div_le_self N P
  have hsource := highPrimeSource_harmonic_sq_lower P Q (N / P) (N - N / P)
  rw [Nat.add_sub_of_le hA] at hsource
  refine hsource.trans ((sum_le_sum fun n hn => ?_).trans ?_)
  · have hnA : N / P < n := by have := (mem_Icc.mp hn).1; omega
    have ht := highPrimeSource_le_row_tail hP hnA Q
    have hpos := highPrimeCoherentSource_nonneg P Q n
    have hprod := mul_nonneg (sub_nonneg.mpr ht) (add_nonneg (hpos.trans ht) hpos)
    exact div_le_div_of_nonneg_right (by nlinarith only [hprod]) (Nat.cast_nonneg n)
  · apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hn).1; omega, (mem_Icc.mp hn).2⟩
    · intro n _ _
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

#print axioms abs_centeredDivisibility_harmonic_window_le
#print axioms abs_highPrimeSource_harmonic_mean_error_le
#print axioms highPrimeSource_harmonic_sq_lower
#print axioms coherentPrimeTail_incidence_lower

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
