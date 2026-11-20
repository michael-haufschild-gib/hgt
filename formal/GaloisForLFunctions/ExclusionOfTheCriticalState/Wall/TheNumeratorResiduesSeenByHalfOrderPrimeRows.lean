import GaloisForLFunctions.ArithmeticPositiveDuality.TheCutoffEnergyOfSignedHalfOrderRows
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.HalfOrderInteractionsOfOddQuotientBands
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerator residues seen by half-order prime rows

Comparing two numerators at the critical fractional order detects every
change of an active denominator digit. On the powers of two, finite energy
of the difference is exactly congruence of the numerators. On an arbitrary
finite set, all translated comparisons recover the full period.
-/

noncomputable section
open Finset MeasureTheory
open GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private theorem centered_prime_atom_ne_zero (n : ℕ) : ordinaryPrimeExcessCoeff n ≠ 0 := by
  unfold ordinaryPrimeExcessCoeff
  split_ifs with hp
  · intro he
    have hv := Real.exp_log (Nat.cast_pos.mpr hp.pos : 0 < (n:ℝ))
    rw [sub_eq_zero.mp he] at hv
    have h₂ : (2:ℝ) < n := hv ▸ Real.exp_one_gt_two
    have h₃ : (n:ℝ) < 3 := hv ▸ Real.exp_one_lt_three
    have hn₂ : 2<n := by exact_mod_cast h₂
    have hn₃ : n<3 := by exact_mod_cast h₃
    omega
  · norm_num

/-- The full signed interaction difference is square integrable precisely
when the two quotient digits agree at every positive denominator. -/
theorem odd_rows_difference_integrable_iff (S : Finset ℕ) (H J : ℕ) :
    Integrable (fun t => (halfRow S (oddBandWeight H) t-halfRow S (oddBandWeight J) t)^2) ↔
      ∀ i ∈ S, 0<i → (H/i%2=1 ↔ J/i%2=1) := by
  have he (t : ℝ) : halfRow S (oddBandWeight H) t-halfRow S (oddBandWeight J) t =
      halfRow S (fun i => oddBandWeight H i-oddBandWeight J i) t := by
    simp only [halfRow,sub_mul,sum_sub_distrib]
  simp_rw [he]
  rw [halfRow_square_integrable_iff]
  apply forall_congr' fun i => forall_congr' fun _ => forall_congr' fun _ => ?_
  by_cases hH : H/i%2=1 <;> by_cases hJ : J/i%2=1 <;>
    simp [oddBandWeight,hH,hJ,centered_prime_atom_ne_zero]

/-- A single numerator row has finite critical energy exactly when it has
no active positive denominator in the observed set. -/
theorem odd_row_square_integrable_iff (S : Finset ℕ) (H : ℕ) :
    Integrable (fun t => halfRow S (oddBandWeight H) t^2) ↔
      ∀ i ∈ S, 0<i → H/i%2=0 := by
  rw [halfRow_square_integrable_iff]
  apply forall_congr' fun i => forall_congr' fun _ => forall_congr' fun _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (H/i) with hh | hh <;>
    simp [oddBandWeight,hh,centered_prime_atom_ne_zero]

/-- The first k binary denominator sites recover exactly the residue modulo
2^k through the square-integrability class of the field. -/
theorem dyadic_odd_rows_integrable_iff_congruent (k H J : ℕ) :
    let S := (range k).image fun i => 2^i
    Integrable (fun t => (halfRow S (oddBandWeight H) t-halfRow S (oddBandWeight J) t)^2) ↔
      H % 2^k = J % 2^k := by
  dsimp only
  rw [odd_rows_difference_integrable_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow]
    by_cases hi : i<k
    · have hh := h (2^i) (mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩) (by positivity)
      simp only [Nat.testBit_eq_decide_div_mod_eq,hh]
    · simp [hi]
  · intro h m hm _
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
    have he := congrArg (fun x => Nat.testBit x i) h
    simpa only [Nat.testBit_mod_two_pow,decide_eq_true (mem_range.mp hi),Bool.true_and,
      Nat.testBit_eq_decide_div_mod_eq,decide_eq_decide] using he

private theorem digit_shift_iff {n : ℕ} (hn : 0<n) (T : ℕ) :
    (∀ H : ℕ, (H+T)/n%2=1 ↔ H/n%2=1) ↔ 2*n ∣ T := by
  constructor
  · intro h
    have hpar : T/n%2=0 := by
      have hz := h 0
      simp only [zero_add,Nat.zero_div,Nat.zero_mod,Nat.zero_ne_one,iff_false] at hz
      omega
    have hrem := Nat.mod_lt T hn
    have hrec := Nat.mod_add_div T n
    have hz : T%n=0 := by
      by_contra! hr
      have hb : n-T%n<n := by omega
      have he : n-T%n+T=(T/n+1)*n := by
        rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (T/n) n]
        omega
      have hh := h (n-T%n)
      rw [he,Nat.mul_div_cancel _ hn,Nat.div_eq_of_lt hb] at hh
      omega
    obtain ⟨j,hj⟩ := Nat.dvd_of_mod_eq_zero hpar
    refine ⟨j,?_⟩
    rw [hz,zero_add,hj] at hrec
    rw [← hrec]
    ac_rfl
  · rintro ⟨j,rfl⟩ H
    rw [show 2*n*j=(2*j)*n by ac_rfl,Nat.add_mul_div_right _ _ hn]
    omega

/-- Requiring finite comparison energy at every translate identifies the
precise period of each positive denominator, simultaneously. -/
theorem odd_rows_all_translates_integrable_iff (S : Finset ℕ) (T : ℕ) :
    (∀ H : ℕ, Integrable (fun t =>
      (halfRow S (oddBandWeight (H+T)) t-halfRow S (oddBandWeight H) t)^2)) ↔
      ∀ n ∈ S, 0<n → 2*n ∣ T := by
  simp only [odd_rows_difference_integrable_iff]
  constructor
  · exact fun h n hn hp => (digit_shift_iff hp T).mp fun H => h H n hn hp
  · exact fun h H n hn hp => (digit_shift_iff hp T).mpr (h n hn hp) H

#print axioms odd_rows_difference_integrable_iff
#print axioms dyadic_odd_rows_integrable_iff_congruent
#print axioms odd_rows_all_translates_integrable_iff

/-- Weighted Hamming distance of the observed quotient digits. A changed
digit pays the squared ordinary-prime excess at its denominator. -/
def oddRowDistance (S : Finset ℕ) (H J : ℕ) :=
  ∑ i ∈ S, if H/i%2=J/i%2 then 0 else (ordinaryPrimeExcessCoeff i)^2

private theorem odd_row_residue (S : Finset ℕ) (H J : ℕ) :
    halfRowResidue S (fun i => oddBandWeight H i-oddBandWeight J i)
      (fun i => oddBandWeight H i-oddBandWeight J i) = oddRowDistance S H J := by
  apply sum_congr rfl
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rcases Nat.mod_two_eq_zero_or_one (H/i) with hh | hh <;>
      rcases Nat.mod_two_eq_zero_or_one (J/i) with hj | hj <;>
      simp [oddBandWeight,hi.ne',hh,hj,pow_two]

/-- The measured cutoff energy divided by log(1/ε) converges exactly
to the weighted Hamming distance, including its nonzero values. -/
theorem odd_row_logarithmic_distance (S : Finset ℕ) (H J : ℕ) :
    Filter.Tendsto (fun ε => (∫ t, (cutoffHalfRow ε S (oddBandWeight H) t-
      cutoffHalfRow ε S (oddBandWeight J) t)^2)/Real.log (1/ε)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (oddRowDistance S H J)) := by
  let d := fun i => oddBandWeight H i-oddBandWeight J i
  have he (ε t : ℝ) : cutoffHalfRow ε S d t=
      cutoffHalfRow ε S (oddBandWeight H) t-cutoffHalfRow ε S (oddBandWeight J) t := by
    simp only [cutoffHalfRow,d,sub_mul,sum_sub_distrib]
  simpa only [he,←sq,show halfRowResidue S d d=oddRowDistance S H J from odd_row_residue S H J] using
    cutoff_half_pairing_residue S d d

theorem odd_row_distance_triangle (S : Finset ℕ) (A B C : ℕ) :
    oddRowDistance S A C ≤ oddRowDistance S A B+oddRowDistance S B C := by
  simp only [oddRowDistance,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  by_cases h : A/i%2=B/i%2
  · simp [h]
  · by_cases h' : B/i%2=C/i%2
    · simp [h,h']
    · by_cases h'' : A/i%2=C/i%2 <;> simp [h,h',h'',sq_nonneg]

/-- Two numerator classes have zero distance exactly when their quotient
digits agree at the observed sites. -/
theorem odd_row_distance_eq_zero_iff (S : Finset ℕ) (H J : ℕ) :
    oddRowDistance S H J=0 ↔ ∀ i∈S, 0<i → (H/i%2=1 ↔ J/i%2=1) := by
  rw [oddRowDistance,sum_eq_zero_iff_of_nonneg (fun i _ => by split <;> positivity)]
  apply forall_congr' fun i => forall_congr' fun _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rcases Nat.mod_two_eq_zero_or_one (H/i) with hh | hh <;>
      rcases Nat.mod_two_eq_zero_or_one (J/i) with hj | hj <;>
      simp [hi,hh,hj,centered_prime_atom_ne_zero]

theorem dyadic_odd_row_distance_separates_residues (k H J : ℕ) :
    oddRowDistance ((range k).image fun i => 2^i) H J=0 ↔ H%2^k=J%2^k := by
  rw [odd_row_distance_eq_zero_iff,←odd_rows_difference_integrable_iff]
  exact dyadic_odd_rows_integrable_iff_congruent k H J

#print axioms odd_row_logarithmic_distance
#print axioms odd_row_distance_triangle
#print axioms dyadic_odd_row_distance_separates_residues

end GaloisForLFunctions.ExclusionOfTheCriticalState
