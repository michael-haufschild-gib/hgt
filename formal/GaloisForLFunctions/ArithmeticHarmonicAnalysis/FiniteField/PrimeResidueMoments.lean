import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodTupleSeriesFromRadicalClosedRows
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.PeriodMassShellRows

/-!
# Prime-residue statistics and interval completion

Chinese remaindering factors the complete average of arbitrary real functions
on distinct prime residue fields. Centering and complete-period absolute mass
then bound the error on every interval. No equidistribution assumption enters:
the error is an explicit product of local absolute masses.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

noncomputable section

/-- A product of local observables, evaluated at one common integer. -/
def primeResidueStatistic (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ S, f p (n : ZMod p.val)

/-- The product of the local uniform averages. -/
def primeResidueMean (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) : ℝ :=
  ∏ p ∈ S, (∑ r ∈ range p.val, f p (r : ZMod p.val)) / p.val

/-- The product of the unnormalized local absolute masses. -/
def primeResidueMass (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) : ℝ :=
  ∏ p ∈ S, ∑ r ∈ range p.val, |f p (r : ZMod p.val)|

theorem primeResidue_local_periodic (p : Nat.Primes) (f : ZMod p.val → ℝ) :
    Function.Periodic (fun n : ℕ => f (n : ZMod p.val)) p.val := by
  intro n
  simp only [Nat.cast_add, ZMod.natCast_self, add_zero]

theorem primeResidueStatistic_periodic (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) :
    Function.Periodic (primeResidueStatistic S f) (primeSetProduct S) := by
  intro n
  apply prod_congr rfl
  intro p hp
  obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp
  have hPm : primeSetProduct S = p.val * m := hm
  rw [hPm, mul_comm]
  exact (primeResidue_local_periodic p (f p)).nat_mul m n

/-- Exact independence of all local observables over one squarefree period. -/
theorem sum_primeResidueStatistic (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) :
    ∑ n ∈ range (primeSetProduct S), primeResidueStatistic S f n =
      ∏ p ∈ S, ∑ r ∈ range p.val, f p (r : ZMod p.val) :=
  sum_range_primeSetProduct_prod S _ (fun p => primeResidue_local_periodic p (f p))

theorem sum_primeResidueStatistic_eq_mean (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) :
    ∑ n ∈ range (primeSetProduct S), primeResidueStatistic S f n =
      (primeSetProduct S : ℝ) * primeResidueMean S f := by
  rw [sum_primeResidueStatistic, primeResidueMean, prod_div_distrib,
    ← Nat.cast_prod]
  have hP : (primeSetProduct S : ℝ) ≠ 0 := by
    exact_mod_cast (primeSetProduct_pos S).ne'
  change _ = (primeSetProduct S : ℝ) * (_ / (primeSetProduct S : ℝ))
  field_simp [hP]

theorem sum_abs_primeResidueStatistic (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) :
    ∑ n ∈ range (primeSetProduct S), |primeResidueStatistic S f n| =
      primeResidueMass S f := by
  simp only [primeResidueStatistic, abs_prod]
  exact sum_range_primeSetProduct_prod S _
    (fun p => primeResidue_local_periodic p (fun r => |f p r|))

theorem primeResidueMean_abs_le_mass (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) :
    (primeSetProduct S : ℝ) * |primeResidueMean S f| ≤ primeResidueMass S f := by
  have h := abs_sum_le_sum_abs (primeResidueStatistic S f) (range (primeSetProduct S))
  rw [sum_primeResidueStatistic_eq_mean, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    sum_abs_primeResidueStatistic] at h
  exact h

/-- Boundary completion has a cost determined entirely by local absolute masses. -/
theorem abs_sum_Ico_primeResidueStatistic_sub_mean (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → ZMod p.val → ℝ) (A B : ℕ) :
    |(∑ n ∈ Ico A B, primeResidueStatistic S f n) -
      ((B - A : ℕ) : ℝ) * primeResidueMean S f| ≤ 2 * primeResidueMass S f := by
  have hper : ∀ n, primeResidueStatistic S f (n + primeSetProduct S) -
      primeResidueMean S f = primeResidueStatistic S f n - primeResidueMean S f :=
    fun n => congrArg (fun x => x - primeResidueMean S f)
      (primeResidueStatistic_periodic S f n)
  have hmean : ∑ n ∈ range (primeSetProduct S),
      (primeResidueStatistic S f n - primeResidueMean S f) = 0 := by
    rw [sum_sub_distrib, sum_primeResidueStatistic_eq_mean]
    simp only [sum_const, card_range, nsmul_eq_mul, sub_self]
  have h := SuccessorShellArithmetic.abs_sum_Ico_periodic_le_period_mass
    (primeSetProduct_pos S) (fun n => primeResidueStatistic S f n - primeResidueMean S f)
    hper hmean A B
  simp only [sum_sub_distrib, sum_const, card_Ico, nsmul_eq_mul] at h
  refine h.trans ?_
  calc
    _ ≤ ∑ n ∈ range (primeSetProduct S),
        (|primeResidueStatistic S f n| + |primeResidueMean S f|) :=
      sum_le_sum fun n _ => abs_sub _ _
    _ = primeResidueMass S f + (primeSetProduct S : ℝ) * |primeResidueMean S f| := by
      rw [sum_add_distrib, sum_abs_primeResidueStatistic]
      simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ 2 * primeResidueMass S f := by
      linarith only [primeResidueMean_abs_le_mass S f]

/-- Cosine observables have local absolute mass at most the residue-field size. -/
theorem primeResidueMass_cos_le (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) :
    primeResidueMass S (fun p r => Real.cos (θ p r)) ≤ (primeSetProduct S : ℝ) := by
  rw [primeResidueMass, primeSetProduct, Nat.cast_prod]
  apply prod_le_prod
  · intro p _
    exact sum_nonneg fun r _ => abs_nonneg _
  · intro p _
    calc
      _ ≤ ∑ _r ∈ range p.val, (1 : ℝ) :=
        sum_le_sum fun r _ => Real.abs_cos_le_one _
      _ = (p.val : ℝ) := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]

/-- Approximate independence of cosine statistics on any integer interval. -/
theorem abs_sum_Ico_primeResidueCos_sub_mean (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) (A B : ℕ) :
    |(∑ n ∈ Ico A B, ∏ p ∈ S, Real.cos (θ p (n : ZMod p.val))) -
      ((B - A : ℕ) : ℝ) *
        (∏ p ∈ S, (∑ r ∈ range p.val, Real.cos (θ p (r : ZMod p.val))) / p.val)| ≤
      2 * (primeSetProduct S : ℝ) :=
  (abs_sum_Ico_primeResidueStatistic_sub_mean S (fun p r => Real.cos (θ p r)) A B).trans
    (mul_le_mul_of_nonneg_left (primeResidueMass_cos_le S θ) (by positivity))

/-- Dividing by the sample size gives the explicit `2P/N` independence error. -/
theorem abs_average_primeResidueCos_sub_mean (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) (A N : ℕ) :
    |(∑ n ∈ Ico A (A + (N + 1)), ∏ p ∈ S, Real.cos (θ p (n : ZMod p.val))) /
      ((N : ℝ) + 1) -
        (∏ p ∈ S, (∑ r ∈ range p.val, Real.cos (θ p (r : ZMod p.val))) / p.val)| ≤
      2 * (primeSetProduct S : ℝ) / ((N : ℝ) + 1) := by
  have h := abs_sum_Ico_primeResidueCos_sub_mean S θ A (A + (N + 1))
  simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one] at h
  have hN : (0 : ℝ) < N + 1 := by positivity
  have he (x y : ℝ) : x / ((N : ℝ) + 1) - y =
      (x - ((N : ℝ) + 1) * y) / ((N : ℝ) + 1) := by
    rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hN)]
  rw [he, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right h hN.le

#print axioms sum_primeResidueStatistic
#print axioms abs_sum_Ico_primeResidueStatistic_sub_mean
#print axioms abs_average_primeResidueCos_sub_mean

end

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
