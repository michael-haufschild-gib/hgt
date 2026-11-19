import GaloisForLFunctions.ArithmeticPositiveDuality.TheGramKernelOfHalfOrderDiscrepancy
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest

/-!
# Half-order interactions of the odd-quotient bands

A single numerator selects all active denominator sites. Half-order
fractional discrepancy first recovers each signed excursion, then gives
a finite logarithmic interaction between adjacent bands on a common axis.
-/

noncomputable section
open MeasureTheory Finset
open GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Prime excess at a site selected by the parity digit of the common numerator. -/
def oddBandWeight (H n : ℕ) : ℝ := if H/n%2=1 then ordinaryPrimeExcessCoeff n else 0

/-- Recovery of the actual signed arithmetic excursion by a square-root test. -/
theorem odd_band_abel_recovery (a b H : ℕ) :
    (∫ t, cutPower (-(1/2)) t *
      field (Ioc a b) Nat.cast (oddBandWeight H) (-(1/2)) t) =
        Real.pi * oddQuotientPrimeExcess (Ioc a b) H := by
  have h := half_order_tail (Ioc a b) Nat.cast (oddBandWeight H) 0
  simp only [sub_zero] at h
  rw [h]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hp : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.zero_le a |>.trans_lt (mem_Ioc.mp hn).1)
  rw [if_pos hp]
  rfl

/-- The critical mixed Gram integral is finite for the two bands meeting at b.
The parity digits in both factors refer to exactly the same H. -/
theorem odd_band_mixed_energy (a b c H : ℕ) :
    (∫ t, halfRow (Ioc a b) (oddBandWeight H) t * halfRow (Ioc b c) (oddBandWeight H) t) =
      ∑ i ∈ Ioc a b, ∑ j ∈ Ioc b c, (oddBandWeight H i * oddBandWeight H j) *
        (2*Real.log ((Real.sqrt i + Real.sqrt j)/Real.sqrt (j-i : ℝ))) := by
  apply separated_halfRow_pairing
  intro i hi j hj
  exact ⟨(Nat.zero_le a).trans_lt (mem_Ioc.mp hi).1, (mem_Ioc.mp hi).2.trans_lt (mem_Ioc.mp hj).1⟩

private lemma log_kernel_odd_series {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    HasSum (fun k : ℕ => 2*(1/(2*(k:ℝ)+1))*(Real.sqrt p/Real.sqrt q)^(2*k+1))
      (2*Real.log ((Real.sqrt p+Real.sqrt q)/Real.sqrt (q-p))) := by
  let a := Real.sqrt p
  let b := Real.sqrt q
  have ha : 0 < a := Real.sqrt_pos_of_pos hp
  have hb : 0 < b := Real.sqrt_pos_of_pos (hp.trans hpq)
  have hab : a < b := Real.sqrt_lt_sqrt hp.le hpq
  have hr : a/b < 1 := (div_lt_one hb).mpr hab
  have hh := Real.hasSum_log_sub_log_of_abs_lt_one
    (by rw [abs_of_pos (div_pos ha hb)]; exact hr)
  have hs : 0 < Real.sqrt (q-p) := Real.sqrt_pos_of_pos (sub_pos.mpr hpq)
  have hfac : q-p=(b-a)*(b+a) := by
    rw [show (b-a)*(b+a)=b^2-a^2 by ring, Real.sq_sqrt (hp.trans hpq).le, Real.sq_sqrt hp.le]
  have hrat : ((a+b)/Real.sqrt (q-p))^2 = (1+a/b)/(1-a/b) := by
    rw [div_pow, Real.sq_sqrt (sub_pos.mpr hpq).le, hfac]
    field_simp [hb.ne', (sub_pos.mpr hab).ne', (add_pos hb ha).ne', (sub_pos.mpr hr).ne']
    ring
  have hlog := congrArg Real.log hrat
  rw [Real.log_pow, Real.log_div (by positivity : 1+a/b≠0) (sub_pos.mpr hr).ne'] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  exact hlog.symm ▸ hh

/-- Odd square-root moments separate the two opposite bands exactly. The
k-th term is the product of a positive-power moment in the lower band and
a negative-power moment in the upper band, both with their original signs. -/
theorem odd_band_separated_moments (a b c H : ℕ) :
    HasSum (fun k : ℕ => (2*(1/(2*(k:ℝ)+1))) *
      (∑ i ∈ Ioc a b, oddBandWeight H i * (Real.sqrt i)^(2*k+1)) *
      (∑ j ∈ Ioc b c, oddBandWeight H j / (Real.sqrt j)^(2*k+1)))
      (∫ t, halfRow (Ioc a b) (oddBandWeight H) t * halfRow (Ioc b c) (oddBandWeight H) t) := by
  rw [odd_band_mixed_energy]
  have h := hasSum_sum fun i (hi : i ∈ Ioc a b) => hasSum_sum fun j (hj : j ∈ Ioc b c) =>
    (log_kernel_odd_series (Nat.cast_pos.mpr ((Nat.zero_le a).trans_lt (mem_Ioc.mp hi).1))
      (Nat.cast_lt.mpr ((mem_Ioc.mp hi).2.trans_lt (mem_Ioc.mp hj).1))).mul_left
        (oddBandWeight H i * oddBandWeight H j)
  apply h.congr_fun
  intro k
  rw [Finset.mul_sum (Ioc a b), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_pow]
  ring

#print axioms odd_band_separated_moments
#print axioms odd_band_abel_recovery
#print axioms odd_band_mixed_energy

end GaloisForLFunctions.ExclusionOfTheCriticalState
