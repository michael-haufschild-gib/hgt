import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic

/-!
# Simple polynomial zeros at ordinary differential-equation points

Below the characteristic, differentiation lowers a positive root multiplicity by one.
Consequently a nonzero polynomial solution of a second-order linear equation cannot
have a multiple zero where the leading coefficient is nonzero. The degree restriction
is essential in positive characteristic, where Frobenius powers have zero derivative.
-/

noncomputable section

namespace GaloisForLFunctions.PolynomialODE

open Polynomial

variable {K : Type*} [Field K]

private theorem multiplicity_le_degree {f : K[X]} (hf : f ≠ 0) (z : K) :
    f.rootMultiplicity z ≤ f.natDegree := by
  have h := natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd z) hf
  simpa only [(monic_X_sub_C z).natDegree_pow, natDegree_X_sub_C, mul_one] using h

private theorem cast_ne_zero_below_char (p : ℕ) [CharP K p]
    {m : ℕ} (hpos : 0 < m) (hlt : m < p) : (m : K) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff K p]
  exact Nat.not_dvd_of_pos_of_lt hpos hlt

/-- A positive-degree polynomial below the characteristic has nonzero derivative. -/
theorem derivative_ne_zero_below_char (p : ℕ) [CharP K p]
    {f : K[X]} (hpos : 0 < f.natDegree) (hlt : f.natDegree < p) :
    f.derivative ≠ 0 := by
  intro hzero
  have h := congrArg (fun g : K[X] => g.coeff (f.natDegree - 1)) hzero
  rw [coeff_derivative, Nat.sub_add_cancel hpos, coeff_zero] at h
  have hn : ((f.natDegree - 1 : ℕ) : K) + 1 = f.natDegree := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun m : ℕ => (m : K)) (Nat.sub_add_cancel hpos)
  rw [hn] at h
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hpos))
    (cast_ne_zero_below_char p hpos hlt)) h

/-- Ordinary points of a second-order equation have simple zeros for solutions below the
characteristic. -/
theorem simple_zero_of_secondOrder (p : ℕ) [CharP K p]
    {a b c f : K[X]} (hf : f ≠ 0) (hdegree : f.natDegree < p)
    (hode : a * f.derivative.derivative + b * f.derivative + c * f = 0)
    {z : K} (ha : a.eval z ≠ 0) (hz : f.IsRoot z) :
    f.derivative.eval z ≠ 0 := by
  intro hd
  have hm : 1 < f.rootMultiplicity z :=
    (one_lt_rootMultiplicity_iff_isRoot hf).mpr ⟨hz, hd⟩
  have hbound := multiplicity_le_degree hf z
  have hf' := derivative_ne_zero_below_char p (by omega : 0 < f.natDegree) hdegree
  have hm' := derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hz
    (mem_nonZeroDivisors_of_ne_zero (cast_ne_zero_below_char p (by omega)
      (lt_of_le_of_lt hbound hdegree)))
  have hbound' := multiplicity_le_degree hf' z
  have hdegree' : f.derivative.natDegree < p :=
    (natDegree_derivative_le f).trans_lt (by omega)
  have hf'' := derivative_ne_zero_below_char p
    (by omega : 0 < f.derivative.natDegree) hdegree'
  have hm'' := derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
    (show f.derivative.IsRoot z from hd)
    (mem_nonZeroDivisors_of_ne_zero (cast_ne_zero_below_char p (by omega)
      (lt_of_le_of_lt hbound' hdegree')))
  have ha0 : a ≠ 0 := by intro h; exact ha (by rw [h, eval_zero])
  have hprod : a * f.derivative.derivative ≠ 0 := mul_ne_zero ha0 hf''
  have hdvd0 : (X - C z) ^ (f.rootMultiplicity z - 1) ∣ f :=
    (le_rootMultiplicity_iff hf).mp (Nat.sub_le _ _)
  have hdvd1 : (X - C z) ^ (f.rootMultiplicity z - 1) ∣ f.derivative := by
    rw [← hm']
    exact f.derivative.pow_rootMultiplicity_dvd z
  have hdvd2 : (X - C z) ^ (f.rootMultiplicity z - 1) ∣
      a * f.derivative.derivative := by
    have he : a * f.derivative.derivative = -(b * f.derivative + c * f) := by
      linear_combination hode
    rw [he]
    exact dvd_neg.mpr (dvd_add (dvd_mul_of_dvd_right hdvd1 b)
      (dvd_mul_of_dvd_right hdvd0 c))
  have hle := (le_rootMultiplicity_iff hprod).mpr hdvd2
  rw [rootMultiplicity_mul hprod, rootMultiplicity_eq_zero ha, zero_add] at hle
  omega

end GaloisForLFunctions.PolynomialODE
