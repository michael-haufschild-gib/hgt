import GaloisForLFunctions.KodairaParshinAbc.Legendre.DeuringPolynomials
import GaloisForLFunctions.HTGeometry.Polynomial.LowDegreeODE
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Ordinary and elliptic zeros of the Deuring numerator

The binomial-square polynomial has simple roots away from both cusps. Its weight-two
numerator has no common root with it. The Riccati identity then confines repeated
numerator roots to the quadratic elliptic divisor.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial

variable {K : Type*} [Field K]

private theorem factorial_ne_zero_below_char (p : ℕ) [CharP K p]
    (m : ℕ) (hm : m < p) : (m.factorial : K) ≠ 0 := by
  induction m with
  | zero =>
    rw [Nat.factorial_zero, Nat.cast_one]
    exact one_ne_zero
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    apply mul_ne_zero _ (ih (by omega))
    rw [ne_eq, CharP.cast_eq_zero_iff K p]
    exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos m) hm

private theorem two_ne_zero_odd_char (n : ℕ) [CharP K (2 * n + 1)] : (2 : K) ≠ 0 := by
  have h := CharP.cast_eq_zero K (2 * n + 1)
  push_cast at h
  intro h2
  rw [h2, zero_mul, zero_add] at h
  exact one_ne_zero h

/-- The Deuring polynomial avoids the cusp `1` in its natural characteristic. -/
theorem binomialSquare_eval_one_ne_zero (n : ℕ) [CharP K (2 * n + 1)] :
    (binomialSquare n : K[X]).eval 1 ≠ 0 := by
  rw [binomialSquare_eval_one]
  intro hzero
  have h := congrArg (fun m : ℕ => (m : K))
    (Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega))
  push_cast at h
  rw [hzero, zero_mul, zero_mul] at h
  exact factorial_ne_zero_below_char (2 * n + 1) (2 * n) (by omega) h.symm

/-- Every root of a Deuring polynomial is simple, over any extension of its prime field. -/
theorem binomialSquare_root_simple (n : ℕ) [CharP K (2 * n + 1)]
    (z : K) (hz : (binomialSquare n : K[X]).IsRoot z) :
    (binomialSquare n : K[X]).derivative.eval z ≠ 0 := by
  have h0 : z ≠ 0 := by
    intro h; subst z
    exact one_ne_zero ((binomialSquare_eval_zero (R := K) n).symm.trans hz)
  have h1 : z ≠ 1 := by
    intro h; subst z
    exact binomialSquare_eval_one_ne_zero n hz
  apply PolynomialODE.simple_zero_of_secondOrder (2 * n + 1)
    (a := 4 * X * (1 - X)) (b := 4 * (1 - 2 * X)) (c := -1)
    (binomialSquare_monic n).ne_zero
    (by rw [binomialSquare_natDegree]; omega)
    (by simpa only [neg_one_mul, sub_eq_add_neg] using
      binomialSquare_picardFuchs_of_char (R := K) n) _ hz
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero (two_ne_zero_odd_char (K := K) n)
      (two_ne_zero_odd_char (K := K) n) using 1
    norm_num
  simpa only [eval_mul, eval_ofNat, eval_X, eval_sub, eval_one] using
    mul_ne_zero (mul_ne_zero h4 h0) (sub_ne_zero.mpr h1.symm)

/-- The Deuring polynomial is separable without a supersingularity assumption. -/
theorem binomialSquare_separable (n : ℕ) [CharP K (2 * n + 1)] :
    (binomialSquare n : K[X]).Separable := by
  classical
  apply (separable_map (algebraMap K (AlgebraicClosure K))).mp
  rw [map_binomialSquare]
  apply (nodup_roots_iff_of_splits (binomialSquare_monic n).ne_zero
    (IsAlgClosed.splits _)).mp
  rw [Multiset.nodup_iff_count_le_one]
  intro z
  rw [count_roots]
  apply not_lt.mp
  intro hm
  have h := (one_lt_rootMultiplicity_iff_isRoot (binomialSquare_monic n).ne_zero).mp hm
  exact binomialSquare_root_simple n z h.1 h.2

/-- There are exactly `n` geometric Deuring roots, counted without multiplicity. -/
theorem binomialSquare_card_roots (n : ℕ) [CharP K (2 * n + 1)] :
    Fintype.card ((binomialSquare n : K[X]).rootSet (AlgebraicClosure K)) = n := by
  rw [card_rootSet_eq_natDegree (binomialSquare_separable n)
    (IsAlgClosed.splits _), binomialSquare_natDegree]

private theorem six_ne_zero (n : ℕ) [CharP K (2 * n + 1)] (hn : 2 ≤ n) :
    (6 : K) ≠ 0 := by
  have h3 : (3 : K) ≠ 0 := by
    have hcast : ((3 : ℕ) : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K (2 * n + 1) 3]
      exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    simpa only [Nat.cast_ofNat] using hcast
  convert mul_ne_zero (two_ne_zero_odd_char (K := K) n) h3 using 1
  norm_num

/-- In characteristic at least five, the weight-two numerator avoids every Deuring root. -/
theorem binomialSquare_operator_no_common_zero (n : ℕ) [CharP K (2 * n + 1)]
    (hn : 2 ≤ n) (z : K) :
    (binomialSquare n : K[X]).eval z ≠ 0 ∨
      (legendreOperator (binomialSquare n : K[X])).eval z ≠ 0 := by
  by_cases hz : (binomialSquare n : K[X]).eval z ≠ 0
  · exact Or.inl hz
  right
  push Not at hz
  have h0 : z ≠ 0 := by
    intro h; subst z
    rw [binomialSquare_eval_zero] at hz
    exact one_ne_zero hz
  have h1 : z ≠ 1 := by
    intro h; subst z
    exact binomialSquare_eval_one_ne_zero n hz
  simp only [legendreOperator, eval_add, eval_mul, eval_sub, eval_one, eval_ofNat,
    eval_X, hz, mul_zero, zero_add]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (six_ne_zero n hn) h0)
    (sub_ne_zero.mpr h1.symm)) (binomialSquare_root_simple n z hz)

/-- The ordinary numerator and the Deuring polynomial are coprime over the prime field
and over every field extension. -/
theorem binomialSquare_operator_coprime (n : ℕ) [CharP K (2 * n + 1)] (hn : 2 ≤ n) :
    IsCoprime (binomialSquare n : K[X]) (legendreOperator (binomialSquare n)) := by
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).mpr
  intro z
  rw [← eval_map_algebraMap, ← eval_map_algebraMap]
  have hmap :
      (legendreOperator (binomialSquare n : K[X])).map (algebraMap K (AlgebraicClosure K)) =
        legendreOperator (binomialSquare n : (AlgebraicClosure K)[X]) := by
    simp [legendreOperator, ← Polynomial.derivative_map, map_binomialSquare]
  rw [map_binomialSquare, hmap]
  exact binomialSquare_operator_no_common_zero n hn z

/-- Repeated numerator zeros can occur only on the elliptic quadratic. -/
theorem binomialSquare_operator_multiple_zero (n : ℕ) [CharP K (2 * n + 1)]
    (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).eval z ≠ 0 ∨
      (legendreOperator (binomialSquare n : K[X])).derivative.eval z ≠ 0 ∨
        z ^ 2 - z + 1 = 0 := by
  by_contra h
  push Not at h
  obtain ⟨hB, hdB, hL⟩ := h
  have hH : (binomialSquare n : K[X]).eval z ≠ 0 :=
    (binomialSquare_operator_no_common_zero n hn z).resolve_right (not_not.mpr hB)
  have he := legendreOperator_riccati_defect (binomialSquare n : K[X])
  rw [binomialSquare_picardFuchs_of_char, mul_zero] at he
  have hv := congrArg (Polynomial.eval z) he
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat, eval_X, eval_one,
    hB, hdB, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, sub_zero, zero_add, eval_zero] at hv
  exact (mul_ne_zero hL (pow_ne_zero 2 hH)) hv

/-- Every repeated numerator root is exactly double; higher multiplicities are impossible. -/
theorem binomialSquare_operator_no_triple_zero (n : ℕ) [CharP K (2 * n + 1)]
    (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).eval z ≠ 0 ∨
      (legendreOperator (binomialSquare n : K[X])).derivative.eval z ≠ 0 ∨
        (legendreOperator (binomialSquare n : K[X])).derivative.derivative.eval z ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hB, hdB, hddB⟩ := h
  have hH : (binomialSquare n : K[X]).eval z ≠ 0 :=
    (binomialSquare_operator_no_common_zero n hn z).resolve_right (not_not.mpr hB)
  have hL : z ^ 2 - z + 1 = 0 :=
    ((binomialSquare_operator_multiple_zero n hn z).resolve_left (not_not.mpr hB)).resolve_left
      (not_not.mpr hdB)
  have hb := hB
  simp only [legendreOperator, eval_add, eval_mul, eval_sub, eval_one, eval_ofNat,
    eval_X] at hb
  have hp := congrArg (Polynomial.eval z) (binomialSquare_picardFuchs_of_char (R := K) n)
  have hfirst := congrArg (Polynomial.eval z) (binomialSquare_operator_derivative (R := K) n)
  have hsecond := congrArg (Polynomial.eval z)
    (binomialSquare_operator_secondDerivative (R := K) n)
  simp only [eval_sub, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_zero,
    hdB, hddB, mul_zero] at hp hfirst hsecond
  have hprod : 2 * (1 - 2 * z) * (binomialSquare n : K[X]).eval z = 0 := by
    linear_combination
      -(6 * z * (1 - z)) * hsecond - 3 * (1 - 2 * z) * hp -
        6 * (1 - 2 * z) * hfirst + 5 * hb
  have hc : 1 - 2 * z = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hH)).resolve_left
      (two_ne_zero_odd_char n)
  have h3 : (3 : K) = 0 := by
    linear_combination 4 * hL - (1 - 2 * z) * hc
  apply six_ne_zero (K := K) n hn
  linear_combination 2 * h3

/-- The geometric multiplicity of every numerator root is at most two. -/
theorem binomialSquare_operator_rootMultiplicity_le_two (n : ℕ) [CharP K (2 * n + 1)]
    (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).rootMultiplicity z ≤ 2 := by
  by_contra hm
  have h0 := isRoot_iterate_derivative_of_lt_rootMultiplicity
    (p := legendreOperator (binomialSquare n : K[X])) (t := z) (n := 0) (by omega)
  have h1 := isRoot_iterate_derivative_of_lt_rootMultiplicity
    (p := legendreOperator (binomialSquare n : K[X])) (t := z) (n := 1) (by omega)
  have h2 := isRoot_iterate_derivative_of_lt_rootMultiplicity
    (p := legendreOperator (binomialSquare n : K[X])) (t := z) (n := 2) (by omega)
  rcases binomialSquare_operator_no_triple_zero n hn z with h | h | h
  · exact h h0
  · exact h h1
  · exact h h2

end GaloisForLFunctions.KodairaParshinAbc.Legendre
