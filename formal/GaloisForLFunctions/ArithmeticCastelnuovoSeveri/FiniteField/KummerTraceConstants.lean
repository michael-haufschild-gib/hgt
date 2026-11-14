import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerCyclicCovers
import Mathlib.Algebra.CharP.Frobenius

/-!
# Trace-zero constants for Kummer equations

In the field with `Q²` elements, the difference `x-x^Q` is negated by the
`Q`-power Frobenius. A polynomial root bound supplies a nonzero such difference,
so the coefficient required in a trace-normalized Kummer equation exists in
the specified field. Ratios of two nonzero choices are Frobenius-fixed.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- The specified finite extension retains the characteristic of its prime field. -/
instance squareConstantField_charP (s : ℕ) : CharP (SquareConstantField p s) p :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod p) (SquareConstantField p s)).injective p

/-- The square of the `Q`-power Frobenius is the identity on the chosen field. -/
theorem squareConstantField_frobenius_sq (s : ℕ) (x : SquareConstantField p s) :
    (x ^ p ^ (s + 1)) ^ p ^ (s + 1) = x := by
  letI := Fintype.ofFinite (SquareConstantField p s)
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, squareConstantField_card] at h
  rw [← pow_mul, ← pow_add, show (s + 1) + (s + 1) = 2 * (s + 1) by omega]
  exact h

/-- Frobenius differences are trace-zero, in every characteristic. -/
theorem squareConstantField_difference_traceZero (s : ℕ) (x : SquareConstantField p s) :
    (x - x ^ p ^ (s + 1)) ^ p ^ (s + 1) = -(x - x ^ p ^ (s + 1)) := by
  rw [sub_pow_char_pow, squareConstantField_frobenius_sq]
  ring

/-- The `Q`-power Frobenius is nontrivial on the field of order `Q²`. -/
theorem squareConstantField_exists_not_fixed (s : ℕ) :
    ∃ x : SquareConstantField p s, x ^ p ^ (s + 1) ≠ x := by
  classical
  letI := Fintype.ofFinite (SquareConstantField p s)
  let f : (SquareConstantField p s)[X] := X ^ p ^ (s + 1) - X
  have hQ : 1 < p ^ (s + 1) := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hf : f ≠ 0 := by
    intro he
    have hc := congrArg (fun P : (SquareConstantField p s)[X] => P.coeff (p ^ (s + 1))) he
    simp only [f, coeff_sub, coeff_X_pow_self, coeff_X,
      if_neg (Ne.symm (ne_of_gt hQ)), sub_zero, coeff_zero] at hc
    exact one_ne_zero hc
  have hd : f.natDegree ≤ p ^ (s + 1) := by
    exact (natDegree_sub_le _ _).trans (by simp only [natDegree_X_pow, natDegree_X]; omega)
  have hcard : p ^ (s + 1) < Fintype.card (SquareConstantField p s) := by
    rw [← Nat.card_eq_fintype_card, squareConstantField_card]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  obtain ⟨x, hx⟩ := f.exists_eval_ne_zero_of_natDegree_lt_card hf
    (by rw [Cardinal.mk_fintype, Nat.cast_lt]; exact hd.trans_lt hcard)
  exact ⟨x, sub_ne_zero.mp (by simpa only [f, eval_sub, eval_pow, eval_X] using hx)⟩

/-- A nonzero trace-zero element exists over the exact field of definition. -/
theorem squareConstantField_exists_traceZero (s : ℕ) :
    ∃ η : SquareConstantField p s, η ≠ 0 ∧ η ^ p ^ (s + 1) = -η := by
  obtain ⟨x, hx⟩ := squareConstantField_exists_not_fixed p s
  exact ⟨x - x ^ p ^ (s + 1), sub_ne_zero.mpr (Ne.symm hx),
    squareConstantField_difference_traceZero p s x⟩

/-- A fixed choice of nonzero trace-zero coefficient. -/
def kummerTraceConstant (s : ℕ) : (SquareConstantField p s)ˣ :=
  Units.mk0 (squareConstantField_exists_traceZero p s).choose
    (squareConstantField_exists_traceZero p s).choose_spec.1

/-- The chosen constant has the Frobenius behavior required by the curve equation. -/
theorem kummerTraceConstant_frobenius (s : ℕ) :
    (kummerTraceConstant p s : SquareConstantField p s) ^ p ^ (s + 1) =
      -(kummerTraceConstant p s : SquareConstantField p s) :=
  (squareConstantField_exists_traceZero p s).choose_spec.2

/-- Trace-zero elements differ from the chosen coefficient by a Frobenius-fixed ratio. -/
theorem kummerTraceConstant_ratio_fixed (s : ℕ) (x : SquareConstantField p s)
    (hx : x ^ p ^ (s + 1) = -x) :
    (x / (kummerTraceConstant p s : SquareConstantField p s)) ^ p ^ (s + 1) =
      x / (kummerTraceConstant p s : SquareConstantField p s) := by
  rw [div_pow, hx, kummerTraceConstant_frobenius, neg_div_neg_eq]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
