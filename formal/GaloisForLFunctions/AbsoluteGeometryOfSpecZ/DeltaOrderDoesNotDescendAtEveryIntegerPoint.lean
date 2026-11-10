import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArithmeticSquareIsADeltaRing
import GaloisForLFunctions.SignFreePurityMechanisms.TheFermatQuotientIsTheDerivativeAtAPrime

/-!
# The defect of descending a p-derivation to an integer point

The diagonal point of the arithmetic square commutes with the p-derivation
exactly on elements whose first and pth ghost components agree.
Without this compatibility, evaluated derivative jets do not measure
integer valuation: the Teichmüller element `[p]` has zero positive jets
but diagonal value `p`, which is not divisible by `p²`.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open SignFreePurityMechanisms

variable {p : ℕ+} (hp : p.Prime)

/-- The difference of the two p-derivations is the displacement of the integer point. -/
theorem mul_delta_descent_defect (x : ghostRing) :
    ((p : ℕ) : ℤ) * (ghostComponent 1 (delta p hp x) -
      fermatQuotient p (ghostComponent 1 x)) =
        ghostComponent p x - ghostComponent 1 x := by
  letI : Fact (p : ℕ).Prime := ⟨hp⟩
  have hx := congrArg (ghostComponent 1) (frobenius_eq_pow_add_delta p hp x)
  rw [ghostComponent_frobenius, mul_one, map_add, map_pow, map_mul, map_natCast] at hx
  have hq := mul_fermatQuotient (p : ℕ) (ghostComponent 1 x)
  linear_combination -hx - hq

/-- Descent of the derivative is equivalent to equality of the two integer values. -/
theorem delta_descends_iff (x : ghostRing) :
    ghostComponent 1 (delta p hp x) = fermatQuotient p (ghostComponent 1 x) ↔
      ghostComponent p x = ghostComponent 1 x := by
  have hd := mul_delta_descent_defect hp x
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (show (p : ℕ).Prime from hp).ne_zero
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at hd
    exact sub_eq_zero.mp hd.symm
  · intro h
    rw [h, sub_self] at hd
    exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hp0)

theorem delta_zero : delta p hp 0 = 0 := by
  apply natCast_mul_left_cancel_ghost (show (p : ℕ).Prime from hp).ne_zero
  have h := frobenius_eq_pow_add_delta p hp 0
  simpa only [map_zero, zero_pow (show (p : ℕ).Prime from hp).ne_zero,
    zero_add, mul_zero] using h.symm

/-- Every positive derivative jet of a Teichmüller element vanishes. -/
theorem iterate_delta_teichmuller (a : ℤ) (j : ℕ) :
    (delta p hp)^[j + 1] (teichmuller a) = 0 := by
  induction j with
  | zero => simpa only [zero_add, Function.iterate_one] using delta_teichmuller p hp a
  | succ j ih => rw [Function.iterate_succ_apply', ih, delta_zero hp]

/-- Evaluated delta jets can vanish to every order while the integer value has order one. -/
theorem exists_delta_jets_without_integer_order :
    ∃ x : ghostRing,
      ghostComponent 1 x = ((p : ℕ) : ℤ) ∧
      (∀ j : ℕ, ((p : ℕ) : ℤ) ∣ ghostComponent 1 ((delta p hp)^[j] x)) ∧
      ¬ ((p : ℕ) : ℤ) ^ 2 ∣ ghostComponent 1 x := by
  refine ⟨teichmuller ((p : ℕ) : ℤ), ?_, ?_, ?_⟩
  · simp only [ghostComponent_teichmuller, PNat.one_coe, pow_one]
  · intro j
    cases j with
    | zero => simp only [Function.iterate_zero_apply, ghostComponent_teichmuller,
        PNat.one_coe, pow_one, dvd_refl]
    | succ j => rw [iterate_delta_teichmuller hp, map_zero]; exact dvd_zero _
  · simp only [ghostComponent_teichmuller, PNat.one_coe, pow_one]
    intro h
    have hn : (p : ℕ) ^ 2 ∣ (p : ℕ) := by exact_mod_cast h
    have hle := Nat.le_of_dvd (show (p : ℕ).Prime from hp).pos hn
    nlinarith only [hle, (show (p : ℕ).Prime from hp).two_le]

#print axioms delta_descends_iff
#print axioms exists_delta_jets_without_integer_order

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
