import GaloisForLFunctions.KodairaParshinAbc.Legendre.DeuringZeros

/-!
# Exact multiplicity of the weight-two Deuring numerator

At a numerator root, the Riccati identity identifies derivative vanishing with the
elliptic equation `z²-z+1 = 0`. The absence of triple zeros gives the exact
multiplicity: two on that quadratic and one away from it.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K]

/-- Every numerator root on the elliptic quadratic has vanishing first derivative. -/
theorem binomialSquare_operator_elliptic_derivative (n : ℕ) [CharP K (2 * n + 1)]
    (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).eval z ≠ 0 ∨
      z ^ 2 - z + 1 ≠ 0 ∨
        (legendreOperator (binomialSquare n : K[X])).derivative.eval z = 0 := by
  by_cases hB : (legendreOperator (binomialSquare n : K[X])).eval z = 0
  · by_cases hL : z ^ 2 - z + 1 = 0
    · refine Or.inr (Or.inr ?_)
      have hH : (binomialSquare n : K[X]).eval z ≠ 0 :=
        (binomialSquare_operator_no_common_zero n hn z).resolve_right (not_not.mpr hB)
      have h0 : z ≠ 0 := by
        intro hz
        subst z
        norm_num at hL
      have h1 : 1 - z ≠ 0 := by
        intro hz
        have hz1 : z = 1 := (sub_eq_zero.mp hz).symm
        subst z
        norm_num at hL
      have h2 : (2 : K) ≠ 0 := by
        rw [ne_eq, ← Nat.cast_ofNat, CharP.cast_eq_zero_iff K (2 * n + 1)]
        exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      have h3 : (3 : K) ≠ 0 := by
        rw [ne_eq, ← Nat.cast_ofNat, CharP.cast_eq_zero_iff K (2 * n + 1)]
        exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      have h6 : (6 : K) ≠ 0 := by
        convert mul_ne_zero h2 h3 using 1
        norm_num
      have he := legendreOperator_riccati_defect (binomialSquare n : K[X])
      rw [binomialSquare_picardFuchs_of_char, mul_zero] at he
      have hv := congrArg (Polynomial.eval z) he
      simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat, eval_X, eval_one,
        hB, hL, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        add_zero, sub_zero, eval_zero] at hv
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left
        (mul_ne_zero (mul_ne_zero h6 h0) h1))).resolve_right hH
    · exact Or.inr (Or.inl hL)
  · exact Or.inl hB

/-- The double roots are exactly the numerator roots on the elliptic quadratic. -/
theorem binomialSquare_operator_rootMultiplicity_eq_two_iff
    (n : ℕ) [CharP K (2 * n + 1)] (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).rootMultiplicity z = 2 ↔
      (legendreOperator (binomialSquare n : K[X])).eval z = 0 ∧ z ^ 2 - z + 1 = 0 := by
  have hne := (binomialSquare_operator_monic (R := K) n).ne_zero
  constructor
  · intro hm
    have hz := (one_lt_rootMultiplicity_iff_isRoot hne).mp (by omega : 1 <
      (legendreOperator (binomialSquare n : K[X])).rootMultiplicity z)
    exact ⟨hz.1, ((binomialSquare_operator_multiple_zero n hn z).resolve_left
      (not_not.mpr hz.1)).resolve_left (not_not.mpr hz.2)⟩
  · rintro ⟨hB, hL⟩
    have hd := ((binomialSquare_operator_elliptic_derivative n hn z).resolve_left
      (not_not.mpr hB)).resolve_left (not_not.mpr hL)
    have hm := (one_lt_rootMultiplicity_iff_isRoot hne).mpr ⟨hB, hd⟩
    have hb := binomialSquare_operator_rootMultiplicity_le_two n hn z
    omega

/-- The simple roots are exactly the numerator roots outside the elliptic quadratic. -/
theorem binomialSquare_operator_rootMultiplicity_eq_one_iff
    (n : ℕ) [CharP K (2 * n + 1)] (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).rootMultiplicity z = 1 ↔
      (legendreOperator (binomialSquare n : K[X])).eval z = 0 ∧ z ^ 2 - z + 1 ≠ 0 := by
  have hne := (binomialSquare_operator_monic (R := K) n).ne_zero
  constructor
  · intro hm
    have hz := (rootMultiplicity_pos hne).mp (by omega : 0 <
      (legendreOperator (binomialSquare n : K[X])).rootMultiplicity z)
    refine ⟨hz, fun hL => ?_⟩
    have htwo := (binomialSquare_operator_rootMultiplicity_eq_two_iff n hn z).mpr ⟨hz, hL⟩
    omega
  · rintro ⟨hB, hL⟩
    have hp := (rootMultiplicity_pos hne).mpr hB
    have hb := binomialSquare_operator_rootMultiplicity_le_two n hn z
    have hnot : (legendreOperator (binomialSquare n : K[X])).rootMultiplicity z ≠ 2 :=
      fun htwo => hL ((binomialSquare_operator_rootMultiplicity_eq_two_iff n hn z).mp htwo).2
    omega

/-- A pointwise formula gives the entire geometric multiplicity function. -/
theorem binomialSquare_operator_rootMultiplicity
    (n : ℕ) [CharP K (2 * n + 1)] (hn : 2 ≤ n) (z : K) :
    (legendreOperator (binomialSquare n : K[X])).rootMultiplicity z =
      if (legendreOperator (binomialSquare n : K[X])).eval z = 0 then
        if z ^ 2 - z + 1 = 0 then 2 else 1
      else 0 := by
  classical
  by_cases hB : (legendreOperator (binomialSquare n : K[X])).eval z = 0
  · rw [if_pos hB]
    by_cases hL : z ^ 2 - z + 1 = 0
    · rw [if_pos hL]
      exact (binomialSquare_operator_rootMultiplicity_eq_two_iff n hn z).mpr ⟨hB, hL⟩
    · rw [if_neg hL]
      exact (binomialSquare_operator_rootMultiplicity_eq_one_iff n hn z).mpr ⟨hB, hL⟩
  · rw [if_neg hB]
    exact rootMultiplicity_eq_zero hB

end GaloisForLFunctions.KodairaParshinAbc.Legendre
