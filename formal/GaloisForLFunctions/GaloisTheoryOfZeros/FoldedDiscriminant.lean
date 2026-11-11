import GaloisForLFunctions.HTGeometry.MonicDiscriminantProducts
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Discriminants under the quotient by negation

For a monic equation `Q` of degree `n`, the equation `Q(X²)` has discriminant
`4^n (-1)^n Q(0) disc(Q)²`. The square erases the discriminant sign of the
quotient equation. The identity includes repeated roots and degree zero.
-/

noncomputable section

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.GaloisTheoryOfZeros

private def rootEquation (s : List ℂ) : ℂ[X] :=
  (s.map fun a => X - C a).prod

private theorem rootEquation_nil : rootEquation [] = 1 := rfl

private theorem rootEquation_cons (a : ℂ) (s : List ℂ) :
    rootEquation (a :: s) = (X - C a) * rootEquation s := rfl

private theorem rootEquation_monic (s : List ℂ) : (rootEquation s).Monic := by
  induction s with
  | nil => exact monic_one
  | cons a s ih => exact (monic_X_sub_C a).mul ih

private theorem squareEquation_monic (a : ℂ) : (X ^ 2 - C a : ℂ[X]).Monic :=
  monic_X_pow_sub_C a (by decide)

private theorem squareEquation_natDegree (a : ℂ) :
    (X ^ 2 - C a : ℂ[X]).natDegree = 2 := by
  exact natDegree_X_pow_sub_C

private theorem squareEquation_discr (a : ℂ) :
    (X ^ 2 - C a : ℂ[X]).discr = 4 * a := by
  rw [discr_of_degree_eq_two (by
    rw [degree_eq_natDegree (squareEquation_monic a).ne_zero, squareEquation_natDegree])]
  simp

private theorem squareEquation_resultant (a b : ℂ) :
    resultant (X ^ 2 - C a : ℂ[X]) (X ^ 2 - C b) = (a - b) ^ 2 := by
  have h : (X ^ 2 - C b : ℂ[X]) = C (a - b) + (X ^ 2 - C a) * 1 := by
    rw [map_sub]
    ring
  conv_lhs => arg 2; rw [h]
  rw [monic_resultant_add_mul (squareEquation_monic a), resultant_C_right,
    coeff_natDegree, (squareEquation_monic a).leadingCoeff,
    squareEquation_natDegree, one_pow, one_mul]

private theorem rootEquation_comp_monic (s : List ℂ) :
    ((rootEquation s).comp (X ^ 2)).Monic :=
  (rootEquation_monic s).comp (monic_X_pow 2) (by simp)

private theorem squareEquation_resultant_comp (a : ℂ) (s : List ℂ) :
    resultant (X ^ 2 - C a : ℂ[X]) ((rootEquation s).comp (X ^ 2)) =
      ((rootEquation s).eval a) ^ 2 := by
  induction s with
  | nil => simp only [rootEquation_nil, one_comp, resultant_one_right,
      natDegree_one, pow_zero, eval_one, one_pow]
  | cons b s ih =>
    rw [rootEquation_cons, mul_comp, sub_comp, X_comp, C_comp,
      monic_resultant_mul_right (squareEquation_monic a), squareEquation_resultant, ih,
      eval_mul, eval_sub, eval_X, eval_C, mul_pow]

private theorem discr_rootEquation_comp (s : List ℂ) :
    ((rootEquation s).comp (X ^ 2)).discr =
      4 ^ s.length * s.prod * (rootEquation s).discr ^ 2 := by
  induction s with
  | nil =>
    simp only [rootEquation_nil, one_comp, List.length_nil, pow_zero, List.prod_nil,
      one_mul]
    rw [show (1 : ℂ[X]).discr = 1 from Polynomial.discr_C 1, one_pow]
  | cons a s ih =>
    rw [rootEquation_cons, mul_comp, sub_comp, X_comp, C_comp,
      discr_mul_of_monic (squareEquation_monic a) (rootEquation_comp_monic s),
      squareEquation_discr, ih, squareEquation_resultant_comp,
      discr_mul_of_monic (monic_X_sub_C a) (rootEquation_monic s),
      resultant_X_sub_C_left _ _ _ le_rfl,
      discr_of_degree_eq_one (degree_X_sub_C a),
      List.length_cons, List.prod_cons, pow_succ]
    ring

private theorem eval_zero_rootEquation (s : List ℂ) :
    (rootEquation s).eval 0 = (-1) ^ s.length * s.prod := by
  induction s with
  | nil => simp only [rootEquation_nil, eval_one, List.length_nil, pow_zero,
      List.prod_nil, mul_one]
  | cons a s ih =>
    rw [rootEquation_cons, eval_mul, eval_sub, eval_X, eval_C, ih,
      List.length_cons, List.prod_cons, pow_succ]
    ring

/-- The discriminant of the doubled equation loses the quotient discriminant sign. -/
theorem discr_comp_square_complex {Q : ℂ[X]} (hQ : Q.Monic) :
    (Q.comp (X ^ 2)).discr =
      4 ^ Q.natDegree * ((-1) ^ Q.natDegree * Q.coeff 0) * Q.discr ^ 2 := by
  let s := Q.roots.toList
  have heq : rootEquation s = Q := by
    have h := (IsAlgClosed.splits Q).eq_prod_roots_of_monic hQ
    simpa only [rootEquation, s, Multiset.prod_coe, Multiset.map_coe,
      Multiset.coe_toList] using h.symm
  have hlen : s.length = Q.natDegree := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  have hprod : s.prod = (-1) ^ Q.natDegree * Q.coeff 0 := by
    have h := eval_zero_rootEquation s
    rw [heq, hlen, ← coeff_zero_eq_eval_zero] at h
    rw [h, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  simpa only [heq, hlen, hprod] using discr_rootEquation_comp s

/-- The same identity in the real coefficient field, without separability assumptions. -/
theorem discr_comp_square_real {Q : ℝ[X]} (hQ : Q.Monic) :
    (Q.comp (X ^ 2)).discr =
      4 ^ Q.natDegree * ((-1) ^ Q.natDegree * Q.coeff 0) * Q.discr ^ 2 := by
  apply Complex.ofRealHom.injective
  have h := discr_comp_square_complex (hQ.map Complex.ofRealHom)
  rw [map_discr_of_monic Complex.ofRealHom (hQ.comp (monic_X_pow 2) (by simp))]
  simpa only [Polynomial.map_comp, Polynomial.map_pow, map_X,
    hQ.natDegree_map, coeff_map, ← map_discr_of_monic Complex.ofRealHom hQ,
    map_mul, map_pow, map_neg, map_one, map_ofNat] using h

/-- The odd equation has the same lost sign, with the extra squared value at zero. -/
theorem discr_X_mul_comp_square_real {Q : ℝ[X]} (hQ : Q.Monic) :
    (X * Q.comp (X ^ 2)).discr =
      4 ^ Q.natDegree * ((-1) ^ Q.natDegree * Q.coeff 0 ^ 3) * Q.discr ^ 2 := by
  have hx : (X : ℝ[X]).discr = 1 := discr_of_degree_eq_one degree_X
  have hr : resultant (X : ℝ[X]) (Q.comp (X ^ 2)) = Q.coeff 0 := by
    have h := resultant_X_sub_C_left (Q.comp (X ^ 2))
      (Q.comp (X ^ 2)).natDegree 0 le_rfl
    simpa only [map_zero, sub_zero, eval_comp, eval_pow, eval_X, zero_pow (by decide),
      ← coeff_zero_eq_eval_zero] using h
  rw [discr_mul_of_monic monic_X (hQ.comp (monic_X_pow 2) (by simp)), hx, one_mul, hr,
    discr_comp_square_real hQ]
  ring

/-- The doubled equation is separable exactly when its quotient is separable
and the branch point zero is absent. -/
theorem separable_comp_square_real_iff {Q : ℝ[X]} (hQ : Q.Monic) :
    (Q.comp (X ^ 2)).Separable ↔ Q.Separable ∧ Q.coeff 0 ≠ 0 := by
  have h := monic_discr_eq_zero_iff_not_separable (hQ.comp (monic_X_pow 2) (by simp))
  rw [discr_comp_square_real hQ] at h
  have hfour : (4 : ℝ) ^ Q.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsign : (-1 : ℝ) ^ Q.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [mul_eq_zero, hfour, hsign, false_or, pow_eq_zero_iff (by decide : 2 ≠ 0),
    monic_discr_eq_zero_iff_not_separable hQ] at h
  tauto

/-- Away from collisions the doubled discriminant sign reads only the value
at the branch point; the quotient discriminant contributes a square. -/
theorem discr_comp_square_nonneg_iff {Q : ℝ[X]} (hQ : Q.Monic) :
    0 ≤ (Q.comp (X ^ 2)).discr ↔
      0 ≤ (-1 : ℝ) ^ Q.natDegree * Q.coeff 0 ∨ ¬ Q.Separable := by
  rw [discr_comp_square_real hQ]
  by_cases hd : Q.discr = 0
  · simp only [hd, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl, true_iff]
    exact Or.inr ((monic_discr_eq_zero_iff_not_separable hQ).mp hd)
  · have hs : Q.Separable := by
      simpa only [not_not] using mt (monic_discr_eq_zero_iff_not_separable hQ).mpr hd
    have hp : 0 < (4 : ℝ) ^ Q.natDegree := pow_pos (by norm_num) _
    have hsq : 0 < Q.discr ^ 2 := sq_pos_of_ne_zero hd
    rw [mul_nonneg_iff_of_pos_right hsq, mul_nonneg_iff_of_pos_left hp]
    simp only [hs, not_true_eq_false, or_false]

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.discr_comp_square_complex
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.discr_comp_square_real
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.separable_comp_square_real_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.discr_comp_square_nonneg_iff
