import GaloisForLFunctions.HTGeometry.Polynomial.DicksonCoefficients
import GaloisForLFunctions.HTGeometry.Polynomial.DicksonCriticalFibers
import GaloisForLFunctions.HTGeometry.ShiftTwistDescent

/-!
# Affine symmetries of normalized Chebyshev polynomials

The vanishing subleading coefficient rules out translations. The coefficient
two degrees below the leading term then forces the slope to be `1` or `-1`.
For arbitrary slopes, the only additional solutions are constant maps to roots.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The invertible affine symmetries in every degree at least two are identity and reflection. -/
theorem dickson_affine_symmetry_iff (n : ℕ) (a : Kˣ) (b : K) :
    (dickson 1 (1 : K) (n + 2)).comp (C (a : K) * X + C b) =
        C ((a : K) ^ (n + 2)) * dickson 1 (1 : K) (n + 2) ↔
      b = 0 ∧ ((a : K) = 1 ∨ (a : K) = -1) := by
  constructor
  · intro h
    have ha : (a : K) ≠ 0 := Units.ne_zero a
    have hn : ((n + 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd : (dickson 1 (1 : K) (n + 2)).natDegree = n + 2 :=
      natDegree_eq_of_le_of_coeff_ne_zero (dickson_natDegree_le _)
        (by rw [show n + 2 = (n + 1) + 1 by omega, dickson_coeff_top]; exact one_ne_zero)
    have hdscale : ((dickson 1 (1 : K) (n + 2)).comp (C (a : K) * X)).natDegree = n + 2 := by
      rw [natDegree_comp, natDegree_C_mul ha, natDegree_X, mul_one, hd]
    have hshift := _root_.HTGeometry.shiftTwist_coeff_sub_one
      (sigma := RingEquiv.refl K) (c := b / (a : K)) hdscale (by omega : 0 < n + 2)
    have hinner : (C (a : K) * X).comp (X + C (b / (a : K))) =
        C (a : K) * X + C b := by
      simp only [mul_comp, C_comp, X_comp, mul_add, ← C_mul]
      congr 2
      field_simp
    rw [_root_.HTGeometry.shiftTwist_refl, comp_assoc, hinner, h] at hshift
    simp only [show n + 2 - 1 = n + 1 by omega, RingEquiv.refl_apply,
      coeff_C_mul, comp_C_mul_X_coeff, dickson_coeff_subleading,
      show n + 2 = (n + 1) + 1 by omega, dickson_coeff_top, mul_zero, zero_mul,
      one_mul, zero_add] at hshift
    have hbdiv : b / (a : K) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hshift.symm).resolve_right
        (pow_ne_zero _ ha))).resolve_left hn
    have hb : b = 0 := (div_eq_zero_iff.mp hbdiv).resolve_right ha
    refine ⟨hb, ?_⟩
    have hc := congrArg (fun P : K[X] => P.coeff n) h
    simp only [hb, C_0, add_zero, comp_C_mul_X_coeff, coeff_C_mul,
      dickson_coeff_subleading_two] at hc
    have heq : (((n + 2 : ℕ) : K) * (a : K) ^ n) * ((a : K) ^ 2 - 1) = 0 := by
      rw [pow_add] at hc
      linear_combination hc
    have hsq := (mul_eq_zero.mp heq).resolve_left (mul_ne_zero hn (pow_ne_zero n ha))
    have hfac : ((a : K) - 1) * ((a : K) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with hp | hm
    · exact Or.inl (sub_eq_zero.mp hp)
    · exact Or.inr (eq_neg_of_add_eq_zero_left hm)
  · rintro ⟨rfl, ha | ha⟩
    · simp only [ha, C_1, one_mul, C_0, add_zero, comp_X, one_pow]
    · simp only [ha, C_neg, C_1, neg_mul, one_mul, C_0, add_zero]
      exact dickson_comp_neg_X (n + 2)

/-- Full affine classification, with the constant-map degeneracy stated explicitly. -/
theorem dickson_affine_classification (n : ℕ) (a b : K) :
    (dickson 1 (1 : K) (n + 2)).comp (C a * X + C b) =
        C (a ^ (n + 2)) * dickson 1 (1 : K) (n + 2) ↔
      (a = 0 ∧ (dickson 1 (1 : K) (n + 2)).eval b = 0) ∨
        (b = 0 ∧ (a = 1 ∨ a = -1)) := by
  by_cases ha : a = 0
  · simp only [ha, C_0, zero_mul, zero_add, zero_pow (by omega : n + 2 ≠ 0),
      comp_C, C_eq_zero]
    simp
  · simpa only [ha, false_and, false_or, Units.val_mk0] using
      dickson_affine_symmetry_iff n (Units.mk0 a ha) b

/-- Preserving the zero set already forces an affine map to be identity or reflection. -/
theorem dickson_affine_roots_iff [IsAlgClosed K] (n : ℕ) (a : Kˣ) (b : K) :
    Set.MapsTo (fun x : K => (a : K) * x + b)
      {x | (dickson 1 (1 : K) (n + 2)).eval x = 0}
      {x | (dickson 1 (1 : K) (n + 2)).eval x = 0} ↔
      b = 0 ∧ ((a : K) = 1 ∨ (a : K) = -1) := by
  have ha : (a : K) ≠ 0 := Units.ne_zero a
  constructor
  · intro h
    have hsep : (dickson 1 (1 : K) (n + 2)).Separable := dickson_separable_succ (n + 1)
    have hd : (dickson 1 (1 : K) (n + 2)).natDegree = n + 2 :=
      natDegree_eq_of_le_of_coeff_ne_zero (dickson_natDegree_le _)
        (by rw [show n + 2 = (n + 1) + 1 by omega, dickson_coeff_top]; exact one_ne_zero)
    have hm : (dickson 1 (1 : K) (n + 2)).Monic := by
      change (dickson 1 (1 : K) (n + 2)).leadingCoeff = 1
      rw [← coeff_natDegree, hd]
      exact dickson_coeff_top (n + 1)
    have hdiv : dickson 1 (1 : K) (n + 2) ∣
        (dickson 1 (1 : K) (n + 2)).comp (C (a : K) * X + C b) := by
      apply (show IsCoprime _ _ from hsep).dvd_of_dvd_mul_left
      apply (Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul hsep.ne_zero).mp
      intro x hx
      simpa only [IsRoot, eval_comp, eval_add, eval_mul, eval_C, eval_X,
        Set.mem_setOf_eq] using h hx
    have hdegree :
        ((dickson 1 (1 : K) (n + 2)).comp (C (a : K) * X + C b)).natDegree ≤
          (dickson 1 (1 : K) (n + 2)).natDegree := by
      rw [natDegree_comp, natDegree_linear ha, mul_one]
    have hpoly := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hm hdiv hdegree
    have hlc :
        ((dickson 1 (1 : K) (n + 2)).comp (C (a : K) * X + C b)).leadingCoeff =
          (a : K) ^ (n + 2) := by
      rw [leadingCoeff_comp (by rw [natDegree_linear ha]; exact one_ne_zero),
        hm.leadingCoeff, leadingCoeff_linear ha, hd, one_mul]
    rw [hlc] at hpoly
    exact (dickson_affine_symmetry_iff n a b).mp (hpoly.trans (mul_comm _ _))
  · intro h x hx
    have hp := congrArg (Polynomial.eval x) ((dickson_affine_symmetry_iff n a b).mpr h)
    change (dickson 1 (1 : K) (n + 2)).eval x = 0 at hx
    simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X, hx, mul_zero,
      Set.mem_setOf_eq] using hp

end GaloisForLFunctions.HTGeometry
