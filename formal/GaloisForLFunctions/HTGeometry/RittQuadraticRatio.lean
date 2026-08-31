import GaloisForLFunctions.HTGeometry.RittRatioConnection

/-!
# The quadratic branch carries a second relation

The one configuration in which a trivial denominator fails to produce the affine connection is a
numerator of degree exactly two with a nonzero linear inhomogeneity.  There the two top coefficient
equations are

`Φ(P₂)·a² = c·P₂`,   `Φ(P₁)·a + 2·Φ(P₂)·a·b = c·P₁ + α`,

and dividing the second by the first still eliminates the eigenvalue, leaving

`Φ(P₁/P₂) = a·(P₁/P₂) + a·α/(c·P₂) − 2·b`.

So the quadratic branch is not information-free: alongside the homogeneous relation for its leading
coefficient it carries an affine relation for the ratio of the two top coefficients, whose
inhomogeneity is the shift's constant term corrected by an explicit multiple of `1/P₂`.  Once the
classification pins `P₂` as a monomial that correction is explicit too.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- **The quadratic branch's ratio relation.** -/
theorem ratio_quadratic_of_polynomial_cross (Φ : K →+* K) {a b c α β : K} (ha : a ≠ 0)
    (hc : c ≠ 0) {P : K[X]} (hD : P.natDegree = 2)
    (hnum : twistComp Φ (C a * X + C b) P = C c * P + (C α * X + C β)) :
    Φ (P.coeff 1 / P.coeff 2)
      = a * (P.coeff 1 / P.coeff 2) + a * α / (c * P.coeff 2) - 2 * b := by
  classical
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hD
    omega
  have hlc : P.coeff 2 ≠ 0 := by
    have : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    rwa [hD] at this
  have hmapdeg : ∀ n : ℕ, 2 ≤ n → (P.map Φ).natDegree ≤ n := by
    intro n hn
    have := natDegree_map_le (f := Φ) (p := P)
    omega
  have hRHS : ∀ k : ℕ, (C c * P + (C α * X + C β)).coeff k
      = c * P.coeff k + (α * (if 1 = k then 1 else 0) + (if k = 0 then β else 0)) := by
    intro k
    rw [coeff_add, coeff_C_mul, coeff_add, coeff_C_mul, coeff_X, coeff_C, mul_ite, mul_one,
      mul_zero]
  have hlead : Φ (P.coeff 2) * a ^ 2 = c * P.coeff 2 := by
    have h := congrArg (fun R : K[X] => R.coeff 2) hnum
    simp only [twistComp] at h
    rw [coeff_comp_linear_of_natDegree_le ha (hmapdeg 2 le_rfl), coeff_map, hRHS 2,
      if_neg (by omega : ¬ (1 : ℕ) = 2), if_neg (by omega : ¬ (2 : ℕ) = 0)] at h
    linear_combination h
  have hsub : Φ (P.coeff 1) * a + Φ (P.coeff 2) * 2 * a * b = c * P.coeff 1 + α := by
    have h := congrArg (fun R : K[X] => R.coeff 1) hnum
    simp only [twistComp] at h
    rw [coeff_comp_linear_sub_one ha (hmapdeg 2 le_rfl), coeff_map, coeff_map, hRHS 1,
      if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = 0)] at h
    push_cast at h
    linear_combination h
  have hΦlc : Φ (P.coeff 2) ≠ 0 := fun h => hlc ((RingHom.injective Φ) (by rw [h, map_zero]))
  have key : Φ (P.coeff 1) * (c * P.coeff 2)
      = (a * (c * P.coeff 1 + α) - 2 * b * c * P.coeff 2) * Φ (P.coeff 2) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 ha) ?_
    linear_combination (a * c * P.coeff 2) * hsub - (a * (c * P.coeff 1 + α)) * hlead
  rw [map_div₀]
  field_simp
  linear_combination (a ^ 0) * key

/-- **The quadratic branch's constant-term relation.**  The third coefficient equation, read as a
relation for the ratio of the constant coefficient to the leading one. -/
theorem ratio_quadratic_constant_of_polynomial_cross (Φ : K →+* K) {a b c α β : K} (ha : a ≠ 0)
    (hc : c ≠ 0) {P : K[X]} (hD : P.natDegree = 2)
    (hnum : twistComp Φ (C a * X + C b) P = C c * P + (C α * X + C β)) :
    Φ (P.coeff 0 / P.coeff 2)
      = a ^ 2 * (P.coeff 0 / P.coeff 2) - a * b * (P.coeff 1 / P.coeff 2) + b ^ 2
        + a * (a * β - α * b) / (c * P.coeff 2) := by
  classical
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hD
    omega
  have hlc : P.coeff 2 ≠ 0 := by
    have h : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    rwa [hD] at h
  have hmapdeg : ∀ n : ℕ, 2 ≤ n → (P.map Φ).natDegree ≤ n := by
    intro n hn
    have := natDegree_map_le (f := Φ) (p := P)
    omega
  have hRHS : ∀ k : ℕ, (C c * P + (C α * X + C β)).coeff k
      = c * P.coeff k + (α * (if 1 = k then 1 else 0) + (if k = 0 then β else 0)) := by
    intro k
    rw [coeff_add, coeff_C_mul, coeff_add, coeff_C_mul, coeff_X, coeff_C, mul_ite, mul_one,
      mul_zero]
  have hE2 : Φ (P.coeff 2) * a ^ 2 = c * P.coeff 2 := by
    have h := congrArg (fun R : K[X] => R.coeff 2) hnum
    simp only [twistComp] at h
    rw [coeff_comp_linear_of_natDegree_le ha (hmapdeg 2 le_rfl), coeff_map, hRHS 2,
      if_neg (by omega : ¬ (1 : ℕ) = 2), if_neg (by omega : ¬ (2 : ℕ) = 0)] at h
    linear_combination h
  have hE1 : Φ (P.coeff 1) * a + Φ (P.coeff 2) * 2 * a * b = c * P.coeff 1 + α := by
    have h := congrArg (fun R : K[X] => R.coeff 1) hnum
    simp only [twistComp] at h
    rw [coeff_comp_linear_sub_one ha (hmapdeg 2 le_rfl), coeff_map, coeff_map, hRHS 1,
      if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = 0)] at h
    push_cast at h
    linear_combination h
  have hE0 : Φ (P.coeff 2) * b ^ 2 + Φ (P.coeff 1) * b + Φ (P.coeff 0)
      = c * P.coeff 0 + β := by
    have h := congrArg (fun R : K[X] => R.coeff 0) hnum
    simp only [twistComp] at h
    rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, eval_comp] at h
    simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add] at h
    rw [Polynomial.eval_eq_sum_range' (n := 3) (by have := hmapdeg 2 le_rfl; omega) b] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_map, pow_zero,
      pow_one, mul_one] at h
    rw [← Polynomial.coeff_zero_eq_eval_zero] at h
    linear_combination h
  have hΦlc : Φ (P.coeff 2) ≠ 0 := fun h => hlc ((RingHom.injective Φ) (by rw [h, map_zero]))
  have key : Φ (P.coeff 0) * (c * P.coeff 2)
      = (a ^ 2 * (c * P.coeff 0 + β) + c * P.coeff 2 * b ^ 2
          - a * (c * P.coeff 1 + α) * b) * Φ (P.coeff 2) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 ha) ?_
    linear_combination (a ^ 2 * c * P.coeff 2) * hE0 - (a * c * P.coeff 2 * b) * hE1
      + (a * b * (c * P.coeff 1 + α) - a ^ 2 * (c * P.coeff 0 + β)) * hE2
  rw [map_div₀]
  field_simp
  linear_combination (a ^ 0) * key

/-- **The linear branch's constant-term relation.**  When the linear part of the inhomogeneity
vanishes, a numerator of degree one still carries a second relation: the ratio of its constant
coefficient to its leading one solves an affine equation whose inhomogeneity is the shift's constant
term corrected by an explicit multiple of `1/P₁`. -/
theorem ratio_linear_of_polynomial_cross (Φ : K →+* K) {a b c β : K} (ha : a ≠ 0)
    (hc : c ≠ 0) {P : K[X]} (hD : P.natDegree = 1)
    (hnum : twistComp Φ (C a * X + C b) P = C c * P + (C (0 : K) * X + C β)) :
    Φ (P.coeff 0 / P.coeff 1)
      = a * (P.coeff 0 / P.coeff 1) + a * β / (c * P.coeff 1) - b := by
  classical
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hD
    omega
  have hlc : P.coeff 1 ≠ 0 := by
    have h : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    rwa [hD] at h
  have hmapdeg : ∀ n : ℕ, 1 ≤ n → (P.map Φ).natDegree ≤ n := by
    intro n hn
    have := natDegree_map_le (f := Φ) (p := P)
    omega
  have hRHS : ∀ k : ℕ, (C c * P + (C (0 : K) * X + C β)).coeff k
      = c * P.coeff k + (if k = 0 then β else 0) := by
    intro k
    rw [coeff_add, coeff_C_mul, coeff_add, coeff_C_mul, coeff_X, coeff_C, mul_ite, mul_one,
      mul_zero, ite_self, zero_add]
  have hF1 : Φ (P.coeff 1) * a = c * P.coeff 1 := by
    have h := congrArg (fun R : K[X] => R.coeff 1) hnum
    simp only [twistComp] at h
    rw [coeff_comp_linear_of_natDegree_le ha (hmapdeg 1 le_rfl), coeff_map, hRHS 1,
      if_neg (by omega : ¬ (1 : ℕ) = 0)] at h
    linear_combination h
  have hF0 : Φ (P.coeff 1) * b + Φ (P.coeff 0) = c * P.coeff 0 + β := by
    have h := congrArg (fun R : K[X] => R.coeff 0) hnum
    simp only [twistComp] at h
    rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, eval_comp] at h
    simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add] at h
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by have := hmapdeg 1 le_rfl; omega) b] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_map, pow_zero,
      pow_one, mul_one] at h
    rw [← Polynomial.coeff_zero_eq_eval_zero] at h
    linear_combination h
  have hΦlc : Φ (P.coeff 1) ≠ 0 := fun h => hlc ((RingHom.injective Φ) (by rw [h, map_zero]))
  have key : Φ (P.coeff 0) * (c * P.coeff 1)
      = (a * (c * P.coeff 0 + β) - c * P.coeff 1 * b) * Φ (P.coeff 1) := by
    refine mul_left_cancel₀ ha ?_
    linear_combination (a * c * P.coeff 1) * hF0 - (a * (c * P.coeff 0 + β)) * hF1
  rw [map_div₀]
  field_simp
  linear_combination (a ^ 0) * key

end GaloisForLFunctions.HTGeometry
