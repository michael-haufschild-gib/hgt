import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# The scaling symmetry of a horizon observation

Reparametrising the source by `t ↦ c t` multiplies the `i`-th coefficient of every jet by `c^i`.
It carries a jet to a jet, its reciprocal to the reciprocal of the image, and the horizon to itself,
so it carries the fibre of an observation bijectively to the fibre of the rescaled observation.

The count of compatible source jets is therefore an invariant of the scaling orbit of the
observation, not of the observation itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-! ## Dilating a polynomial -/

/-- **The coefficients of a dilated polynomial.** -/
theorem coeff_comp_C_mul_X (P : K[X]) (c : K) (i : ℕ) :
    (P.comp (C c * X)).coeff i = P.coeff i * c ^ i := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, add_mul]
  | monomial k a =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_monomial]
    by_cases hik : i = k
    · rw [if_pos hik, if_pos hik.symm, hik]
      ring
    · rw [if_neg hik, if_neg (fun h => hik h.symm), mul_zero, zero_mul]

theorem comp_C_mul_X_comp (P : K[X]) {c : K} (hc : c ≠ 0) :
    (P.comp (C c * X)).comp (C c⁻¹ * X) = P := by
  refine Polynomial.ext fun i => ?_
  rw [coeff_comp_C_mul_X, coeff_comp_C_mul_X, mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hc, one_pow, mul_one]

theorem degree_comp_C_mul_X (P : K[X]) {c : K} (hc : c ≠ 0) :
    (P.comp (C c * X)).degree = P.degree := by
  refine le_antisymm ?_ ?_
  · refine Polynomial.degree_le_iff_coeff_zero _ _ |>.2 fun j hj => ?_
    rw [coeff_comp_C_mul_X, Polynomial.coeff_eq_zero_of_degree_lt hj, zero_mul]
  · conv_lhs => rw [← comp_C_mul_X_comp P hc]
    refine Polynomial.degree_le_iff_coeff_zero _ _ |>.2 fun j hj => ?_
    rw [coeff_comp_C_mul_X, Polynomial.coeff_eq_zero_of_degree_lt hj, zero_mul]

theorem X_pow_dvd_comp_C_mul_X_iff {P : K[X]} {c : K} (hc : c ≠ 0) (L : ℕ) :
    (X : K[X]) ^ L ∣ P.comp (C c * X) ↔ (X : K[X]) ^ L ∣ P := by
  rw [Polynomial.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h k hk
    have := h k hk
    rw [coeff_comp_C_mul_X] at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 (pow_ne_zero k hc)
  · intro h k hk
    rw [coeff_comp_C_mul_X, h k hk, zero_mul]

/-! ## The fibre of the rescaled observation -/

/-- **Dilation carries the fibre of an observation to the fibre of the rescaled one.** -/
noncomputable def criticalFibreScale {c : K} (hc : c ≠ 0) (m n : ℕ) (U V : K[X]) :
    criticalFibre K m n U V ≃
      criticalFibre K m n (U.comp (C c * X)) (V.comp (C c * X)) where
  toFun p := ⟨(p.1.1.comp (C c * X), p.1.2.comp (C c * X)), by
      rw [degree_comp_C_mul_X _ hc]; exact p.2.1, by
      rw [degree_comp_C_mul_X _ hc]; exact p.2.2.1, by
      have hid : (criticalLowProduct (U.comp (C c * X)) (V.comp (C c * X))
          (p.1.1.comp (C c * X)) (p.1.2.comp (C c * X)) - 1)
          = (criticalLowProduct U V p.1.1 p.1.2 - 1).comp (C c * X) := by
        simp only [criticalLowProduct, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.mul_comp, Polynomial.one_comp]
      rw [hid, X_pow_dvd_comp_C_mul_X_iff hc]
      exact p.2.2.2⟩
  invFun p := ⟨(p.1.1.comp (C c⁻¹ * X), p.1.2.comp (C c⁻¹ * X)), by
      rw [degree_comp_C_mul_X _ (inv_ne_zero hc)]; exact p.2.1, by
      rw [degree_comp_C_mul_X _ (inv_ne_zero hc)]; exact p.2.2.1, by
      have hid : (criticalLowProduct U V
          (p.1.1.comp (C c⁻¹ * X)) (p.1.2.comp (C c⁻¹ * X)) - 1)
          = (criticalLowProduct (U.comp (C c * X)) (V.comp (C c * X)) p.1.1 p.1.2 - 1).comp
            (C c⁻¹ * X) := by
        simp only [criticalLowProduct, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.mul_comp, Polynomial.one_comp, comp_C_mul_X_comp _ hc]
      rw [hid, X_pow_dvd_comp_C_mul_X_iff (inv_ne_zero hc)]
      exact p.2.2.2⟩
  left_inv p := by
    refine Subtype.ext ?_
    exact Prod.ext (comp_C_mul_X_comp _ hc) (comp_C_mul_X_comp _ hc)
  right_inv p := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_ <;>
      · refine Polynomial.ext fun i => ?_
        rw [coeff_comp_C_mul_X, coeff_comp_C_mul_X, mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hc, one_pow, mul_one]

/-- **The fibre count is an invariant of the scaling orbit of the observation.** -/
theorem nat_card_criticalFibre_comp_C_mul_X {c : K} (hc : c ≠ 0) (U V : K[X]) :
    Nat.card (criticalFibre K m n (U.comp (C c * X)) (V.comp (C c * X)))
      = Nat.card (criticalFibre K m n U V) :=
  (Nat.card_congr (criticalFibreScale hc m n U V)).symm


/-- Multiplying by a constant does not raise the degree. -/
theorem degree_C_mul_le (a : K) (P : K[X]) : (Polynomial.C a * P).degree ≤ P.degree := by
  calc (Polynomial.C a * P).degree ≤ (Polynomial.C a : K[X]).degree + P.degree :=
        Polynomial.degree_mul_le _ _
    _ ≤ 0 + P.degree := by
        gcongr
        exact Polynomial.degree_C_le
    _ = P.degree := zero_add _

/-! ## The unit symmetry -/

/-- **Scaling the jet and its reciprocal by inverse constants is a symmetry of the fibre.**  The
compatibility equation is literally unchanged: each term of the low product carries one factor of the
constant and one of its inverse. -/
theorem criticalLowProduct_unit_scale {l : K} (hl : l ≠ 0) (U V A B : K[X]) :
    criticalLowProduct (C l * U) (C l⁻¹ * V) (C l * A) (C l⁻¹ * B)
      = criticalLowProduct U V A B := by
  have hll : (C l : K[X]) * C l⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hl, map_one]
  simp only [criticalLowProduct]
  linear_combination (A * B + A * V + U * B) * hll

/-- **The unit symmetry of the fibre.**  It rescales the observed packets by inverse constants and
leaves the target `1 + U V` fixed. -/
noncomputable def criticalFibreUnitScale {l : K} (hl : l ≠ 0) (m n : ℕ) (U V : K[X]) :
    criticalFibre K m n U V ≃ criticalFibre K m n (C l * U) (C l⁻¹ * V) where
  toFun p := ⟨(C l * p.1.1, C l⁻¹ * p.1.2), by
      exact lt_of_le_of_lt (degree_C_mul_le _ _) p.2.1, by
      exact lt_of_le_of_lt (degree_C_mul_le _ _) p.2.2.1, by
      rw [criticalLowProduct_unit_scale hl]
      exact p.2.2.2⟩
  invFun p := ⟨(C l⁻¹ * p.1.1, C l * p.1.2), by
      exact lt_of_le_of_lt (degree_C_mul_le _ _) p.2.1, by
      exact lt_of_le_of_lt (degree_C_mul_le _ _) p.2.2.1, by
      have hid : criticalLowProduct U V (C l⁻¹ * p.1.1) (C l * p.1.2)
          = criticalLowProduct (C l * U) (C l⁻¹ * V) p.1.1 p.1.2 := by
        have hll : (C l : K[X]) * C l⁻¹ = 1 := by
          rw [← Polynomial.C_mul, mul_inv_cancel₀ hl, map_one]
        simp only [criticalLowProduct]
        linear_combination (p.1.1 * p.1.2) * hll
      rw [hid]
      exact p.2.2.2⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show Polynomial.C l⁻¹ * (Polynomial.C l * p.1.1) = p.1.1
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hl, map_one, one_mul]
    · show Polynomial.C l * (Polynomial.C l⁻¹ * p.1.2) = p.1.2
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hl, map_one, one_mul]
  right_inv p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show Polynomial.C l * (Polynomial.C l⁻¹ * p.1.1) = p.1.1
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hl, map_one, one_mul]
    · show Polynomial.C l⁻¹ * (Polynomial.C l * p.1.2) = p.1.2
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hl, map_one, one_mul]

/-- **The fibre count is unchanged by the unit symmetry.** -/
theorem nat_card_criticalFibre_unit_scale {l : K} (hl : l ≠ 0) (U V : K[X]) :
    Nat.card (criticalFibre K m n (C l * U) (C l⁻¹ * V))
      = Nat.card (criticalFibre K m n U V) :=
  (Nat.card_congr (criticalFibreUnitScale hl m n U V)).symm

end GaloisForLFunctions.HTGeometry
