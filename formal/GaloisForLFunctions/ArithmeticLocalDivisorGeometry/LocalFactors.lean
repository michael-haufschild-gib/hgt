import GaloisForLFunctions.HTGeometry.PolynomialHeatProduct

/-!
# Local divisor factors and the exact one-factor repair region

The variable is the squared horizontal displacement. A conjugate spectral pair at offsets
`u ± iδ` contributes `Y² + 2(u² - δ²)Y + (u² + δ²)²`. This is nonnegative on the
positive axis, but its coefficient cone is smaller. Adjoining one real divisor factor enlarges
the exact cone from `δ² ≤ u²` to `δ² ≤ 3u²`. Multiplicities are retained as powers of factors.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section

/-- The monic factor of a conjugate pair, in squared horizontal displacement. -/
def pairFactor (u δ : ℝ) : ℝ[X] :=
  X ^ 2 + C (2 * (u ^ 2 - δ ^ 2)) * X + C ((u ^ 2 + δ ^ 2) ^ 2)

/-- The norm-square identity separates real-axis positivity from coefficient positivity. -/
theorem pairFactor_eval (u δ x : ℝ) :
    (pairFactor u δ).eval (x ^ 2) = (x ^ 2 + u ^ 2 - δ ^ 2) ^ 2 + 4 * u ^ 2 * δ ^ 2 := by
  simp only [pairFactor, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  ring

theorem pairFactor_eval_nonneg (u δ x : ℝ) : 0 ≤ (pairFactor u δ).eval (x ^ 2) := by
  rw [pairFactor_eval]
  positivity

/-- A single pair belongs to the coefficient cone exactly outside the forty-five degree cone. -/
theorem coeffNonneg_pairFactor_iff (u δ : ℝ) :
    CoeffNonneg (pairFactor u δ) ↔ δ ^ 2 ≤ u ^ 2 := by
  constructor
  · intro h
    have h1 := h 1
    simp only [pairFactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at h1
    norm_num at h1
    linarith
  · intro h n
    have ha : 0 ≤ 2 * (u ^ 2 - δ ^ 2) := by linarith
    simp only [pairFactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    split_ifs <;> positivity

/-- The complete transition across one additional real divisor point. -/
theorem pairFactor_mul_linear (u δ c : ℝ) :
    pairFactor u δ * (X + C c) =
      X ^ 3 + C (c + 2 * (u ^ 2 - δ ^ 2)) * X ^ 2 +
        C ((u ^ 2 + δ ^ 2) ^ 2 + 2 * c * (u ^ 2 - δ ^ 2)) * X +
        C (c * (u ^ 2 + δ ^ 2) ^ 2) := by
  simp only [pairFactor, map_add, map_mul, map_sub, map_pow, map_ofNat]
  ring

/-- Both mixed coefficients must be paid when adjoining a real factor. -/
theorem coeffNonneg_pairFactor_mul_linear_iff (u δ c : ℝ) (hc : 0 ≤ c) :
    CoeffNonneg (pairFactor u δ * (X + C c)) ↔
      2 * (δ ^ 2 - u ^ 2) ≤ c ∧
        2 * c * (δ ^ 2 - u ^ 2) ≤ (u ^ 2 + δ ^ 2) ^ 2 := by
  rw [pairFactor_mul_linear]
  constructor
  · intro h
    have h1 := h 1
    have h2 := h 2
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at h1 h2
    norm_num at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ n
    have ha : 0 ≤ c + 2 * (u ^ 2 - δ ^ 2) := by linarith
    have hb : 0 ≤ (u ^ 2 + δ ^ 2) ^ 2 + 2 * c * (u ^ 2 - δ ^ 2) := by linarith
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    split_ifs <;> positivity

/-- A real divisor point can repair precisely the larger cone `δ² ≤ 3u²`. -/
theorem exists_linear_repair_iff (u δ : ℝ) :
    (∃ c : ℝ, 0 ≤ c ∧ CoeffNonneg (pairFactor u δ * (X + C c))) ↔
      δ ^ 2 ≤ 3 * u ^ 2 := by
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨h1, h2⟩ := (coeffNonneg_pairFactor_mul_linear_iff u δ c hc).mp h
    by_contra hbad
    have hd : 3 * u ^ 2 < δ ^ 2 := lt_of_not_ge hbad
    have hb : 0 ≤ 2 * (δ ^ 2 - u ^ 2) := by nlinarith only [hd, sq_nonneg u]
    have hsq := mul_le_mul_of_nonneg_left h1 hb
    have hprod : 0 < (δ ^ 2 - 3 * u ^ 2) * (3 * δ ^ 2 - u ^ 2) :=
      mul_pos (by linarith) (by nlinarith only [hd, sq_nonneg u])
    nlinarith only [h2, hsq, hprod]
  · intro h
    refine ⟨u ^ 2 + δ ^ 2, by positivity, ?_⟩
    rw [coeffNonneg_pairFactor_mul_linear_iff u δ _ (by positivity)]
    constructor
    · linarith
    · have hprod := mul_nonneg (show 0 ≤ 3 * u ^ 2 - δ ^ 2 by linarith)
        (show 0 ≤ u ^ 2 + δ ^ 2 by positivity)
      nlinarith only [hprod]

/-- At the repair boundary the two mixed coefficients vanish simultaneously. -/
theorem pairFactor_boundary_repair (u δ : ℝ) (h : δ ^ 2 = 3 * u ^ 2) :
    pairFactor u δ * (X + C (4 * u ^ 2)) = X ^ 3 + C (64 * u ^ 6) := by
  rw [pairFactor_mul_linear, h]
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat]
  ring

end

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
