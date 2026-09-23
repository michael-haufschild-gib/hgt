import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-!
# Ultrametric resolvent susceptibility

For integers `p ≥ 2` and `m ≥ 2`, this module constructs the formal Taylor series whose
coefficients are forced by the one-sided ultrametric resolvent constraint

`Q(X) = B(X) + p^(1-m) Q(X / p)`.

The rational boundary term `B` contains the two lowest shells.  We prove coefficientwise that the
constraint has one and only one formal solution.  The analytic identification with a normally
convergent resolvent trace and the external q-difference hypertranscendence theorem are deliberately
not claimed here.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The constant scale multiplier `p^(1-m)`, written without integer exponents. -/
def ultrametricResolventScale (p m : ℕ) : ℚ :=
  (p : ℚ) / (p : ℚ) ^ m

/-- The `k`-th Taylor coefficient of
`(p-2)/(1+X)^m + 1/(p+X)^m`. -/
def ultrametricResolventBoundaryCoefficient (p m k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (Nat.choose (m + k - 1) k : ℚ) *
    ((p : ℚ) - 2 + 1 / (p : ℚ) ^ (m + k))

/-- The coefficient multiplier contributed by `p^(1-m) Q(X/p)`. -/
def ultrametricResolventCoefficientScale (p m k : ℕ) : ℚ :=
  (p : ℚ) / (p : ℚ) ^ (m + k)

/-- The Taylor coefficient uniquely forced by the affine scale constraint. -/
def ultrametricResolventCoefficient (p m k : ℕ) : ℚ :=
  ultrametricResolventBoundaryCoefficient p m k /
    (1 - ultrametricResolventCoefficientScale p m k)

/-- The two-shell rational boundary defect, represented by its Taylor series. -/
def ultrametricResolventBoundary (p m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (ultrametricResolventBoundaryCoefficient p m)

/-- The formal ultrametric higher-resolvent susceptibility. -/
def ultrametricResolventSusceptibility (p m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (ultrametricResolventCoefficient p m)

@[simp]
theorem coeff_ultrametricResolventBoundary (p m k : ℕ) :
    coeff k (ultrametricResolventBoundary p m) =
      ultrametricResolventBoundaryCoefficient p m k := by
  simp [ultrametricResolventBoundary]

@[simp]
theorem coeff_ultrametricResolventSusceptibility (p m k : ℕ) :
    coeff k (ultrametricResolventSusceptibility p m) =
      ultrametricResolventCoefficient p m k := by
  simp [ultrametricResolventSusceptibility]

/-- The denominator in every forced Taylor coefficient is strictly positive. -/
theorem ultrametricResolventCoefficient_denominator_pos
    {p m : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m) (k : ℕ) :
    0 < 1 - ultrametricResolventCoefficientScale p m k := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by
    exact_mod_cast (show 1 < p by omega)
  have hpow : (p : ℚ) < (p : ℚ) ^ (m + k) := by
    calc
      (p : ℚ) = (p : ℚ) ^ (1 : ℕ) := by simp
      _ < (p : ℚ) ^ (m + k) :=
        pow_lt_pow_right₀ hpQ (by omega)
  have hpowpos : 0 < (p : ℚ) ^ (m + k) :=
    pow_pos (by positivity) _
  exact sub_pos.mpr ((div_lt_iff₀ hpowpos).2 (by simpa using hpow))

/-- The scale multiplier followed by coefficient rescaling is the explicit shell multiplier. -/
theorem ultrametricResolventScale_mul_rescale_power
    {p m : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    ultrametricResolventScale p m * ((p : ℚ)⁻¹) ^ k =
      ultrametricResolventCoefficientScale p m k := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 by omega)
  rw [ultrametricResolventScale, ultrametricResolventCoefficientScale, pow_add,
    inv_pow]
  field_simp [hp0]

/-- Coefficientwise affine scale recursion. -/
theorem ultrametricResolventCoefficient_recursion
    {p m : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m) (k : ℕ) :
    ultrametricResolventCoefficient p m k =
      ultrametricResolventBoundaryCoefficient p m k +
        ultrametricResolventScale p m * ((p : ℚ)⁻¹) ^ k *
          ultrametricResolventCoefficient p m k := by
  have hden :
      1 - ultrametricResolventCoefficientScale p m k ≠ 0 :=
    ne_of_gt (ultrametricResolventCoefficient_denominator_pos hp hm k)
  rw [ultrametricResolventScale_mul_rescale_power hp k]
  unfold ultrametricResolventCoefficient
  field_simp [hden]
  ring

/-- **Exact formal susceptibility constraint.**  A two-shell defect and one contractive scale
rescaling determine the complete one-sided ultrametric resolvent series. -/
theorem ultrametricResolventSusceptibility_constraint
    {p m : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m) :
    ultrametricResolventSusceptibility p m =
      ultrametricResolventBoundary p m +
        ultrametricResolventScale p m •
          PowerSeries.rescale ((p : ℚ)⁻¹)
            (ultrametricResolventSusceptibility p m) := by
  ext k
  simp only [coeff_ultrametricResolventSusceptibility, map_add,
    coeff_ultrametricResolventBoundary, PowerSeries.coeff_smul,
    PowerSeries.coeff_rescale, smul_eq_mul]
  simpa [mul_assoc] using ultrametricResolventCoefficient_recursion hp hm k

/-- **Formal rigidity.**  The affine ultrametric resolvent constraint has no second formal
solution; no initial value or normalization is required. -/
theorem ultrametricResolventSusceptibility_unique
    {p m : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m)
    {R : PowerSeries ℚ}
    (hR : R = ultrametricResolventBoundary p m +
      ultrametricResolventScale p m •
        PowerSeries.rescale ((p : ℚ)⁻¹) R) :
    R = ultrametricResolventSusceptibility p m := by
  ext k
  have hcoeff := congrArg (PowerSeries.coeff k) hR
  simp only [map_add, coeff_ultrametricResolventBoundary,
    PowerSeries.coeff_smul, PowerSeries.coeff_rescale, smul_eq_mul] at hcoeff
  rw [← mul_assoc, ultrametricResolventScale_mul_rescale_power hp k] at hcoeff
  rw [coeff_ultrametricResolventSusceptibility,
    ultrametricResolventCoefficient]
  have hden :
      1 - ultrametricResolventCoefficientScale p m k ≠ 0 :=
    ne_of_gt (ultrametricResolventCoefficient_denominator_pos hp hm k)
  apply (eq_div_iff hden).2
  linear_combination hcoeff

end

end GaloisForLFunctions.HTGeometry
