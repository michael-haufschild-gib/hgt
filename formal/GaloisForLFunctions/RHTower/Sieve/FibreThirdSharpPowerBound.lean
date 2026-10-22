import GaloisForLFunctions.RHTower.Sieve.FibreThirdPowerBound
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIThirdDerivativeSharp

/-!
# Power envelope for the sharp third-derivative fibre bound

The Type I fibre at divisor `b` of a dyadic range `A ≤ B ≤ 2A` carries the sharp third-derivative
bound `16 · 1368 (W λ^(1/6) + √W λ^(-1/6))` with width `W` and scale
`λ = T (r/b) / (72 π m⁴)` at the fibre's starting point. Bounding the width by `4A/b` and `λ`
between `T r b³ / (1152 π A⁴)` and `T r b³ / (72 π A⁴)` gives a power envelope in `b`, which
factors exactly as `C₁ b^(-1/2) + C₂ b^(-1)`.

## Main results

- `sharpThirdDerivativeFibreBound_le_powerEnvelope`: the fibre bound is at most the power
  envelope.
- `sharpThirdDerivativeFibrePowerEnvelope_eq_factored`: the power envelope equals
  `C₁ b^(-1/2) + C₂ b^(-1)`.

## Hypotheses

Both results are unconditional explicit inequalities and identities. They assume `T, r > 0`,
`1 ≤ A`, `1 ≤ b`, and for the envelope bound `b ≤ A` and `A ≤ B ≤ 2A`.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

private def sharpFibreLow (A b : ℕ) : ℕ := (A - 1) / b + 1
private def sharpFibreHigh (B b : ℕ) : ℕ := (B - 1) / b + 1

/-- Power envelope `16 · 1368 ((4A/b) (T r b³ / (72 π A⁴))^(1/6) + √(4A/b) (T r b³ / (1152 π A⁴))^(-1/6))`
for the fibre at divisor `b`. -/
def sharpThirdDerivativeFibrePowerEnvelope (T r : ℝ) (A b : ℕ) : ℝ :=
  16 * 1368 * ((4 * (A : ℝ) / b) *
      (T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4)) ^ (1 / 6 : ℝ)
    + Real.sqrt (4 * (A : ℝ) / b) *
      (T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4)) ^ (-(1 / 6 : ℝ)))

/-- Assuming `T, r > 0`, `1 ≤ b ≤ A` and `A ≤ B ≤ 2A`, the sharp third-derivative fibre bound at `b`
is at most the power envelope. -/
theorem sharpThirdDerivativeFibreBound_le_powerEnvelope {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B b : ℕ}
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hbA : b ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    sharpThirdDerivativeFibreBound T r A B b ≤
      sharpThirdDerivativeFibrePowerEnvelope T r A b := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hwidth := cast_fibre_width_le_four_mul_div hb hbA hAB hBA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / b) (((A - 1) / b + 1 : ℕ) : ℝ) :=
    nearDiagonalLambda3_pos hT (div_pos hr hb0)
      (by exact_mod_cast (Nat.le_add_left 1 ((A - 1) / b)))
  have hupp0 : 0 < T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4) := by positivity
  have hlow0 : 0 < T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4) := by positivity
  have hlamUp := nearDiagonalLambda3_fibre_le hT hr hA hb
  have hlamLow := le_nearDiagonalLambda3_fibre hT hr hA hb hbA
  have hfirstPow := Real.rpow_le_rpow hlam0.le hlamUp (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hwidthSqrt := Real.sqrt_le_sqrt hwidth
  have hsecondPow : nearDiagonalLambda3 T (r / b) (((A - 1) / b + 1 : ℕ) : ℝ) ^
        (-(1 / 6 : ℝ)) ≤
      (T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4)) ^ (-(1 / 6 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlow0 hlamLow (by norm_num)
  have hfirst0 : 0 ≤ nearDiagonalLambda3 T (r / b)
      (((A - 1) / b + 1 : ℕ) : ℝ) ^ (1 / 6 : ℝ) := by positivity
  have hsecond0 : 0 ≤ nearDiagonalLambda3 T (r / b)
      (((A - 1) / b + 1 : ℕ) : ℝ) ^ (-(1 / 6 : ℝ)) := by positivity
  rw [sharpThirdDerivativeFibreBound, sharpThirdDerivativeTypeIBound,
    sharpThirdDerivativeFibrePowerEnvelope]
  have hfirst := mul_le_mul hwidth hfirstPow hfirst0 (by positivity)
  have hsecond := mul_le_mul hwidthSqrt hsecondPow hsecond0 (by positivity)
  exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num)

/-- First coefficient `C₁ = 16 · 1368 · 4A · (T r / (72 π A⁴))^(1/6)` of the factored envelope. -/
def sharpThirdDerivativeFibreFirstCoefficient (T r : ℝ) (A : ℕ) : ℝ :=
  16 * 1368 * (4 * (A : ℝ)) *
    (T * r / (72 * Real.pi * (A : ℝ) ^ 4)) ^ (1 / 6 : ℝ)

/-- Second coefficient `C₂ = 16 · 1368 · √(4A) · (T r / (1152 π A⁴))^(-1/6)` of the factored
envelope. -/
def sharpThirdDerivativeFibreSecondCoefficient (T r : ℝ) (A : ℕ) : ℝ :=
  16 * 1368 * Real.sqrt (4 * (A : ℝ)) *
    (T * r / (1152 * Real.pi * (A : ℝ) ^ 4)) ^ (-(1 / 6 : ℝ))

/-- Factored envelope `C₁ b^(-1/2) + C₂ b^(-1)`. -/
def sharpThirdDerivativeFibreFactoredEnvelope (T r : ℝ) (A b : ℕ) : ℝ :=
  sharpThirdDerivativeFibreFirstCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))
    + sharpThirdDerivativeFibreSecondCoefficient T r A * (b : ℝ)⁻¹

private theorem cube_rpow_one_sixth {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C) :
    (C * b ^ 3) ^ (1 / 6 : ℝ) = C ^ (1 / 6 : ℝ) * b ^ (1 / 2 : ℝ) := by
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hb.le]
  congr 2
  norm_num

private theorem cube_rpow_neg_sixth {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C) :
    (C * b ^ 3) ^ (-(1 / 6 : ℝ)) = C ^ (-(1 / 6 : ℝ)) * b ^ (-(1 / 2 : ℝ)) := by
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hb.le]
  congr 2
  norm_num

private theorem sqrt_div_nat {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt (a / b) = Real.sqrt a * b ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow ha hb.le, Real.rpow_neg hb.le,
    ← Real.sqrt_eq_rpow]
  rw [div_eq_mul_inv]

private theorem inv_mul_rpow_half_sharp {b : ℝ} (hb : 0 < b) :
    b⁻¹ * b ^ (1 / 2 : ℝ) = b ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
  congr 1
  norm_num

private theorem rpow_neg_half_sq {b : ℝ} (hb : 0 < b) :
    b ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) = b⁻¹ := by
  rw [← Real.rpow_add hb, ← Real.rpow_neg_one, Real.rpow_neg_one]
  norm_num
  rw [Real.rpow_neg_one]

/-- For `T, r > 0` and `A, b ≥ 1`, the power envelope equals `C₁ b^(-1/2) + C₂ b^(-1)`. -/
theorem sharpThirdDerivativeFibrePowerEnvelope_eq_factored {T r : ℝ} {A b : ℕ}
    (hT : 0 < T) (hr : 0 < r) (hA : 1 ≤ A) (hb : 1 ≤ b) :
    sharpThirdDerivativeFibrePowerEnvelope T r A b =
      sharpThirdDerivativeFibreFactoredEnvelope T r A b := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  set C : ℝ := T * r / (72 * Real.pi * (A : ℝ) ^ 4) with hCdef
  set D : ℝ := T * r / (1152 * Real.pi * (A : ℝ) ^ 4) with hDdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have heqC : T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4) = C * (b : ℝ) ^ 3 := by
    rw [hCdef]
    ring
  have heqD : T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4) = D * (b : ℝ) ^ 3 := by
    rw [hDdef]
    ring
  rw [sharpThirdDerivativeFibrePowerEnvelope, sharpThirdDerivativeFibreFactoredEnvelope,
    sharpThirdDerivativeFibreFirstCoefficient, sharpThirdDerivativeFibreSecondCoefficient,
    heqC, heqD, cube_rpow_one_sixth hb0 hC0, cube_rpow_neg_sixth hb0 hD0,
    sqrt_div_nat (by positivity) hb0, div_eq_mul_inv]
  rw [show (4 * (A : ℝ) * (b : ℝ)⁻¹) *
      (C ^ (1 / 6 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ)) =
      4 * (A : ℝ) * C ^ (1 / 6 : ℝ) *
        ((b : ℝ)⁻¹ * (b : ℝ) ^ (1 / 2 : ℝ)) by ring,
    inv_mul_rpow_half_sharp hb0]
  rw [show (Real.sqrt (4 * (A : ℝ)) * (b : ℝ) ^ (-(1 / 2 : ℝ))) *
      (D ^ (-(1 / 6 : ℝ)) * (b : ℝ) ^ (-(1 / 2 : ℝ))) =
      Real.sqrt (4 * (A : ℝ)) * D ^ (-(1 / 6 : ℝ)) *
        ((b : ℝ) ^ (-(1 / 2 : ℝ)) * (b : ℝ) ^ (-(1 / 2 : ℝ))) by ring,
    rpow_neg_half_sq hb0]
  rw [hCdef, hDdef]
  ring

end

end RHTower.Sieve
