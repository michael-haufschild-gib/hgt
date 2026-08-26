import GaloisForLFunctions.RHTower.Sieve.FibrePowerBound
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIThirdDerivative

/-!
# Explicit power envelope for third-derivative type-I fibres

On a dyadic block `A ≤ n < B ≤ 2A`, the fibre at `b ≤ A` has length at most `4A/b`, while its
left endpoint lies between `A/b` and `2A/b`.  These inequalities turn the exact third-derivative
envelope into explicit powers of `A`, `b`, and `T r`.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

private def fibreLow (A b : ℕ) : ℕ := (A - 1) / b + 1
private def fibreHigh (B b : ℕ) : ℕ := (B - 1) / b + 1

theorem cast_fibre_width_le_four_mul_div {A B b : ℕ}
    (hb : 1 ≤ b) (hbA : b ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (((fibreHigh B b - fibreLow A b : ℕ) : ℝ)) ≤ 4 * (A : ℝ) / b := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hwidth : fibreHigh B b - fibreLow A b ≤ fibreHigh B b := Nat.sub_le _ _
  have hcastWidth : (((fibreHigh B b - fibreLow A b : ℕ) : ℝ)) ≤ (fibreHigh B b : ℝ) := by
    exact_mod_cast hwidth
  have hhigh := cast_fibre_high_le (B := B) hb (le_trans hbA hAB)
  have hBcast : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hBA
  rw [le_div_iff₀ hb0]
  calc
    (((fibreHigh B b - fibreLow A b : ℕ) : ℝ)) * b
        ≤ (fibreHigh B b : ℝ) * b :=
      mul_le_mul_of_nonneg_right hcastWidth (Nat.cast_nonneg _)
    _ = (b : ℝ) * (fibreHigh B b : ℝ) := by ring
    _ ≤ 2 * (B : ℝ) := hhigh
    _ ≤ 4 * (A : ℝ) := by linarith

private theorem nearDiagonalLambda3_fibre_eq {T r : ℝ} {A b : ℕ} (hb : 1 ≤ b) :
    nearDiagonalLambda3 T (r / b) (fibreLow A b : ℝ) =
      T * r * (b : ℝ) ^ 3 /
        (72 * Real.pi * ((b : ℝ) * (fibreLow A b : ℝ)) ^ 4) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [nearDiagonalLambda3]
  field_simp

theorem nearDiagonalLambda3_fibre_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A b : ℕ} (hA : 1 ≤ A) (hb : 1 ≤ b) :
    nearDiagonalLambda3 T (r / b) (fibreLow A b : ℝ) ≤
      T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlow := le_cast_fibre_low hA hb
  have hmul : (A : ℝ) ≤ (b : ℝ) * (fibreLow A b : ℝ) := by
    rw [div_le_iff₀ hb0] at hlow
    calc
      (A : ℝ) ≤ (fibreLow A b : ℝ) * b := hlow
      _ = (b : ℝ) * (fibreLow A b : ℝ) := by ring
  have hpow : (A : ℝ) ^ 4 ≤ ((b : ℝ) * (fibreLow A b : ℝ)) ^ 4 :=
    pow_le_pow_left₀ hA0.le hmul 4
  rw [nearDiagonalLambda3_fibre_eq hb]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem le_nearDiagonalLambda3_fibre {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A b : ℕ} (hA : 1 ≤ A) (hb : 1 ≤ b) (hbA : b ≤ A) :
    T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4) ≤
      nearDiagonalLambda3 T (r / b) (fibreLow A b : ℝ) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hfl0 : (0 : ℝ) < (fibreLow A b : ℝ) := by
    exact_mod_cast (Nat.le_add_left 1 ((A - 1) / b))
  have hhigh := cast_fibre_high_le (B := A) hb hbA
  have hpow : ((b : ℝ) * (fibreLow A b : ℝ)) ^ 4 ≤ (2 * (A : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hhigh 4
  rw [nearDiagonalLambda3_fibre_eq hb]
  have hnum : 0 ≤ T * r * (b : ℝ) ^ 3 := by positivity
  have hstep : T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (2 * (A : ℝ)) ^ 4) ≤
      T * r * (b : ℝ) ^ 3 /
        (72 * Real.pi * ((b : ℝ) * (fibreLow A b : ℝ)) ^ 4) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 72 * Real.pi * (2 * (A : ℝ)) ^ 4)
      (by positivity : 0 < 72 * Real.pi * ((b : ℝ) * (fibreLow A b : ℝ)) ^ 4)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpow (by positivity)) hnum
  have heq : 1152 * Real.pi * (A : ℝ) ^ 4 =
      72 * Real.pi * (2 * (A : ℝ)) ^ 4 := by ring
  rw [heq]
  exact hstep

/-- Explicit two-branch envelope for a third-derivative fibre. -/
def thirdDerivativeFibrePowerEnvelope (T r : ℝ) (A b : ℕ) : ℝ :=
  256 * ((4 * (A : ℝ) / b) *
      (1368 ^ 2 * (T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4))) ^ (1 / 6 : ℝ)
    + (4 * (A : ℝ) / b) ^ (1 / 2 : ℝ) *
      (T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4)) ^ (-(1 / 4 : ℝ)))

theorem thirdDerivativeFibreBound_le_powerEnvelope {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B b : ℕ}
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hbA : b ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    thirdDerivativeFibreBound T r A B b ≤ thirdDerivativeFibrePowerEnvelope T r A b := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hwidth := cast_fibre_width_le_four_mul_div hb hbA hAB hBA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / b) (fibreLow A b : ℝ) :=
    nearDiagonalLambda3_pos hT (div_pos hr hb0)
      (by exact_mod_cast (Nat.le_add_left 1 ((A - 1) / b)))
  have hupp0 : 0 < T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4) := by positivity
  have hlow0 : 0 < T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4) := by positivity
  have hlamUp := nearDiagonalLambda3_fibre_le hT hr hA hb
  have hlamLow := le_nearDiagonalLambda3_fibre hT hr hA hb hbA
  have hbaseUp : 1368 ^ 2 * nearDiagonalLambda3 T (r / b) (fibreLow A b : ℝ) ≤
      1368 ^ 2 * (T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4)) :=
    mul_le_mul_of_nonneg_left hlamUp (by positivity)
  have hfirstPow := Real.rpow_le_rpow (by positivity) hbaseUp (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hwidthSqrt := Real.rpow_le_rpow (Nat.cast_nonneg _) hwidth
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsecondPow : nearDiagonalLambda3 T (r / b) (fibreLow A b : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (T * r * (b : ℝ) ^ 3 / (1152 * Real.pi * (A : ℝ) ^ 4)) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlow0 hlamLow (by norm_num)
  have hfirst0 : 0 ≤ (1368 ^ 2 * nearDiagonalLambda3 T (r / b)
      (fibreLow A b : ℝ)) ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hsecond0 : 0 ≤ nearDiagonalLambda3 T (r / b)
      (fibreLow A b : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hlam0.le _
  rw [thirdDerivativeFibreBound, thirdDerivativeTypeIBound,
    thirdDerivativeFibrePowerEnvelope]
  have hfirst := mul_le_mul hwidth hfirstPow hfirst0 (by positivity)
  have hsecond := mul_le_mul hwidthSqrt hsecondPow hsecond0
    (Real.rpow_nonneg (by positivity) _)
  exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num)

private theorem mul_cube_rpow_one_sixth {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C) :
    (C * b ^ 3) ^ (1 / 6 : ℝ) = C ^ (1 / 6 : ℝ) * b ^ (1 / 2 : ℝ) := by
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hb.le]
  congr 2
  norm_num

private theorem mul_cube_rpow_neg_quarter {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C) :
    (C * b ^ 3) ^ (-(1 / 4 : ℝ)) = C ^ (-(1 / 4 : ℝ)) * b ^ (-(3 / 4 : ℝ)) := by
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hb.le]
  congr 2
  norm_num

private theorem div_rpow_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (a / b) ^ (1 / 2 : ℝ) = a ^ (1 / 2 : ℝ) * b ^ (-(1 / 2 : ℝ)) := by
  rw [div_eq_mul_inv, Real.mul_rpow ha (by positivity), Real.inv_rpow hb.le,
    Real.rpow_neg hb.le]

private theorem inv_mul_rpow_half {b : ℝ} (hb : 0 < b) :
    b⁻¹ * b ^ (1 / 2 : ℝ) = b ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
  congr 1
  norm_num

private theorem rpow_neg_half_mul_neg_three_quarters {b : ℝ} (hb : 0 < b) :
    b ^ (-(1 / 2 : ℝ)) * b ^ (-(3 / 4 : ℝ)) = b ^ (-(5 / 4 : ℝ)) := by
  rw [← Real.rpow_add hb]
  congr 1
  norm_num

/-- Coefficient of the summable `b⁻¹ᐟ²` branch. -/
def thirdDerivativeFibreFirstCoefficient (T r : ℝ) (A : ℕ) : ℝ :=
  256 * (4 * (A : ℝ)) *
    (1368 ^ 2 * (T * r / (72 * Real.pi * (A : ℝ) ^ 4))) ^ (1 / 6 : ℝ)

/-- Coefficient of the summable `b⁻⁵ᐟ⁴` branch. -/
def thirdDerivativeFibreSecondCoefficient (T r : ℝ) (A : ℕ) : ℝ :=
  256 * (4 * (A : ℝ)) ^ (1 / 2 : ℝ) *
    (T * r / (1152 * Real.pi * (A : ℝ) ^ 4)) ^ (-(1 / 4 : ℝ))

/-- The power envelope factored into its two divisor weights. -/
def thirdDerivativeFibreFactoredEnvelope (T r : ℝ) (A b : ℕ) : ℝ :=
  thirdDerivativeFibreFirstCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))
    + thirdDerivativeFibreSecondCoefficient T r A * (b : ℝ) ^ (-(5 / 4 : ℝ))

theorem thirdDerivativeFibrePowerEnvelope_eq_factored {T r : ℝ} {A b : ℕ}
    (hT : 0 < T) (hr : 0 < r) (hA : 1 ≤ A) (hb : 1 ≤ b) :
    thirdDerivativeFibrePowerEnvelope T r A b =
      thirdDerivativeFibreFactoredEnvelope T r A b := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  set C : ℝ := 1368 ^ 2 * (T * r / (72 * Real.pi * (A : ℝ) ^ 4)) with hCdef
  set D : ℝ := T * r / (1152 * Real.pi * (A : ℝ) ^ 4) with hDdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have heqC : 1368 ^ 2 * (T * r * (b : ℝ) ^ 3 /
      (72 * Real.pi * (A : ℝ) ^ 4)) = C * (b : ℝ) ^ 3 := by
    rw [hCdef]
    ring
  have heqD : T * r * (b : ℝ) ^ 3 /
      (1152 * Real.pi * (A : ℝ) ^ 4) = D * (b : ℝ) ^ 3 := by
    rw [hDdef]
    ring
  rw [thirdDerivativeFibrePowerEnvelope, thirdDerivativeFibreFactoredEnvelope,
    thirdDerivativeFibreFirstCoefficient, thirdDerivativeFibreSecondCoefficient,
    heqC, heqD, mul_cube_rpow_one_sixth hb0 hC0,
    mul_cube_rpow_neg_quarter hb0 hD0, div_rpow_half (by positivity) hb0,
    div_eq_mul_inv]
  rw [show (4 * (A : ℝ) * (b : ℝ)⁻¹) * (C ^ (1 / 6 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ)) =
      4 * (A : ℝ) * C ^ (1 / 6 : ℝ) *
        ((b : ℝ)⁻¹ * (b : ℝ) ^ (1 / 2 : ℝ)) by ring,
    inv_mul_rpow_half hb0]
  rw [show ((4 * (A : ℝ)) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (-(1 / 2 : ℝ))) *
      (D ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (-(3 / 4 : ℝ))) =
      (4 * (A : ℝ)) ^ (1 / 2 : ℝ) * D ^ (-(1 / 4 : ℝ)) *
        ((b : ℝ) ^ (-(1 / 2 : ℝ)) * (b : ℝ) ^ (-(3 / 4 : ℝ))) by ring,
    rpow_neg_half_mul_neg_three_quarters hb0]
  rw [hCdef, hDdef]
  ring

end

end RHTower.Sieve
