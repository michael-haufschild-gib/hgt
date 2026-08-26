import GaloisForLFunctions.RHTower.Sieve.FibreThirdSharpAggregate

/-!
# Mixed second- and sharp third-derivative Type-I fibres

The second-derivative estimate has the stronger reciprocal tail, while the sharp third-derivative
estimate has the smaller main term on long divisor fibres.  This file selects between them at the
exact crossover where the second-derivative kernel meets the sharp third-derivative main term.
The resulting pointwise envelope keeps both advantages without assuming an exponent pair.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

/-- Main coefficient enlarged by the exact geometric-mean crossover reserve. -/
def secondThirdMixedFibreMainCoefficient (T r : ℝ) (A : ℕ) : ℝ :=
  sharpThirdDerivativeFibreFirstCoefficient T r A +
    Real.sqrt (fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A)

/-- Fibre envelope selected at the exact second/third derivative crossover. -/
def secondThirdMixedFibreBound (T r : ℝ) (A B b : ℕ) : ℝ :=
  if fibreKernel T r A ≤
      secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) then
    fibreBound T r A B b
  else sharpThirdDerivativeFibreBound T r A B b

theorem secondThirdMixedFibreBound_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B b : ℕ} (hb : 1 ≤ b) : 0 ≤ secondThirdMixedFibreBound T r A B b := by
  rw [secondThirdMixedFibreBound]
  split_ifs
  · rw [fibreBound]
    positivity
  · exact sharpThirdDerivativeFibreBound_nonneg hT hr hb

/-- Each fibre is controlled by the derivative test selected at the exact crossover. -/
theorem norm_sum_ndExp_secondThird_mixed_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B b : ℕ} (hb : 1 ≤ b)
    (hspan : ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1))
    (hrA : r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ))
    (hlam3 : nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1)
    (hlam2 : fibreKernel T r A ≤
        secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
      nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ m ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1), ndExp T r m b‖
      ≤ secondThirdMixedFibreBound T r A B b := by
  rw [secondThirdMixedFibreBound]
  split_ifs with hlow
  · rw [fibreBound]
    exact norm_sum_ndExp_le hT hr hb _ _ (Nat.le_add_left 1 _) hrA (hlam2 hlow)
  · rw [sharpThirdDerivativeFibreBound]
    exact norm_sum_ndExp_third_sharp_le hT hr hb _ _ (Nat.le_add_left 1 _) hspan hrA hlam3

private theorem rpow_neg_half_sq_mixed {b : ℝ} (hb : 0 < b) :
    b ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) = b⁻¹ := by
  rw [← Real.rpow_add hb, ← Real.rpow_neg_one, Real.rpow_neg_one]
  norm_num
  rw [Real.rpow_neg_one]

/-- The mixed fibre has the sharp `b⁻¹ᐟ²` main term and second-derivative `b⁻¹` tail. -/
theorem secondThirdMixedFibreBound_le_powerEnvelope {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B b : ℕ}
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hbA : b ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    secondThirdMixedFibreBound T r A B b ≤
      2 * secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))
        + fibreTail T r B / b := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hC1 : 0 < sharpThirdDerivativeFibreFirstCoefficient T r A := by
    rw [sharpThirdDerivativeFibreFirstCoefficient]
    positivity
  have hC2 : 0 < sharpThirdDerivativeFibreSecondCoefficient T r A := by
    rw [sharpThirdDerivativeFibreSecondCoefficient]
    positivity
  have hprod : 0 ≤ fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A :=
    mul_nonneg (fibreKernel_nonneg T r A) hC2.le
  have hsqrt := Real.sq_sqrt hprod
  have hD : 0 < secondThirdMixedFibreMainCoefficient T r A := by
    rw [secondThirdMixedFibreMainCoefficient]
    positivity
  have hC1D : sharpThirdDerivativeFibreFirstCoefficient T r A ≤
      secondThirdMixedFibreMainCoefficient T r A := by
    rw [secondThirdMixedFibreMainCoefficient]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hbalance : fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A ≤
      secondThirdMixedFibreMainCoefficient T r A ^ 2 := by
    calc
      fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A =
          Real.sqrt (fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A) ^ 2 :=
        hsqrt.symm
      _ ≤ secondThirdMixedFibreMainCoefficient T r A ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _)
          (by
            rw [secondThirdMixedFibreMainCoefficient]
            exact le_add_of_nonneg_left hC1.le) 2
  have hw : 0 < (b : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hb0 _
  rw [secondThirdMixedFibreBound]
  split_ifs with hlow
  · have hfb := fibreBound_le hT hr hA hb (le_trans hbA hAB)
    have htail : 0 ≤ fibreTail T r B / (b : ℝ) :=
      div_nonneg (fibreTail_nonneg T r B) hb0.le
    have hmain : 0 ≤ secondThirdMixedFibreMainCoefficient T r A *
        (b : ℝ) ^ (-(1 / 2 : ℝ)) := mul_nonneg hD.le hw.le
    calc
      fibreBound T r A B b ≤ fibreKernel T r A + fibreTail T r B / b := hfb
      _ ≤ secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) +
          fibreTail T r B / b := add_le_add hlow le_rfl
      _ ≤ (secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) +
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))) +
          fibreTail T r B / b := add_le_add (le_add_of_nonneg_right hmain) le_rfl
      _ = 2 * secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) +
          fibreTail T r B / b := by ring
  · have hhigh : secondThirdMixedFibreMainCoefficient T r A *
        (b : ℝ) ^ (-(1 / 2 : ℝ)) < fibreKernel T r A := lt_of_not_ge hlow
    have hmul := mul_lt_mul_of_pos_right hhigh hC2
    have hcw : sharpThirdDerivativeFibreSecondCoefficient T r A *
        (b : ℝ) ^ (-(1 / 2 : ℝ)) < secondThirdMixedFibreMainCoefficient T r A := by
      apply lt_of_mul_lt_mul_left _ hD.le
      calc
        secondThirdMixedFibreMainCoefficient T r A *
              (sharpThirdDerivativeFibreSecondCoefficient T r A *
                (b : ℝ) ^ (-(1 / 2 : ℝ))) =
            (secondThirdMixedFibreMainCoefficient T r A *
                (b : ℝ) ^ (-(1 / 2 : ℝ))) *
              sharpThirdDerivativeFibreSecondCoefficient T r A := by ring
        _ < fibreKernel T r A * sharpThirdDerivativeFibreSecondCoefficient T r A := hmul
        _ ≤ secondThirdMixedFibreMainCoefficient T r A ^ 2 := hbalance
        _ = secondThirdMixedFibreMainCoefficient T r A *
              secondThirdMixedFibreMainCoefficient T r A := by ring
    have htailThird : sharpThirdDerivativeFibreSecondCoefficient T r A * (b : ℝ)⁻¹ ≤
        secondThirdMixedFibreMainCoefficient T r A *
          (b : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← rpow_neg_half_sq_mixed hb0]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcw.le hw.le
    have hsharp := sharpThirdDerivativeFibreBound_le_powerEnvelope hT hr hA hb hbA hAB hBA
    rw [sharpThirdDerivativeFibrePowerEnvelope_eq_factored hT hr hA hb,
      sharpThirdDerivativeFibreFactoredEnvelope] at hsharp
    have hfirst : sharpThirdDerivativeFibreFirstCoefficient T r A *
        (b : ℝ) ^ (-(1 / 2 : ℝ)) ≤ secondThirdMixedFibreMainCoefficient T r A *
          (b : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hC1D hw.le
    have htail : 0 ≤ fibreTail T r B / (b : ℝ) :=
      div_nonneg (fibreTail_nonneg T r B) hb0.le
    calc
      sharpThirdDerivativeFibreBound T r A B b ≤
          sharpThirdDerivativeFibreFirstCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) +
            sharpThirdDerivativeFibreSecondCoefficient T r A * (b : ℝ)⁻¹ := hsharp
      _ ≤ secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) +
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) :=
        add_le_add hfirst htailThird
      _ ≤ (secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) +
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))) +
          fibreTail T r B / b := le_add_of_nonneg_right htail
      _ = 2 * secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) +
          fibreTail T r B / b := by ring

end

end RHTower.Sieve
