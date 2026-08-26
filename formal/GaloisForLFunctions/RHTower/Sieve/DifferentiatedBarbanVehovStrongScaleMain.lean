import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovGeneralScaleMain

/-!
# Cubic-scale Barban--Vehov main terms

The cubic identities are direct specializations of the general logarithmic-scale collapse at
`p = 3`.  Keeping these names preserves the downstream API while centralizing all kernel algebra in
`DifferentiatedBarbanVehovGeneralScaleMain`.
-/

namespace RHTower.Sieve

noncomputable section

private theorem log_cube_eq_three_mul (M : ℕ) :
    Real.log (((M ^ 3 : ℕ) : ℝ)) = 3 * Real.log (M : ℝ) := by
  push_cast
  rw [Real.log_pow]
  norm_num

theorem barbanVehovLongHarmonicKernelContinuous_cube
    {M q r : ℕ} (hM : 0 < M) (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongHarmonicKernelContinuous (M ^ 3) (M ^ 3 * M) q r =
      Real.log M / (Nat.lcm q r : ℝ) := by
  exact barbanVehovLongHarmonicKernelContinuous_eq (p := 3)
    (pow_pos hM 3) hM hq hr (log_cube_eq_three_mul M)

theorem barbanVehovLongFirstLogKernelContinuous_cube
    {M q r : ℕ} (hM : 0 < M) (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongFirstLogKernelContinuous (M ^ 3) (M ^ 3 * M) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log M * Real.log ((M : ℝ) / (r : ℝ)) +
          (5 / 2 : ℝ) * Real.log M ^ 2) := by
  (convert barbanVehovLongFirstLogKernelContinuous_eq (p := (3 : ℝ))
    (pow_pos hM 3) hM hq hr (log_cube_eq_three_mul M) using 1; norm_num)

theorem barbanVehovLongSecondLogKernelContinuous_cube
    {M q r : ℕ} (hM : 0 < M) (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongSecondLogKernelContinuous (M ^ 3) (M ^ 3 * M) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log M * Real.log ((M : ℝ) / (q : ℝ)) *
            Real.log ((M : ℝ) / (r : ℝ)) +
          (5 / 2 : ℝ) * Real.log M ^ 2 *
            (Real.log ((M : ℝ) / (q : ℝ)) + Real.log ((M : ℝ) / (r : ℝ))) +
          (19 / 3 : ℝ) * Real.log M ^ 3) := by
  (convert barbanVehovLongSecondLogKernelContinuous_eq (p := (3 : ℝ))
    (pow_pos hM 3) hM hq hr (log_cube_eq_three_mul M) using 1; norm_num)

theorem barbanVehovFullLongBaseContinuous_cube_eq_polynomialMain
    {M : ℕ} (hM : 0 < M) :
    barbanVehovFullLongBaseContinuous (M ^ 3) M =
      barbanVehovLongBasePolynomialMain M := by
  exact barbanVehovFullLongBaseContinuous_eq_polynomialMain (p := 3)
    (pow_pos hM 3) hM (log_cube_eq_three_mul M)

theorem barbanVehovFullLongCrossContinuous_cube_eq_polynomialMain
    {M : ℕ} (hM : 0 < M) :
    barbanVehovFullLongCrossContinuous (M ^ 3) M =
      barbanVehovLongCrossPolynomialMain 3 M := by
  exact barbanVehovFullLongCrossContinuous_eq_polynomialMain
    (pow_pos hM 3) hM (log_cube_eq_three_mul M)

theorem barbanVehovFullLongDerivativeContinuous_cube_eq_polynomialMain
    {M : ℕ} (hM : 0 < M) :
    barbanVehovFullLongDerivativeContinuous (M ^ 3) M =
      barbanVehovLongDerivativePolynomialMain 3 M := by
  exact barbanVehovFullLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hM 3) hM (log_cube_eq_three_mul M)

end

end RHTower.Sieve
