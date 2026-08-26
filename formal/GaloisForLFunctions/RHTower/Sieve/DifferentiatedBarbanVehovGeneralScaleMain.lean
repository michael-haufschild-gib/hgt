import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovGeneralScaleError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovPolynomialMain
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovSharpSummatory

/-!
# Continuous differentiated Barban--Vehov main at a general logarithmic scale

If `log L = p log M`, the continuous harmonic-log kernels collapse exactly onto the three Selberg
forms already present in the corpus.  This identifies the base, cross, and derivative moments with
their polynomial main terms for every admissible logarithmic scale, rather than only `L = M^3`.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

private theorem log_natDiv_of_dvd_general
    {e d : ℕ} (he : 0 < e) (hd : 0 < d) (hde : d ∣ e) :
    Real.log (((e / d : ℕ) : ℝ)) = Real.log (e : ℝ) - Real.log (d : ℝ) := by
  rw [Nat.cast_div hde (by exact_mod_cast hd.ne')]
  exact Real.log_div (by exact_mod_cast he.ne') (by exact_mod_cast hd.ne')

private theorem log_long_div_general
    {L M e : ℕ} {p : ℝ} (hL : 0 < L) (hM : 0 < M) (he : 0 < e)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    Real.log ((((L * M : ℕ) : ℝ) / (e : ℝ))) =
      (p + 1) * Real.log (M : ℝ) - Real.log (e : ℝ) := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast
  rw [Real.log_div (mul_ne_zero hLR hMR) heR, Real.log_mul hLR hMR, hlog]
  ring

private theorem log_lower_div_general
    {L M e : ℕ} {p : ℝ} (hL : 0 < L) (he : 0 < e)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    Real.log (((L : ℝ) / (e : ℝ))) =
      p * Real.log (M : ℝ) - Real.log (e : ℝ) := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  rw [Real.log_div hLR heR, hlog]

/-- Continuous undifferentiated lcm fibre at a general logarithmic scale. -/
theorem barbanVehovLongHarmonicKernelContinuous_eq
    {L M q r : ℕ} {p : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hq : 0 < q) (hr : 0 < r)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    barbanVehovLongHarmonicKernelContinuous L (L * M) q r =
      Real.log M / (Nat.lcm q r : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  rw [barbanVehovLongHarmonicKernelContinuous,
    log_long_div_general hL hM he hlog, log_lower_div_general hL he hlog]
  ring

/-- Continuous once-differentiated lcm fibre at a general logarithmic scale. -/
theorem barbanVehovLongFirstLogKernelContinuous_eq
    {L M q r : ℕ} {p : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hq : 0 < q) (hr : 0 < r)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    barbanVehovLongFirstLogKernelContinuous L (L * M) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log M * Real.log ((M : ℝ) / (r : ℝ)) +
          (p - 1 / 2) * Real.log M ^ 2) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have her := log_natDiv_of_dvd_general he hr (Nat.dvd_lcm_right q r)
  have hMr : Real.log ((M : ℝ) / (r : ℝ)) =
      Real.log (M : ℝ) - Real.log (r : ℝ) :=
    Real.log_div (by exact_mod_cast hM.ne') (by exact_mod_cast hr.ne')
  rw [barbanVehovLongFirstLogKernelContinuous]
  rw [log_long_div_general hL hM he hlog, log_lower_div_general hL he hlog,
    her, hMr]
  ring

/-- Continuous twice-differentiated lcm fibre at a general logarithmic scale. -/
theorem barbanVehovLongSecondLogKernelContinuous_eq
    {L M q r : ℕ} {p : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hq : 0 < q) (hr : 0 < r)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    barbanVehovLongSecondLogKernelContinuous L (L * M) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log M * Real.log ((M : ℝ) / (q : ℝ)) *
            Real.log ((M : ℝ) / (r : ℝ)) +
          (p - 1 / 2) * Real.log M ^ 2 *
            (Real.log ((M : ℝ) / (q : ℝ)) +
              Real.log ((M : ℝ) / (r : ℝ))) +
          (p ^ 2 - p + 1 / 3) * Real.log M ^ 3) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have heq := log_natDiv_of_dvd_general he hq (Nat.dvd_lcm_left q r)
  have her := log_natDiv_of_dvd_general he hr (Nat.dvd_lcm_right q r)
  have hMq : Real.log ((M : ℝ) / (q : ℝ)) =
      Real.log (M : ℝ) - Real.log (q : ℝ) :=
    Real.log_div (by exact_mod_cast hM.ne') (by exact_mod_cast hq.ne')
  have hMr : Real.log ((M : ℝ) / (r : ℝ)) =
      Real.log (M : ℝ) - Real.log (r : ℝ) :=
    Real.log_div (by exact_mod_cast hM.ne') (by exact_mod_cast hr.ne')
  rw [barbanVehovLongSecondLogKernelContinuous]
  rw [log_long_div_general hL hM he hlog, log_lower_div_general hL he hlog,
    heq, her, hMq, hMr]
  ring

/-- Continuous base moment equals its Selberg polynomial main at every logarithmic scale. -/
theorem barbanVehovFullLongBaseContinuous_eq_polynomialMain
    {L M : ℕ} {p : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    barbanVehovFullLongBaseContinuous L M =
      barbanVehovLongBasePolynomialMain M := by
  rw [barbanVehovFullLongBaseContinuous, barbanVehovLongBasePolynomialMain]
  calc
    (∑ x ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      barbanVehovWeight M x.1 * barbanVehovWeight M x.2 *
        barbanVehovLongHarmonicKernelContinuous L (L * M) x.1 x.2) =
      ∑ x ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        barbanVehovWeight M x.1 * barbanVehovWeight M x.2 *
          (Real.log M / (Nat.lcm x.1 x.2 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
            rw [barbanVehovLongHarmonicKernelContinuous_eq hL hM
              (Finset.mem_Icc.mp hx1).1 (Finset.mem_Icc.mp hx2).1 hlog]
    _ = Real.log M *
        (∑ x ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          barbanVehovWeight M x.1 * barbanVehovWeight M x.2 /
            (Nat.lcm x.1 x.2 : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring
    _ = Real.log M * barbanVehovSelbergDiagonal M := by
      rw [barbanVehovSelbergDiagonal_eq_lcmQuadratic]

/-- Continuous base--derivative cross moment equals its polynomial main at every logarithmic scale. -/
theorem barbanVehovFullLongCrossContinuous_eq_polynomialMain
    {L M : ℕ} {p : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    barbanVehovFullLongCrossContinuous L M =
      barbanVehovLongCrossPolynomialMain p M := by
  calc
    barbanVehovFullLongCrossContinuous L M =
      ∑ x ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        -(barbanVehovWeight M x.1 * barbanVehovWeight M x.2) *
          (1 / (Nat.lcm x.1 x.2 : ℝ) *
            (Real.log M * Real.log ((M : ℝ) / (x.2 : ℝ)) +
              (p - 1 / 2) * Real.log M ^ 2)) := by
        rw [barbanVehovFullLongCrossContinuous]
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
        rw [barbanVehovLongFirstLogKernelContinuous_eq hL hM
          (Finset.mem_Icc.mp hx1).1 (Finset.mem_Icc.mp hx2).1 hlog]
    _ = -(Real.log M * barbanVehovSelbergMixedDiagonal M +
          (p - 1 / 2) * Real.log M ^ 2 * barbanVehovSelbergDiagonal M) := by
      rw [barbanVehovSelbergMixedDiagonal,
        barbanVehovSelbergDiagonal_eq_lcmQuadratic]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = barbanVehovLongCrossPolynomialMain p M := by
      rw [barbanVehovLongCrossPolynomialMain]

/-- Continuous derivative-square moment equals its polynomial main at every logarithmic scale. -/
theorem barbanVehovFullLongDerivativeContinuous_eq_polynomialMain
    {L M : ℕ} {p : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hlog : Real.log (L : ℝ) = p * Real.log (M : ℝ)) :
    barbanVehovFullLongDerivativeContinuous L M =
      barbanVehovLongDerivativePolynomialMain p M := by
  let leftMixed : ℝ :=
    ∑ x ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      barbanVehovWeight M x.1 * barbanVehovWeight M x.2 *
        Real.log ((M : ℝ) / (x.1 : ℝ)) / (Nat.lcm x.1 x.2 : ℝ)
  calc
    barbanVehovFullLongDerivativeContinuous L M =
      ∑ x ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        barbanVehovWeight M x.1 * barbanVehovWeight M x.2 *
          (1 / (Nat.lcm x.1 x.2 : ℝ) *
            (Real.log M * Real.log ((M : ℝ) / (x.1 : ℝ)) *
                Real.log ((M : ℝ) / (x.2 : ℝ)) +
              (p - 1 / 2) * Real.log M ^ 2 *
                (Real.log ((M : ℝ) / (x.1 : ℝ)) +
                  Real.log ((M : ℝ) / (x.2 : ℝ))) +
              (p ^ 2 - p + 1 / 3) * Real.log M ^ 3)) := by
        rw [barbanVehovFullLongDerivativeContinuous]
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
        rw [barbanVehovLongSecondLogKernelContinuous_eq hL hM
          (Finset.mem_Icc.mp hx1).1 (Finset.mem_Icc.mp hx2).1 hlog]
    _ = Real.log M * barbanVehovSelbergQuadraticLogDiagonal M +
          (p - 1 / 2) * Real.log M ^ 2 *
            (leftMixed + barbanVehovSelbergMixedDiagonal M) +
          (p ^ 2 - p + 1 / 3) * Real.log M ^ 3 *
            barbanVehovSelbergDiagonal M := by
      rw [barbanVehovSelbergQuadraticLogDiagonal,
        barbanVehovSelbergMixedDiagonal,
        barbanVehovSelbergDiagonal_eq_lcmQuadratic]
      dsimp [leftMixed]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = Real.log M * barbanVehovSelbergQuadraticLogDiagonal M +
          (2 * p - 1) * Real.log M ^ 2 *
            barbanVehovSelbergMixedDiagonal M +
          (p ^ 2 - p + 1 / 3) * Real.log M ^ 3 *
            barbanVehovSelbergDiagonal M := by
      have hleft : leftMixed = barbanVehovSelbergMixedDiagonal M := by
        exact barbanVehovSelbergMixedDiagonal_left_eq M
      rw [hleft]
      ring
    _ = barbanVehovLongDerivativePolynomialMain p M := by
      rw [barbanVehovLongDerivativePolynomialMain]

end

end RHTower.Sieve
