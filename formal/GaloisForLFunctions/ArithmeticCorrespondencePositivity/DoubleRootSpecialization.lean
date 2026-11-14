import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensBudgetOfACurveIsTheRepulsionEnergyOfItsSpectrum

/-!
# The double-root specialization of the spectral Mertens row

The two-root Euler coefficient is a divided difference of powers. At a
collision it remains regular and becomes `(k+1) a^k`, the same local
degeneration as an irregular weight-one Eisenstein coefficient. For a
double root on the unit circle its cumulative square norm is exactly
`N(N+1)(2N+1)/6`; the simple-spectrum linear bound has a cubic boundary.
-/

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open PowerSeries Finset

noncomputable section

/-- The two-root Mertens row is the finite convolution of the two geometric sequences. -/
theorem spectralMertensRow_two (a b : ℂ) (k : ℕ) :
    spectralMertensRow ![a, b] k =
      ∑ j ∈ range (k + 1), a ^ j * b ^ (k - j) := by
  simp only [spectralMertensRow, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, coeff_mul, coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ _ k

/-- The collision value does not require division by the root separation. -/
theorem spectralMertensRow_double (a : ℂ) (k : ℕ) :
    spectralMertensRow ![a, a] k = ((k + 1 : ℕ) : ℂ) * a ^ k := by
  rw [spectralMertensRow_two]
  calc
    _ = ∑ _j ∈ range (k + 1), a ^ k := by
      apply sum_congr rfl
      intro j hj
      rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hj))]
    _ = _ := by simp

/-- Equality with the collision sequence characterizes a repeated root. -/
theorem spectralMertensRow_collision_iff (a b : ℂ) :
    (∀ k : ℕ, spectralMertensRow ![a, b] k = ((k + 1 : ℕ) : ℂ) * a ^ k) ↔
      a = b := by
  constructor
  · intro h
    have h1 := h 1
    simp only [spectralMertensRow_two, sum_range_succ, sum_range_zero,
      pow_zero, pow_one, Nat.sub_zero, Nat.sub_self, zero_add, one_mul, mul_one] at h1
    norm_num only [Nat.cast_ofNat] at h1
    linear_combination -h1
  · rintro rfl
    exact spectralMertensRow_double a

/-- The repeated-root Euler series inverts the square of one local factor. -/
theorem doubleRootEulerSeries_mul (a : ℂ) :
    (PowerSeries.mk fun k => ((k + 1 : ℕ) : ℂ) * a ^ k) *
      (1 - C a * X) ^ 2 = 1 := by
  have hseries : (PowerSeries.mk fun k => ((k + 1 : ℕ) : ℂ) * a ^ k) =
      (PowerSeries.mk fun k => a ^ k) * (PowerSeries.mk fun k => a ^ k) := by
    ext k
    rw [coeff_mk, ← spectralMertensRow_double]
    simp [spectralMertensRow, Fin.prod_univ_two]
  rw [hseries]
  calc
    _ = ((PowerSeries.mk fun k => a ^ k) * (1 - C a * X)) ^ 2 := by ring
    _ = 1 := by rw [geom_mul_one_sub, one_pow]

/-- A unit-circle double root has exactly linear coefficient norm. -/
theorem spectralMertensRow_double_phase_norm (θ : ℝ) (k : ℕ) :
    ‖spectralMertensRow
      ![Complex.exp ((θ : ℂ) * Complex.I), Complex.exp ((θ : ℂ) * Complex.I)] k‖ =
        (k : ℝ) + 1 := by
  rw [spectralMertensRow_double, norm_mul, norm_pow]
  simp [Complex.norm_exp]

/-- Exact cubic energy at a collision of two pure roots. -/
theorem spectralMertensRow_double_phase_energy (θ : ℝ) (N : ℕ) :
    (∑ k ∈ range N, ‖spectralMertensRow
      ![Complex.exp ((θ : ℂ) * Complex.I), Complex.exp ((θ : ℂ) * Complex.I)] k‖ ^ 2) =
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6 := by
  simp only [spectralMertensRow_double_phase_norm]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

end

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
