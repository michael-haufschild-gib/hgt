import Mathlib

/-!
# Bilateral exponential repair mechanics

The exact algebraic core of the bilateral weighted-convolution repair scale.
-/

namespace BilateralExponentialRepair

noncomputable section

/-- Exponential basis cost at repair stage `n`. -/
def stageWeight (n : ℕ) (k : ℤ) : ℝ :=
  Real.exp ((n : ℝ) * |(k : ℝ)|)

/-- Positive real exponential reporter at stage `n`. -/
def boundaryReporter (n : ℕ) (k : ℤ) : ℝ :=
  Real.exp ((n : ℝ) * (k : ℝ))

/-- Unit horizontal intervention multiplier. -/
def unitTilt (k : ℤ) : ℝ :=
  Real.exp (k : ℝ)

/-- Integral-clock phase multiplier. -/
def phase (t : ℝ) (k : ℤ) : ℂ :=
  Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)

theorem boundaryReporter_pos (n : ℕ) (k : ℤ) : 0 < boundaryReporter n k :=
  Real.exp_pos _

theorem stageWeight_pos (n : ℕ) (k : ℤ) : 0 < stageWeight n k :=
  Real.exp_pos _

/-- The stage-`n` boundary reporter is dominated by the stage-`n` basis cost. -/
theorem boundaryReporter_le_stageWeight (n : ℕ) (k : ℤ) :
    boundaryReporter n k ≤ stageWeight n k := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (le_abs_self (k : ℝ)) (Nat.cast_nonneg n)

/-- A unit horizontal intervention shifts the boundary reporter to the next stage exactly. -/
theorem boundaryReporter_mul_unitTilt (n : ℕ) (k : ℤ) :
    boundaryReporter n k * unitTilt k = boundaryReporter (n + 1) k := by
  rw [boundaryReporter, unitTilt, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The unit intervention is bounded from stage `n+1` into stage `n`. -/
theorem stageWeight_mul_unitTilt_le (n : ℕ) (k : ℤ) :
    stageWeight n k * unitTilt k ≤ stageWeight (n + 1) k := by
  rw [stageWeight, unitTilt, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hk : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
  nlinarith

/-- The grade loss is attained on every nonnegative clock ray. -/
theorem stageWeight_mul_unitTilt_eq_of_nonneg (n : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    stageWeight n k * unitTilt k = stageWeight (n + 1) k := by
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  simp only [stageWeight, unitTilt, abs_of_nonneg hkR, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem boundaryReporter_eq_stageWeight_of_nonneg (n : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    boundaryReporter n k = stageWeight n k := by
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  simp [boundaryReporter, stageWeight, abs_of_nonneg hkR]

/-- On positive atoms, the next reporter/current-stage-cost ratio is exactly `exp k`. -/
theorem nextReporter_eq_exp_mul_stageWeight (n k : ℕ) :
    boundaryReporter (n + 1) (k : ℤ) = Real.exp k * stageWeight n (k : ℤ) := by
  calc
    boundaryReporter (n + 1) (k : ℤ) =
        boundaryReporter n (k : ℤ) * unitTilt (k : ℤ) :=
      (boundaryReporter_mul_unitTilt n (k : ℤ)).symm
    _ = stageWeight n (k : ℤ) * Real.exp k := by
      rw [boundaryReporter_eq_stageWeight_of_nonneg n (by positivity), unitTilt]
      norm_num
    _ = Real.exp k * stageWeight n (k : ℤ) := mul_comm _ _

/-- The next boundary reporter has no finite uniform bound on the current stage. -/
theorem nextReporter_not_uniformly_bounded (n : ℕ) :
    ¬ ∃ C : ℝ, ∀ k : ℕ,
      boundaryReporter (n + 1) (k : ℤ) ≤ C * stageWeight n (k : ℤ) := by
  rintro ⟨C, hC⟩
  have htend : Filter.Tendsto (fun k : ℕ => Real.exp (k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ k : ℕ in Filter.atTop, C + 1 ≤ Real.exp (k : ℝ) :=
    htend.eventually (Filter.eventually_ge_atTop (C + 1))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  have hlarge := hK K le_rfl
  have hbound := hC K
  rw [nextReporter_eq_exp_mul_stageWeight] at hbound
  have hwpos : 0 < stageWeight n (K : ℤ) := stageWeight_pos _ _
  have hexp_le : Real.exp (K : ℝ) ≤ C := by
    exact le_of_mul_le_mul_right hbound hwpos
  linarith

/-- Reflection preserves every stage weight. -/
@[simp] theorem stageWeight_neg (n : ℕ) (k : ℤ) :
    stageWeight n (-k) = stageWeight n k := by
  simp [stageWeight]

/-- Reflection exchanges positive and negative boundary reporters. -/
@[simp] theorem boundaryReporter_neg (n : ℕ) (k : ℤ) :
    boundaryReporter n (-k) = (boundaryReporter n k)⁻¹ := by
  rw [boundaryReporter, boundaryReporter, ← Real.exp_neg]
  congr 1
  push_cast
  ring

/-- Integral phase has unit modulus, hence costs no repair grade. -/
@[simp] theorem norm_phase (t : ℝ) (k : ℤ) : ‖phase t k‖ = 1 := by
  simpa [phase, mul_comm] using Complex.norm_exp_ofReal_mul_I (t * (k : ℝ))

/-- Integral phase observation is exactly `2π`-periodic. -/
@[simp] theorem phase_add_two_pi (t : ℝ) (k : ℤ) :
    phase (t + 2 * Real.pi) k = phase t k := by
  rw [phase, phase]
  have harg :
      ((((t + 2 * Real.pi) * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
        (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I) +
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end BilateralExponentialRepair
