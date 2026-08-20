import GaloisForLFunctions.HilbertMetric.FanoCommutator

/-!
# Bogomolny--Prasad--Sommerfield bounds

Unconditional finite-dimensional square-completion bounds and the self-commutator Fano instance.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Two-channel quadratic energy. -/
def bpsEnergy (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

/-- Bilinear signed charge paired with `bpsEnergy`. -/
def bpsCharge (x y : ℝ) : ℝ := 2 * x * y

/-- Negative-chirality square completion. -/
theorem bpsEnergy_eq_charge_add_defect (x y : ℝ) :
    bpsEnergy x y = bpsCharge x y + (x - y) ^ 2 := by
  simp only [bpsEnergy, bpsCharge]
  ring

/-- Positive-chirality square completion. -/
theorem bpsEnergy_eq_neg_charge_add_defect (x y : ℝ) :
    bpsEnergy x y = -bpsCharge x y + (x + y) ^ 2 := by
  simp only [bpsEnergy, bpsCharge]
  ring

/-- Universal scalar BPS bound. -/
theorem abs_bpsCharge_le_bpsEnergy (x y : ℝ) :
    |bpsCharge x y| ≤ bpsEnergy x y := by
  rw [abs_le]
  constructor
  · simp only [bpsEnergy, bpsCharge]
    nlinarith [sq_nonneg (x + y)]
  · simp only [bpsEnergy, bpsCharge]
    nlinarith [sq_nonneg (x - y)]

/-- Positive-charge saturation is the first-order equation `x = y`. -/
theorem bpsEnergy_eq_charge_iff (x y : ℝ) :
    bpsEnergy x y = bpsCharge x y ↔ x = y := by
  constructor
  · intro h
    rw [bpsEnergy_eq_charge_add_defect] at h
    nlinarith [sq_nonneg (x - y)]
  · rintro rfl
    simp only [bpsEnergy, bpsCharge]
    ring

/-- Negative-charge saturation is the opposite first-order equation `x = -y`. -/
theorem bpsEnergy_eq_neg_charge_iff (x y : ℝ) :
    bpsEnergy x y = -bpsCharge x y ↔ x = -y := by
  constructor
  · intro h
    rw [bpsEnergy_eq_neg_charge_add_defect] at h
    nlinarith [sq_nonneg (x + y)]
  · rintro rfl
    simp [bpsEnergy, bpsCharge]
    ring

/-- Absolute-charge saturation is the union of the two chiral first-order equations. -/
theorem bpsEnergy_eq_abs_charge_iff (x y : ℝ) :
    bpsEnergy x y = |bpsCharge x y| ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    by_cases hq : 0 ≤ bpsCharge x y
    · rw [abs_of_nonneg hq] at h
      exact Or.inl ((bpsEnergy_eq_charge_iff x y).mp h)
    · rw [abs_of_nonpos (le_of_not_ge hq)] at h
      exact Or.inr ((bpsEnergy_eq_neg_charge_iff x y).mp h)
  · rintro (hxy | hxy)
    · rw [abs_of_nonneg]
      · exact (bpsEnergy_eq_charge_iff x y).mpr hxy
      · rw [hxy, bpsCharge]
        nlinarith [sq_nonneg y]
    · rw [abs_of_nonpos]
      · exact (bpsEnergy_eq_neg_charge_iff x y).mpr hxy
      · rw [hxy, bpsCharge]
        nlinarith [sq_nonneg y]

variable {n : Type*} [Fintype n]

/-- Squared column energy in the self-commutator Fano problem. -/
def fanoBPSEnergy (A : Matrix n n ℝ) : ℝ :=
  Matrix.trace ((A.transpose * A) * (A.transpose * A))

/-- Matrix-square charge in the self-commutator Fano problem. -/
def fanoBPSCharge (A : Matrix n n ℝ) : ℝ :=
  matrixHilbertSchmidtEnergy (A * A)

/-- Half the self-commutator energy: exact Fano BPS defect. -/
def fanoBPSDefect (A : Matrix n n ℝ) : ℝ :=
  matrixHilbertSchmidtEnergy (matrixSelfCommutator A) / 2

/-- Exact Fano BPS decomposition. -/
theorem fanoBPSEnergy_eq_charge_add_defect (A : Matrix n n ℝ) :
    fanoBPSEnergy A = fanoBPSCharge A + fanoBPSDefect A := by
  have h := selfCommutator_energy_eq_two_mul_defect A
  simp only [fanoBPSEnergy, fanoBPSCharge, fanoBPSDefect]
  linarith

/-- Fano BPS bound: matrix-square charge cannot exceed squared column energy. -/
theorem fanoBPSCharge_le_energy (A : Matrix n n ℝ) :
    fanoBPSCharge A ≤ fanoBPSEnergy A := by
  exact squareEnergy_le_trace_columnEnergy_sq A

/-- Fano BPS saturation is exactly normality. -/
theorem fanoBPSEnergy_eq_charge_iff (A : Matrix n n ℝ) :
    fanoBPSEnergy A = fanoBPSCharge A ↔ matrixSelfCommutator A = 0 := by
  exact trace_columnEnergy_sq_eq_squareEnergy_iff A

end

end GaloisForLFunctions.HilbertMetric
