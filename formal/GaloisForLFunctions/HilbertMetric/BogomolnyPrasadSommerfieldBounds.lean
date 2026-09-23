import GaloisForLFunctions.HilbertMetric.FanoCommutator
import GaloisForLFunctions.HilbertMetric.TransverseDegreePhase

/-!
# Bogomolny--Prasad--Sommerfield bounds

Unconditional finite-dimensional square-completion bounds and the self-commutator Fano instance.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Two-channel quadratic energy. -/
def bpsEnergy (x y : ℝ) : ℝ := x ^ (2 : ℕ) + y ^ (2 : ℕ)

/-- Bilinear signed charge paired with `bpsEnergy`. -/
def bpsCharge (x y : ℝ) : ℝ := 2 * x * y

/-- Negative-chirality square completion. -/
theorem bpsEnergy_eq_charge_add_defect (x y : ℝ) :
    bpsEnergy x y = bpsCharge x y + (x - y) ^ (2 : ℕ) := by
  simp only [bpsEnergy, bpsCharge]
  ring

/-- Positive-chirality square completion. -/
theorem bpsEnergy_eq_neg_charge_add_defect (x y : ℝ) :
    bpsEnergy x y = -bpsCharge x y + (x + y) ^ (2 : ℕ) := by
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

/-! ## Transverse Fano square-completion bounds -/

variable {ι : Type*} [Fintype ι]

/-- Sharp baseline charge in the equal-gap transverse channel law. -/
def transverseChannelBPSCharge
    (loweringCharge topDegree : ℝ) : ℝ :=
  loweringCharge - (Fintype.card ι : ℝ) *
    (topDegree * (topDegree - 4) / 4)

/-- Sum of channel phase-square BPS defects. -/
def transverseChannelBPSDefect (topDegree : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i, ((topDegree - 1) * p i - (topDegree - 2) / 2) ^ (2 : ℕ)

/-- Equal-gap transverse Fano margin is charge plus phase defect. -/
theorem transverseChannelFanoMargin_eq_bpsCharge_add_defect
    (loweringCharge topDegree : ℝ) (p : ι → ℝ) :
    transverseChannelFanoMargin loweringCharge topDegree p =
      transverseChannelBPSCharge (ι := ι) loweringCharge topDegree +
        transverseChannelBPSDefect topDegree p := by
  exact transverseChannelFanoMargin_square_card loweringCharge topDegree p

/-- Equal-gap transverse-channel BPS bound. -/
theorem transverseChannelBPSCharge_le_fanoMargin
    (loweringCharge topDegree : ℝ) (p : ι → ℝ) :
    transverseChannelBPSCharge (ι := ι) loweringCharge topDegree ≤
      transverseChannelFanoMargin loweringCharge topDegree p :=
  transverseChannelFanoMargin_lower_bound loweringCharge topDegree p

/-- Equal-gap saturation is channelwise phase balance. -/
theorem transverseChannelBPSSaturation_iff
    (loweringCharge topDegree : ℝ) (p : ι → ℝ) :
    transverseChannelFanoMargin loweringCharge topDegree p =
        transverseChannelBPSCharge (ι := ι) loweringCharge topDegree ↔
      ∀ i, (topDegree - 1) * p i = (topDegree - 2) / 2 := by
  rw [transverseChannelFanoMargin_eq_bpsCharge_add_defect]
  constructor
  · intro h i
    have hzero : transverseChannelBPSDefect topDegree p = 0 := by linarith
    have hi : ((topDegree - 1) * p i - (topDegree - 2) / 2) ^ (2 : ℕ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_hj : j ∈ Finset.univ) => sq_nonneg
          ((topDegree - 1) * p j - (topDegree - 2) / 2))).1
        hzero i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    have hzero : transverseChannelBPSDefect topDegree p = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      rw [h i, sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    rw [hzero, add_zero]

/-- Sharp baseline charge in the unequal-gap transverse channel law. -/
def unequalGapChannelBPSCharge
    (loweringCharge : ℝ) (lowerDegree gap : ι → ℝ) : ℝ :=
  loweringCharge + ∑ i, (lowerDegree i - (gap i - 1) ^ (2 : ℕ) / 4)

/-- Sum of unequal-gap phase-square BPS defects. -/
def unequalGapChannelBPSDefect (gap p : ι → ℝ) : ℝ :=
  ∑ i, (gap i * p i - (gap i - 1) / 2) ^ (2 : ℕ)

/-- Unequal-gap transverse Fano margin is charge plus phase defect. -/
theorem unequalGapChannelFanoMargin_eq_bpsCharge_add_defect
    (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) :
    unequalGapChannelFanoMargin loweringCharge lowerDegree gap p =
      unequalGapChannelBPSCharge loweringCharge lowerDegree gap +
        unequalGapChannelBPSDefect gap p := by
  exact unequalGapChannelFanoMargin_square_separated loweringCharge lowerDegree gap p

/-- Unequal-gap transverse-channel BPS bound. -/
theorem unequalGapChannelBPSCharge_le_fanoMargin
    (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) :
    unequalGapChannelBPSCharge loweringCharge lowerDegree gap ≤
      unequalGapChannelFanoMargin loweringCharge lowerDegree gap p := by
  rw [unequalGapChannelFanoMargin_eq_bpsCharge_add_defect]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => sq_nonneg (gap i * p i - (gap i - 1) / 2))

/-- Unequal-gap saturation is channelwise phase balance. -/
theorem unequalGapChannelBPSSaturation_iff
    (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) :
    unequalGapChannelFanoMargin loweringCharge lowerDegree gap p =
        unequalGapChannelBPSCharge loweringCharge lowerDegree gap ↔
      ∀ i, gap i * p i = (gap i - 1) / 2 := by
  rw [unequalGapChannelFanoMargin_eq_bpsCharge_add_defect]
  constructor
  · intro h i
    have hzero : unequalGapChannelBPSDefect gap p = 0 := by linarith
    have hi : (gap i * p i - (gap i - 1) / 2) ^ (2 : ℕ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_hj : j ∈ Finset.univ) => sq_nonneg
          (gap j * p j - (gap j - 1) / 2))).1
        hzero i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    have hzero : unequalGapChannelBPSDefect gap p = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      rw [h i, sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    rw [hzero, add_zero]

end

end GaloisForLFunctions.HilbertMetric
