import GaloisForLFunctions.HTGeometry.SourcePairRealGradedHigherTraceAnomaly

/-!
# Positive quartic graded realification of a source pair

The canonical graded realification of `a ± ib` preserves signed traces in degrees one and two,
but its quartic anomaly changes sign. This file uses the Pell solution `7² - 2 * 5² = -1`:
real even nodes `a ± 7b` and real odd nodes `5b, 5b, -5b, -5b` still preserve the first two
signed traces, while their quartic defect is

`100 b² (6 a² + 23 b²)`.

It is nonnegative and vanishes exactly when `b = 0`. Thus one positive fourth-order supertrace,
rather than a joint signed cubic/quartic test, faithfully records every move of a conjugate source
pair to a real divisor. This is a finite source-coordinate construction; it does not assert the
global theta-stage assembly or source-side vanishing law required by RH.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pell-scaled real-divisor even block with nodes `a ± 7b`. -/
def sourcePairPositiveQuarticRealEvenBlock (a b : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((a + 7 * b : ℝ) : ℂ), ((a - 7 * b : ℝ) : ℂ)]

/-- Four real odd nodes `5b,5b,-5b,-5b`. -/
def sourcePairPositiveQuarticRealOddBlock (b : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![((5 * b : ℝ) : ℂ), ((5 * b : ℝ) : ℂ),
    ((-5 * b : ℝ) : ℂ), ((-5 * b : ℝ) : ℂ)]

/-- Power trace of the Pell-scaled real even block. -/
def sourcePairPositiveQuarticRealEvenMoment (n : ℕ) (a b : ℝ) : ℂ :=
  ((a + 7 * b : ℝ) : ℂ) ^ n + ((a - 7 * b : ℝ) : ℂ) ^ n

/-- Power trace of the Pell-scaled four-node real odd block. -/
def sourcePairPositiveQuarticRealOddMoment (n : ℕ) (b : ℝ) : ℂ :=
  2 * ((5 * b : ℝ) : ℂ) ^ n + 2 * ((-5 * b : ℝ) : ℂ) ^ n

/-- Signed power-trace defect of the positive-quartic graded lift. -/
def sourcePairPositiveQuarticGradedAnomaly (n : ℕ) (a b : ℝ) : ℂ :=
  sourcePairPositiveQuarticRealEvenMoment n a b -
    sourcePairPositiveQuarticRealOddMoment n b - sourcePairMoment n a b

/-- Real positive quartic orientation charge. -/
def sourcePairPositiveQuarticCharge (a b : ℝ) : ℝ :=
  100 * b ^ (2 : ℕ) * (6 * a ^ (2 : ℕ) + 23 * b ^ (2 : ℕ))

theorem sourcePairPositiveQuarticRealEvenBlock_trace_pow (n : ℕ) (a b : ℝ) :
    (sourcePairPositiveQuarticRealEvenBlock a b ^ n).trace =
      sourcePairPositiveQuarticRealEvenMoment n a b := by
  rw [sourcePairPositiveQuarticRealEvenBlock, Matrix.diagonal_pow,
    Matrix.trace_diagonal, Fin.sum_univ_two]
  simp [sourcePairPositiveQuarticRealEvenMoment]

theorem sourcePairPositiveQuarticRealOddBlock_trace_pow (n : ℕ) (b : ℝ) :
    (sourcePairPositiveQuarticRealOddBlock b ^ n).trace =
      sourcePairPositiveQuarticRealOddMoment n b := by
  rw [sourcePairPositiveQuarticRealOddBlock, Matrix.diagonal_pow,
    Matrix.trace_diagonal, Fin.sum_univ_four]
  simp [sourcePairPositiveQuarticRealOddMoment]
  ring

/-- The Pell lift preserves total first trace. -/
theorem sourcePairPositiveQuarticGradedAnomaly_one (a b : ℝ) :
    sourcePairPositiveQuarticGradedAnomaly 1 a b = 0 := by
  simp [sourcePairPositiveQuarticGradedAnomaly,
    sourcePairPositiveQuarticRealEvenMoment,
    sourcePairPositiveQuarticRealOddMoment, sourcePairMoment]

/-- `7² - 2 * 5² = -1` makes the complete quadratic trace exact. -/
theorem sourcePairPositiveQuarticGradedAnomaly_two (a b : ℝ) :
    sourcePairPositiveQuarticGradedAnomaly 2 a b = 0 := by
  simp [sourcePairPositiveQuarticGradedAnomaly,
    sourcePairPositiveQuarticRealEvenMoment,
    sourcePairPositiveQuarticRealOddMoment, sourcePairMoment]
  ring_nf
  simp [Complex.I_sq]

/-- Exact quartic defect: a positive polynomial detecting the transverse coordinate. -/
theorem sourcePairPositiveQuarticGradedAnomaly_four (a b : ℝ) :
    sourcePairPositiveQuarticGradedAnomaly 4 a b =
      (sourcePairPositiveQuarticCharge a b : ℂ) := by
  simp [sourcePairPositiveQuarticGradedAnomaly,
    sourcePairPositiveQuarticRealEvenMoment,
    sourcePairPositiveQuarticRealOddMoment, sourcePairMoment,
    sourcePairPositiveQuarticCharge]
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem sourcePairPositiveQuarticCharge_nonneg (a b : ℝ) :
    0 ≤ sourcePairPositiveQuarticCharge a b := by
  simp only [sourcePairPositiveQuarticCharge]
  positivity

/-- Quartic charge vanishes exactly on a real source pair. -/
theorem sourcePairPositiveQuarticCharge_eq_zero_iff (a b : ℝ) :
    sourcePairPositiveQuarticCharge a b = 0 ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have hb2 : 0 < b ^ (2 : ℕ) := sq_pos_of_ne_zero hb
    have hfactor : 0 < 6 * a ^ (2 : ℕ) + 23 * b ^ (2 : ℕ) := by positivity
    have hcharge : 0 < sourcePairPositiveQuarticCharge a b := by
      simp only [sourcePairPositiveQuarticCharge]
      positivity
    exact hcharge.ne' h
  · rintro rfl
    simp [sourcePairPositiveQuarticCharge]

/-- One quartic supertrace is a faithful realness reporter. -/
theorem sourcePairPositiveQuarticGradedAnomaly_four_eq_zero_iff (a b : ℝ) :
    sourcePairPositiveQuarticGradedAnomaly 4 a b = 0 ↔ b = 0 := by
  rw [sourcePairPositiveQuarticGradedAnomaly_four,
    Complex.ofReal_eq_zero, sourcePairPositiveQuarticCharge_eq_zero_iff]

theorem sourcePairPositiveQuarticGradedAnomaly_four_re_nonneg (a b : ℝ) :
    0 ≤ (sourcePairPositiveQuarticGradedAnomaly 4 a b).re := by
  rw [sourcePairPositiveQuarticGradedAnomaly_four]
  simpa using sourcePairPositiveQuarticCharge_nonneg a b

/-- Quartic anomaly is literally the signed difference of the three matrix power traces. -/
theorem sourcePairPositiveQuarticGradedAnomaly_four_eq_matrixTrace (a b : ℝ) :
    sourcePairPositiveQuarticGradedAnomaly 4 a b =
      (sourcePairPositiveQuarticRealEvenBlock a b ^ (4 : ℕ)).trace -
        (sourcePairPositiveQuarticRealOddBlock b ^ (4 : ℕ)).trace -
          (sourcePairBlock a b ^ (4 : ℕ)).trace := by
  rw [sourcePairPositiveQuarticRealEvenBlock_trace_pow,
    sourcePairPositiveQuarticRealOddBlock_trace_pow,
    sourcePairBlock_trace_pow_four]
  rfl

/-- Characteristic divisor of the Pell-scaled real even block. -/
def sourcePairPositiveQuarticRealEvenDivisor (a b : ℝ) (z : ℂ) : ℂ :=
  (z - ((a + 7 * b : ℝ) : ℂ)) * (z - ((a - 7 * b : ℝ) : ℂ))

theorem sourcePairPositiveQuarticRealEvenDivisor_zero_im (a b : ℝ) {z : ℂ}
    (hz : sourcePairPositiveQuarticRealEvenDivisor a b z = 0) : z.im = 0 := by
  rcases mul_eq_zero.mp hz with hz | hz
  · have : z = ((a + 7 * b : ℝ) : ℂ) := sub_eq_zero.mp hz
    rw [this]
    simp
  · have : z = ((a - 7 * b : ℝ) : ℂ) := sub_eq_zero.mp hz
    rw [this]
    simp

/-- Closed source-only alternative: a nonreal source pair moves to a real divisor and leaves one
strictly positive quartic supertrace defect. -/
theorem sourcePair_real_or_positiveQuarticGradedAnomaly_moves_divisor (a b : ℝ) :
    b = 0 ∨
      (∃ z : ℂ, sourcePairDivisor a b z = 0 ∧ z.im ≠ 0) ∧
      (∀ z : ℂ, sourcePairPositiveQuarticRealEvenDivisor a b z = 0 → z.im = 0) ∧
      0 < (sourcePairPositiveQuarticGradedAnomaly 4 a b).re := by
  by_cases hb : b = 0
  · exact Or.inl hb
  · right
    refine ⟨⟨(a : ℂ) + (b : ℂ) * I, sourcePairDivisor_at_upper a b, ?_⟩,
      fun z hz => sourcePairPositiveQuarticRealEvenDivisor_zero_im a b hz, ?_⟩
    simpa [sourcePair_upper_im] using hb
    rw [sourcePairPositiveQuarticGradedAnomaly_four]
    have hb2 : 0 < b ^ (2 : ℕ) := sq_pos_of_ne_zero hb
    simp only [Complex.ofReal_re, sourcePairPositiveQuarticCharge]
    positivity

end

end GaloisForLFunctions.HTGeometry
