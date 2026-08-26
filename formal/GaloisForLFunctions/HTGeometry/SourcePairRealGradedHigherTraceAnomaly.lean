import GaloisForLFunctions.HTGeometry.GradedRegularizedTraceDeterminantRigidity

/-!
# Source-pair real graded higher-trace anomaly

A literal real source cell

`[[a, -b], [b, a]]`

has conjugate characteristic nodes `a ± ib`.  This file constructs a source-coordinate-defined
graded replacement with real even nodes `a ± b` and four real odd nodes `b, b, -b, -b`.
Its signed traces agree with the source in degrees one and two, so the correction is invisible to
the first trace and to the quadratic Hilbert--Carleman jet.  The first two possible anomalies are

`A₃ = 12 a b²`,

`A₄ = 4 b² (6 a² - b²)`.

They vanish simultaneously exactly when `b = 0`.  Hence every genuine move of a nonreal source
pair to the real even divisor carries a nonzero, source-defined anomaly in degree three or four.
This is a finite local construction.  It does not assert that the odd poles cancel or escape under
an infinite Xi completion.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal real two-plane source block in coefficient coordinates `(a,b)`. -/
def sourcePairBlock (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), -(b : ℂ); (b : ℂ), (a : ℂ)]

/-- Real-divisor even block, defined directly from the source coefficients. -/
def sourcePairRealEvenBlock (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((a + b : ℝ) : ℂ), ((a - b : ℝ) : ℂ)]

/-- Four-channel odd carrier, defined directly from the transverse source coefficient. -/
def sourcePairRealOddBlock (b : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(b : ℂ), (b : ℂ), -(b : ℂ), -(b : ℂ)]

/-- Power trace of the literal real source block with conjugate characteristic pair `a ± ib`. -/
def sourcePairMoment (n : ℕ) (a b : ℝ) : ℂ :=
  ((a : ℂ) + (b : ℂ) * I) ^ n + ((a : ℂ) - (b : ℂ) * I) ^ n

/-- Power trace of the real-divisor even block with nodes `a ± b`. -/
def sourcePairRealEvenMoment (n : ℕ) (a b : ℝ) : ℂ :=
  ((a + b : ℝ) : ℂ) ^ n + ((a - b : ℝ) : ℂ) ^ n

/-- Power trace of the four-node real odd carrier `b,b,-b,-b`. -/
def sourcePairRealOddMoment (n : ℕ) (b : ℝ) : ℂ :=
  2 * (b : ℂ) ^ n + 2 * (-(b : ℂ)) ^ n

/-- Every declared even moment is the actual matrix power trace of the real even block. -/
theorem sourcePairRealEvenBlock_trace_pow (n : ℕ) (a b : ℝ) :
    (sourcePairRealEvenBlock a b ^ n).trace = sourcePairRealEvenMoment n a b := by
  rw [sourcePairRealEvenBlock, Matrix.diagonal_pow, Matrix.trace_diagonal,
    Fin.sum_univ_two]
  simp [sourcePairRealEvenMoment]

/-- Every declared odd moment is the actual matrix power trace of the real odd block. -/
theorem sourcePairRealOddBlock_trace_pow (n : ℕ) (b : ℝ) :
    (sourcePairRealOddBlock b ^ n).trace = sourcePairRealOddMoment n b := by
  rw [sourcePairRealOddBlock, Matrix.diagonal_pow, Matrix.trace_diagonal,
    Fin.sum_univ_four]
  simp [sourcePairRealOddMoment]
  ring

/-- Degree-one source moment is the actual power trace of the literal source block. -/
theorem sourcePairBlock_trace_pow_one (a b : ℝ) :
    (sourcePairBlock a b ^ 1).trace = sourcePairMoment 1 a b := by
  simp [sourcePairBlock, sourcePairMoment, Matrix.trace_fin_two]

/-- Degree-two source moment is the actual power trace of the literal source block. -/
theorem sourcePairBlock_trace_pow_two (a b : ℝ) :
    (sourcePairBlock a b ^ 2).trace = sourcePairMoment 2 a b := by
  norm_num [pow_succ, sourcePairBlock, sourcePairMoment, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Degree-three source moment is the actual power trace of the literal source block. -/
theorem sourcePairBlock_trace_pow_three (a b : ℝ) :
    (sourcePairBlock a b ^ 3).trace = sourcePairMoment 3 a b := by
  norm_num [pow_succ, sourcePairBlock, sourcePairMoment, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]

/-- Degree-four source moment is the actual power trace of the literal source block. -/
theorem sourcePairBlock_trace_pow_four (a b : ℝ) :
    (sourcePairBlock a b ^ 4).trace = sourcePairMoment 4 a b := by
  norm_num [pow_succ, sourcePairBlock, sourcePairMoment, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  norm_num [Complex.I_sq]

/-- Signed higher-trace anomaly of the real graded lift. -/
def sourcePairRealGradedAnomaly (n : ℕ) (a b : ℝ) : ℂ :=
  sourcePairRealEvenMoment n a b - sourcePairRealOddMoment n b - sourcePairMoment n a b

/-- Characteristic divisor of the literal source conjugate pair. -/
def sourcePairDivisor (a b : ℝ) (z : ℂ) : ℂ :=
  (z - ((a : ℂ) + (b : ℂ) * I)) * (z - ((a : ℂ) - (b : ℂ) * I))

/-- Characteristic divisor of the real even block. -/
def sourcePairRealEvenDivisor (a b : ℝ) (z : ℂ) : ℂ :=
  (z - ((a + b : ℝ) : ℂ)) * (z - ((a - b : ℝ) : ℂ))

/-- The pair divisor is the characteristic determinant of the literal source block. -/
theorem sourcePairDivisor_eq_charDivisor (a b : ℝ) (z : ℂ) :
    sourcePairDivisor a b z =
      (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - sourcePairBlock a b).det := by
  simp [sourcePairDivisor, sourcePairBlock, Matrix.det_fin_two]
  ring_nf
  simp [Complex.I_sq]

/-- The new even divisor is the characteristic determinant of the explicit real even block. -/
theorem sourcePairRealEvenDivisor_eq_charDivisor (a b : ℝ) (z : ℂ) :
    sourcePairRealEvenDivisor a b z =
      (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - sourcePairRealEvenBlock a b).det := by
  simp [sourcePairRealEvenDivisor, sourcePairRealEvenBlock, Matrix.det_fin_two]

/-- The graded correction preserves the complete first trace. -/
theorem sourcePairRealGradedAnomaly_one (a b : ℝ) :
    sourcePairRealGradedAnomaly 1 a b = 0 := by
  simp [sourcePairRealGradedAnomaly, sourcePairRealEvenMoment,
    sourcePairRealOddMoment, sourcePairMoment]

/-- The graded correction preserves the complete quadratic trace. -/
theorem sourcePairRealGradedAnomaly_two (a b : ℝ) :
    sourcePairRealGradedAnomaly 2 a b = 0 := by
  simp [sourcePairRealGradedAnomaly, sourcePairRealEvenMoment,
    sourcePairRealOddMoment, sourcePairMoment]
  ring_nf
  simp [Complex.I_sq]

/-- Exact cubic trace anomaly of the real graded lift. -/
theorem sourcePairRealGradedAnomaly_three (a b : ℝ) :
    sourcePairRealGradedAnomaly 3 a b = 12 * (a : ℂ) * (b : ℂ) ^ 2 := by
  simp [sourcePairRealGradedAnomaly, sourcePairRealEvenMoment,
    sourcePairRealOddMoment, sourcePairMoment]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Exact quartic trace anomaly of the real graded lift. -/
theorem sourcePairRealGradedAnomaly_four (a b : ℝ) :
    sourcePairRealGradedAnomaly 4 a b =
      4 * (b : ℂ) ^ 2 * (6 * (a : ℂ) ^ 2 - (b : ℂ) ^ 2) := by
  simp [sourcePairRealGradedAnomaly, sourcePairRealEvenMoment,
    sourcePairRealOddMoment, sourcePairMoment]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The cubic anomaly is literally the signed difference of the three matrix power traces. -/
theorem sourcePairRealGradedAnomaly_three_eq_matrixTrace (a b : ℝ) :
    sourcePairRealGradedAnomaly 3 a b =
      (sourcePairRealEvenBlock a b ^ 3).trace -
        (sourcePairRealOddBlock b ^ 3).trace - (sourcePairBlock a b ^ 3).trace := by
  rw [sourcePairRealEvenBlock_trace_pow, sourcePairRealOddBlock_trace_pow,
    sourcePairBlock_trace_pow_three]
  rfl

/-- The quartic anomaly is literally the signed difference of the three matrix power traces. -/
theorem sourcePairRealGradedAnomaly_four_eq_matrixTrace (a b : ℝ) :
    sourcePairRealGradedAnomaly 4 a b =
      (sourcePairRealEvenBlock a b ^ 4).trace -
        (sourcePairRealOddBlock b ^ 4).trace - (sourcePairBlock a b ^ 4).trace := by
  rw [sourcePairRealEvenBlock_trace_pow, sourcePairRealOddBlock_trace_pow,
    sourcePairBlock_trace_pow_four]
  rfl

/-- Cubic and quartic anomalies jointly detect exactly the horizontal source displacement. -/
theorem sourcePairRealGradedHigherTraceAnomaly_faithful (a b : ℝ) :
    sourcePairRealGradedAnomaly 3 a b = 0 ∧
      sourcePairRealGradedAnomaly 4 a b = 0 ↔ b = 0 := by
  rw [sourcePairRealGradedAnomaly_three, sourcePairRealGradedAnomaly_four]
  constructor
  · rintro ⟨h3, h4⟩
    by_contra hb
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
    have haC : (a : ℂ) = 0 := by
      have h12a : 12 * (a : ℂ) = 0 :=
        (mul_eq_zero.mp h3).resolve_right (pow_ne_zero 2 hbC)
      exact (mul_eq_zero.mp h12a).resolve_left (by norm_num)
    rw [haC, zero_pow (by norm_num)] at h4
    norm_num at h4
    exact hb h4
  · rintro rfl
    norm_num

/-- Every zero of the new even divisor is real. -/
theorem sourcePairRealEvenDivisor_zero_im (a b : ℝ) {z : ℂ}
    (hz : sourcePairRealEvenDivisor a b z = 0) : z.im = 0 := by
  rcases mul_eq_zero.mp hz with hz | hz
  · have : z = ((a + b : ℝ) : ℂ) := sub_eq_zero.mp hz
    rw [this]
    simp
  · have : z = ((a - b : ℝ) : ℂ) := sub_eq_zero.mp hz
    rw [this]
    simp

/-- The upper source node remains a zero of the literal source divisor. -/
theorem sourcePairDivisor_at_upper (a b : ℝ) :
    sourcePairDivisor a b ((a : ℂ) + (b : ℂ) * I) = 0 := by
  simp [sourcePairDivisor]

/-- The imaginary coordinate of the upper source node is the literal block coefficient `b`. -/
theorem sourcePair_upper_im (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * I).im) = b := by
  simp

/-- Closed source-only alternative: either the source block was real already, or this graded lift
moves its nonreal divisor to a real divisor and records the move in degree three or four. -/
theorem sourcePair_real_or_realGradedHigherTraceAnomaly_moves_divisor (a b : ℝ) :
    b = 0 ∨
      (∃ z : ℂ, sourcePairDivisor a b z = 0 ∧ z.im ≠ 0) ∧
      (∀ z : ℂ, sourcePairRealEvenDivisor a b z = 0 → z.im = 0) ∧
      (sourcePairRealGradedAnomaly 3 a b ≠ 0 ∨
        sourcePairRealGradedAnomaly 4 a b ≠ 0) := by
  by_cases hb : b = 0
  · exact Or.inl hb
  · right
    refine ⟨⟨(a : ℂ) + (b : ℂ) * I, sourcePairDivisor_at_upper a b, ?_⟩,
      fun z hz => sourcePairRealEvenDivisor_zero_im a b hz, ?_⟩
    simpa [sourcePair_upper_im] using hb
    by_contra h
    push Not at h
    exact hb ((sourcePairRealGradedHigherTraceAnomaly_faithful a b).mp h)

end

end GaloisForLFunctions.HTGeometry
