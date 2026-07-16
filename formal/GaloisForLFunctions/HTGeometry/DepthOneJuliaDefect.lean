import GaloisForLFunctions.HTGeometry.ClockDescentAnomaly

/-!
# The depth-one source anomaly factors through the Julia defect

For a positive source contraction with scalar coordinate `q`, the depth-one displacement `1 - q`
is not an arbitrary positive coefficient.  It factors through the canonical Julia/Stinespring
defect `sqrt (1 - q^2)`, followed by a scalar contraction.  This supplies the local Markov cell
required by a conormal-corona integration of source descent anomalies.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V O : Type*}
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup O] [Module K O]

/-- Every source descent anomaly splits canonically into a universal clock displacement and the
observation of the source displacement. -/
theorem clockDescentAnomaly_eq_clockDisplacement_add_sourceDisplacement
    (source : V →ₗ[K] V) (observe : V →ₗ[K] O) (shadow : O →ₗ[K] O) :
    clockDescentAnomaly source observe shadow =
      (shadow - LinearMap.id).comp observe +
        observe.comp (LinearMap.id - source) := by
  ext v
  simp [clockDescentAnomaly]

/-- Exact factorization of a positive depth-one shift displacement through its Julia defect. -/
theorem depthOneShiftDefect_julia_factor
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.sqrt (1 - q ^ 2) * Real.sqrt ((1 - q) / (1 + q)) = 1 - q := by
  have hminus : 0 ≤ 1 - q := by linarith
  have hplus : 0 < 1 + q := by linarith
  have hsq : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hratio : 0 ≤ (1 - q) / (1 + q) := div_nonneg hminus hplus.le
  have hsquare :
      (Real.sqrt (1 - q ^ 2) * Real.sqrt ((1 - q) / (1 + q))) ^ 2 =
        (1 - q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsq, Real.sq_sqrt hratio]
    field_simp
    ring
  have hleft :
      0 ≤ Real.sqrt (1 - q ^ 2) * Real.sqrt ((1 - q) / (1 + q)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- The second factor in the Julia factorization is itself a positive contraction. -/
theorem depthOneShiftDefect_residual_contractive
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ Real.sqrt ((1 - q) / (1 + q)) ∧
      Real.sqrt ((1 - q) / (1 + q)) ≤ 1 := by
  have hminus : 0 ≤ 1 - q := by linarith
  have hplus : 0 < 1 + q := by linarith
  constructor
  · exact Real.sqrt_nonneg _
  · rw [Real.sqrt_le_one]
    exact (div_le_one hplus).2 (by linarith)

/-- Exponential source shifts with nonnegative frequency have the exact Julia factorization. -/
theorem depthOneExponentialShift_julia_factor
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    Real.sqrt (1 - Real.exp (-lambda) ^ 2) *
        Real.sqrt ((1 - Real.exp (-lambda)) / (1 + Real.exp (-lambda))) =
      1 - Real.exp (-lambda) :=
  depthOneShiftDefect_julia_factor (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlambda))

end

end GaloisForLFunctions.HTGeometry
