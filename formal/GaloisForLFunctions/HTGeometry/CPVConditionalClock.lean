import GaloisForLFunctions.HTGeometry.CPVThermalRadiation
import Mathlib

/-!
# Normalized conditional clocks from the thermal pair

The stationary two-mode state in arXiv:2601.07437 generates an exact
oscillator clock family on the corpus `lp` Hilbert space. Its overlap is a
convergent geometric resolvent and never vanishes at finite thermal scale.
This distinguishes classical clock coordinates from orthogonal quantum readings.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV
open scoped BigOperators

/-- Oscillator phase in the Schrödinger time orientation. -/
def clockPhase (t : ℝ) : ℂ := Complex.exp (-(t : ℂ) * Complex.I)

@[simp] theorem clockPhase_norm (t : ℝ) : ‖clockPhase t‖ = 1 := by
  simp [clockPhase, Complex.norm_exp]

@[simp] theorem clockPhase_zero : clockPhase 0 = 1 := by simp [clockPhase]

/-- Time differences combine the two unitary phases. -/
theorem clockPhase_mul_conj (s t : ℝ) :
    clockPhase t * (starRingEnd ℂ) (clockPhase s) = clockPhase (t - s) := by
  simp only [clockPhase, ← Complex.exp_conj, map_mul, map_neg,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, Complex.ofReal_sub]
  congr 1
  ring

/-- Actual conditional state after reading the oscillator clock at `t`. -/
def conditionalClock (tau t : ℝ) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun n => radiationVector tau n * clockPhase t ^ n,
    HilbertSchmidt.memℓp_of_sq (by
      simpa only [norm_mul, norm_pow, clockPhase_norm, one_pow, mul_one]
        using HilbertSchmidt.summable_coe_sq (radiationVector tau))⟩

@[simp] theorem conditionalClock_apply (tau t : ℝ) (n : ℕ) :
    conditionalClock tau t n = radiationVector tau n * clockPhase t ^ n := rfl

/-- Conditioning changes phases while preserving every occupation probability. -/
theorem conditionalClock_probability (tau t : ℝ) (n : ℕ) :
    ‖conditionalClock tau t n‖ ^ 2 = radiationMass tau n := by
  simp only [conditionalClock_apply, norm_mul, norm_pow, clockPhase_norm, one_pow,
    mul_one, radiationVector_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (radiationMass_pos tau n).le

/-- Every conditional oscillator state is normalized. -/
theorem conditionalClock_norm_sq (tau t : ℝ) : ‖conditionalClock tau t‖ ^ 2 = 1 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  simp only [conditionalClock_probability]
  exact (radiationMass_hasSum tau).tsum_eq

/-- The initial conditional state is exactly the thermal half-density. -/
theorem conditionalClock_zero (tau : ℝ) : conditionalClock tau 0 = radiationVector tau := by
  apply lp.ext
  funext n
  simp

/-- Coordinatewise overlap integrand, before summing the infinite Hilbert series. -/
theorem conditionalClock_overlap_term (tau s t : ℝ) (n : ℕ) :
    conditionalClock tau t n * (starRingEnd ℂ) (conditionalClock tau s n) =
      ((1 - thermalRatio tau : ℝ) : ℂ) *
        ((thermalRatio tau : ℂ) * clockPhase (t - s)) ^ n := by
  rw [conditionalClock_apply, conditionalClock_apply, map_mul, map_pow]
  calc
    radiationVector tau n * clockPhase t ^ n *
        ((starRingEnd ℂ) (radiationVector tau n) * (starRingEnd ℂ) (clockPhase s) ^ n) =
      (radiationVector tau n * (starRingEnd ℂ) (radiationVector tau n)) *
        (clockPhase t * (starRingEnd ℂ) (clockPhase s)) ^ n := by rw [mul_pow]; ring
    _ = (radiationMass tau n : ℂ) * clockPhase (t - s) ^ n := by
      rw [clockPhase_mul_conj, radiationVector_apply]
      simp only [Complex.conj_ofReal, ← Complex.ofReal_mul]
      rw [← sq, Real.sq_sqrt (radiationMass_pos tau n).le]
    _ = _ := by
      simp only [radiationMass, canonicalThermalMass, Complex.ofReal_mul,
        Complex.ofReal_pow, mul_pow]
      ring

/-- The clock overlap is exactly a geometric resolvent. -/
theorem conditionalClock_overlap (tau s t : ℝ) :
    inner ℂ (conditionalClock tau s) (conditionalClock tau t) =
      ((1 - thermalRatio tau : ℝ) : ℂ) /
        (1 - (thermalRatio tau : ℂ) * clockPhase (t - s)) := by
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, conditionalClock_overlap_term]
  have hnorm : ‖(thermalRatio tau : ℂ) * clockPhase (t - s)‖ < 1 := by
    rw [norm_mul, clockPhase_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (thermalRatio_pos tau)]
    exact thermalRatio_lt_one tau
  rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one hnorm).tsum_eq, div_eq_mul_inv]

/-- No two clock readings are orthogonal at a finite thermal scale. -/
theorem conditionalClock_ne_orthogonal (tau s t : ℝ) :
    inner ℂ (conditionalClock tau s) (conditionalClock tau t) ≠ 0 := by
  rw [conditionalClock_overlap]
  apply div_ne_zero
  · exact_mod_cast ne_of_gt (sub_pos.mpr (thermalRatio_lt_one tau))
  · intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_one, norm_mul, clockPhase_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thermalRatio_pos tau)] at he
    linarith [thermalRatio_lt_one tau]

/-- Schrödinger derivative of the basic phase. -/
theorem clockPhase_hasDerivAt (t : ℝ) :
    HasDerivAt clockPhase (-Complex.I * clockPhase t) t := by
  convert! (((hasDerivAt_id t).ofReal_comp.neg).mul_const Complex.I).cexp using 1
  simp [clockPhase]
  ring

/-- Exact Schrödinger evolution for every occupation coefficient. -/
theorem conditionalClock_hasDerivAt (tau t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => conditionalClock tau s n)
      (-Complex.I * (n : ℂ) * conditionalClock tau t n) t := by
  have h := ((clockPhase_hasDerivAt t).pow n).const_mul (radiationVector tau n)
  convert! h using 1
  cases n with
  | zero => simp
  | succ n =>
    simp only [conditionalClock_apply, Nat.succ_sub_one, pow_succ]
    ring

/-- The phase-dressed purification remains stationary for every diagonal spectrum. -/
theorem conditionalPair_stationary (tau t : ℝ) (E : ℕ → ℂ) :
    thermofieldLeftAction E (thermofieldDiagonalKernel (conditionalClock tau t)) -
      thermofieldRightAction E (thermofieldDiagonalKernel (conditionalClock tau t)) = 0 := by
  rw [thermofieldDiagonalKernel_central, sub_self]

end GaloisForLFunctions.HTGeometry.CPV
