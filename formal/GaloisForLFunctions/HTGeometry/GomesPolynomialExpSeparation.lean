import GaloisForLFunctions.HTGeometry.GomesPolynomialMomentGerm

/-!
# Strict exponential separation of polynomial profiles

The exponential map gives a nonnegative comparison density whose integral vanishes
exactly when two finite polynomial profiles agree. This supplies a direct separating
observable for the Gomes-inspired reconstruction experiment, without appealing to an
infinite moment sequence or analytic continuation.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The pointwise monotonicity pairing of log-density and density differences. -/
def gomesPolynomialSeparationDensity (H K : ℝ[X]) (x : ℝ) : ℝ :=
  (H.eval x - K.eval x) * (dilatonWeight H x - dilatonWeight K x)

/-- Strictly increasing exponentiation makes the comparison density nonnegative. -/
theorem gomesPolynomialSeparationDensity_nonneg (H K : ℝ[X]) (x : ℝ) :
    0 ≤ gomesPolynomialSeparationDensity H K x := by
  unfold gomesPolynomialSeparationDensity dilatonWeight
  rcases le_total (K.eval x) (H.eval x) with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.exp_le_exp.mpr h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.exp_le_exp.mpr h))

/-- The comparison vanishes at a point exactly when the two log-densities agree there. -/
theorem gomesPolynomialSeparationDensity_zero_iff (H K : ℝ[X]) (x : ℝ) :
    gomesPolynomialSeparationDensity H K x = 0 ↔ H.eval x = K.eval x := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with ha | hb
    · exact sub_eq_zero.mp ha
    · exact Real.exp_injective (sub_eq_zero.mp hb)
  · intro h
    simp only [gomesPolynomialSeparationDensity, h, sub_self, zero_mul]

/-- The comparison density is continuous for arbitrary real polynomials. -/
theorem gomesPolynomialSeparationDensity_continuous (H K : ℝ[X]) :
    Continuous (gomesPolynomialSeparationDensity H K) :=
  (H.continuous.sub K.continuous).mul
    ((gomesDilatonWeight_continuous H).sub (gomesDilatonWeight_continuous K))

/-- Swapping the compared profiles leaves the pointwise separation unchanged. -/
theorem gomesPolynomialSeparationDensity_symm (H K : ℝ[X]) :
    gomesPolynomialSeparationDensity H K = gomesPolynomialSeparationDensity K H := by
  funext x
  unfold gomesPolynomialSeparationDensity
  ring

/-- Both finite exponential tails control every term in the comparison density. -/
theorem gomesPolynomialSeparationDensity_integrable (P Q : GomesFinitePolynomialProfile) :
    Integrable (gomesPolynomialSeparationDensity P.val Q.val) := by
  have hp := gomesPolynomialAmplitude_integrable P (P.val - Q.val)
  have hq := gomesPolynomialAmplitude_integrable Q (P.val - Q.val)
  apply (hp.sub hq).congr (Eventually.of_forall (fun x => ?_))
  change (P.val - Q.val).eval x * Real.exp (P.val.eval x) -
      (P.val - Q.val).eval x * Real.exp (Q.val.eval x) = _
  simp only [eval_sub, gomesPolynomialSeparationDensity, dilatonWeight]
  ring

/-- The integrated monotonicity pairing is a finite real separation functional. -/
def gomesPolynomialSeparation (P Q : GomesFinitePolynomialProfile) : ℝ :=
  ∫ x : ℝ, gomesPolynomialSeparationDensity P.val Q.val x

/-- Separation is nonnegative for every pair in the finite tensor sector. -/
theorem gomesPolynomialSeparation_nonneg (P Q : GomesFinitePolynomialProfile) :
    0 ≤ gomesPolynomialSeparation P Q :=
  integral_nonneg (gomesPolynomialSeparationDensity_nonneg P.val Q.val)

/-- The integrated comparison detects equality of the full polynomial profile exactly. -/
theorem gomesPolynomialSeparation_zero_iff (P Q : GomesFinitePolynomialProfile) :
    gomesPolynomialSeparation P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg
      (gomesPolynomialSeparationDensity_nonneg P.val Q.val)
      (gomesPolynomialSeparationDensity_integrable P Q)).mp h
    have he : gomesPolynomialSeparationDensity P.val Q.val = 0 :=
      ((gomesPolynomialSeparationDensity_continuous P.val Q.val).ae_eq_iff_eq
        (μ := (volume : Measure ℝ)) continuous_const).mp hae
    apply Subtype.ext
    apply Polynomial.funext
    intro x
    exact (gomesPolynomialSeparationDensity_zero_iff P.val Q.val x).mp (congrFun he x)
  · rintro rfl
    unfold gomesPolynomialSeparation
    simp only [gomesPolynomialSeparationDensity, sub_self, zero_mul, integral_zero]

/-- Distinct finite profiles have a strictly positive separation. -/
theorem gomesPolynomialSeparation_pos_iff (P Q : GomesFinitePolynomialProfile) :
    0 < gomesPolynomialSeparation P Q ↔ P ≠ Q := by
  constructor
  · intro h he
    have hz := (gomesPolynomialSeparation_zero_iff P Q).mpr he
    rw [hz] at h
    exact (lt_irrefl 0) h
  · intro h
    have hz : gomesPolynomialSeparation P Q ≠ 0 :=
      fun hz => h ((gomesPolynomialSeparation_zero_iff P Q).mp hz)
    exact lt_of_le_of_ne (gomesPolynomialSeparation_nonneg P Q) hz.symm

/-- The integrated separation is symmetric. -/
theorem gomesPolynomialSeparation_symm (P Q : GomesFinitePolynomialProfile) :
    gomesPolynomialSeparation P Q = gomesPolynomialSeparation Q P := by
  unfold gomesPolynomialSeparation
  rw [gomesPolynomialSeparationDensity_symm]

end GaloisForLFunctions.HTGeometry
