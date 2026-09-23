import GaloisForLFunctions.HTGeometry.ClockTwoSpeciesConformalTime
import GaloisForLFunctions.HTGeometry.ClockSlabProbe
import GaloisForLFunctions.HTGeometry.ConfocalNullSupportFixedPoint
import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity

/-!
# Penrose compactification as an explicit conformal clock

The squared conformal factor in arXiv:2303.04638, equation (30), is the
product of two Cauchy factors in null coordinates. On the central worldline
it gives the smooth scale `4/(1+t²)²`. Its logarithm supplies a literal
instance of the corpus's conformal-time potential, including its geometric
defect and exact recovery from two calibrated species.
-/

open scoped ContDiff
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Squared conformal factor in the paper's two null coordinates. -/
def penroseScaleSq (u v : ℝ) : ℝ := 4 / ((1 + u ^ (2 : ℕ)) * (1 + v ^ (2 : ℕ)))

theorem penroseScaleSq_positive (u v : ℝ) : 0 < penroseScaleSq u v := by
  unfold penroseScaleSq
  positivity

/-- Compactification contracts the squared scale to at most four. -/
theorem penroseScaleSq_le_four (u v : ℝ) : penroseScaleSq u v ≤ 4 := by
  unfold penroseScaleSq
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg (sq_nonneg u) (sq_nonneg v)]

/-- The same factor compactifies the corpus's confocal Lorentz null coordinates. -/
theorem penroseScaleSq_confocal (q : ℝ × ℝ) :
    penroseScaleSq (HTGeometry.confocalNullMinus q) (HTGeometry.confocalNullPlus q) =
      4 / ((1 + (q.2 - q.1) ^ (2 : ℕ)) * (1 + (q.2 + q.1) ^ (2 : ℕ))) := rfl

/-- The factor is four times the Jacobian of the arctangent null-coordinate compactification. -/
theorem penroseScaleSq_arctan_jacobian (u v : ℝ) :
    penroseScaleSq u v = 4 * deriv Real.arctan u * deriv Real.arctan v := by
  rw [(Real.hasDerivAt_arctan u).deriv, (Real.hasDerivAt_arctan v).deriv]
  unfold penroseScaleSq
  field_simp

/-- The apparent eighth-degree denominator in equation (28) factors as a positive square. -/
theorem penrose_denominator_factorization (t r : ℝ) :
    r ^ (8 : ℕ) + t ^ (8 : ℕ) - 4 * (r ^ (2 : ℕ) - 1) * t ^ (6 : ℕ) + 4 * r ^ (6 : ℕ) +
      2 * (3 * r ^ (4 : ℕ) - 2 * r ^ (2 : ℕ) + 3) * t ^ (4 : ℕ) + 6 * r ^ (4 : ℕ) -
      4 * (r ^ (6 : ℕ) + r ^ (4 : ℕ) - r ^ (2 : ℕ) - 1) * t ^ (2 : ℕ) + 4 * r ^ (2 : ℕ) + 1 =
        ((1 + (t - r) ^ (2 : ℕ)) * (1 + (t + r) ^ (2 : ℕ))) ^ (2 : ℕ) := by
  ring

/-- Smooth logarithm of the scale factor on the central worldline. -/
def penroseLogScale (t : ℝ) : ℝ := Real.log 2 - Real.log (1 + t ^ (2 : ℕ))

theorem contDiff_penroseLogScale : ContDiff ℝ ∞ penroseLogScale := by
  unfold penroseLogScale
  exact contDiff_const.sub ((contDiff_const.add (contDiff_id.pow 2)).log
    (fun t => by positivity))

/-- The exponential chart scale is exactly the paper's central conformal factor squared. -/
theorem exp_two_penroseLogScale (t : ℝ) :
    Real.exp (2 * penroseLogScale t) = penroseScaleSq t t := by
  unfold penroseLogScale penroseScaleSq
  rw [mul_sub, Real.exp_sub, show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
    show 2 * Real.log (1 + t ^ (2 : ℕ)) = Real.log (1 + t ^ (2 : ℕ)) + Real.log (1 + t ^ (2 : ℕ)) by ring,
    Real.exp_add, Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < 2),
    Real.exp_log (by positivity : 0 < 1 + t ^ (2 : ℕ))]
  ring

/-- First derivative of the actual conformal exponent. -/
theorem hasDerivAt_penroseLogScale (t : ℝ) :
    HasDerivAt penroseLogScale (-2 * t / (1 + t ^ (2 : ℕ))) t := by
  have h := (hasDerivAt_const t (Real.log 2)).sub
    (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).log
      (by positivity : 1 + t ^ (2 : ℕ) ≠ 0))
  exact h.congr_deriv (by dsimp; ring)


/-- The second derivative is proved from the rational first derivative. -/
theorem hasDerivAt_deriv_penroseLogScale (t : ℝ) :
    HasDerivAt (deriv penroseLogScale) (2 * (t ^ (2 : ℕ) - 1) / (1 + t ^ (2 : ℕ)) ^ (2 : ℕ)) t := by
  have hd : deriv penroseLogScale = fun t => -2 * t / (1 + t ^ (2 : ℕ)) :=
    funext fun t => (hasDerivAt_penroseLogScale t).deriv
  rw [hd]
  have h := ((hasDerivAt_id t).const_mul (-2)).div
    ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2))
      (by positivity : 1 + t ^ (2 : ℕ) ≠ 0)
  exact h.congr_deriv (by dsimp; ring)


/-- Exact potential of every clock species and every conformal weight. -/
theorem conformalTimePotential_penrose (a massSq t : ℝ) :
    conformalTimePotential (-1) a massSq penroseLogScale t =
      (4 * massSq - 2 * a + (2 * a + 4 * a ^ (2 : ℕ)) * t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ)) ^ (2 : ℕ) := by
  unfold conformalTimePotential
  rw [exp_two_penroseLogScale, (hasDerivAt_penroseLogScale t).deriv,
    (hasDerivAt_deriv_penroseLogScale t).deriv]
  unfold penroseScaleSq
  field_simp
  ring

/-- Calibrated squared masses separated by one recover the exact compactification scale. -/
theorem penrose_two_species_reconstruction (a massSq t : ℝ) :
    conformalTimePotential (-1) a (massSq + 1) penroseLogScale t -
      conformalTimePotential (-1) a massSq penroseLogScale t = penroseScaleSq t t := by
  rw [conformalTimePotential_penrose, conformalTimePotential_penrose]
  unfold penroseScaleSq
  ring

/-- The massless four-dimensional potential changes sign at exactly `3 t² = 1`. -/
theorem penrose_massless_potential_nonnegative_iff (t : ℝ) :
    0 ≤ conformalTimePotential (-1) 1 0 penroseLogScale t ↔ 1 ≤ 3 * t ^ (2 : ℕ) := by
  rw [conformalTimePotential_penrose, le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The potential formula holds on the corpus's actual Lorentz metric chart in every dimension. -/
theorem penrose_actual_metric_chart (n : ℕ) (a massSq : ℝ) (x : Fin (n + 2) → ℝ) :
    (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.conformalPotential
      a massSq (timeLift penroseLogScale) x =
        (4 * massSq - 2 * a + (2 * a + 4 * a ^ (2 : ℕ)) * (x 0) ^ (2 : ℕ)) / (1 + (x 0) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  rw [conformalPotential_timeLift (slabEps n) (slabEps_ne_zero n)
    contDiff_penroseLogScale, slabEps_zero]
  norm_num only [inv_neg, inv_one]
  exact conformalTimePotential_penrose a massSq (x 0)

/-- Squared interval transport for an arbitrary four-metric under the paper's conformal scale. -/
theorem penrose_clock_interval (u v : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    clockSquaredInterval4 (penroseScaleSq u v • g) z =
      penroseScaleSq u v * clockSquaredInterval4 g z := by
  simp [clockSquaredInterval4, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Every null direction, for every four-metric, survives the explicit compactification. -/
theorem penrose_clock_null_iff (u v : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    clockSquaredInterval4 (penroseScaleSq u v • g) z = 0 ↔ clockSquaredInterval4 g z = 0 := by
  rw [penrose_clock_interval, mul_eq_zero]
  simp [(penroseScaleSq_positive u v).ne']

/-- The signs of all clock intervals are also preserved. -/
theorem penrose_clock_timelike_iff (u v : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    clockSquaredInterval4 (penroseScaleSq u v • g) z < 0 ↔ clockSquaredInterval4 g z < 0 := by
  rw [penrose_clock_interval]
  have hp := penroseScaleSq_positive u v
  constructor
  · intro h
    by_contra hn
    have hz := le_of_not_gt hn
    have hprod := mul_nonneg hp.le hz
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hp h

end GaloisForLFunctions.HTGeometry
