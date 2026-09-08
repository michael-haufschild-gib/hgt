import GaloisForLFunctions.HTGeometry.PolynomialRadialCurvature
import GaloisForLFunctions.HTGeometry.RadialPolynomialCorrection

/-!
# Exact regularity classification for polynomial radial pole sources

Apply the paper's radial inverse to E₁(r)=P(r)/r for every real polynomial P.
The unique polynomial metric correction splits into a linear residue term and
the already formalized regular inverse of P.divX. This converts the curvature
obstruction into a positive, sharp replacement rule: at nonzero coupling, finite
central Kretschmann curvature holds exactly when the source residue P(0)
vanishes. Its finite value is then fixed by the next source coefficient.
-/
noncomputable section
open Polynomial Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Exact pole-source inverse, reusing the regular polynomial inverse. -/
def radialPolePolynomialCorrection (P : ℝ[X]) : ℝ[X] :=
  C (4 * Real.pi * P.coeff 0) * X + radialPolynomialCorrection P.divX

/-- The regular quadratic factor after removing the pole residue. -/
def radialPolePolynomialCore (P : ℝ[X]) : ℝ[X] := (radialPolynomialCorrection P.divX).divX.divX

/-- The metric induced by the polynomial source at unrestricted coupling. -/
def radialPolePolynomialMetric (P : ℝ[X]) (β r : ℝ) : ℝ :=
  1 + β * (radialPolePolynomialCorrection P).eval r

/-- The exact polynomial radial equation for a source with at most a simple pole. -/
theorem radialPolePolynomialCorrection_equation (P : ℝ[X]) :
    radialPolynomialOperator (radialPolePolynomialCorrection P) = C (8 * Real.pi) * X * P := by
  have h := radialPolynomialCorrection_equation P.divX
  unfold radialPolynomialOperator radialPolynomialSource at h
  have hc : C (8 * Real.pi * P.coeff 0) = C (4 * Real.pi * P.coeff 0) + C (4 * Real.pi * P.coeff 0) := by
    rw [← map_add]
    congr 1
    ring
  unfold radialPolePolynomialCorrection radialPolynomialOperator
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, mul_one]
  calc
    _ = (C (4 * Real.pi * P.coeff 0) + C (4 * Real.pi * P.coeff 0)) * X +
        (radialPolynomialCorrection P.divX + X * (radialPolynomialCorrection P.divX).derivative) := by ring
    _ = C (8 * Real.pi * P.coeff 0) * X + C (8 * Real.pi) * (X ^ 2 * P.divX) := by rw [← hc, h]
    _ = C (8 * Real.pi) * X * (X * P.divX + C (P.coeff 0)) := by
      simp only [map_mul]
      ring
    _ = C (8 * Real.pi) * X * P := congrArg (fun Q : ℝ[X] => C (8 * Real.pi) * X * Q) (X_mul_divX_add P)

/-- Full polynomial solution classification; no proposed equation is assumed as a premise. -/
theorem radialPolePolynomialCorrection_unique (P H : ℝ[X]) :
    radialPolynomialOperator H = C (8 * Real.pi) * X * P ↔ H = radialPolePolynomialCorrection P := by
  constructor
  · intro h
    exact radialPolynomialOperator_injective (h.trans (radialPolePolynomialCorrection_equation P).symm)
  · rintro rfl
    exact radialPolePolynomialCorrection_equation P

theorem radialPolePolynomialCorrection_center (P : ℝ[X]) : (radialPolePolynomialCorrection P).eval 0 = 0 := by
  simp only [radialPolePolynomialCorrection, eval_add, eval_mul, eval_C, eval_X,
    radialPolynomialCorrection_zero, mul_zero, add_zero]

/-- The residue determines the entire linear metric coefficient. -/
theorem radialPolePolynomialCorrection_linear_coeff (P : ℝ[X]) :
    (radialPolePolynomialCorrection P).coeff 1 = 4 * Real.pi * P.coeff 0 := by
  simp [radialPolePolynomialCorrection, radialPolynomialCorrection_coeff_one]

/-- The next source coefficient determines the finite core invariant. -/
theorem radialPolePolynomialCore_center (P : ℝ[X]) :
    (radialPolePolynomialCore P).eval 0 = 8 * Real.pi * P.coeff 1 / 3 := by
  rw [radialPolePolynomialCore, radialPolynomialCorrection_normalized_core, ← coeff_zero_eq_eval_zero,
    coeff_divX, zero_add]

/-- Actual differential equation, obtained from the polynomial operator identity. -/
theorem radialPolePolynomialCorrection_hasDerivAt (P : ℝ[X]) (r : ℝ) :
    HasDerivAt (fun s => s * (radialPolePolynomialCorrection P).eval s) (8 * Real.pi * r * P.eval r) r := by
  have h := congrArg (fun Q : ℝ[X] => Q.eval r) (radialPolePolynomialCorrection_equation P)
  simp only [radialPolynomialOperator, eval_add, eval_mul, eval_C, eval_X] at h
  have hd := (hasDerivAt_id r).mul ((radialPolePolynomialCorrection P).hasDerivAt r)
  apply hd.congr_deriv
  simpa only [id_eq, one_mul] using h

/-- The same correction is the literal anchored radial integral. -/
theorem radialPolePolynomialCorrection_primitive (P : ℝ[X]) (r : ℝ) :
    r * (radialPolePolynomialCorrection P).eval r = ∫ s in 0..r, 8 * Real.pi * s * P.eval s := by
  have hc : Continuous (fun s : ℝ => 8 * Real.pi * s * P.eval s) :=
    (continuous_const.mul continuous_id).mul P.continuous
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => radialPolePolynomialCorrection_hasDerivAt P s) (hc.intervalIntegrable 0 r)
  simpa only [zero_mul, sub_zero] using h.symm

theorem radialPolePolynomialCorrection_integral (P : ℝ[X]) (r : ℝ) :
    (radialPolePolynomialCorrection P).eval r = (∫ s in 0..r, 8 * Real.pi * s * P.eval s) / r := by
  by_cases hr : r = 0
  · subst r
    simp only [radialPolePolynomialCorrection_center, intervalIntegral.integral_same, zero_div]
  · apply (eq_div_iff hr).mpr
    simpa only [mul_comm] using radialPolePolynomialCorrection_primitive P r

/-- Exact bridge to the complete polynomial curvature classification. -/
theorem radialPolePolynomialMetric_decomposition (P : ℝ[X]) (β : ℝ) :
    radialPolePolynomialMetric P β =
      polynomialRadialCoreMetric (4 * Real.pi * β * P.coeff 0) (C β * radialPolePolynomialCore P) := by
  funext r
  have h := congrArg (fun Q : ℝ[X] => Q.eval r) (radialPolynomialCorrection_quadratic_factor P.divX)
  simp only [eval_mul, eval_pow, eval_X] at h
  unfold radialPolePolynomialMetric radialPolePolynomialCorrection polynomialRadialCoreMetric
  simp only [eval_add, eval_mul, eval_C, eval_X]
  rw [h]
  unfold radialPolePolynomialCore
  ring

/-- Complete finite-curvature criterion and the exact surviving value, including zero coupling. -/
theorem radialPolePolynomialMetric_finite_limit_iff (P : ℝ[X]) (β k : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (radialPolePolynomialMetric P β) (exp t)) atBot (𝓝 k) ↔
      β * P.coeff 0 = 0 ∧ k = 512 * Real.pi ^ 2 * β ^ 2 * P.coeff 1 ^ 2 / 3 := by
  rw [radialPolePolynomialMetric_decomposition, polynomialRadialCoreMetric_finite_limit_iff,
    eval_mul, eval_C, radialPolePolynomialCore_center]
  have ha : 4 * Real.pi * β * P.coeff 0 = 0 ↔ β * P.coeff 0 = 0 := by
    simp only [mul_eq_zero, show (4 : ℝ) ≠ 0 by norm_num, Real.pi_ne_zero, false_or]
  have hk : 24 * (β * (8 * Real.pi * P.coeff 1 / 3)) ^ 2 =
      512 * Real.pi ^ 2 * β ^ 2 * P.coeff 1 ^ 2 / 3 := by ring
  rw [ha, hk]

/-- At positive coupling, exactly the removable source poles give finite central curvature. -/
theorem radialPolePolynomialMetric_regular_iff (P : ℝ[X]) (b : ℝ) :
    (∃ k : ℝ, Tendsto (fun t => radialKretschmannScalar (radialPolePolynomialMetric P (exp b)) (exp t)) atBot (𝓝 k)) ↔
      P.eval 0 = 0 := by
  simp only [radialPolePolynomialMetric_finite_limit_iff, mul_eq_zero, exp_ne_zero,
    false_or, coeff_zero_eq_eval_zero]
  constructor
  · rintro ⟨k, hk, _⟩
    exact hk
  · intro h
    exact ⟨512 * Real.pi ^ 2 * exp b ^ 2 * P.coeff 1 ^ 2 / 3, h, rfl⟩

/-- Every nonremovable source pole instead gives divergent curvature at positive coupling. -/
theorem radialPolePolynomialMetric_diverges_iff (P : ℝ[X]) (b : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (radialPolePolynomialMetric P (exp b)) (exp t)) atBot atTop ↔
      P.eval 0 ≠ 0 := by
  rw [radialPolePolynomialMetric_decomposition, polynomialRadialCoreMetric_diverges_iff]
  simp only [ne_eq, mul_eq_zero, show (4 : ℝ) ≠ 0 by norm_num, Real.pi_ne_zero, exp_ne_zero,
    false_or, coeff_zero_eq_eval_zero]

end GaloisForLFunctions.HTGeometry
