import GaloisForLFunctions.HTGeometry.RadialPolynomialCorrection
import GaloisForLFunctions.HTGeometry.EinastoRadialGravity
import GaloisForLFunctions.HTGeometry.BurkertRadialGravity

/-!
# Exact radial density response to polynomial metric corrections

Apply the regular inverse of arXiv:2608.23600, equation (15), to the corpus's
polynomial, Einasto and Burkert radial metrics. The actual derivative in the
Einstein density changes by exactly minus the inserted source. This statement
is exact for this affine density operator, without a perturbative remainder.
The curvature functional uses the Ricci convention printed in equation (9).
-/
noncomputable section
open Polynomial Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Equation (13), as a functional of the actual radial metric. -/
def radialEinsteinDensity (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 - f r - r * deriv f r) / (8 * Real.pi * r ^ 2)

/-- Equation (9), including the actual first and second derivatives. -/
def radialRicciScalar (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r ^ 2 * deriv (deriv f) r + 4 * r * deriv f r + 2 * f r - 2) / r ^ 2

/-- Insert the constructed regular correction into an existing radial metric. -/
def radialCorrectedMetric (f : ℝ → ℝ) (P : ℝ[X]) (β r : ℝ) : ℝ :=
  f r + β * (radialPolynomialCorrection P).eval r

theorem radialPolynomialCorrection_derivative_balance (P : ℝ[X]) (r : ℝ) :
    (radialPolynomialCorrection P).eval r +
      r * deriv (fun s => (radialPolynomialCorrection P).eval s) r =
        8 * Real.pi * r ^ 2 * P.eval r := by
  rw [((radialPolynomialCorrection P).hasDerivAt r).deriv]
  have h := congrArg (fun Q : ℝ[X] => Q.eval r) (radialPolynomialCorrection_equation P)
  simpa only [radialPolynomialOperator, radialPolynomialSource, eval_add, eval_mul,
    eval_C, eval_X, eval_pow, mul_assoc] using h

/-- Exact cancellation of the density source on every polynomial background. -/
theorem radialPolynomialMetric_density_response (B P : ℝ[X]) (β t : ℝ) :
    radialEinsteinDensity (radialCorrectedMetric (fun r => B.eval r) P β) (Real.exp t) =
      radialEinsteinDensity (fun r => B.eval r) (Real.exp t) - β * P.eval (Real.exp t) := by
  have hd := (B.hasDerivAt (Real.exp t)).add
    (((radialPolynomialCorrection P).hasDerivAt (Real.exp t)).const_mul β)
  simp only [Pi.add_def] at hd
  have hb := radialPolynomialCorrection_derivative_balance P (Real.exp t)
  rw [((radialPolynomialCorrection P).hasDerivAt (Real.exp t)).deriv] at hb
  unfold radialEinsteinDensity radialCorrectedMetric
  rw [hd.deriv, (B.hasDerivAt (Real.exp t)).deriv]
  field_simp
  linear_combination -β * hb

/-- The existing Einasto metric has precisely the supplied halo density. -/
theorem radialEinsteinDensity_einasto (d l a t : ℝ) :
    radialEinsteinDensity (einastoMetric d l a) (Real.exp t) =
      einastoDensity d l a (Real.exp t) := by
  unfold radialEinsteinDensity
  rw [einastoMetric_radial_Einstein_law]
  field_simp

/-- Polynomial correction sources cancel exactly on every Einasto background. -/
theorem einastoPolynomialCorrection_density (d l a β t : ℝ) (P : ℝ[X]) :
    radialEinsteinDensity (radialCorrectedMetric (einastoMetric d l a) P β) (Real.exp t) =
      einastoDensity d l a (Real.exp t) - β * P.eval (Real.exp t) := by
  have hd := (einastoMetric_derivative d l a t).add
    (((radialPolynomialCorrection P).hasDerivAt (Real.exp t)).const_mul β)
  simp only [Pi.add_def] at hd
  have hb := radialPolynomialCorrection_derivative_balance P (Real.exp t)
  rw [((radialPolynomialCorrection P).hasDerivAt (Real.exp t)).deriv] at hb
  have he := einastoMetric_radial_Einstein_law d l a t
  rw [(einastoMetric_derivative d l a t).deriv] at he
  unfold radialEinsteinDensity radialCorrectedMetric
  rw [hd.deriv]
  apply (div_eq_iff (by positivity : 8 * Real.pi * Real.exp t ^ 2 ≠ 0)).mpr
  linear_combination he - β * hb

/-- The corrected Einasto center remains normalized for every polynomial source. -/
theorem einastoPolynomialCorrection_center (d l a β : ℝ) (P : ℝ[X]) :
    radialCorrectedMetric (einastoMetric d l a) P β 0 = 1 := by
  simp [radialCorrectedMetric, radialPolynomialCorrection_zero, einastoMetric]

/-- The existing scaled Burkert metric also realizes its actual density. -/
theorem radialEinsteinDensity_burkert (d l t : ℝ) :
    radialEinsteinDensity (scaledBurkertMetric d l) (Real.exp t) =
      Real.exp d * burkertDensity (Real.exp t / Real.exp l) := by
  unfold radialEinsteinDensity
  rw [scaledBurkertMetric_radial_Einstein_law]
  field_simp

/-- The same regular inverse works without change on every scaled Burkert background. -/
theorem burkertPolynomialCorrection_density (d l β t : ℝ) (P : ℝ[X]) :
    radialEinsteinDensity (radialCorrectedMetric (scaledBurkertMetric d l) P β) (Real.exp t) =
      Real.exp d * burkertDensity (Real.exp t / Real.exp l) - β * P.eval (Real.exp t) := by
  have hd := (scaledBurkertMetric_derivative d l t).add
    (((radialPolynomialCorrection P).hasDerivAt (Real.exp t)).const_mul β)
  simp only [Pi.add_def] at hd
  have hb := radialPolynomialCorrection_derivative_balance P (Real.exp t)
  rw [((radialPolynomialCorrection P).hasDerivAt (Real.exp t)).deriv] at hb
  have he := scaledBurkertMetric_radial_Einstein_law d l t
  rw [(scaledBurkertMetric_derivative d l t).deriv] at he
  unfold radialEinsteinDensity radialCorrectedMetric
  rw [hd.deriv]
  apply (div_eq_iff (by positivity : 8 * Real.pi * Real.exp t ^ 2 ≠ 0)).mpr
  linear_combination he - β * hb

theorem burkertPolynomialCorrection_center (d l β : ℝ) (P : ℝ[X]) :
    radialCorrectedMetric (scaledBurkertMetric d l) P β 0 = 1 := by
  simp [radialCorrectedMetric, radialPolynomialCorrection_zero, scaledBurkertMetric]

/-- Constant-curvature core metric in the convention used by the paper. -/
def quadraticCoreMetric (c r : ℝ) : ℝ := 1 - c * r ^ 2

theorem quadraticCoreMetric_hasDerivAt (c r : ℝ) :
    HasDerivAt (quadraticCoreMetric c) (-2 * c * r) r := by
  have h := (((hasDerivAt_id r).pow 2).const_mul c).const_sub 1
  apply h.congr_deriv
  simp only [id_eq, Nat.cast_ofNat]
  ring

theorem quadraticCoreMetric_derivative (c : ℝ) :
    deriv (quadraticCoreMetric c) = fun r => -2 * c * r := by
  funext r
  exact (quadraticCoreMetric_hasDerivAt c r).deriv

theorem quadraticCoreMetric_second_derivative (c : ℝ) :
    deriv (deriv (quadraticCoreMetric c)) = fun _ => -2 * c := by
  rw [quadraticCoreMetric_derivative]
  funext r
  simp

/-- Actual differentiation gives the paper's signed constant scalar curvature. -/
theorem quadraticCoreMetric_ricci (c t : ℝ) :
    radialRicciScalar (quadraticCoreMetric c) (Real.exp t) = -12 * c := by
  unfold radialRicciScalar
  rw [quadraticCoreMetric_second_derivative, quadraticCoreMetric_derivative]
  unfold quadraticCoreMetric
  field_simp
  ring

/-- The core Einstein density fixes the mixed tt component to minus R/4. -/
theorem quadraticCoreMetric_density (c t : ℝ) :
    radialEinsteinDensity (quadraticCoreMetric c) (Real.exp t) = 3 * c / (8 * Real.pi) := by
  unfold radialEinsteinDensity
  rw [quadraticCoreMetric_derivative]
  unfold quadraticCoreMetric
  field_simp
  ring

/-- The constructed constant-source inverse is exactly another quadratic core. -/
theorem quadraticCoreMetric_correction (c q β : ℝ) :
    radialCorrectedMetric (quadraticCoreMetric c) (C q) β =
      quadraticCoreMetric (c - β * (8 * Real.pi * q / 3)) := by
  funext r
  unfold radialCorrectedMetric
  rw [radialPolynomialCorrection_constant]
  simp only [eval_mul, eval_C, eval_pow, eval_X, quadraticCoreMetric]
  ring

/-- Exact curvature shift caused by the regular integral inverse of a constant source. -/
theorem quadraticCoreMetric_correction_ricci (c q β t : ℝ) :
    radialRicciScalar (radialCorrectedMetric (quadraticCoreMetric c) (C q) β) (Real.exp t) =
      -12 * c + 32 * Real.pi * β * q := by
  rw [quadraticCoreMetric_correction, quadraticCoreMetric_ricci]
  ring

end GaloisForLFunctions.HTGeometry
