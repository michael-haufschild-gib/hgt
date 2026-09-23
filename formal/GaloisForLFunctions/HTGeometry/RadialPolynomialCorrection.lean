import GaloisForLFunctions.HTGeometry.PolynomialSmoothApproximation
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# The regular radial curvature-correction inverse on polynomial sources

Equation (15) of arXiv:2608.23600 is inverted using the corpus's exact
polynomial antiderivative. The constructed correction solves (r h)'=8πr²P,
is regular at the origin, and is uniquely determined among all polynomial
solutions. The arbitrary integration constant produces the excluded C/r mode.
All polynomial and scalar parameters are unrestricted data.
-/
noncomputable section
open Polynomial Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The weighted source in the radial first-order equation. -/
def radialPolynomialSource (P : ℝ[X]) : ℝ[X] := C (8 * Real.pi) * (X ^ (2 : ℕ) * P)

/-- Reuse the existing anchored antiderivative at the regular center. -/
def radialPolynomialPrimitive (P : ℝ[X]) : ℝ[X] :=
  anchoredRealAntiderivative (radialPolynomialSource P) 0 0

/-- Polynomial division by X removes the center zero of the exact primitive. -/
def radialPolynomialCorrection (P : ℝ[X]) : ℝ[X] := (radialPolynomialPrimitive P).divX

/-- Polynomial radial differential operator. -/
def radialPolynomialOperator (H : ℝ[X]) : ℝ[X] := H + X * H.derivative

theorem radialPolynomialPrimitive_zero (P : ℝ[X]) : (radialPolynomialPrimitive P).eval 0 = 0 := by
  exact eval_anchoredRealAntiderivative_anchor _ _ _

theorem radialPolynomialPrimitive_derivative (P : ℝ[X]) :
    (radialPolynomialPrimitive P).derivative = radialPolynomialSource P :=
  derivative_anchoredRealAntiderivative _ _ _

theorem radialPolynomialCorrection_primitive (P : ℝ[X]) :
    X * radialPolynomialCorrection P = radialPolynomialPrimitive P := by
  have h := X_mul_divX_add (radialPolynomialPrimitive P)
  rw [coeff_zero_eq_eval_zero, radialPolynomialPrimitive_zero, C_0, add_zero] at h
  exact h

/-- The radial inverse is an exact polynomial identity, including the origin. -/
theorem radialPolynomialCorrection_equation (P : ℝ[X]) :
    radialPolynomialOperator (radialPolynomialCorrection P) = radialPolynomialSource P := by
  have h := congrArg Polynomial.derivative (radialPolynomialCorrection_primitive P)
  simpa only [derivative_mul, derivative_X, one_mul, radialPolynomialPrimitive_derivative,
    radialPolynomialOperator] using h

/-- No nonzero polynomial belongs to the homogeneous radial kernel. -/
theorem radialPolynomialOperator_injective : Function.Injective radialPolynomialOperator := by
  intro A B h
  have hz : (X * (A - B)).derivative = 0 := by
    have he : (X * (A - B)).derivative = radialPolynomialOperator A - radialPolynomialOperator B := by
      simp only [derivative_mul, derivative_X, derivative_sub, one_mul, radialPolynomialOperator]
      ring
    rw [he, h, sub_self]
  have hc := Polynomial.eq_C_of_derivative_eq_zero hz
  rw [coeff_X_mul_zero, C_0] at hc
  have hab : A - B = 0 := (mul_eq_zero.mp hc).resolve_left X_ne_zero
  exact sub_eq_zero.mp hab

/-- Complete polynomial solution classification, without a supplied equation hypothesis. -/
theorem radialPolynomialCorrection_unique (P H : ℝ[X]) :
    radialPolynomialOperator H = radialPolynomialSource P ↔ H = radialPolynomialCorrection P := by
  constructor
  · intro h
    exact radialPolynomialOperator_injective (h.trans (radialPolynomialCorrection_equation P).symm)
  · rintro rfl
    exact radialPolynomialCorrection_equation P

theorem radialPolynomialCorrection_zero (P : ℝ[X]) : (radialPolynomialCorrection P).eval 0 = 0 := by
  have h := congrArg (fun Q : ℝ[X] => Q.eval 0) (radialPolynomialCorrection_equation P)
  simpa [radialPolynomialOperator, radialPolynomialSource] using h

theorem radialPolynomialCorrection_coeff_zero (P : ℝ[X]) : (radialPolynomialCorrection P).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, radialPolynomialCorrection_zero]

theorem radialPolynomialCorrection_coeff_one (P : ℝ[X]) : (radialPolynomialCorrection P).coeff 1 = 0 := by
  have h := congrArg (fun Q : ℝ[X] => Q.coeff 1) (radialPolynomialCorrection_equation P)
  have hs : radialPolynomialSource P = C (8 * Real.pi) * (X * (X * P)) := by
    unfold radialPolynomialSource
    ring
  rw [hs] at h
  simp only [radialPolynomialOperator, coeff_add, coeff_X_mul, coeff_derivative,
    coeff_C_mul, coeff_X_mul_zero] at h
  norm_num at h
  linarith

/-- Each source coefficient is shifted up two orders and divided by its exact radial weight. -/
theorem radialPolynomialCorrection_coeff (P : ℝ[X]) (n : ℕ) :
    (radialPolynomialCorrection P).coeff (n + 2) = 8 * Real.pi * P.coeff n / (n + 3 : ℝ) := by
  have h := congrArg (fun Q : ℝ[X] => Q.coeff (n + 2)) (radialPolynomialPrimitive_derivative P)
  simp only [coeff_derivative, radialPolynomialSource, coeff_C_mul, coeff_X_pow_mul] at h
  rw [radialPolynomialCorrection, coeff_divX]
  apply (eq_div_iff (by positivity : (n + 3 : ℝ) ≠ 0)).mpr
  convert h using 1
  push_cast
  ring

/-- The exact primitive is the actual interval integral from the regular center. -/
theorem radialPolynomialCorrection_integral_balance (P : ℝ[X]) (r : ℝ) :
    r * (radialPolynomialCorrection P).eval r = ∫ s in 0..r, 8 * Real.pi * s ^ (2 : ℕ) * P.eval s := by
  have h := congrArg (fun Q : ℝ[X] => Q.eval r) (radialPolynomialCorrection_primitive P)
  rw [eval_mul, eval_X, radialPolynomialPrimitive,
    eval_anchoredRealAntiderivative_eq_add_integral] at h
  simpa only [zero_add, radialPolynomialSource, eval_mul, eval_C, eval_pow, eval_X, mul_assoc] using h

/-- Equation (15) holds at every radius; the polynomial gives the regular value at zero. -/
theorem radialPolynomialCorrection_integral (P : ℝ[X]) (r : ℝ) :
    (radialPolynomialCorrection P).eval r = (∫ s in 0..r, 8 * Real.pi * s ^ (2 : ℕ) * P.eval s) / r := by
  by_cases hr : r = 0
  · subst r
    simp only [radialPolynomialCorrection_zero, intervalIntegral.integral_same, zero_div]
  · apply (eq_div_iff hr).mpr
    simpa only [mul_comm] using radialPolynomialCorrection_integral_balance P r

/-- The constructed correction satisfies the actual differential equation. -/
theorem radialPolynomialCorrection_hasDerivAt (P : ℝ[X]) (r : ℝ) :
    HasDerivAt (fun s => s * (radialPolynomialCorrection P).eval s) (8 * Real.pi * r ^ (2 : ℕ) * P.eval r) r := by
  have h := congrArg (fun Q : ℝ[X] => Q.eval r) (radialPolynomialCorrection_equation P)
  simp only [radialPolynomialOperator, radialPolynomialSource, eval_add, eval_mul, eval_X, eval_C, eval_pow] at h
  have hd := (hasDerivAt_id r).mul ((radialPolynomialCorrection P).hasDerivAt r)
  apply hd.congr_deriv
  simpa only [id_eq, one_mul, mul_assoc] using h

/-- The regular correction starts at quadratic order, exactly. -/
theorem radialPolynomialCorrection_quadratic_factor (P : ℝ[X]) :
    radialPolynomialCorrection P = X ^ (2 : ℕ) * (radialPolynomialCorrection P).divX.divX := by
  have h0 := X_mul_divX_add (radialPolynomialCorrection P)
  rw [radialPolynomialCorrection_coeff_zero, C_0, add_zero] at h0
  have h1 := X_mul_divX_add (radialPolynomialCorrection P).divX
  rw [coeff_divX, zero_add, radialPolynomialCorrection_coeff_one, C_0, add_zero] at h1
  calc
    radialPolynomialCorrection P = X * (radialPolynomialCorrection P).divX := h0.symm
    _ = X * (X * (radialPolynomialCorrection P).divX.divX) := congrArg (fun Q : ℝ[X] => X * Q) h1.symm
    _ = X ^ (2 : ℕ) * (radialPolynomialCorrection P).divX.divX := by ring

theorem radialPolynomialCorrection_normalized_core (P : ℝ[X]) :
    (radialPolynomialCorrection P).divX.divX.eval 0 = 8 * Real.pi * P.eval 0 / 3 := by
  rw [← coeff_zero_eq_eval_zero, coeff_divX, coeff_divX]
  simpa only [zero_add, Nat.cast_zero, coeff_zero_eq_eval_zero] using radialPolynomialCorrection_coeff P 0

/-- Analytic regularity of the primitive is inherited by the exact polynomial inverse. -/
theorem radialPolynomialCorrection_contDiff (P : ℝ[X]) :
    ContDiff ℝ ⊤ (fun r => (radialPolynomialCorrection P).eval r) := by
  simpa using (radialPolynomialCorrection P).contDiff_aeval (𝕜 := ℝ) ⊤

/-- The origin derivative vanishes as required for a smooth metric correction. -/
theorem radialPolynomialCorrection_derivative_zero (P : ℝ[X]) :
    deriv (fun r => (radialPolynomialCorrection P).eval r) 0 = 0 := by
  rw [((radialPolynomialCorrection P).hasDerivAt 0).deriv, ← coeff_zero_eq_eval_zero,
    coeff_derivative, zero_add, radialPolynomialCorrection_coeff_one, zero_mul]


/-- Exact normalized quadratic core limit along every positive radial approach. -/
theorem radialPolynomialCorrection_core_limit (P : ℝ[X]) :
    Tendsto (fun t => (radialPolynomialCorrection P).eval (Real.exp t) / Real.exp t ^ (2 : ℕ)) atBot
      (𝓝 (8 * Real.pi * P.eval 0 / 3)) := by
  have he : (fun t => (radialPolynomialCorrection P).eval (Real.exp t) / Real.exp t ^ (2 : ℕ)) =
      (fun t => (radialPolynomialCorrection P).divX.divX.eval (Real.exp t)) := by
    funext t
    have h := congrArg (fun Q : ℝ[X] => Q.eval (Real.exp t))
      (radialPolynomialCorrection_quadratic_factor P)
    simp only [eval_mul, eval_pow, eval_X] at h
    rw [h]
    field_simp
  rw [he, ← radialPolynomialCorrection_normalized_core]
  exact ((radialPolynomialCorrection P).divX.divX.continuous.continuousAt.tendsto).comp Real.tendsto_exp_atBot

/-- A constant curvature source produces a purely quadratic metric correction. -/
theorem radialPolynomialCorrection_constant (c : ℝ) :
    radialPolynomialCorrection (C c) = C (8 * Real.pi * c / 3) * X ^ (2 : ℕ) := by
  ext n
  cases n with
  | zero => simp only [radialPolynomialCorrection_coeff_zero, coeff_C_mul, coeff_X_pow, OfNat.zero_ne_ofNat, if_false, mul_zero]
  | succ n =>
    cases n with
    | zero => simpa only [Nat.zero_add] using (show (radialPolynomialCorrection (C c)).coeff 1 = (C (8 * Real.pi * c / 3) * X ^ (2 : ℕ)).coeff 1 by simp [radialPolynomialCorrection_coeff_one])
    | succ n =>
      change (radialPolynomialCorrection (C c)).coeff (n + 2) = (C (8 * Real.pi * c / 3) * X ^ (2 : ℕ)).coeff (n + 2)
      rw [radialPolynomialCorrection_coeff]
      by_cases hn : n = 0
      · subst n
        norm_num
      · simp [coeff_C, hn]

/-- Full integration-constant family away from the center. -/
def radialPolynomialCorrectionFamily (P : ℝ[X]) (c r : ℝ) : ℝ :=
  (radialPolynomialCorrection P).eval r + c / r

/-- Every integration constant solves the same radial equation at every positive radius. -/
theorem radialPolynomialCorrectionFamily_equation (P : ℝ[X]) (c t : ℝ) :
    HasDerivAt (fun r => r * radialPolynomialCorrectionFamily P c r)
      (8 * Real.pi * Real.exp t ^ (2 : ℕ) * P.eval (Real.exp t)) (Real.exp t) := by
  have he : (fun r => r * radialPolynomialCorrectionFamily P c r) =ᶠ[𝓝 (Real.exp t)]
      (fun r => r * (radialPolynomialCorrection P).eval r + c) := by
    filter_upwards [eventually_gt_nhds (Real.exp_pos t)] with r hr
    unfold radialPolynomialCorrectionFamily
    field_simp [hr.ne']
  exact ((radialPolynomialCorrection_hasDerivAt P (Real.exp t)).add_const c).congr_of_eventuallyEq he

/-- The integration constant is exactly the coefficient of the singular 1/r mode. -/
theorem radialPolynomialCorrectionFamily_singular_coefficient (P : ℝ[X]) (c : ℝ) :
    Tendsto (fun t => Real.exp t * radialPolynomialCorrectionFamily P c (Real.exp t)) atBot (𝓝 c) := by
  have he : (fun t => Real.exp t * radialPolynomialCorrectionFamily P c (Real.exp t)) =
      (fun t => Real.exp t * (radialPolynomialCorrection P).eval (Real.exp t) + c) := by
    funext t
    unfold radialPolynomialCorrectionFamily
    field_simp
  rw [he]
  have hh := (radialPolynomialCorrection P).continuous.continuousAt.tendsto.comp Real.tendsto_exp_atBot
  simpa only [zero_mul, zero_add, Function.comp_apply] using (Real.tendsto_exp_atBot.mul hh).add_const c

/-- Regularity forces precisely the zero integration constant; no singular mode survives. -/
theorem radialPolynomialCorrectionFamily_regular_iff (P : ℝ[X]) (c : ℝ) :
    ContinuousAt (radialPolynomialCorrectionFamily P c) 0 ↔ c = 0 := by
  constructor
  · intro hc
    have h := Real.tendsto_exp_atBot.mul (hc.tendsto.comp Real.tendsto_exp_atBot)
    simp only [zero_mul] at h
    exact (tendsto_nhds_unique (radialPolynomialCorrectionFamily_singular_coefficient P c) h)
  · rintro rfl
    unfold radialPolynomialCorrectionFamily
    simp only [zero_div, add_zero]
    exact (radialPolynomialCorrection P).continuous.continuousAt

end GaloisForLFunctions.HTGeometry
