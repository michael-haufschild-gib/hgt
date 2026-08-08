/-
# The argument principle for the regularized determinant of a matrix

The regularized determinant of a finite matrix is the Schur product `∏ᵢ (1 + z tᵢ)e^{−z tᵢ}`, so
its logarithmic derivative is `∑ᵢ (tᵢ/(1 + z tᵢ) − tᵢ)` and the contour integral splits factor by
factor: the constant terms integrate to zero, and `tᵢ/(1 + z tᵢ) = (z − (−1/tᵢ))⁻¹` contributes
`2πi` exactly when `−1/tᵢ` lies inside the circle.

Main results:
* `logDeriv_schurFactor`, `logDeriv_finiteDet2` — the logarithmic derivative, factor by factor.
* `circleIntegral_schurFactor_inside`, `circleIntegral_schurFactor_outside` — each factor's
  contribution to the contour integral.
-/
import GaloisForLFunctions.HTGeometry.FiniteDeterminantZeros
import GaloisForLFunctions.HTGeometry.ArgumentPrincipleSingleZero
import Mathlib.Analysis.Calculus.LogDeriv

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset Complex Metric

/-- The logarithmic derivative of one Schur factor. -/
theorem logDeriv_schurFactor (t : ℂ) {z : ℂ} (hz : 1 + z * t ≠ 0) :
    logDeriv (fun w : ℂ => (1 + w * t) * Complex.exp (-(w * t))) z = t / (1 + z * t) - t := by
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => 1 + w * t) z := by fun_prop
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(w * t))) z := by fun_prop
  have hgz : Complex.exp (-(z * t)) ≠ 0 := Complex.exp_ne_zero _
  have hmul := logDeriv_mul (f := fun w : ℂ => 1 + w * t)
    (g := fun w : ℂ => Complex.exp (-(w * t))) z hz hgz hd1 hd2
  have h1 : logDeriv (fun w : ℂ => 1 + w * t) z = t / (1 + z * t) := by
    rw [logDeriv_apply]
    congr 1
    simp
  have h2 : logDeriv (fun w : ℂ => Complex.exp (-(w * t))) z = -t := by
    rw [logDeriv_apply]
    have hda : HasDerivAt (fun w : ℂ => Complex.exp (-(w * t)))
        (Complex.exp (-(z * t)) * (-t)) z := by
      have hbase := HasDerivAt.cexp (((hasDerivAt_id z).mul_const t).neg)
      simpa using hbase
    rw [hda.deriv, mul_comm, mul_div_assoc, div_self hgz, mul_one]
  rw [hmul, h1, h2]
  ring

variable {m : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] {M U T : Matrix m m ℂ}

/-- The logarithmic derivative of the regularized determinant, factor by factor. -/
theorem logDeriv_finiteDet2 (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) {z : ℂ}
    (hz : ∀ i, 1 + z * T i i ≠ 0) :
    logDeriv (finiteDet2 M) z = ∑ i, (T i i / (1 + z * T i i) - T i i) := by
  have hfun : finiteDet2 M
      = ∏ i : m, fun w : ℂ => (1 + w * T i i) * Complex.exp (-(w * T i i)) := by
    funext w
    rw [finiteDet2_eq_prod hU1 hU2 hT hMT w, Finset.prod_apply]
  calc logDeriv (finiteDet2 M) z
      = logDeriv (fun w : ℂ => ∏ i : m, (1 + w * T i i) * Complex.exp (-(w * T i i))) z := by
        congr 1
        funext w
        exact finiteDet2_eq_prod hU1 hU2 hT hMT w
    _ = ∑ i : m, logDeriv (fun w : ℂ => (1 + w * T i i) * Complex.exp (-(w * T i i))) z :=
        logDeriv_prod (f := fun (i : m) (w : ℂ) => (1 + w * T i i) * Complex.exp (-(w * T i i)))
          (x := z) (fun i _ => mul_ne_zero (hz i) (Complex.exp_ne_zero _))
          (fun i _ => by fun_prop)
    _ = ∑ i, (T i i / (1 + z * T i i) - T i i) :=
        Finset.sum_congr rfl fun i _ => logDeriv_schurFactor (T i i) (hz i)

/-- The constant part of a Schur factor contributes nothing. -/
theorem circleIntegral_const_eq_zero (t c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∮ _z in C(c, r), t) = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
    continuousOn_const (fun _ _ => differentiableAt_const _)

/-- **A Schur factor whose reciprocal zero lies inside contributes `2πi`.** -/
theorem circleIntegral_schurFactor_inside {t c : ℂ} {r : ℝ} (hr : 0 < r) (ht : t ≠ 0)
    (hne : ∀ z ∈ sphere c r, 1 + z * t ≠ 0) (hmem : -t⁻¹ ∈ ball c r) :
    (∮ z in C(c, r), (t / (1 + z * t) - t)) = 2 * Real.pi * Complex.I := by
  have hrw : ∀ z ∈ sphere c r, t / (1 + z * t) = (z - -t⁻¹)⁻¹ := by
    intro z hz
    have h1 : 1 + z * t ≠ 0 := hne z hz
    field_simp
    ring
  have hci1 : CircleIntegrable (fun z : ℂ => t / (1 + z * t)) c r := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    exact (continuousAt_const.div
      (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
      (hne z hz)).continuousWithinAt
  have hci2 : CircleIntegrable (fun _ : ℂ => t) c r :=
    ContinuousOn.circleIntegrable hr.le continuousOn_const
  rw [circleIntegral.integral_sub hci1 hci2, circleIntegral_const_eq_zero t c hr.le, sub_zero,
    circleIntegral.integral_congr hr.le hrw,
    circleIntegral.integral_sub_inv_of_mem_ball hmem]

/-- **A Schur factor whose reciprocal zero lies outside contributes nothing.** -/
theorem circleIntegral_schurFactor_outside {t c : ℂ} {r : ℝ} (hr : 0 < r) (ht : t ≠ 0)
    (hne : ∀ z ∈ sphere c r, 1 + z * t ≠ 0) (hout : -t⁻¹ ∉ ball c r) :
    (∮ z in C(c, r), (t / (1 + z * t) - t)) = 0 := by
  have houtcl : -t⁻¹ ∉ closedBall c r := by
    intro hcl
    rcases lt_or_eq_of_le (mem_closedBall.mp hcl) with hlt | heq
    · exact hout (mem_ball.mpr hlt)
    · refine hne (-t⁻¹) (Metric.mem_sphere.mpr heq) ?_
      field_simp
      norm_num
  have hrw : ∀ z ∈ sphere c r, t / (1 + z * t) = (z - -t⁻¹)⁻¹ := by
    intro z hz
    have h1 : 1 + z * t ≠ 0 := hne z hz
    field_simp
    ring
  have hci1 : CircleIntegrable (fun z : ℂ => t / (1 + z * t)) c r := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    exact (continuousAt_const.div
      (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
      (hne z hz)).continuousWithinAt
  have hci2 : CircleIntegrable (fun _ : ℂ => t) c r :=
    ContinuousOn.circleIntegrable hr.le continuousOn_const
  have hzero : (∮ z in C(c, r), (z - -t⁻¹)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      ?_ (fun z hz => ?_)
    · intro z hz
      have hzne : z - -t⁻¹ ≠ 0 := by
        intro hcon
        rw [sub_eq_zero] at hcon
        exact houtcl (by rw [← hcon]; exact hz)
      exact ((continuousAt_id.sub continuousAt_const).inv₀ hzne).continuousWithinAt
    · have hzne : z - -t⁻¹ ≠ 0 := by
        intro hcon
        rw [sub_eq_zero] at hcon
        exact houtcl (by rw [← hcon]; exact ball_subset_closedBall hz.1)
      exact (differentiableAt_id.sub_const _).inv hzne
  rw [circleIntegral.integral_sub hci1 hci2, circleIntegral_const_eq_zero t c hr.le, sub_zero,
    circleIntegral.integral_congr hr.le hrw, hzero]

end GaloisForLFunctions.HTGeometry
