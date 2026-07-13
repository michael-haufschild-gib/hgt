import GaloisForLFunctions.HTGeometry.BernsteinSzegoDensity
import Mathlib.Analysis.Complex.MeanValue

/-!
# Mean-value identities for the Bernstein--Szegő model

The zero-free reversed OPUC polynomial permits division throughout the closed unit disk.  The
complex mean-value theorem then proves the exact monomial orthogonality needed for finite-moment
reproduction.  This is the analytic heart of the Bernstein--Szegő prefix theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial
open scoped ComplexConjugate ComplexOrder

noncomputable section

/-- On the unit circle the weighted top-polynomial/monomial integrand is the boundary value of a
holomorphic quotient on the closed disk. -/
theorem bernsteinSzego_monomial_integrand_identity
    {N j : ℕ} (hj : j ≤ N) (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) {z : ℂ} (hz : ‖z‖ = 1) :
    (finiteOPUCPolynomial c hG).eval z * star (z ^ j) *
        ((Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹) =
      z ^ (N - j) * ((finiteOPUCReversedPolynomial c hG).eval z)⁻¹ := by
  let p := finiteOPUCPolynomial c hG
  let q := finiteOPUCReversedPolynomial c hG
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by simp [hz])
  have hq0 : q.eval z ≠ 0 :=
    finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG (by simp [hz])
  have hp0 : p.eval z ≠ 0 := by
    intro hp
    have he := finiteOPUCReversedPolynomial_eval_unitCircle c hG hz
    simp [p, hp] at he
    exact hq0 he
  have heval : q.eval z = z ^ N * star (p.eval z) := by
    exact finiteOPUCReversedPolynomial_eval_unitCircle c hG hz
  have hnorm : (Complex.normSq (q.eval z) : ℂ) = star (p.eval z) * p.eval z := by
    change (Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ) = _
    rw [finiteOPUCReversedPolynomial_normSq_eq_on_unitCircle c hG hz,
      Complex.normSq_eq_conj_mul_self]
    rfl
  change p.eval z * star (z ^ j) * ((Complex.normSq (q.eval z) : ℂ)⁻¹) =
    z ^ (N - j) * (q.eval z)⁻¹
  rw [hnorm, show star (z ^ j) = (z⁻¹) ^ j by
    calc
      star (z ^ j) = star z ^ j := by
        exact map_pow (starRingEnd ℂ) z j
      _ = (z⁻¹) ^ j := by
        exact congrArg (fun w : ℂ => w ^ j) (Complex.inv_eq_conj hz).symm]
  rw [heval]
  field_simp
  apply congrArg (fun w : ℂ => w / star (p.eval z))
  calc
    (1 / z) ^ j * z ^ N = (1 / z) ^ j * (z ^ j * z ^ (N - j)) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    _ = ((1 / z) * z) ^ j * z ^ (N - j) := by
      rw [← mul_assoc, mul_pow]
    _ = z ^ (N - j) := by simp [div_eq_mul_inv, inv_mul_cancel₀ hz0]

/-- The circle average of a nonnegative power divided by a polynomial that is zero-free on the
closed disk is its value at the origin. -/
theorem polynomial_power_div_circleAverage
    (q : Polynomial ℂ) (k : ℕ)
    (hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0) :
    Real.circleAverage (fun z : ℂ => z ^ k * (q.eval z)⁻¹) 0 1 =
      (0 : ℂ) ^ k * (q.eval 0)⁻¹ := by
  apply DiffContOnCl.circleAverage
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hzc : ‖z‖ ≤ 1 := by
    have hzabs : z ∈ closure (Metric.ball (0 : ℂ) 1) := by simpa using hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closure_ball_subset_closedBall hzabs
    simpa [Metric.mem_closedBall, dist_zero_right] using hz'
  exact ((differentiableAt_id.pow k).mul
    (q.differentiableAt.inv (hq z hzc))).differentiableWithinAt

/-- Every monomial of degree below `N` is orthogonal to the normalized degree-`N` polynomial for
the reciprocal-square Bernstein--Szegő weight. -/
theorem bernsteinSzego_monomial_orthogonal
    {N j : ℕ} (hj : j < N) (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    Real.circleAverage
        (fun z : ℂ =>
          (finiteOPUCPolynomial c hG).eval z * star (z ^ j) *
            ((Complex.normSq
              ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹)) 0 1 = 0 := by
  rw [Real.circleAverage_congr_sphere (f₂ := fun z : ℂ =>
    z ^ (N - j) * ((finiteOPUCReversedPolynomial c hG).eval z)⁻¹) (by
      intro z hz
      apply bernsteinSzego_monomial_integrand_identity hj.le c hG
      simpa [Metric.mem_sphere, dist_zero_right] using hz)]
  rw [polynomial_power_div_circleAverage]
  · have hsub : N - j ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hj)
    simp [hsub]
  · intro z hz
    exact finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG hz

/-- The degree-`N` polynomial has squared norm one for its Bernstein--Szegő weight. -/
theorem bernsteinSzego_polynomial_normalized
    {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    Real.circleAverage
        (fun z : ℂ =>
          (finiteOPUCPolynomial c hG).eval z *
            star ((finiteOPUCPolynomial c hG).eval z) *
            ((Complex.normSq
              ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹)) 0 1 = 1 := by
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ : ℂ => (1 : ℂ)) (by
    intro z hz
    have hznorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hq0 := finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG
      (z := z) (by simp [hznorm])
    have hp0 : (finiteOPUCPolynomial c hG).eval z ≠ 0 := by
      intro hp
      have he := finiteOPUCReversedPolynomial_eval_unitCircle c hG hznorm
      rw [hp] at he
      simp at he
      exact hq0 he
    dsimp only
    rw [finiteOPUCReversedPolynomial_normSq_eq_on_unitCircle c hG hznorm,
      Complex.normSq_eq_conj_mul_self]
    field_simp [hp0, star_eq_zero.not.mpr hp0]
    rfl)]
  exact Real.circleAverage_const 1 0 1

end

end GaloisForLFunctions.HTGeometry
