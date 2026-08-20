/-
# The closure of the determinant graph for a power-trace sequence

The determinant-completion statement, at every order, with the order-`p` regularized
determinant of a power-trace sequence in place of the finite-rank one.  A family of determinants factored as the order-`p`
regularized determinant times the exponential of a normalized polynomial converges to the same shape:
the regularized factor converges by continuity in the power traces, its derivative converges by
termwise differentiation, and the polynomial factor is pinned by the logarithmic derivative.

Main results:
* `differentiableAt_tracePowerDet` — the order-`p` determinant is differentiable.
* `exists_poly_limit_of_tendsto_tracePowerDet` — **the closure of the determinant graph**.
-/
import GaloisForLFunctions.HTGeometry.TracePowerDetDerivative
import GaloisForLFunctions.HTGeometry.ExpFactorPointwiseClosure

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem tracePowerDet_ne_zero (p : ℕ) (τ : ℕ → ℂ) (z : ℂ) : tracePowerDet p τ z ≠ 0 := by
  rw [tracePowerDet]
  exact Complex.exp_ne_zero _

theorem differentiableAt_tracePowerDet {p : ℕ} (hp : 0 < p) {τ : ℕ → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖τ (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    DifferentiableAt ℂ (fun w : ℂ => tracePowerDet p τ w) z :=
  ((differentiableAt_tracePowerDetExp hp hB1 hS0 hbound hr hrB hz).neg).cexp

/-- **The closure of the determinant graph on the spectral side.**  A family of determinants that
factor as the order-`p` regularized determinant of a converging spectrum times the exponential of a
normalized polynomial of bounded degree has a limit of the same shape. -/
theorem exists_poly_limit_of_tendsto_tracePowerDet {J p : ℕ} (hp : 0 < p)
    {τ : ℕ → ℕ → ℂ} {σ : ℕ → ℂ} {B S : ℝ} (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ (n : ℕ) (k : ℕ), ‖τ n (k + p)‖ ≤ S * B ^ k)
    (hboundmu : ∀ k : ℕ, ‖σ (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Tendsto (fun n => τ n (k + p)) atTop
      (nhds (σ (k + p))))
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1)
    {P : ℕ → Polynomial ℂ} (hdeg : ∀ n, (P n).natDegree ≤ J + 1)
    (hP0 : ∀ n, (P n).coeff 0 = 0)
    {v : Fin (J + 1) → ℂ} (hv : Function.Injective v) (hvU : ∀ i, v i ∈ ball (0 : ℂ) r)
    {F : ℂ → ℂ} {Fd : Fin (J + 1) → ℂ}
    (hFval : ∀ z ∈ ball (0 : ℂ) r, Tendsto
      (fun n => tracePowerDet p (τ n) z * Complex.exp (Polynomial.eval z (P n))) atTop
      (nhds (F z)))
    (hFder : ∀ i, Tendsto
      (fun n => deriv (fun w : ℂ =>
        tracePowerDet p (τ n) w * Complex.exp (Polynomial.eval w (P n))) (v i)) atTop
      (nhds (Fd i)))
    (hFne : ∀ i, F (v i) ≠ 0) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ J + 1 ∧ Q.coeff 0 = 0 ∧
      (∀ h : ℕ, Tendsto (fun n => (P n).coeff h) atTop (nhds (Q.coeff h))) ∧
      ∀ z ∈ ball (0 : ℂ) r, F z = tracePowerDet p σ z * Complex.exp (Polynomial.eval z Q) := by
  classical
  -- the value of the exponential factor at each node
  have hEval : ∀ i, Tendsto (fun n => Complex.exp (Polynomial.eval (v i) (P n))) atTop
      (nhds (F (v i) / tracePowerDet p σ (v i))) := by
    intro i
    have hE : Tendsto (fun n => tracePowerDet p (τ n) (v i)) atTop
        (nhds (tracePowerDet p σ (v i))) := by
      have hzB : ‖v i‖ * B < 1 := by
        have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
        have hzr : ‖v i‖ ≤ r := by
          have := hvU i
          rw [mem_ball, dist_zero_right] at this
          exact this.le
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr hB0) hrB
      exact tendsto_tracePowerDet_of_tendsto hp hB1 hbound hconv hzB
    have hquot := (hFval (v i) (hvU i)).div hE (tracePowerDet_ne_zero p σ (v i))
    refine hquot.congr fun n => ?_
    show tracePowerDet p (τ n) (v i) * Complex.exp (Polynomial.eval (v i) (P n))
        / tracePowerDet p (τ n) (v i) = Complex.exp (Polynomial.eval (v i) (P n))
    rw [mul_comm, mul_div_assoc, div_self (tracePowerDet_ne_zero p (τ n) (v i)), mul_one]
  -- the derivative of the exponential factor at each node
  have hEder : ∀ i, Tendsto
      (fun n => deriv (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i)) atTop
      (nhds ((Fd i - deriv (fun w : ℂ => tracePowerDet p σ w) (v i)
          * (F (v i) / tracePowerDet p σ (v i))) / tracePowerDet p σ (v i))) := by
    intro i
    have hEd : Tendsto (fun n => deriv (fun w : ℂ => tracePowerDet p (τ n) w) (v i)) atTop
        (nhds (deriv (fun w : ℂ => tracePowerDet p σ w) (v i))) :=
      tendsto_deriv_tracePowerDet_of_tendsto_tracePower hp hB1 hS0 hbound hboundmu hconv hr hrB
        (hvU i)
    have hE : Tendsto (fun n => tracePowerDet p (τ n) (v i)) atTop
        (nhds (tracePowerDet p σ (v i))) := by
      have hzB : ‖v i‖ * B < 1 := by
        have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
        have hzr : ‖v i‖ ≤ r := by
          have := hvU i
          rw [mem_ball, dist_zero_right] at this
          exact this.le
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr hB0) hrB
      exact tendsto_tracePowerDet_of_tendsto hp hB1 hbound hconv hzB
    have hstep := ((hFder i).sub (hEd.mul (hEval i))).div hE (tracePowerDet_ne_zero p σ (v i))
    refine hstep.congr fun n => ?_
    have hEdn : DifferentiableAt ℂ (fun w : ℂ => tracePowerDet p (τ n) w) (v i) :=
      differentiableAt_tracePowerDet hp hB1 hS0 (hbound n) hr hrB (hvU i)
    have hGdn : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i) :=
      (((P n).hasDerivAt (v i)).cexp).differentiableAt
    have hprod : deriv (fun w : ℂ =>
        tracePowerDet p (τ n) w * Complex.exp (Polynomial.eval w (P n))) (v i)
        = deriv (fun w : ℂ => tracePowerDet p (τ n) w) (v i)
            * Complex.exp (Polynomial.eval (v i) (P n))
          + tracePowerDet p (τ n) (v i)
            * deriv (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i) :=
      deriv_mul hEdn hGdn
    show (deriv (fun w : ℂ =>
        tracePowerDet p (τ n) w * Complex.exp (Polynomial.eval w (P n))) (v i)
        - deriv (fun w : ℂ => tracePowerDet p (τ n) w) (v i)
          * Complex.exp (Polynomial.eval (v i) (P n)))
        / tracePowerDet p (τ n) (v i)
      = deriv (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i)
    have hEne : tracePowerDet p (τ n) (v i) ≠ 0 := tracePowerDet_ne_zero p (τ n) (v i)
    rw [hprod]
    field_simp
    ring
  obtain ⟨Q, hQdeg, hQ0, hQcoeff⟩ :=
    exists_poly_limit_of_tendsto_exp_samples hdeg hP0 hv hEval hEder
      (fun i => div_ne_zero (hFne i) (tracePowerDet_ne_zero p σ (v i)))
  refine ⟨Q, hQdeg, hQ0, hQcoeff, fun z hz => ?_⟩
  have hE : Tendsto (fun n => tracePowerDet p (τ n) z) atTop (nhds (tracePowerDet p σ z)) := by
    have hzB : ‖z‖ * B < 1 := by
      have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
      have hzr : ‖z‖ ≤ r := by
        rw [mem_ball, dist_zero_right] at hz
        exact hz.le
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr hB0) hrB
    exact tendsto_tracePowerDet_of_tendsto hp hB1 hbound hconv hzB
  have hpoly : Tendsto (fun n => Polynomial.eval z (P n)) atTop
      (nhds (Polynomial.eval z Q)) := tendsto_eval_of_tendsto_coeff hdeg hQdeg hQcoeff z
  have hexp : Tendsto (fun n => Complex.exp (Polynomial.eval z (P n))) atTop
      (nhds (Complex.exp (Polynomial.eval z Q))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp hpoly
  exact tendsto_nhds_unique (hFval z hz) (hE.mul hexp)

end

end GaloisForLFunctions.HTGeometry
