/-
# The closure of the determinant graph on the spectral side

The determinant-completion statement, at every order, with the Schatten-`p` determinant of a
spectrum in place of the finite-rank one.  A family of determinants factored as the order-`p`
regularized determinant times the exponential of a normalized polynomial converges to the same shape:
the regularized factor converges by continuity in the power traces, its derivative converges by
termwise differentiation, and the polynomial factor is pinned by the logarithmic derivative.

Main results:
* `differentiableAt_schattenDet` — the order-`p` determinant is differentiable.
* `exists_poly_limit_of_tendsto_spectralDet` — **the closure of the determinant graph**.
-/
import GaloisForLFunctions.HTGeometry.SchattenDetDerivative
import GaloisForLFunctions.HTGeometry.ExpFactorPointwiseClosure

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

theorem schattenDet_ne_zero (p : ℕ) (lam : ι → ℂ) (z : ℂ) : schattenDet p lam z ≠ 0 := by
  rw [schattenDet]
  exact Complex.exp_ne_zero _

theorem differentiableAt_schattenDet {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    DifferentiableAt ℂ (fun w : ℂ => schattenDet p lam w) z :=
  ((differentiableAt_schattenDetExp hp hB1 hS0 hbound hr hrB hz).neg).cexp

/-- **The closure of the determinant graph on the spectral side.**  A family of determinants that
factor as the order-`p` regularized determinant of a converging spectrum times the exponential of a
normalized polynomial of bounded degree has a limit of the same shape. -/
theorem exists_poly_limit_of_tendsto_spectralDet {J p : ℕ} (hp : 0 < p)
    {lam : ℕ → ι → ℂ} {mu : ι → ℂ} {B S : ℝ} (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ (n : ℕ) (k : ℕ), ‖schattenTracePower (lam n) (k + p)‖ ≤ S * B ^ k)
    (hboundmu : ∀ k : ℕ, ‖schattenTracePower mu (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Tendsto (fun n => schattenTracePower (lam n) (k + p)) atTop
      (nhds (schattenTracePower mu (k + p))))
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1)
    {P : ℕ → Polynomial ℂ} (hdeg : ∀ n, (P n).natDegree ≤ J + 1)
    (hP0 : ∀ n, (P n).coeff 0 = 0)
    {v : Fin (J + 1) → ℂ} (hv : Function.Injective v) (hvU : ∀ i, v i ∈ ball (0 : ℂ) r)
    {F : ℂ → ℂ} {Fd : Fin (J + 1) → ℂ}
    (hFval : ∀ z ∈ ball (0 : ℂ) r, Tendsto
      (fun n => schattenDet p (lam n) z * Complex.exp (Polynomial.eval z (P n))) atTop
      (nhds (F z)))
    (hFder : ∀ i, Tendsto
      (fun n => deriv (fun w : ℂ =>
        schattenDet p (lam n) w * Complex.exp (Polynomial.eval w (P n))) (v i)) atTop
      (nhds (Fd i)))
    (hFne : ∀ i, F (v i) ≠ 0) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ J + 1 ∧ Q.coeff 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) r, F z = schattenDet p mu z * Complex.exp (Polynomial.eval z Q) := by
  classical
  -- the value of the exponential factor at each node
  have hEval : ∀ i, Tendsto (fun n => Complex.exp (Polynomial.eval (v i) (P n))) atTop
      (nhds (F (v i) / schattenDet p mu (v i))) := by
    intro i
    have hE : Tendsto (fun n => schattenDet p (lam n) (v i)) atTop
        (nhds (schattenDet p mu (v i))) := by
      have hzB : ‖v i‖ * B < 1 := by
        have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
        have hzr : ‖v i‖ ≤ r := by
          have := hvU i
          rw [mem_ball, dist_zero_right] at this
          exact this.le
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr hB0) hrB
      exact tendsto_schattenDet_of_tendsto_tracePower hp hB1 hS0 hbound hconv hzB
    have hquot := (hFval (v i) (hvU i)).div hE (schattenDet_ne_zero p mu (v i))
    refine hquot.congr fun n => ?_
    show schattenDet p (lam n) (v i) * Complex.exp (Polynomial.eval (v i) (P n))
        / schattenDet p (lam n) (v i) = Complex.exp (Polynomial.eval (v i) (P n))
    rw [mul_comm, mul_div_assoc, div_self (schattenDet_ne_zero p (lam n) (v i)), mul_one]
  -- the derivative of the exponential factor at each node
  have hEder : ∀ i, Tendsto
      (fun n => deriv (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i)) atTop
      (nhds ((Fd i - deriv (fun w : ℂ => schattenDet p mu w) (v i)
          * (F (v i) / schattenDet p mu (v i))) / schattenDet p mu (v i))) := by
    intro i
    have hEd : Tendsto (fun n => deriv (fun w : ℂ => schattenDet p (lam n) w) (v i)) atTop
        (nhds (deriv (fun w : ℂ => schattenDet p mu w) (v i))) :=
      tendsto_deriv_schattenDet_of_tendsto_tracePower hp hB1 hS0 hbound hboundmu hconv hr hrB
        (hvU i)
    have hE : Tendsto (fun n => schattenDet p (lam n) (v i)) atTop
        (nhds (schattenDet p mu (v i))) := by
      have hzB : ‖v i‖ * B < 1 := by
        have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
        have hzr : ‖v i‖ ≤ r := by
          have := hvU i
          rw [mem_ball, dist_zero_right] at this
          exact this.le
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr hB0) hrB
      exact tendsto_schattenDet_of_tendsto_tracePower hp hB1 hS0 hbound hconv hzB
    have hstep := ((hFder i).sub (hEd.mul (hEval i))).div hE (schattenDet_ne_zero p mu (v i))
    refine hstep.congr fun n => ?_
    have hEdn : DifferentiableAt ℂ (fun w : ℂ => schattenDet p (lam n) w) (v i) :=
      differentiableAt_schattenDet hp hB1 hS0 (hbound n) hr hrB (hvU i)
    have hGdn : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i) :=
      (((P n).hasDerivAt (v i)).cexp).differentiableAt
    have hprod : deriv (fun w : ℂ =>
        schattenDet p (lam n) w * Complex.exp (Polynomial.eval w (P n))) (v i)
        = deriv (fun w : ℂ => schattenDet p (lam n) w) (v i)
            * Complex.exp (Polynomial.eval (v i) (P n))
          + schattenDet p (lam n) (v i)
            * deriv (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i) :=
      deriv_mul hEdn hGdn
    show (deriv (fun w : ℂ =>
        schattenDet p (lam n) w * Complex.exp (Polynomial.eval w (P n))) (v i)
        - deriv (fun w : ℂ => schattenDet p (lam n) w) (v i)
          * Complex.exp (Polynomial.eval (v i) (P n)))
        / schattenDet p (lam n) (v i)
      = deriv (fun w : ℂ => Complex.exp (Polynomial.eval w (P n))) (v i)
    have hEne : schattenDet p (lam n) (v i) ≠ 0 := schattenDet_ne_zero p (lam n) (v i)
    rw [hprod]
    field_simp
    ring
  obtain ⟨Q, hQdeg, hQ0, hQcoeff⟩ :=
    exists_poly_limit_of_tendsto_exp_samples hdeg hP0 hv hEval hEder
      (fun i => div_ne_zero (hFne i) (schattenDet_ne_zero p mu (v i)))
  refine ⟨Q, hQdeg, hQ0, fun z hz => ?_⟩
  have hE : Tendsto (fun n => schattenDet p (lam n) z) atTop (nhds (schattenDet p mu z)) := by
    have hzB : ‖z‖ * B < 1 := by
      have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
      have hzr : ‖z‖ ≤ r := by
        rw [mem_ball, dist_zero_right] at hz
        exact hz.le
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr hB0) hrB
    exact tendsto_schattenDet_of_tendsto_tracePower hp hB1 hS0 hbound hconv hzB
  have hpoly : Tendsto (fun n => Polynomial.eval z (P n)) atTop
      (nhds (Polynomial.eval z Q)) := tendsto_eval_of_tendsto_coeff hdeg hQdeg hQcoeff z
  have hexp : Tendsto (fun n => Complex.exp (Polynomial.eval z (P n))) atTop
      (nhds (Complex.exp (Polynomial.eval z Q))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp hpoly
  exact tendsto_nhds_unique (hFval z hz) (hE.mul hexp)

end

end GaloisForLFunctions.HTGeometry
