/-
# The closure of the determinant graph on the spectral side

The spectral instance of the power-trace closure: a family of determinants factored as the order-`p`
regularized determinant times the exponential of a normalized polynomial converges to the same
shape, with the determinant read off the spectrum rather than an abstract power-trace sequence.

Main results:
* `differentiableAt_schattenDet` — the order-`p` determinant is differentiable.
* `exists_poly_limit_of_tendsto_spectralDet` — **the closure of the determinant graph**.
-/
import GaloisForLFunctions.HTGeometry.SchattenDetDerivative
import GaloisForLFunctions.HTGeometry.TracePowerDeterminantGraphClosure

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

theorem schattenDet_ne_zero (p : ℕ) (lam : ι → ℂ) (z : ℂ) : schattenDet p lam z ≠ 0 :=
  tracePowerDet_ne_zero p (schattenTracePower lam) z

theorem differentiableAt_schattenDet {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    DifferentiableAt ℂ (fun w : ℂ => schattenDet p lam w) z :=
  differentiableAt_tracePowerDet hp hB1 hS0 hbound hr hrB hz

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
      (∀ h : ℕ, Tendsto (fun n => (P n).coeff h) atTop (nhds (Q.coeff h))) ∧
      ∀ z ∈ ball (0 : ℂ) r, F z = schattenDet p mu z * Complex.exp (Polynomial.eval z Q) :=
  exists_poly_limit_of_tendsto_tracePowerDet hp hB1 hS0 hbound hboundmu hconv hr hrB hdeg hP0
    hv hvU hFval hFder hFne

end

end GaloisForLFunctions.HTGeometry
