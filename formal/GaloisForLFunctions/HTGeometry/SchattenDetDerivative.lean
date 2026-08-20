/-
# The derivative of the order-`p` regularized determinant of a spectrum

The spectral instance of the power-trace determinant's derivative layer: the regularized exponent
is a power series whose terms are dominated by a geometric majorant inside the reciprocal spectral
radius, so it may be differentiated termwise, and the derivative is again continuous in the power
traces.  Every statement is the corresponding statement for the power-trace sequence of the
spectrum.

Main results:
* `schattenDetExpTerm`, `deriv_schattenDetExpTerm` — the terms and their derivatives.
* `hasSum_deriv_schattenDetExp`, `deriv_schattenDetExp_eq` — **termwise differentiation**.
* `tendsto_deriv_schattenDetExp_of_tendsto_tracePower` — the derivative is continuous in the power
  traces.
* `deriv_schattenDet_eq`, `tendsto_deriv_schattenDet_of_tendsto_tracePower` — **the same for the
  determinant itself**.
-/
import GaloisForLFunctions.HTGeometry.SchattenSpectralDeterminant
import GaloisForLFunctions.HTGeometry.TracePowerDetDerivative

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- The `k`-th term of the regularized exponent. -/
def schattenDetExpTerm (p : ℕ) (lam : ι → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  tracePowerDetExpTerm p (schattenTracePower lam) k z

theorem schattenDetExp_eq_tsum_term (p : ℕ) (lam : ι → ℂ) (z : ℂ) :
    schattenDetExp p lam z = ∑' k : ℕ, schattenDetExpTerm p lam k z := rfl

theorem natCast_add_ne_zero {p : ℕ} (hp : 0 < p) (k : ℕ) : ((k + p : ℕ) : ℂ) ≠ 0 :=
  natCast_add_pos_ne_zero hp k

theorem deriv_schattenDetExpTerm {p : ℕ} (hp : 0 < p) (lam : ι → ℂ) (k : ℕ) (z : ℂ) :
    deriv (schattenDetExpTerm p lam k) z
      = z ^ (k + p - 1) * schattenTracePower lam (k + p) :=
  deriv_tracePowerDetExpTerm hp (schattenTracePower lam) k z

theorem norm_schattenDetExpTerm_le {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (_hr : 0 < r) (k : ℕ) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖schattenDetExpTerm p lam k w‖ ≤ (S * r ^ p) * (r * B) ^ k :=
  norm_tracePowerDetExpTerm_le hp hB1 hS0 hbound _hr k hw

/-- **Termwise differentiation of the regularized exponent.** -/
theorem hasSum_deriv_schattenDetExp {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    HasSum (fun k : ℕ => z ^ (k + p - 1) * schattenTracePower lam (k + p))
      (deriv (fun w : ℂ => schattenDetExp p lam w) z) :=
  hasSum_deriv_tracePowerDetExp hp hB1 hS0 hbound hr hrB hz

theorem deriv_schattenDetExp_eq {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    deriv (fun w : ℂ => schattenDetExp p lam w) z
      = ∑' k : ℕ, z ^ (k + p - 1) * schattenTracePower lam (k + p) :=
  deriv_tracePowerDetExp_eq hp hB1 hS0 hbound hr hrB hz

theorem differentiableAt_schattenDetExp {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    DifferentiableAt ℂ (fun w : ℂ => schattenDetExp p lam w) z :=
  differentiableAt_tracePowerDetExp hp hB1 hS0 hbound hr hrB hz

/-- **The derivative of the regularized exponent is continuous in the power traces.** -/
theorem tendsto_deriv_schattenDetExp_of_tendsto_tracePower {p : ℕ} (hp : 0 < p)
    {L : Type*} {l : Filter L} {lam : L → ι → ℂ} {mu : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ (a : L) (k : ℕ), ‖schattenTracePower (lam a) (k + p)‖ ≤ S * B ^ k)
    (hboundmu : ∀ k : ℕ, ‖schattenTracePower mu (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Filter.Tendsto (fun a => schattenTracePower (lam a) (k + p)) l
      (nhds (schattenTracePower mu (k + p))))
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    Filter.Tendsto (fun a => deriv (fun w : ℂ => schattenDetExp p (lam a) w) z) l
      (nhds (deriv (fun w : ℂ => schattenDetExp p mu w) z)) :=
  tendsto_deriv_tracePowerDetExp_of_tendsto_tracePower hp hB1 hS0 hbound hboundmu hconv hr hrB hz

/-- The derivative of the order-`p` determinant. -/
theorem deriv_schattenDet_eq {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    deriv (fun w : ℂ => schattenDet p lam w) z
      = -(schattenDet p lam z) * deriv (fun w : ℂ => schattenDetExp p lam w) z :=
  deriv_tracePowerDet_eq hp hB1 hS0 hbound hr hrB hz

/-- **The derivative of the order-`p` determinant is continuous in the power traces.** -/
theorem tendsto_deriv_schattenDet_of_tendsto_tracePower {p : ℕ} (hp : 0 < p)
    {L : Type*} {l : Filter L} {lam : L → ι → ℂ} {mu : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ (a : L) (k : ℕ), ‖schattenTracePower (lam a) (k + p)‖ ≤ S * B ^ k)
    (hboundmu : ∀ k : ℕ, ‖schattenTracePower mu (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Filter.Tendsto (fun a => schattenTracePower (lam a) (k + p)) l
      (nhds (schattenTracePower mu (k + p))))
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    Filter.Tendsto (fun a => deriv (fun w : ℂ => schattenDet p (lam a) w) z) l
      (nhds (deriv (fun w : ℂ => schattenDet p mu w) z)) :=
  tendsto_deriv_tracePowerDet_of_tendsto_tracePower hp hB1 hS0 hbound hboundmu hconv hr hrB hz

end

end GaloisForLFunctions.HTGeometry
