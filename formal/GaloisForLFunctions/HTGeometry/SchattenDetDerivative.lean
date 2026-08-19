/-
# The derivative of the order-`p` regularized determinant of a spectrum

The regularized exponent is a power series whose terms are dominated by a geometric majorant inside
the reciprocal spectral radius, so it may be differentiated termwise; the derivative is again a
series with the same kind of majorant, hence again continuous in the power traces.  This is what
lets the closure argument for the determinant fibre run on the spectral side, where no uniform
convergence of the determinants is available.

Main results:
* `schattenDetExpTerm`, `deriv_schattenDetExpTerm` — the terms and their derivatives.
* `hasSum_deriv_schattenDetExp`, `deriv_schattenDetExp_eq` — **termwise differentiation**.
* `tendsto_deriv_schattenDetExp_of_tendsto_tracePower` — the derivative is continuous in the power
  traces.
* `deriv_schattenDet_eq`, `tendsto_deriv_schattenDet_of_tendsto_tracePower` — **the same for the
  determinant itself**.
-/
import GaloisForLFunctions.HTGeometry.SchattenSpectralDeterminant
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- The `k`-th term of the regularized exponent. -/
def schattenDetExpTerm (p : ℕ) (lam : ι → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  z ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower lam (k + p)

theorem schattenDetExp_eq_tsum_term (p : ℕ) (lam : ι → ℂ) (z : ℂ) :
    schattenDetExp p lam z = ∑' k : ℕ, schattenDetExpTerm p lam k z := rfl

theorem natCast_add_ne_zero {p : ℕ} (hp : 0 < p) (k : ℕ) : ((k + p : ℕ) : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (by omega)

theorem deriv_schattenDetExpTerm {p : ℕ} (hp : 0 < p) (lam : ι → ℂ) (k : ℕ) (z : ℂ) :
    deriv (schattenDetExpTerm p lam k) z
      = z ^ (k + p - 1) * schattenTracePower lam (k + p) := by
  have hne : ((k + p : ℕ) : ℂ) ≠ 0 := natCast_add_ne_zero hp k
  have hfun : schattenDetExpTerm p lam k
      = fun w : ℂ => w ^ (k + p)
        * (schattenTracePower lam (k + p) / ((k + p : ℕ) : ℂ)) := by
    funext w
    rw [schattenDetExpTerm]
    field_simp
  have h1 : HasDerivAt (fun w : ℂ => w ^ (k + p))
      (((k + p : ℕ) : ℂ) * z ^ (k + p - 1)) z := by
    simpa using hasDerivAt_pow (k + p) z
  have h2 := h1.mul_const (schattenTracePower lam (k + p) / ((k + p : ℕ) : ℂ))
  rw [hfun, h2.deriv]
  field_simp

theorem norm_schattenDetExpTerm_le {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (_hr : 0 < r) (k : ℕ) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖schattenDetExpTerm p lam k w‖ ≤ (S * r ^ p) * (r * B) ^ k := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hden : (1 : ℝ) ≤ ‖((k + p : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hstep : ‖schattenDetExpTerm p lam k w‖ ≤ ‖w‖ ^ (k + p) * (S * B ^ k) := by
    rw [schattenDetExpTerm, norm_mul, norm_div, norm_pow]
    refine mul_le_mul ?_ (hbound k) (norm_nonneg _) (by positivity)
    rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖((k + p : ℕ) : ℂ)‖)]
    nlinarith [pow_nonneg (norm_nonneg w) (k + p)]
  refine le_trans hstep ?_
  have hpow : ‖w‖ ^ (k + p) ≤ r ^ (k + p) :=
    pow_le_pow_left₀ (norm_nonneg w) hw (k + p)
  have hfin : r ^ (k + p) * (S * B ^ k) = (S * r ^ p) * (r * B) ^ k := by
    rw [pow_add, mul_pow]
    ring
  calc ‖w‖ ^ (k + p) * (S * B ^ k)
      ≤ r ^ (k + p) * (S * B ^ k) := by
        refine mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (S * r ^ p) * (r * B) ^ k := hfin

/-- **Termwise differentiation of the regularized exponent.** -/
theorem hasSum_deriv_schattenDetExp {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    HasSum (fun k : ℕ => z ^ (k + p - 1) * schattenTracePower lam (k + p))
      (deriv (fun w : ℂ => schattenDetExp p lam w) z) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hrB0 : 0 ≤ r * B := mul_nonneg hr.le hB0
  have hu : Summable fun k : ℕ => (S * r ^ p) * (r * B) ^ k :=
    (summable_geometric_of_lt_one hrB0 hrB).mul_left _
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (schattenDetExpTerm p lam k) (ball (0 : ℂ) r) := by
    intro k
    have hfun : schattenDetExpTerm p lam k
        = fun w : ℂ => w ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower lam (k + p) := rfl
    have hd : Differentiable ℂ (schattenDetExpTerm p lam k) := by
      rw [hfun]
      exact ((differentiable_pow (k + p)).div_const _).mul_const _
    exact hd.differentiableOn
  have hle : ∀ (k : ℕ) (w : ℂ), w ∈ ball (0 : ℂ) r →
      ‖schattenDetExpTerm p lam k w‖ ≤ (S * r ^ p) * (r * B) ^ k := by
    intro k w hw
    refine norm_schattenDetExpTerm_le hp hB1 hS0 hbound hr k ?_
    rw [mem_ball, dist_zero_right] at hw
    exact hw.le
  have hsum := Complex.hasSum_deriv_of_summable_norm hu hdiff isOpen_ball hle hz
  have hfun2 : (fun k : ℕ => deriv (schattenDetExpTerm p lam k) z)
      = fun k : ℕ => z ^ (k + p - 1) * schattenTracePower lam (k + p) := by
    funext k
    exact deriv_schattenDetExpTerm hp lam k z
  rw [hfun2] at hsum
  exact hsum

theorem deriv_schattenDetExp_eq {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    deriv (fun w : ℂ => schattenDetExp p lam w) z
      = ∑' k : ℕ, z ^ (k + p - 1) * schattenTracePower lam (k + p) :=
  ((hasSum_deriv_schattenDetExp hp hB1 hS0 hbound hr hrB hz).tsum_eq).symm

theorem differentiableAt_schattenDetExp {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    DifferentiableAt ℂ (fun w : ℂ => schattenDetExp p lam w) z := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hrB0 : 0 ≤ r * B := mul_nonneg hr.le hB0
  have hu : Summable fun k : ℕ => (S * r ^ p) * (r * B) ^ k :=
    (summable_geometric_of_lt_one hrB0 hrB).mul_left _
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (schattenDetExpTerm p lam k) (ball (0 : ℂ) r) := by
    intro k
    have hfun : schattenDetExpTerm p lam k
        = fun w : ℂ => w ^ (k + p) / ((k + p : ℕ) : ℂ) * schattenTracePower lam (k + p) := rfl
    have hd : Differentiable ℂ (schattenDetExpTerm p lam k) := by
      rw [hfun]
      exact ((differentiable_pow (k + p)).div_const _).mul_const _
    exact hd.differentiableOn
  have hle : ∀ (k : ℕ) (w : ℂ), w ∈ ball (0 : ℂ) r →
      ‖schattenDetExpTerm p lam k w‖ ≤ (S * r ^ p) * (r * B) ^ k := by
    intro k w hw
    refine norm_schattenDetExpTerm_le hp hB1 hS0 hbound hr k ?_
    rw [mem_ball, dist_zero_right] at hw
    exact hw.le
  have hon := Complex.differentiableOn_tsum_of_summable_norm hu hdiff isOpen_ball hle
  exact hon.differentiableAt (isOpen_ball.mem_nhds hz)

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
      (nhds (deriv (fun w : ℂ => schattenDetExp p mu w) z)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hrB0 : 0 ≤ r * B := mul_nonneg hr.le hB0
  have hzr : ‖z‖ ≤ r := by
    rw [mem_ball, dist_zero_right] at hz
    exact hz.le
  have hdom : Summable fun k : ℕ => (S * r ^ (p - 1)) * (r * B) ^ k :=
    (summable_geometric_of_lt_one hrB0 hrB).mul_left _
  have hbnd : ∀ (c : ι → ℂ), (∀ k : ℕ, ‖schattenTracePower c (k + p)‖ ≤ S * B ^ k) →
      ∀ k : ℕ, ‖z ^ (k + p - 1) * schattenTracePower c (k + p)‖
        ≤ (S * r ^ (p - 1)) * (r * B) ^ k := by
    intro c hc k
    have hexp : k + p - 1 = k + (p - 1) := by omega
    rw [norm_mul, norm_pow, hexp]
    have hpow : ‖z‖ ^ (k + (p - 1)) ≤ r ^ (k + (p - 1)) :=
      pow_le_pow_left₀ (norm_nonneg z) hzr _
    calc ‖z‖ ^ (k + (p - 1)) * ‖schattenTracePower c (k + p)‖
        ≤ r ^ (k + (p - 1)) * (S * B ^ k) := by
          refine mul_le_mul hpow (hc k) (norm_nonneg _) (by positivity)
      _ = (S * r ^ (p - 1)) * (r * B) ^ k := by
          rw [pow_add, mul_pow]
          ring
  rw [deriv_schattenDetExp_eq hp hB1 hS0 hboundmu hr hrB hz]
  refine Filter.Tendsto.congr
    (fun a => (deriv_schattenDetExp_eq hp hB1 hS0 (hbound a) hr hrB hz).symm) ?_
  exact tendsto_tsum_of_dominated_convergence hdom (fun k => (hconv k).const_mul _)
    (Filter.Eventually.of_forall fun a k => hbnd (lam a) (hbound a) k)

/-- The derivative of the order-`p` determinant. -/
theorem deriv_schattenDet_eq {p : ℕ} (hp : 0 < p) {lam : ι → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hS0 : 0 ≤ S)
    (hbound : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ S * B ^ k)
    {r : ℝ} (hr : 0 < r) (hrB : r * B < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    deriv (fun w : ℂ => schattenDet p lam w) z
      = -(schattenDet p lam z) * deriv (fun w : ℂ => schattenDetExp p lam w) z := by
  have hd := differentiableAt_schattenDetExp hp hB1 hS0 hbound hr hrB hz
  have h := (hd.hasDerivAt.neg).cexp
  have hval : deriv (fun w : ℂ => schattenDet p lam w) z
      = Complex.exp (-schattenDetExp p lam z)
        * -deriv (fun w : ℂ => schattenDetExp p lam w) z := h.deriv
  rw [hval, schattenDet]
  ring

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
      (nhds (deriv (fun w : ℂ => schattenDet p mu w) z)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hzr : ‖z‖ ≤ r := by
    rw [mem_ball, dist_zero_right] at hz
    exact hz.le
  have hzB : ‖z‖ * B < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzr hB0) hrB
  have hdet := tendsto_schattenDet_of_tendsto_tracePower hp hB1 hS0 hbound hconv hzB
  have hexp := tendsto_deriv_schattenDetExp_of_tendsto_tracePower hp hB1 hS0 hbound hboundmu
    hconv hr hrB hz
  rw [deriv_schattenDet_eq hp hB1 hS0 hboundmu hr hrB hz]
  refine Filter.Tendsto.congr
    (fun a => (deriv_schattenDet_eq hp hB1 hS0 (hbound a) hr hrB hz).symm) ?_
  exact (hdet.neg).mul hexp

end

end GaloisForLFunctions.HTGeometry
