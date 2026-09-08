import GaloisForLFunctions.HTGeometry.EinastoQuadraticRadialInverse
import Mathlib.Topology.Algebra.Order.Field

/-!
# A finite first-order Einasto metric correction with divergent curvature

For the shape-one Einasto halo, the actual regular radial integral in equation
(15) of arXiv:2608.23600 vanishes at zero but has a nonzero linear term. The
resulting first-order metric is twice differentiable at every positive radius.
Its spherical-lapse Kretschmann expression diverges at the center for every
nonzero perturbation coefficient. The zero-coupling metric retains the corpus's
finite Kretschmann limit. Both algebraic R² signs have the same obstruction.

This is an exact statement about the constructed first-order metric family;
it does not identify that approximation with a full nonlinear field solution.
The proof uses the nonnegative angular-curvature contribution, so no cancellation
among first and second metric derivatives can hide the divergence.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Standard spherical-lapse Kretschmann expression with actual derivatives. -/
def radialKretschmannScalar (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (deriv (deriv f) r) ^ 2 + 4 * (deriv f r / r) ^ 2 + 4 * ((1 - f r) / r ^ 2) ^ 2

/-- The first-order metric obtained from the actual curvature source integral. -/
def einastoQuadraticPerturbedMetric (d l σ β r : ℝ) : ℝ :=
  einastoMetric d l 0 r + β * einastoQuadraticCorrection d l σ r

theorem radialKretschmannScalar_einasto (d l a r : ℝ) :
    radialKretschmannScalar (einastoMetric d l a) r = einastoRadialKretschmann d l a r := rfl

/-- The angular term is a lower bound independent of any derivative cancellations. -/
theorem radialKretschmannScalar_angular_lower (f : ℝ → ℝ) (r : ℝ) :
    4 * ((1 - f r) / r ^ 2) ^ 2 ≤ radialKretschmannScalar f r := by
  unfold radialKretschmannScalar
  nlinarith [sq_nonneg (deriv (deriv f) r), sq_nonneg (deriv f r / r)]

theorem einastoQuadraticPerturbedMetric_zero_coupling (d l σ : ℝ) :
    einastoQuadraticPerturbedMetric d l σ 0 = einastoMetric d l 0 := by
  funext r
  simp only [einastoQuadraticPerturbedMetric, zero_mul, add_zero]

theorem einastoQuadraticPerturbedMetric_continuous (d l σ β : ℝ) :
    Continuous (einastoQuadraticPerturbedMetric d l σ β) :=
  (einastoMetric_continuous d l 0).add (continuous_const.mul (einastoQuadraticCorrection_continuous d l σ))

theorem einastoQuadraticPerturbedMetric_center (d l σ β : ℝ) :
    einastoQuadraticPerturbedMetric d l σ β 0 = 1 := by
  simp only [einastoQuadraticPerturbedMetric, einastoMetric_zero, einastoQuadraticCorrection_center,
    mul_zero, add_zero]

/-- Finite central lapse for every perturbation parameter, despite the curvature obstruction. -/
theorem einastoQuadraticPerturbedMetric_core_limit (d l σ β : ℝ) :
    Tendsto (einastoQuadraticPerturbedMetric d l σ β) (𝓝 0) (𝓝 1) := by
  simpa only [einastoQuadraticPerturbedMetric_center] using
    (einastoQuadraticPerturbedMetric_continuous d l σ β).continuousAt.tendsto (x := 0)

/-- Divergence occurs inside a whole static central neighborhood, not at a lapse zero. -/
theorem einastoQuadraticPerturbedMetric_eventually_pos (d l σ β : ℝ) :
    ∀ᶠ t in atBot, 0 < einastoQuadraticPerturbedMetric d l σ β (exp t) := by
  have h := (einastoQuadraticPerturbedMetric_core_limit d l σ β).comp tendsto_exp_atBot
  exact h.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

theorem einastoQuadraticPerturbedMetric_hasDerivAt (d l σ β t : ℝ) :
    HasDerivAt (einastoQuadraticPerturbedMetric d l σ β)
      (deriv (einastoMetric d l 0) (exp t) + β * deriv (einastoQuadraticCorrection d l σ) (exp t)) (exp t) := by
  have hf := einastoMetric_derivative d l 0 t
  have hh := einastoQuadraticCorrection_hasDerivAt d l σ t
  unfold einastoQuadraticPerturbedMetric
  rw [hf.deriv, hh.deriv]
  simpa only [Pi.add_def] using hf.add (hh.const_mul β)

/-- The curvature divergence occurs in an actual twice-differentiable positive-radius metric. -/
theorem einastoQuadraticPerturbedMetric_twice_differentiable (d l σ β t : ℝ) :
    DifferentiableAt ℝ (deriv (einastoQuadraticPerturbedMetric d l σ β)) (exp t) := by
  have h := (einastoMetric_second_derivative d l 0 t).differentiableAt.add
    ((einastoQuadraticCorrection_twice_differentiable d l σ t).const_mul β)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoQuadraticPerturbedMetric_hasDerivAt d l σ β (log r)).deriv
  simpa only [exp_log hr, Pi.add_apply] using he

/-- Exact first-order deficit of the actual corrected metric. -/
theorem einastoQuadraticPerturbedMetric_linear_limit (d l σ β : ℝ) :
    Tendsto (fun t => (1 - einastoQuadraticPerturbedMetric d l σ β (exp t)) / exp t) atBot
      (𝓝 (80 * Real.pi * β * exp d / exp l)) := by
  have hc := (einastoCore_continuous d l 0).continuousAt.tendsto.comp tendsto_exp_atBot
  have hb := (tendsto_exp_atBot.mul hc).const_mul 2
  have hh := (einastoQuadraticCorrection_linear_limit d l σ).const_mul β
  have he : (fun t => (1 - einastoQuadraticPerturbedMetric d l σ β (exp t)) / exp t) =
      (fun t => 2 * (exp t * einastoCore d l 0 (exp t)) - β * (einastoQuadraticCorrection d l σ (exp t) / exp t)) := by
    funext t
    unfold einastoQuadraticPerturbedMetric
    rw [einastoMetric_core]
    field_simp
    ring
  rw [he]
  have hlim := hb.sub hh
  simp only [zero_mul, mul_zero, zero_sub, Function.comp_apply] at hlim
  have hcoeff : -(β * (-80 * Real.pi * exp d / exp l)) = 80 * Real.pi * β * exp d / exp l := by ring
  rw [hcoeff] at hlim
  exact hlim

/-- The scaled angular-curvature contribution has a strictly positive limit at nonzero coupling. -/
theorem einastoQuadraticPerturbedMetric_scaled_angular_limit (d l σ β : ℝ) :
    Tendsto (fun t => 4 * ((1 - einastoQuadraticPerturbedMetric d l σ β (exp t)) / exp t) ^ 2) atBot
      (𝓝 (4 * (80 * Real.pi * β * exp d / exp l) ^ 2)) :=
  ((einastoQuadraticPerturbedMetric_linear_limit d l σ β).pow 2).const_mul 4

/-- Complete coupling classification: exactly the nonzero first-order perturbations have divergent curvature. -/
theorem einastoQuadraticPerturbedMetric_curvature_diverges_iff (d l σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoQuadraticPerturbedMetric d l σ β) (exp t)) atBot atTop ↔
      β ≠ 0 := by
  constructor
  · intro h hβ
    subst β
    simp only [einastoQuadraticPerturbedMetric_zero_coupling, radialKretschmannScalar_einasto] at h
    have hf := einastoRadialKretschmann_core_limit d l 0
    have hgt := h.eventually_gt_atTop (512 * Real.pi ^ 2 * exp d ^ 2 / 3 + 1)
    have hlt := hf.eventually (eventually_lt_nhds (by linarith :
      512 * Real.pi ^ 2 * exp d ^ 2 / 3 < 512 * Real.pi ^ 2 * exp d ^ 2 / 3 + 1))
    obtain ⟨t, ht, ht'⟩ := (hgt.and hlt).exists
    linarith
  · intro hβ
    have hne : 80 * Real.pi * β * exp d / exp l ≠ 0 := by
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hβ) (exp_ne_zero d)) (exp_ne_zero l)
    have hp : 0 < 4 * (80 * Real.pi * β * exp d / exp l) ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_ne_zero hne)
    have hi : Tendsto (fun t : ℝ => exp (-t) ^ 2) atBot atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)
    have ha := (einastoQuadraticPerturbedMetric_scaled_angular_limit d l σ β).pos_mul_atTop hp hi
    apply tendsto_atTop_mono (fun t => ?_) ha
    have he : 4 * ((1 - einastoQuadraticPerturbedMetric d l σ β (exp t)) / exp t) ^ 2 * exp (-t) ^ 2 =
        4 * ((1 - einastoQuadraticPerturbedMetric d l σ β (exp t)) / exp t ^ 2) ^ 2 := by
      rw [exp_neg]
      field_simp
    rw [he]
    exact radialKretschmannScalar_angular_lower _ _

/-- The paper's literal appendix integral therefore produces a singular first-order metric at every positive coupling. -/
theorem einastoQuadraticAppendixMetric_curvature_diverges (d l b : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoQuadraticPerturbedMetric d l (-1) (exp b)) (exp t))
      atBot atTop :=
  (einastoQuadraticPerturbedMetric_curvature_diverges_iff d l (-1) (exp b)).mpr (exp_ne_zero b)

/-- Correcting only the algebraic sign does not remove the same local curvature obstruction. -/
theorem einastoQuadraticCorrectedSignMetric_curvature_diverges (d l b : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoQuadraticPerturbedMetric d l 1 (exp b)) (exp t))
      atBot atTop :=
  (einastoQuadraticPerturbedMetric_curvature_diverges_iff d l 1 (exp b)).mpr (exp_ne_zero b)

end GaloisForLFunctions.HTGeometry
