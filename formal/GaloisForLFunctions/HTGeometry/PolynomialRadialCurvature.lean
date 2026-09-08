import GaloisForLFunctions.HTGeometry.EinastoQuadraticCurvatureObstruction

/-!
# Sharp positive replacement: curvature regularity of every polynomial radial core

The obstruction in the exponential Einasto correction suggests the exact
replacement criterion: the linear metric coefficient must vanish. For every
polynomial B and unrestricted a, classify the actual Kretschmann scalar of
f(r)=1+a r+r²B(r). The pole has exact coefficient 8a². When a=0, curvature
extends as a polynomial and its finite central value is 24 B(0)². Thus the
positive survivor is a complete regularity classification, not just a failed
example or a sufficient condition selected in advance.
-/
noncomputable section
open Polynomial Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def polynomialRadialCoreMetric (a : ℝ) (B : ℝ[X]) (r : ℝ) : ℝ := 1 + a * r + r ^ 2 * B.eval r

def polynomialRadialCoreSlope (a : ℝ) (B : ℝ[X]) (r : ℝ) : ℝ :=
  a + 2 * r * B.eval r + r ^ 2 * B.derivative.eval r

def polynomialRadialCoreSecond (B : ℝ[X]) (r : ℝ) : ℝ :=
  2 * B.eval r + 4 * r * B.derivative.eval r + r ^ 2 * B.derivative.derivative.eval r

/-- The complete curvature polynomial after removing the linear metric mode. -/
def polynomialRadialRegularKretschmann (B : ℝ[X]) (r : ℝ) : ℝ :=
  polynomialRadialCoreSecond B r ^ 2 + 4 * (2 * B.eval r + r * B.derivative.eval r) ^ 2 + 4 * B.eval r ^ 2

theorem polynomialRadialCoreMetric_hasDerivAt (a : ℝ) (B : ℝ[X]) (r : ℝ) :
    HasDerivAt (polynomialRadialCoreMetric a B) (polynomialRadialCoreSlope a B r) r := by
  have h := (((hasDerivAt_id r).const_mul a).const_add 1).add
    (((hasDerivAt_id r).pow 2).mul (B.hasDerivAt r))
  simp only [Pi.add_def, Pi.mul_def, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold polynomialRadialCoreSlope
  simp only [Nat.cast_ofNat]
  ring

theorem polynomialRadialCoreSlope_hasDerivAt (a : ℝ) (B : ℝ[X]) (r : ℝ) :
    HasDerivAt (polynomialRadialCoreSlope a B) (polynomialRadialCoreSecond B r) r := by
  have h := ((((hasDerivAt_id r).const_mul 2).mul (B.hasDerivAt r)).const_add a).add
    (((hasDerivAt_id r).pow 2).mul (B.derivative.hasDerivAt r))
  simp only [Pi.add_def, Pi.mul_def, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold polynomialRadialCoreSecond
  simp only [Nat.cast_ofNat]
  ring

theorem polynomialRadialCoreMetric_derivative (a : ℝ) (B : ℝ[X]) :
    deriv (polynomialRadialCoreMetric a B) = polynomialRadialCoreSlope a B := by
  funext r
  exact (polynomialRadialCoreMetric_hasDerivAt a B r).deriv

theorem polynomialRadialCoreMetric_second_derivative (a : ℝ) (B : ℝ[X]) :
    deriv (deriv (polynomialRadialCoreMetric a B)) = polynomialRadialCoreSecond B := by
  rw [polynomialRadialCoreMetric_derivative]
  funext r
  exact (polynomialRadialCoreSlope_hasDerivAt a B r).deriv

/-- Exact Laurent decomposition of the actual curvature, separating every singular term. -/
theorem polynomialRadialCoreMetric_kretschmann (a : ℝ) (B : ℝ[X]) (t : ℝ) :
    radialKretschmannScalar (polynomialRadialCoreMetric a B) (exp t) =
      8 * a ^ 2 / exp t ^ 2 + 24 * a * B.eval (exp t) / exp t +
        8 * a * B.derivative.eval (exp t) + polynomialRadialRegularKretschmann B (exp t) := by
  unfold radialKretschmannScalar
  rw [polynomialRadialCoreMetric_second_derivative, polynomialRadialCoreMetric_derivative]
  unfold polynomialRadialCoreMetric polynomialRadialCoreSlope polynomialRadialRegularKretschmann
  field_simp
  ring

theorem polynomialRadialRegularKretschmann_continuous (B : ℝ[X]) :
    Continuous (polynomialRadialRegularKretschmann B) := by
  have h0 := B.continuous
  have h1 := B.derivative.continuous
  have h2 := B.derivative.derivative.continuous
  unfold polynomialRadialRegularKretschmann polynomialRadialCoreSecond
  fun_prop

theorem polynomialRadialRegularKretschmann_core (B : ℝ[X]) :
    polynomialRadialRegularKretschmann B 0 = 24 * B.eval 0 ^ 2 := by
  unfold polynomialRadialRegularKretschmann polynomialRadialCoreSecond
  ring

/-- Every nonlinear polynomial term drops out of the leading curvature pole. -/
theorem polynomialRadialCoreMetric_scaled_curvature_limit (a : ℝ) (B : ℝ[X]) :
    Tendsto (fun t => exp t ^ 2 * radialKretschmannScalar (polynomialRadialCoreMetric a B) (exp t)) atBot
      (𝓝 (8 * a ^ 2)) := by
  have he : (fun t => exp t ^ 2 * radialKretschmannScalar (polynomialRadialCoreMetric a B) (exp t)) =
      (fun t => 8 * a ^ 2 + 24 * a * exp t * B.eval (exp t) +
        8 * a * exp t ^ 2 * B.derivative.eval (exp t) + exp t ^ 2 * polynomialRadialRegularKretschmann B (exp t)) := by
    funext t
    rw [polynomialRadialCoreMetric_kretschmann]
    field_simp
  rw [he]
  have h0 := B.continuous
  have h1 := B.derivative.continuous
  have hK := polynomialRadialRegularKretschmann_continuous B
  have hc : Continuous (fun r : ℝ => 8 * a ^ 2 + 24 * a * r * B.eval r +
      8 * a * r ^ 2 * B.derivative.eval r + r ^ 2 * polynomialRadialRegularKretschmann B r) := by
    fun_prop
  simpa [Function.comp_def] using hc.continuousAt.tendsto.comp tendsto_exp_atBot

/-- Vanishing linear mode gives an exact polynomial curvature extension. -/
theorem polynomialRadialCoreMetric_zero_linear_curvature (B : ℝ[X]) (t : ℝ) :
    radialKretschmannScalar (polynomialRadialCoreMetric 0 B) (exp t) = polynomialRadialRegularKretschmann B (exp t) := by
  rw [polynomialRadialCoreMetric_kretschmann]
  ring

/-- A nontrivial regular core survives, with a sharp central invariant. -/
theorem polynomialRadialCoreMetric_regular_limit (B : ℝ[X]) :
    Tendsto (fun t => radialKretschmannScalar (polynomialRadialCoreMetric 0 B) (exp t)) atBot
      (𝓝 (24 * B.eval 0 ^ 2)) := by
  have he : (fun t => radialKretschmannScalar (polynomialRadialCoreMetric 0 B) (exp t)) =
      (fun t => polynomialRadialRegularKretschmann B (exp t)) := by
    funext t
    exact polynomialRadialCoreMetric_zero_linear_curvature B t
  rw [he, ← polynomialRadialRegularKretschmann_core B]
  exact (polynomialRadialRegularKretschmann_continuous B).continuousAt.tendsto.comp tendsto_exp_atBot

/-- The obstruction is exact for every polynomial core, not restricted to one example. -/
theorem polynomialRadialCoreMetric_diverges_iff (a : ℝ) (B : ℝ[X]) :
    Tendsto (fun t => radialKretschmannScalar (polynomialRadialCoreMetric a B) (exp t)) atBot atTop ↔ a ≠ 0 := by
  constructor
  · intro h ha
    subst a
    have hf := polynomialRadialCoreMetric_regular_limit B
    have hgt := h.eventually_gt_atTop (24 * B.eval 0 ^ 2 + 1)
    have hlt := hf.eventually (eventually_lt_nhds (by linarith : 24 * B.eval 0 ^ 2 < 24 * B.eval 0 ^ 2 + 1))
    obtain ⟨t, ht, ht'⟩ := (hgt.and hlt).exists
    linarith
  · intro ha
    have hi : Tendsto (fun t : ℝ => exp (-t) ^ 2) atBot atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp (tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)
    have h := (polynomialRadialCoreMetric_scaled_curvature_limit a B).pos_mul_atTop
      (mul_pos (by norm_num) (sq_pos_of_ne_zero ha)) hi
    have he : (fun t => (exp t ^ 2 * radialKretschmannScalar (polynomialRadialCoreMetric a B) (exp t)) * exp (-t) ^ 2) =
        (fun t => radialKretschmannScalar (polynomialRadialCoreMetric a B) (exp t)) := by
      funext t
      rw [exp_neg]
      field_simp
    rwa [he] at h

/-- Complete finite-limit classification, including the value forced by regularity. -/
theorem polynomialRadialCoreMetric_finite_limit_iff (a k : ℝ) (B : ℝ[X]) :
    Tendsto (fun t => radialKretschmannScalar (polynomialRadialCoreMetric a B) (exp t)) atBot (𝓝 k) ↔
      a = 0 ∧ k = 24 * B.eval 0 ^ 2 := by
  constructor
  · intro h
    have ha : a = 0 := by
      by_contra ha
      have hi := (polynomialRadialCoreMetric_diverges_iff a B).mpr ha
      have hgt := hi.eventually_gt_atTop (k + 1)
      have hlt := h.eventually (eventually_lt_nhds (by linarith : k < k + 1))
      obtain ⟨t, ht, ht'⟩ := (hgt.and hlt).exists
      linarith
    subst a
    exact ⟨rfl, tendsto_nhds_unique h (polynomialRadialCoreMetric_regular_limit B)⟩
  · rintro ⟨rfl, rfl⟩
    exact polynomialRadialCoreMetric_regular_limit B

end GaloisForLFunctions.HTGeometry
