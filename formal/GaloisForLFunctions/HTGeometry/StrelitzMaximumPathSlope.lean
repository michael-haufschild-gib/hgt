import GaloisForLFunctions.HTGeometry.StrelitzMaximumSlope
import GaloisForLFunctions.HTGeometry.StrelitzMaximumPathDerivative

/-!
# Maximum-path realization of the canonical maximum slope

On a differentiable local path of genuine circle maximizers, the choice-free convex right slope of
the logarithmic maximum modulus equals the real first Euler logarithmic jet.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Set

noncomputable section

/-- Derivative of logarithmic modulus along a differentiable logarithmic polar path. -/
theorem hasDerivAt_log_norm_strelitzLogPolarPath
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hfz : coeffFun a (strelitzLogPolarPath θ t) ≠ 0) :
    HasDerivAt
      (fun s => Real.log ‖coeffFun a (strelitzLogPolarPath θ s)‖)
      (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ t) *
        (1 + Complex.I * (θ' : ℂ))).re t := by
  let z := strelitzLogPolarPath θ t
  have hf : HasDerivAt (coeffFun a) (deriv (coeffFun a) z) z :=
    (differentiable_coeffFun ha z).hasDerivAt
  have hcomp := hf.comp t (hasDerivAt_strelitzLogPolarPath hθ)
  have hlog := RHTower.hasDerivAt_log_norm_comp hcomp hfz
  simp only [Function.comp_apply] at hlog
  convert hlog using 1
  simp only [z, eulerLogDeriv]
  apply congrArg Complex.re
  ring

/-- A differentiable local path of circle maximizers differentiates the exact logarithmic maximum
with derivative equal to the real first Euler logarithmic jet. -/
theorem hasDerivAt_strelitzLogMaximum_of_maximumPath
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hmax : ∀ᶠ s : ℝ in nhds t,
      strelitzLogPolarPath θ s ∈ circleMaximumSet (coeffFun a)) :
    HasDerivAt (strelitzLogMaximum a)
      (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ t)).re t := by
  have hfz := coeffFun_ne_zero_of_strelitzLogPolarPath_mem_circleMaximumSet
    ha hn₀ hmax.self_of_nhds
  have hlog := hasDerivAt_log_norm_strelitzLogPolarPath ha hθ hfz
  have him := eulerLogDeriv_im_eq_zero_of_mem_circleMaximumSet ha
    (strelitzLogPolarPath_ne_zero θ t) hfz hmax.self_of_nhds
  have hderiv :
      (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ t) *
        (1 + Complex.I * (θ' : ℂ))).re =
      (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ t)).re := by
    norm_num [Complex.mul_re, him]
  rw [hderiv] at hlog
  apply hlog.congr_of_eventuallyEq
  filter_upwards [hmax] with s hs
  have heq := (mem_circleMaximumSet_iff_norm_eq_coeffCircleMaximumNorm
    ha (by simpa using Real.exp_pos s)).mp hs
  simp only [norm_strelitzLogPolarPath] at heq
  simp [strelitzLogMaximum, heq]

/-- On a differentiable local maximum path, the canonical exact maximum slope is the real first
Euler logarithmic jet at the maximizing point. -/
theorem strelitzMaximumSlope_eq_re_eulerLogDeriv_of_maximumPath
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hmax : ∀ᶠ s : ℝ in nhds t,
      strelitzLogPolarPath θ s ∈ circleMaximumSet (coeffFun a)) :
    strelitzMaximumSlope a t =
      (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ t)).re := by
  exact convexRightSlope_eq_of_hasDerivAt
    (convexOn_strelitzLogMaximum ha hn₀)
    (hasDerivAt_strelitzLogMaximum_of_maximumPath ha hn₀ hθ hmax)

end

end GaloisForLFunctions.HTGeometry
