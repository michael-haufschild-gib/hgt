import GaloisForLFunctions.HTGeometry.MassGaugeHalfWaveL2

/-!
# The analytically damped gauged half-wave symbol

Real-time damping multiplies the half-wave symbol by `e^{-σ Re ω}`.  Since the principal gauged
dispersion satisfies `Re ω ≥ |ξ| ≥ 0` inside the mass chamber, damping can only shrink the symbol,
so for `σ ≥ 0` and `u ≥ 0` the damped symbol keeps the radiation envelope

`|e^{-(σ+iu)ω_{a,λ}(ξ)}| ≤ e^{λ u}`.

Multiplying further by a bounded filter only rescales the envelope by the filter bound.  Damping and
bounded filtering therefore cannot lower the exponential type of the propagator.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

/-- The analytically damped gauged half-wave symbol `e^{-(σ+iu)ω_{a,λ}}`. -/
noncomputable def massGaugeDampedSymbol (a lambda sigma u xi : ℝ) : ℂ :=
  Complex.exp (-((sigma : ℂ) + (u : ℂ) * I) * massGaugeDispersion a lambda xi)

theorem massGaugeDampedSymbol_zero_sigma (a lambda u xi : ℝ) :
    massGaugeDampedSymbol a lambda 0 u xi = massGaugeHalfWaveSymbol a lambda u xi := by
  rw [massGaugeDampedSymbol, massGaugeHalfWaveSymbol]
  congr 1
  push_cast
  ring

theorem continuous_massGaugeDampedSymbol {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 ≤ lambda)
    (sigma u : ℝ) : Continuous (massGaugeDampedSymbol a lambda sigma u) := by
  unfold massGaugeDampedSymbol
  exact Complex.continuous_exp.comp
    (continuous_const.mul (continuous_massGaugeDispersion ha hlambda))

/-- Exact pointwise norm of the damped symbol. -/
theorem norm_massGaugeDampedSymbol (a lambda sigma u xi : ℝ) :
    ‖massGaugeDampedSymbol a lambda sigma u xi‖
      = Real.exp (-(sigma * (massGaugeDispersion a lambda xi).re)
          + u * (massGaugeDispersion a lambda xi).im) := by
  rw [massGaugeDampedSymbol, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im]

/-- **Damping cannot enlarge the radiation envelope.**  In the open mass chamber, for nonnegative
damping and nonnegative time the damped symbol keeps the envelope `e^{λu}`. -/
theorem norm_massGaugeDampedSymbol_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma u : ℝ} (hsigma : 0 ≤ sigma) (hu : 0 ≤ u) (xi : ℝ) :
    ‖massGaugeDampedSymbol a lambda sigma u xi‖ ≤ Real.exp (u * lambda) := by
  rw [norm_massGaugeDampedSymbol]
  refine Real.exp_le_exp.2 ?_
  have hre : 0 ≤ (massGaugeDispersion a lambda xi).re :=
    le_trans (abs_nonneg xi) (abs_le_massGaugeDispersion_re ha.le hlambda.le xi)
  have him : (massGaugeDispersion a lambda xi).im ≤ lambda :=
    le_trans (le_abs_self _) (abs_massGaugeDispersion_im_lt ha hlambda xi).le
  have h1 : sigma * (massGaugeDispersion a lambda xi).re ≥ 0 := mul_nonneg hsigma hre
  have h2 : u * (massGaugeDispersion a lambda xi).im ≤ u * lambda :=
    mul_le_mul_of_nonneg_left him hu
  linarith

end GaloisForLFunctions.HTGeometry
