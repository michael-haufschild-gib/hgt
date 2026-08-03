import GaloisForLFunctions.HTGeometry.ClockTwoDimensionalProbe

/-!
# Two dimensions are conformally rigid: the probe survives a conformal rescaling

In dimension two the conformal transformation law of the scalar d'Alembertian degenerates. The
gradient correction carries the factor `d - 2`, and the flux of the rescaled chart is literally the
flux of the original one, so

`□_{e^{2σ}g} f = e^{-2σ} □_g f`

holds pointwise for every function, with no differentiability hypothesis at all. That is a stronger
statement than the general law, which asks for a smooth argument, and it is what the clock probes
need: they are twice differentiable, not smooth.

Consequently a clock equation on a conformally rescaled two-dimensional chart is the clock equation
on the original chart with the potential multiplied by `e^{2σ}`, and the two-dimensional existence
and determination theorems transport verbatim. Since every Lorentzian metric on a surface is
locally conformally flat, this is the two-dimensional inverse problem in its physical form.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

namespace SmoothMetricChart

variable (M : SmoothMetricChart (1 + 1)) (sigma : (Fin (1 + 1) → ℝ) → ℝ)
  (hsigma : ContDiff ℝ ∞ sigma)

/-- **In two dimensions a conformal rescaling does not change the flux.** -/
theorem flux_conformalRescale_two (f : (Fin (1 + 1) → ℝ) → ℝ) (i : Fin (1 + 1)) :
    (M.conformalRescale sigma hsigma).flux f i = M.flux f i := by
  rw [M.flux_conformalRescale sigma hsigma f i]
  funext x
  norm_num

/-- **The two-dimensional conformal law of the d'Alembertian, for an arbitrary function.** -/
theorem dalembert_conformalRescale_two (f : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ) :
    (M.conformalRescale sigma hsigma).dalembert f x
      = Real.exp (-2 * sigma x) * M.dalembert f x := by
  have hflux : ∀ i : Fin (1 + 1),
      coordPartial i ((M.conformalRescale sigma hsigma).flux f i) x
        = coordPartial i (M.flux f i) x := by
    intro i
    rw [M.flux_conformalRescale_two sigma hsigma f i]
  have hdens : (M.conformalRescale sigma hsigma).density x
      = Real.exp (2 * sigma x) * M.density x := by
    rw [M.conformalRescale_density sigma hsigma x]
    norm_num
  have hinv : (Real.exp (2 * sigma x))⁻¹ = Real.exp (-2 * sigma x) := by
    rw [← Real.exp_neg]
    ring_nf
  rw [dalembert, dalembert, hdens, Finset.sum_congr rfl fun i _ => hflux i, mul_inv, hinv]
  ring

end SmoothMetricChart

/-- **A clock equation on a conformally rescaled surface is a clock equation on the original one,
with the potential weighted by `e^{2σ}`.** -/
theorem solvesPotentialWaveAt_conformalRescale_two (M : SmoothMetricChart (1 + 1))
    (sigma : (Fin (1 + 1) → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma)
    (V u : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ) :
    SolvesPotentialWaveAt (M.conformalRescale sigma hsigma).dalembert V u x
      ↔ SolvesPotentialWaveAt M.dalembert (fun y => Real.exp (2 * sigma y) * V y) u x := by
  have hexp : Real.exp (2 * sigma x) * Real.exp (-2 * sigma x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  simp only [SolvesPotentialWaveAt, M.dalembert_conformalRescale_two sigma hsigma u x]
  constructor
  · intro h
    linear_combination Real.exp (2 * sigma x) * h - M.dalembert u x * hexp
  · intro h
    linear_combination Real.exp (-2 * sigma x) * h - V x * u x * hexp

/-- **Every conformally rescaled two-dimensional Minkowski clock spacetime admits a probe
normalised to `1` at any prescribed event.** -/
theorem exists_clockProbe_conformal_two_dimensional
    {sigma : (Fin (1 + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {V : (Fin (1 + 1) → ℝ) → ℝ}
    (hV : ContDiff ℝ 1 fun y => Real.exp (2 * sigma y) * V y) (x : Fin (1 + 1) → ℝ) :
    ∃ U : (Fin (1 + 1) → ℝ) → ℝ,
      SolvesPotentialWaveAt
          (((SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart).conformalRescale
            sigma hsigma).dalembert V U x ∧
        U x = 1 := by
  obtain ⟨U, hU, hUx⟩ := exists_clockProbe_two_dimensional hV x
  exact ⟨U, (solvesPotentialWaveAt_conformalRescale_two _ sigma hsigma V U x).mpr hU, hUx⟩

/-- **The clock probes determine the potential on a conformally rescaled surface.** -/
theorem potential_eq_of_probes_conformal_two_dimensional
    {sigma : (Fin (1 + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {V₁ V₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (hV₁ : ContDiff ℝ 1 fun y => Real.exp (2 * sigma y) * V₁ y)
    (hprobe : ∀ (U : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ),
      SolvesPotentialWaveAt
          (((SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart).conformalRescale
            sigma hsigma).dalembert V₁ U x →
        SolvesPotentialWaveAt
          (((SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart).conformalRescale
            sigma hsigma).dalembert V₂ U x) :
    V₂ = V₁ := by
  have hflat : (fun y => Real.exp (2 * sigma y) * V₂ y) = fun y => Real.exp (2 * sigma y) * V₁ y := by
    refine potential_eq_of_probes_two_dimensional hV₁ ?_
    intro U x hU
    refine (solvesPotentialWaveAt_conformalRescale_two _ sigma hsigma V₂ U x).mp ?_
    exact hprobe U x ((solvesPotentialWaveAt_conformalRescale_two _ sigma hsigma V₁ U x).mpr hU)
  funext y
  have hy := congrFun hflat y
  exact mul_left_cancel₀ (Real.exp_ne_zero (2 * sigma y)) hy

end GaloisForLFunctions.HTGeometry
