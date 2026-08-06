import GaloisForLFunctions.HTGeometry.WirtingerDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Wirtinger derivatives along a circle

For a continuously real-differentiable `h : ℂ → ℂ` the two partial derivatives of
`(r, θ) ↦ h(r e^{iθ})` are

`∂_θ = i(w ∂h - \bar w ∂̄h)`,   `∂_r = e^{iθ} ∂h + e^{-iθ} ∂̄h`,   `w = r e^{iθ}`,

and the first integrates to zero over a full circle by periodicity.  That single identity is what
replaces a two-dimensional Stokes theorem in the proof of the Cauchy–Pompeiu formula: it says the
two Wirtinger parts contribute equally to the circle mean, so the radial derivative of the circle
mean sees only `∂̄`.

* `HTGeometry.hasDerivAt_circle_angle` : the angular derivative.
* `HTGeometry.hasDerivAt_circle_radius` : the radial derivative.
* `HTGeometry.circleMean` : the mean of `h` over the circle of radius `r`.
* `HTGeometry.circle_angle_integral_eq` : the two Wirtinger parts have equal circle integrals.
-/

open Complex Real intervalIntegral MeasureTheory

namespace HTGeometry

variable {h : ℂ → ℂ}

section Continuity

/-- `wirtingerHol` is continuous in the operator. -/
theorem continuous_wirtingerHol :
    Continuous (fun f' : ℂ →L[ℝ] ℂ => wirtingerHol f') := by
  unfold wirtingerHol
  fun_prop

/-- `wirtingerAntihol` is continuous in the operator. -/
theorem continuous_wirtingerAntihol :
    Continuous (fun f' : ℂ →L[ℝ] ℂ => wirtingerAntihol f') := by
  unfold wirtingerAntihol
  fun_prop

theorem continuous_dz (hC : ContDiff ℝ 1 h) : Continuous (dz h) :=
  continuous_wirtingerHol.comp (hC.continuous_fderiv one_ne_zero)

theorem continuous_dzbar (hC : ContDiff ℝ 1 h) : Continuous (dzbar h) :=
  continuous_wirtingerAntihol.comp (hC.continuous_fderiv one_ne_zero)

end Continuity

section Derivatives

/-- **The angular derivative of `h` on a circle.** -/
theorem hasDerivAt_circle_angle (hd : Differentiable ℝ h) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => h (circleMap 0 r t))
      (Complex.I * (circleMap 0 r θ * dz h (circleMap 0 r θ)
        - (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ))) θ := by
  have hγ : HasDerivAt (circleMap 0 r) (circleMap 0 r θ * Complex.I) θ :=
    hasDerivAt_circleMap 0 r θ
  have hf : HasFDerivAt h (fderiv ℝ h (circleMap 0 r θ)) (circleMap 0 r θ) := (hd _).hasFDerivAt
  have key := hasDerivAt_comp_wirtinger hf hγ
  rw [dz, dzbar]
  convert key using 1
  rw [map_mul, Complex.conj_I]
  ring

/-- **The radial derivative of `h` on a circle.** -/
theorem hasDerivAt_circle_radius (hd : Differentiable ℝ h) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => h (circleMap 0 s θ))
      (Complex.exp (θ * Complex.I) * dz h (circleMap 0 r θ)
        + Complex.exp (-(θ * Complex.I)) * dzbar h (circleMap 0 r θ)) r := by
  have hγ : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (Complex.exp (θ * Complex.I)) r := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := Complex.ofRealCLM.hasDerivAt
    have h2 := h1.mul_const (Complex.exp (θ * Complex.I))
    simpa [circleMap] using h2
  have hγ' : (fun s : ℝ => circleMap 0 s θ) r = circleMap 0 r θ := rfl
  have hf : HasFDerivAt h (fderiv ℝ h (circleMap 0 r θ)) ((fun s : ℝ => circleMap 0 s θ) r) := by
    rw [hγ']; exact (hd _).hasFDerivAt
  have key := hasDerivAt_comp_wirtinger (γ := fun s : ℝ => circleMap 0 s θ) (t := r) hf hγ
  have hconj : (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) = Complex.exp (-(θ * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [dz, dzbar]
  convert key using 1
  rw [hconj]
  ring

end Derivatives

section CircleMean

/-- The mean of `h` over the circle of radius `r`, without the normalising factor. -/
noncomputable def circleMean (h : ℂ → ℂ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), h (circleMap 0 r θ)

/-- **The two Wirtinger parts have equal circle integrals.**  The angular derivative integrates to
zero over a full circle because the circle closes up. -/
theorem circle_angle_integral_eq (hC : ContDiff ℝ 1 h) (r : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * π), circleMap 0 r θ * dz h (circleMap 0 r θ)) =
      ∫ θ in (0 : ℝ)..(2 * π), (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ) := by
  have hd : Differentiable ℝ h := hC.differentiable one_ne_zero
  have hc0 : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hcz : Continuous fun θ : ℝ => dz h (circleMap 0 r θ) := (continuous_dz hC).comp hc0
  have hcb : Continuous fun θ : ℝ => dzbar h (circleMap 0 r θ) := (continuous_dzbar hC).comp hc0
  have hA : Continuous fun θ : ℝ => circleMap 0 r θ * dz h (circleMap 0 r θ) := by fun_prop
  have hB : Continuous fun θ : ℝ =>
      (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ) := by fun_prop
  have hIA : IntervalIntegrable (fun θ : ℝ => circleMap 0 r θ * dz h (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) := hA.intervalIntegrable _ _
  have hIB : IntervalIntegrable
      (fun θ : ℝ => (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) := hB.intervalIntegrable _ _
  have hcont : Continuous fun θ : ℝ =>
      Complex.I * (circleMap 0 r θ * dz h (circleMap 0 r θ)
        - (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ)) := by fun_prop
  have hFTC :
      (∫ θ in (0 : ℝ)..(2 * π),
        Complex.I * (circleMap 0 r θ * dz h (circleMap 0 r θ)
          - (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ))) =
        h (circleMap 0 r (2 * π)) - h (circleMap 0 r 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hasDerivAt_circle_angle hd r θ) (hcont.intervalIntegrable _ _)
  have hper : circleMap 0 r (2 * π) = circleMap 0 r 0 := by
    simpa using periodic_circleMap 0 r 0
  rw [hper, sub_self, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hIA hIB] at hFTC
  rcases mul_eq_zero.mp hFTC with h' | h'
  · exact absurd h' Complex.I_ne_zero
  · exact sub_eq_zero.mp h'

end CircleMean

end HTGeometry
