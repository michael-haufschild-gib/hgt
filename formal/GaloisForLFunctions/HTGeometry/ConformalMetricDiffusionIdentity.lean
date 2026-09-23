import GaloisForLFunctions.HTGeometry.ConformalMetricClockCalculus

/-!
# The conformal clock diffusion identity for a smooth metric

The algebraic conjugation law of a second-order clock calculus is here instantiated at the literal
d'Alembertian of a smooth metric chart: `L = □_g` in divergence form, `Γ(f,h) = Gⁱʲ∂ᵢf∂ⱼh`, and the
conformally rescaled metric `e^{2σ}g`.

In four dimensions the conjugated operator carries no first-order derivative of the measured field:
conjugation by the inverse weight leaves the original d'Alembertian and one scalar defect
`w⁻¹□w`, common to every species, while a calibrated squared mass multiplies the conformal scale
`w²`. Two distinct masses therefore recover the scale itself.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

namespace SmoothMetricChart

variable {d : ℕ} (M : SmoothMetricChart d)

/-! ## The conjugation law at the metric d'Alembertian -/

/-- **The conformal conjugation law of the metric d'Alembertian.** Conjugating the d'Alembertian of
the rescaled metric `e^{2σ}g` by the weight `e^{-aσ}`, `a = (d-2)/2`, returns the original
d'Alembertian plus a zeroth-order defect: no first-order derivative survives. -/
theorem dalembert_conformalRescale_conjugation {sigma u : (Fin d → ℝ) → ℝ}
    (hsigma : ContDiff ℝ ∞ sigma) (hu : ContDiff ℝ ∞ u) (x : Fin d → ℝ) :
    Real.exp ((ExponentialSecondOrderClockCalculus.conformalDimensionWeight d + 2) * sigma x) *
        (M.conformalRescale sigma hsigma).dalembert
          (fun y => Real.exp (-ExponentialSecondOrderClockCalculus.conformalDimensionWeight d
            * sigma y) * u y) x =
      M.dalembert u x +
        (-ExponentialSecondOrderClockCalculus.conformalDimensionWeight d * M.dalembert sigma x -
          ExponentialSecondOrderClockCalculus.conformalDimensionWeight d ^ (2 : ℕ) *
            M.gradPair sigma sigma x) * u x := by
  set S : ↥(smoothScalarAlgebra d) := ⟨sigma, hsigma⟩ with hS
  set U : ↥(smoothScalarAlgebra d) := ⟨u, hu⟩ with hU
  have habs := M.expClockCalculus.conformalWaveSigma_conjugation
    (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) S U
  have hcoe := congrArg (fun v : ↥(smoothScalarAlgebra d) => (v : (Fin d → ℝ) → ℝ) x) habs
  simp only [smoothScalarAlgebra_coe_mul, smoothScalarAlgebra_coe_add,
    smoothScalarAlgebra_coe_sub, smoothScalarAlgebra_coe_smul, expClockCalculus_expSmul,
    smoothExpSmul_coe, expClockCalculus_toSecondOrder, secondOrderCalculus_laplacian,
    secondOrderCalculus_gamma, clockLaplacian_coe, clockGamma_coe, Pi.mul_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hcoe
  rw [M.conformalWaveSigma_eq_dalembert_conformalRescale S
    (smoothExpSmul (-ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) S * U)] at hcoe
  exact hcoe

/-! ## Four dimensions -/

/-- The four-dimensional conjugation weight is `1`. -/
theorem conformalDimensionWeight_four :
    ExponentialSecondOrderClockCalculus.conformalDimensionWeight 4 = 1 := by
  rw [ExponentialSecondOrderClockCalculus.conformalDimensionWeight]
  norm_num

/-- The d'Alembertian of the weight `w = e^σ` is `w(□σ + Γ(σ,σ))`. -/
theorem dalembert_exp {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    (x : Fin d → ℝ) :
    M.dalembert (fun y => Real.exp (sigma y)) x =
      Real.exp (sigma x) * (M.dalembert sigma x + M.gradPair sigma sigma x) := by
  have h := M.dalembert_expSmul 1 hsigma x
  simpa using h

/-- **The four-dimensional conformal clock conjugation at the metric d'Alembertian.** With
`w = e^σ`, conjugation of the rescaled wave operator by `w⁻¹` leaves exactly the original
d'Alembertian and the single geometric defect `w⁻¹□w`. -/
theorem dalembert_conformalRescale_conjugation_four (M : SmoothMetricChart 4)
    {sigma u : (Fin 4 → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) (hu : ContDiff ℝ ∞ u)
    (x : Fin 4 → ℝ) :
    Real.exp (sigma x) ^ (3 : ℕ) *
        (M.conformalRescale sigma hsigma).dalembert
          (fun y => (Real.exp (sigma y))⁻¹ * u y) x =
      M.dalembert u x -
        ((Real.exp (sigma x))⁻¹ * M.dalembert (fun y => Real.exp (sigma y)) x) * u x := by
  have hbase := M.dalembert_conformalRescale_conjugation hsigma hu x
  rw [conformalDimensionWeight_four] at hbase
  have hweight : ∀ y : Fin 4 → ℝ, Real.exp (-1 * sigma y) = (Real.exp (sigma y))⁻¹ := by
    intro y
    rw [neg_mul, one_mul, Real.exp_neg]
  have hcube : Real.exp ((1 + 2) * sigma x) = Real.exp (sigma x) ^ (3 : ℕ) := by
    rw [show ((1 : ℝ) + 2) * sigma x = sigma x + (sigma x + sigma x) by ring, Real.exp_add,
      Real.exp_add]
    ring
  simp only [hweight, hcube] at hbase
  rw [hbase, M.dalembert_exp hsigma x]
  have hne : Real.exp (sigma x) ≠ 0 := Real.exp_ne_zero _
  field_simp
  ring

/-! ## The two-species scale law -/

/-- The conformal clock potential of a species: its calibrated squared mass times the conformal
scale, minus the common geometric defect. -/
noncomputable def conformalClockPotential (sigma : (Fin d → ℝ) → ℝ) (massSq : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  massSq * Real.exp (sigma x) ^ (2 : ℕ) -
    (Real.exp (sigma x))⁻¹ * M.dalembert (fun y => Real.exp (sigma y)) x

/-- **The massive four-dimensional conformal clock law at the metric d'Alembertian.** -/
theorem dalembert_conformalKleinGordon_four (M : SmoothMetricChart 4)
    {sigma u : (Fin 4 → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) (hu : ContDiff ℝ ∞ u)
    (massSq : ℝ) (x : Fin 4 → ℝ) :
    Real.exp (sigma x) ^ (3 : ℕ) *
        ((M.conformalRescale sigma hsigma).dalembert
            (fun y => (Real.exp (sigma y))⁻¹ * u y) x +
          massSq * ((Real.exp (sigma x))⁻¹ * u x)) =
      M.dalembert u x + M.conformalClockPotential sigma massSq x * u x := by
  rw [mul_add, M.dalembert_conformalRescale_conjugation_four hsigma hu x, conformalClockPotential]
  have hne : Real.exp (sigma x) ≠ 0 := Real.exp_ne_zero _
  field_simp
  ring

/-- **Two clock species recover the conformal scale.** The geometric defect is common to both
species, so the difference of their conformal clock potentials, divided by the difference of their
calibrated squared masses, is exactly the conformal scale. -/
theorem twoSpecies_scale_of_conformalClockPotential (sigma : (Fin d → ℝ) → ℝ)
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂) (x : Fin d → ℝ) :
    (M.conformalClockPotential sigma massSq₁ x - M.conformalClockPotential sigma massSq₂ x) /
        (massSq₁ - massSq₂) = Real.exp (sigma x) ^ (2 : ℕ) := by
  have hne : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
  rw [conformalClockPotential, conformalClockPotential]
  field_simp
  ring

end SmoothMetricChart

/-! ## The scale difference in the abstract calculus -/

namespace ExponentialSecondOrderClockCalculus

variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- **The two-mass potential difference is the conformal scale.** In the abstract calculus the
geometric defect cancels between two species, leaving the calibrated mass difference times the
conformal scale. -/
theorem conformalKleinGordonSigma_potential_difference (C : ExponentialSecondOrderClockCalculus A)
    (a massSq₁ massSq₂ : ℝ) (sigma : A) :
    (massSq₁ • C.expSmul 2 sigma + (-a) • C.toSecondOrder.laplacian sigma -
        a ^ (2 : ℕ) • C.toSecondOrder.gamma sigma sigma) -
      (massSq₂ • C.expSmul 2 sigma + (-a) • C.toSecondOrder.laplacian sigma -
        a ^ (2 : ℕ) • C.toSecondOrder.gamma sigma sigma) =
      (massSq₁ - massSq₂) • C.expSmul 2 sigma := by
  rw [sub_smul]
  abel

end ExponentialSecondOrderClockCalculus

end GaloisForLFunctions.HTGeometry
