import GaloisForLFunctions.HTGeometry.HillDrivenChartSecond
import GaloisForLFunctions.HTGeometry.HillChartWave
import GaloisForLFunctions.HTGeometry.HillClockProbe
import GaloisForLFunctions.HTGeometry.KleinGordonRealProbe

/-!
# The driven chart field solves the wave equation of its speed, with a potential

The coordinate second derivatives of the chart field are the second-order families of the previous
file, and the wave equation of the synthesis relates them: the time one is the speed squared times
the sum of the spatial ones, minus the mass term, plus the potential term.

Taking real parts costs nothing on the first two terms, whose multipliers are real. It costs the
reality of the convolving family on the third, and that is exactly the corpus's `IsRealFamily`
hypothesis: for a real density the potential is real, so the real part of the product is the product
of the real parts.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace

section DrivenChartWave

variable {d K : ℕ}

/-- The potential of the driven chart field, read on the event. -/
noncomputable def hillDrivenChartPotential (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2))
    (y : Fin (d + 1) → ℝ) : ℝ := (kgPotential (b.density (y 0)) (kgSpatial d y)).re

theorem coordPartial_coordPartial_hillDrivenChartField_zero
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) :
    coordPartial 0 (coordPartial 0 (hillDrivenChartField a b G₀)) y
      = hillDrivenChartTimeSecond a b G₀ 0 y := by
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < (K + 2 : ℕ) := by
    push_cast
    linarith
  have hcp : coordPartial 0 (hillDrivenChartField a b G₀) = hillDrivenChartTimePartial a b G₀ := by
    funext z
    rw [coordPartial_hillDrivenChartField hN a b G₀ 0 z, hillDrivenChartPartial_zero]
  rw [hcp, coordPartial, (hasFDerivAt_of_isC1OnPi (d + 1) (hillDrivenChartTimePartial a b G₀)
    (hillDrivenChartTimeSecond a b G₀) Set.univ
    (isC1OnPi_hillDrivenChartTimePartial hK a b G₀) y (Set.mem_univ y)).fderiv, piToCLM_single]

theorem coordPartial_coordPartial_hillDrivenChartField_succ
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    coordPartial i.succ (coordPartial i.succ (hillDrivenChartField a b G₀)) y
      = hillDrivenChartSpaceSecond a b G₀ i i.succ y := by
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < (K + 2 : ℕ) := by
    push_cast
    linarith
  have hcp : coordPartial i.succ (hillDrivenChartField a b G₀)
      = hillDrivenChartSpacePartial a b G₀ i := by
    funext z
    rw [coordPartial_hillDrivenChartField hN a b G₀ i.succ z, hillDrivenChartPartial_succ]
  rw [hcp, coordPartial, (hasFDerivAt_of_isC1OnPi (d + 1) (hillDrivenChartSpacePartial a b G₀ i)
    (hillDrivenChartSpaceSecond a b G₀ i) Set.univ
    (isC1OnPi_hillDrivenChartSpacePartial hK a b G₀ i) y (Set.mem_univ y)).fderiv, piToCLM_single]

/-- The spatial second family is the rescaled directional integral. -/
theorem hillDrivenChartSpaceSecond_eq (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) (y : Fin (d + 1) → ℝ) :
    hillDrivenChartSpaceSecond a b G₀ i i.succ y
      = ((((2 * Real.pi)⁻¹ : ℝ) ^ 2) *
        (∫ ξ, (2 * Real.pi * Complex.I *
            ((⟪ξ, EuclideanSpace.basisFun (Fin d) ℝ i⟫ : ℝ) : ℂ)) ^ 2 *
          kgChar (kgSpatial d y) ξ * hillDrivenDensity a b G₀ (y 0) ξ).re) := by
  rw [hillDrivenChartSpaceSecond_succ]
  show (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDrivenDensity a b G₀ (y 0))))
      (kgSpatial d y)).re = _
  rw [kgDir_eq_basisFun, kgSynthesis_dirSq_smul, Complex.re_ofReal_mul]

/-- **The driven chart field satisfies the wave equation of its speed, with the potential.** -/
theorem hillDrivenChartField_wave_identity
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (hreal : IsRealFamily b) (y : Fin (d + 1) → ℝ) :
    coordPartial 0 (coordPartial 0 (hillDrivenChartField a b G₀)) y
      = a.speed (y 0) ^ 2 *
          (∑ i : Fin d,
            coordPartial i.succ (coordPartial i.succ (hillDrivenChartField a b G₀)) y) -
        a.mass ^ 2 * hillDrivenChartField a b G₀ y +
        hillDrivenChartPotential b y * hillDrivenChartField a b G₀ y := by
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < (K + 2 : ℕ) := by
    push_cast
    linarith
  set X : EuclideanSpace ℝ (Fin d) := kgSpatial d y with hX
  have him : (kgPotential (b.density (y 0)) X).im = 0 := kgPotential_im (hreal (y 0)) X
  have hwave := hillDrivenField_wave_equation hN a b G₀ (EuclideanSpace.basisFun (Fin d) ℝ)
    (y 0) X
  have htime : coordPartial 0 (coordPartial 0 (hillDrivenChartField a b G₀)) y
      = (deriv (deriv fun r : ℝ => hillDrivenField a b G₀ r X) (y 0)).re := by
    rw [coordPartial_coordPartial_hillDrivenChartField_zero hK a b G₀ y,
      hillDrivenChartTimeSecond_zero,
      (hasDerivAt_deriv_hillDrivenField hN a b G₀ X (y 0)).deriv]
    rfl
  have hspace : ∀ i : Fin d,
      coordPartial i.succ (coordPartial i.succ (hillDrivenChartField a b G₀)) y
        = (((2 * Real.pi)⁻¹ : ℝ) ^ 2) *
          (∫ ξ, (2 * Real.pi * Complex.I *
              ((⟪ξ, EuclideanSpace.basisFun (Fin d) ℝ i⟫ : ℝ) : ℂ)) ^ 2 *
            kgChar X ξ * hillDrivenDensity a b G₀ (y 0) ξ).re := by
    intro i
    rw [coordPartial_coordPartial_hillDrivenChartField_succ hK a b G₀ y i,
      hillDrivenChartSpaceSecond_eq a b G₀ i y]
  have hfield : hillDrivenChartField a b G₀ y = (hillDrivenField a b G₀ (y 0) X).re := rfl
  rw [htime, hwave, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    Complex.re_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hspace i]
  have hpot : (kgPotential (b.density (y 0)) X * hillDrivenField a b G₀ (y 0) X).re
      = hillDrivenChartPotential b y * hillDrivenChartField a b G₀ y := by
    rw [Complex.mul_re, him, hillDrivenChartPotential, hfield]
    ring
  rw [hpot, hfield]
  have hpi : ((2 * Real.pi) ^ 2 : ℝ) ≠ 0 := by
    have := Real.pi_pos
    positivity
  have hsum : a.speed (y 0) ^ 2 *
      (∑ i : Fin d, ((2 * Real.pi)⁻¹ : ℝ) ^ 2 *
        (∫ ξ, (2 * Real.pi * Complex.I *
            ((⟪ξ, EuclideanSpace.basisFun (Fin d) ℝ i⟫ : ℝ) : ℂ)) ^ 2 *
          kgChar X ξ * hillDrivenDensity a b G₀ (y 0) ξ).re)
      = a.speed (y 0) ^ 2 / (2 * Real.pi) ^ 2 *
        ∑ i : Fin d, (∫ ξ, (2 * Real.pi * Complex.I *
            ((⟪ξ, EuclideanSpace.basisFun (Fin d) ℝ i⟫ : ℝ) : ℂ)) ^ 2 *
          kgChar X ξ * hillDrivenDensity a b G₀ (y 0) ξ).re := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hsum]


/-- **The driven chart field solves the potential-dressed wave equation of its speed.** The
potential is the chart potential of the convolving family, shifted by the mass. -/
theorem solvesPotentialWave_hillDrivenChartField
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (hreal : IsRealFamily b) :
    SolvesPotentialWave (hillWaveOp d a.speed)
      (fun y => hillDrivenChartPotential b y - a.mass ^ 2) (hillDrivenChartField a b G₀) := by
  intro y
  have hwave := hillDrivenChartField_wave_identity hK a b G₀ hreal y
  show hillWaveOp d a.speed (hillDrivenChartField a b G₀) y +
    (hillDrivenChartPotential b y - a.mass ^ 2) * hillDrivenChartField a b G₀ y = 0
  rw [hillWaveOp, hwave]
  ring

end DrivenChartWave

end GaloisForLFunctions.HTGeometry
