import GaloisForLFunctions.HTGeometry.WienerSynthesisTimeDeriv

/-!
# The chart calculus of a density family

Every object of the construction that is read in the chart — the field, each of its partial
derivatives, and each of their partial derivatives — has the same shape: the real part of the
synthesis of a family of densities, evaluated at the chart point.

This file proves the three facts such an object needs, once and for all: it is continuous, its
derivative along the time coordinate synthesises the time derivative of the family, and its
derivative along a spatial coordinate synthesises the derived family. The second-order calculus is
then a matter of instantiating them.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {d N : ℕ}

/-- The chart object attached to a family of densities. -/
noncomputable def kgChartOf (F : ℝ → EuclideanSpace ℝ (Fin d) → ℂ) (y : Fin (d + 1) → ℝ) : ℝ :=
  (kgSynthesis (F (y 0)) (kgSpatial d y)).re

/-! ## Continuity -/

theorem continuous_kgChartOf {F : ℝ → EuclideanSpace ℝ (Fin d) → ℂ}
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N)
    (hfreq : ∀ t : ℝ, Continuous (F t))
    (htime : ∀ ξ : EuclideanSpace ℝ (Fin d), Continuous fun t : ℝ => F t ξ)
    (hbound : ∀ T : ℝ, ∃ B : ℝ, ∀ t : ℝ, |t| ≤ T → ∀ ξ : EuclideanSpace ℝ (Fin d),
      ‖F t ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * B) :
    Continuous (kgChartOf F) := by
  have hjoint : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin d) => kgSynthesis (F p.1) p.2 :=
    continuous_kgSynthesis_param (N := N) hdim hfreq htime hbound
  have hfun : kgChartOf F
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (kgSynthesis (F p.1) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := rfl
  rw [hfun]
  exact (Complex.continuous_re.comp hjoint).comp (continuous_chartPoint d)

/-! ## The time coordinate -/

theorem hasDerivAt_kgChartOf_zero {F F' : ℝ → EuclideanSpace ℝ (Fin d) → ℂ}
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N)
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable (F t) (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hmeas' : ∀ t : ℝ, AEStronglyMeasurable (F' t) (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hderiv : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin d)),
      HasDerivAt (fun r : ℝ => F r ξ) (F' t ξ) t)
    (hbound' : ∀ T : ℝ, ∃ B : ℝ, ∀ t : ℝ, |t| ≤ T → ∀ ξ : EuclideanSpace ℝ (Fin d),
      ‖F' t ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * B)
    (hint : ∀ t : ℝ, Integrable (F t) (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (y : Fin (d + 1) → ℝ) :
    HasDerivAt (fun r : ℝ => kgChartOf F (Function.update y 0 r))
      ((kgSynthesis (F' (y 0)) (kgSpatial d y)).re) (y 0) := by
  have hfun : (fun r : ℝ => kgChartOf F (Function.update y 0 r))
      = fun r : ℝ => (kgSynthesis (F r) (kgSpatial d y)).re := by
    funext r
    rw [kgChartOf, kgSpatial_update_zero, Function.update_self]
  rw [hfun]
  exact hasDerivAt_reOfComplex (hasDerivAt_kgSynthesis_time (N := N) hdim hmeas hmeas' hderiv hbound'
    (kgSpatial d y) (y 0) (hint (y 0)))

/-! ## A spatial coordinate -/

theorem hasDerivAt_kgChartOf_succ {F : ℝ → EuclideanSpace ℝ (Fin d) → ℂ}
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable (F t) (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hint : ∀ t : ℝ, Integrable (F t) (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (h1 : ∀ t : ℝ, Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖F t ξ‖)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    HasDerivAt (fun r : ℝ => kgChartOf F (Function.update y i.succ r))
      ((kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (F (y 0)))
        (kgSpatial d y)).re) (y i.succ) := by
  set X : EuclideanSpace ℝ (Fin d) := kgSpatial d y with hX
  set V : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d i with hV
  have hfun : (fun r : ℝ => kgChartOf F (Function.update y i.succ r))
      = fun r : ℝ => (kgSynthesis (F (y 0)) (X + (r - y i.succ) • V)).re := by
    funext r
    rw [kgChartOf, kgSpatial_update_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
  have hbase : HasDerivAt (fun s : ℝ => (kgSynthesis (F (y 0)) (X + s • V)).re)
      ((kgSynthesis (kgDirDensity V (F (y 0))) X).re) 0 := by
    have hcomplex := hasDerivAt_kgSynthesis_dir_synthesis (hmeas (y 0)) (hint (y 0))
      (h1 (y 0)) X V 0
    have hre := hasDerivAt_reOfComplex hcomplex
    refine hre.congr_deriv ?_
    congr 1
    rw [zero_smul, add_zero]
  have hbase' : HasDerivAt (fun s : ℝ => (kgSynthesis (F (y 0)) (X + s • V)).re)
      ((kgSynthesis (kgDirDensity V (F (y 0))) X).re) (y i.succ - y i.succ) := by
    rw [sub_self]
    exact hbase
  rw [hfun]
  exact HasDerivAt.comp_sub_const (f := fun s : ℝ => (kgSynthesis (F (y 0)) (X + s • V)).re)
    (y i.succ) (y i.succ) hbase'

end GaloisForLFunctions.HTGeometry
