import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSquareNondegenerate
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Analytic uniformization of Brizard's `m = 1/2` family

For every nonzero real scale `q₀`, this module constructs a nonzero complex dilation of the square
period lattice whose analytic invariants equal Brizard's rational `m = 1/2` invariants exactly.
Existence of the required fourth root is unconditional over the algebraically closed field `ℂ`.
The resulting analytic mathlib curve equals the complex base change of Brizard's real curve, has
nonzero discriminant, and carries a globally periodic pole-free `wp` trace satisfying paper
equation (72).
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Brizard parameters at the lemniscatic modulus. -/
noncomputable def halfParameters (q₀ : ℝˣ) : Parameters where
  modulus := 1 / 2
  q₀ := q₀

theorem halfParameters_g₂ (q₀ : ℝˣ) :
    g₂ (halfParameters q₀) = 1 / (q₀ : ℝ) ^ 2 := by
  rw [g₂, halfParameters]
  ring

theorem halfParameters_g₂_ne_zero (q₀ : ℝˣ) : g₂ (halfParameters q₀) ≠ 0 := by
  rw [halfParameters_g₂]
  exact div_ne_zero one_ne_zero (pow_ne_zero 2 q₀.ne_zero)

theorem coe_halfParameters_g₂_ne_zero (q₀ : ℝˣ) :
    (g₂ (halfParameters q₀) : ℂ) ≠ 0 := by
  exact_mod_cast halfParameters_g₂_ne_zero q₀

/-- A fourth root of the ratio between square-lattice and target `g₂`. -/
noncomputable def halfUniformizationRoot (q₀ : ℝˣ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (squarePeriodPair.g₂ / (g₂ (halfParameters q₀) : ℂ)) (by norm_num : 0 < 4))

theorem halfUniformizationRoot_pow_four (q₀ : ℝˣ) :
    halfUniformizationRoot q₀ ^ 4 =
      squarePeriodPair.g₂ / (g₂ (halfParameters q₀) : ℂ) := by
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (squarePeriodPair.g₂ / (g₂ (halfParameters q₀) : ℂ)) (by norm_num : 0 < 4))

theorem halfUniformizationRoot_ne_zero (q₀ : ℝˣ) :
    halfUniformizationRoot q₀ ≠ 0 := by
  intro hzero
  have hpow := halfUniformizationRoot_pow_four q₀
  rw [hzero] at hpow
  norm_num at hpow
  exact (div_ne_zero squarePeriodPair_g₂_ne_zero
    (coe_halfParameters_g₂_ne_zero q₀)) hpow.symm

/-- Nonzero lattice scale selected by the fourth-root construction. -/
noncomputable def halfUniformizationScale (q₀ : ℝˣ) : ℂˣ :=
  Units.mk0 (halfUniformizationRoot q₀) (halfUniformizationRoot_ne_zero q₀)

@[simp] theorem coe_halfUniformizationScale (q₀ : ℝˣ) :
    (halfUniformizationScale q₀ : ℂ) = halfUniformizationRoot q₀ := rfl

/-- The square lattice dilated to Brizard's exact scale. -/
noncomputable def halfUniformizationPeriodPair (q₀ : ℝˣ) : PeriodPair :=
  scalePeriodPair (halfUniformizationScale q₀) squarePeriodPair

theorem halfUniformizationPeriodPair_g₂ (q₀ : ℝˣ) :
    (halfUniformizationPeriodPair q₀).g₂ = (g₂ (halfParameters q₀) : ℂ) := by
  rw [halfUniformizationPeriodPair, scalePeriodPair_g₂,
    coe_halfUniformizationScale]
  have hroot := halfUniformizationRoot_pow_four q₀
  have hr : halfUniformizationRoot q₀ ≠ 0 := halfUniformizationRoot_ne_zero q₀
  have hg : (g₂ (halfParameters q₀) : ℂ) ≠ 0 := coe_halfParameters_g₂_ne_zero q₀
  rw [inv_pow]
  rw [hroot]
  field_simp
  rw [div_self squarePeriodPair_g₂_ne_zero]

theorem halfUniformizationPeriodPair_g₃ (q₀ : ℝˣ) :
    (halfUniformizationPeriodPair q₀).g₃ = (g₃ (halfParameters q₀) : ℂ) := by
  rw [halfUniformizationPeriodPair, scalePeriodPair_g₃,
    squarePeriodPair_g₃_zero]
  simp only [mul_zero]
  norm_cast
  simpa [halfParameters] using (brizard_half_modulus_g₃_zero q₀).symm

/-- Exact equality with the complex base change of Brizard's real Weierstrass curve. -/
theorem halfUniformization_curve (q₀ : ℝˣ) :
    analyticWeierstrassCurve (halfUniformizationPeriodPair q₀) =
      (weierstrassCurve (halfParameters q₀)).map Complex.ofRealHom := by
  ext <;> simp [analyticWeierstrassCurve, weierstrassCurve,
    halfUniformizationPeriodPair_g₂, halfUniformizationPeriodPair_g₃]

/-- Every curve produced by the half-modulus uniformization is nonsingular. -/
theorem halfUniformization_curve_discriminant_ne_zero (q₀ : ℝˣ) :
    (analyticWeierstrassCurve (halfUniformizationPeriodPair q₀)).Δ ≠ 0 := by
  rw [analyticWeierstrassCurve_discriminant, halfUniformizationPeriodPair_g₂,
    halfUniformizationPeriodPair_g₃]
  have hthree : g₃ (halfParameters q₀) = 0 := by
    simpa [halfParameters] using brizard_half_modulus_g₃_zero q₀
  rw [hthree]
  norm_num
  exact halfParameters_g₂_ne_zero q₀

/-- The analytic trace satisfies paper equation (72) with Brizard's exact coefficients. -/
theorem halfUniformization_trace_equation (q₀ : ℝˣ) (x : ℝ) :
    halfShiftWeierstrassPrime (halfUniformizationPeriodPair q₀) x ^ 2 =
      (halfUniformizationPeriodPair q₀).ω₁ ^ 2 *
        (4 * halfShiftWeierstrass (halfUniformizationPeriodPair q₀) x ^ 3 -
          (g₂ (halfParameters q₀) : ℂ) *
            halfShiftWeierstrass (halfUniformizationPeriodPair q₀) x -
          (g₃ (halfParameters q₀) : ℂ)) := by
  simpa only [halfUniformizationPeriodPair_g₂, halfUniformizationPeriodPair_g₃] using
    halfShiftWeierstrass_equation (halfUniformizationPeriodPair q₀) x

theorem halfUniformization_trace_periodic (q₀ : ℝˣ) :
    Function.Periodic (halfShiftWeierstrass (halfUniformizationPeriodPair q₀)) 1 :=
  halfShiftWeierstrass_periodic (halfUniformizationPeriodPair q₀)

/-- Every point of the pole-free trace lies on the complexified Brizard curve. -/
theorem halfUniformization_trace_on_brizard_curve (q₀ : ℝˣ) (x : ℝ) :
    ((weierstrassCurve (halfParameters q₀)).map Complex.ofRealHom).toAffine.Equation
      (halfShiftWeierstrass (halfUniformizationPeriodPair q₀) x)
      (halfShiftWeierstrassPrime (halfUniformizationPeriodPair q₀) x /
        (2 * (halfUniformizationPeriodPair q₀).ω₁)) := by
  rw [← halfUniformization_curve]
  exact halfShiftWeierstrass_on_curve (halfUniformizationPeriodPair q₀) x

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
