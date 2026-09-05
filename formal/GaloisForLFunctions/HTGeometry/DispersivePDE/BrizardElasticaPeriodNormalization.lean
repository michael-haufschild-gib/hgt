import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaWeierstrassTrace
import Mathlib.Tactic

/-!
# Period normalization for Brizard's Weierstrass elastica

Every period pair can be rescaled by the inverse of its first period.  The resulting period pair has
first period exactly one.  Applying the pole-free trace construction then removes the chain-rule
factor from the Weierstrass equation and produces the literal normalized equation used in the paper.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Simultaneous nonzero scaling of both generators of a period pair. -/
noncomputable def scalePeriodPair (c : ℂˣ) (L : PeriodPair) : PeriodPair where
  ω₁ := (c : ℂ) * L.ω₁
  ω₂ := (c : ℂ) * L.ω₂
  indep := by
    let e : ℂ ≃ₗ[ℝ] ℂ := DistribMulAction.toLinearEquiv ℝ ℂ c
    have h := L.indep.map' e.toLinearMap (LinearEquiv.ker e)
    change LinearIndependent ℝ (fun i => e (![L.ω₁, L.ω₂] i)) at h
    have heq : (fun i => e (![L.ω₁, L.ω₂] i)) =
        ![(c : ℂ) * L.ω₁, (c : ℂ) * L.ω₂] := by
      funext i
      fin_cases i <;> rfl
    rw [heq] at h
    exact h

@[simp] theorem scalePeriodPair_ω₁ (c : ℂˣ) (L : PeriodPair) :
    (scalePeriodPair c L).ω₁ = (c : ℂ) * L.ω₁ := rfl

@[simp] theorem scalePeriodPair_ω₂ (c : ℂˣ) (L : PeriodPair) :
    (scalePeriodPair c L).ω₂ = (c : ℂ) * L.ω₂ := rfl

theorem periodPair_omegaOne_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have h := L.indep.ne_zero 0
  simpa using h

noncomputable def normalizedPeriodScale (L : PeriodPair) : ℂˣ :=
  Units.mk0 L.ω₁⁻¹ (inv_ne_zero (periodPair_omegaOne_ne_zero L))

noncomputable def normalizedPeriodPair (L : PeriodPair) : PeriodPair :=
  scalePeriodPair (normalizedPeriodScale L) L

@[simp] theorem normalizedPeriodPair_ω₁ (L : PeriodPair) :
    (normalizedPeriodPair L).ω₁ = 1 := by
  rw [normalizedPeriodPair, scalePeriodPair_ω₁, normalizedPeriodScale]
  exact inv_mul_cancel₀ (periodPair_omegaOne_ne_zero L)

noncomputable def normalizedWeierstrass (L : PeriodPair) (x : ℝ) : ℂ :=
  halfShiftWeierstrass (normalizedPeriodPair L) x

noncomputable def normalizedWeierstrassPrime (L : PeriodPair) (x : ℝ) : ℂ :=
  halfShiftWeierstrassPrime (normalizedPeriodPair L) x

theorem hasDerivAt_normalizedWeierstrass (L : PeriodPair) (x : ℝ) :
    HasDerivAt (normalizedWeierstrass L) (normalizedWeierstrassPrime L x) x := by
  exact hasDerivAt_halfShiftWeierstrass (normalizedPeriodPair L) x

/-- Literal paper equation `(wp')² = 4wp³ - g₂wp - g₃`, globally along the trace. -/
theorem normalizedWeierstrass_equation (L : PeriodPair) (x : ℝ) :
    normalizedWeierstrassPrime L x ^ 2 =
      4 * normalizedWeierstrass L x ^ 3 -
        (normalizedPeriodPair L).g₂ * normalizedWeierstrass L x -
        (normalizedPeriodPair L).g₃ := by
  simpa [normalizedWeierstrass, normalizedWeierstrassPrime] using
    halfShiftWeierstrass_equation (normalizedPeriodPair L) x

theorem normalizedWeierstrass_periodic (L : PeriodPair) :
    Function.Periodic (normalizedWeierstrass L) 1 := by
  exact halfShiftWeierstrass_periodic (normalizedPeriodPair L)

/-- Normalized trace is a point `(wp, wp'/2)` on its short Weierstrass curve. -/
theorem normalizedWeierstrass_on_curve (L : PeriodPair) (x : ℝ) :
    (analyticWeierstrassCurve (normalizedPeriodPair L)).toAffine.Equation
      (normalizedWeierstrass L x) (normalizedWeierstrassPrime L x / 2) := by
  simpa [normalizedWeierstrass, normalizedWeierstrassPrime] using
    halfShiftWeierstrass_on_curve (normalizedPeriodPair L) x

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
