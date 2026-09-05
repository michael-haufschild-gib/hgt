import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaComplementTransport
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNegativeOneUniformization

/-!
# Analytic uniformization of Brizard's `m = 2` family

The third real member of the lemniscatic anharmonic orbit is `m = 2`.  It is the complement of
`m = -1`; both presentations have `g₃ = 0`, and complement transport fixes `g₂`.  Hence the exact
same scaled square lattice uniformizes Brizard's `m = -1` and `m = 2` cubics.  Together with the
scale `q₀ ↦ q₀/2`, this closes the real orbit `{1/2, -1, 2}` at the level of analytic curves and
periodic traces.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Brizard parameters at the complementary lemniscatic modulus `m = 2`. -/
noncomputable def twoParameters (q₀ : ℝˣ) : Parameters where
  modulus := 2
  q₀ := q₀

theorem twoParameters_eq_complement_negativeOne (q₀ : ℝˣ) :
    twoParameters q₀ = complementParameters (negativeParameters negativeOneModulus q₀) := by
  unfold twoParameters complementParameters negativeParameters
  congr 1
  norm_num [negativeOneModulus]

theorem negativeOneParameters_g₃_zero (q₀ : ℝˣ) :
    g₃ (negativeParameters negativeOneModulus q₀) = 0 := by
  rw [g₃]
  norm_num [negativeParameters, negativeOneModulus]

theorem twoParameters_g₂_eq_negativeOne (q₀ : ℝˣ) :
    g₂ (twoParameters q₀) = g₂ (negativeParameters negativeOneModulus q₀) := by
  rw [twoParameters_eq_complement_negativeOne, complement_g₂]

theorem twoParameters_g₃_zero (q₀ : ℝˣ) : g₃ (twoParameters q₀) = 0 := by
  rw [twoParameters_eq_complement_negativeOne, complement_g₃,
    negativeOneParameters_g₃_zero]
  norm_num

/-- The same period pair used for `m = -1`, now read in the `m = 2` chart. -/
noncomputable def twoUniformizationPeriodPair (q₀ : ℝˣ) : PeriodPair :=
  negativeOneUniformizationPeriodPair q₀

theorem twoUniformizationPeriodPair_g₂ (q₀ : ℝˣ) :
    (twoUniformizationPeriodPair q₀).g₂ = (g₂ (twoParameters q₀) : ℂ) := by
  rw [twoUniformizationPeriodPair, negativeOneUniformizationPeriodPair_g₂,
    twoParameters_g₂_eq_negativeOne]

theorem twoUniformizationPeriodPair_g₃ (q₀ : ℝˣ) :
    (twoUniformizationPeriodPair q₀).g₃ = (g₃ (twoParameters q₀) : ℂ) := by
  rw [twoUniformizationPeriodPair, negativeOneUniformizationPeriodPair_g₃,
    negativeOneParameters_g₃_zero, twoParameters_g₃_zero]

/-- Exact analytic curve equality for every nonzero scale at `m = 2`. -/
theorem twoUniformization_curve (q₀ : ℝˣ) :
    analyticWeierstrassCurve (twoUniformizationPeriodPair q₀) =
      (weierstrassCurve (twoParameters q₀)).map Complex.ofRealHom := by
  rw [analyticWeierstrassCurve, weierstrassCurve]
  ext <;> simp [twoUniformizationPeriodPair_g₂, twoUniformizationPeriodPair_g₃]

theorem twoUniformization_curve_discriminant_ne_zero (q₀ : ℝˣ) :
    (analyticWeierstrassCurve (twoUniformizationPeriodPair q₀)).Δ ≠ 0 := by
  exact negativeOneUniformization_curve_discriminant_ne_zero q₀

/-- Paper equation (72) on the analytically uniformized `m = 2` curve. -/
theorem twoUniformization_trace_equation (q₀ : ℝˣ) (x : ℝ) :
    halfShiftWeierstrassPrime (twoUniformizationPeriodPair q₀) x ^ 2 =
      (twoUniformizationPeriodPair q₀).ω₁ ^ 2 *
        (4 * halfShiftWeierstrass (twoUniformizationPeriodPair q₀) x ^ 3 -
          (g₂ (twoParameters q₀) : ℂ) *
            halfShiftWeierstrass (twoUniformizationPeriodPair q₀) x -
          (g₃ (twoParameters q₀) : ℂ)) := by
  simpa only [twoUniformizationPeriodPair_g₂, twoUniformizationPeriodPair_g₃] using
    halfShiftWeierstrass_equation (twoUniformizationPeriodPair q₀) x

theorem twoUniformization_trace_periodic (q₀ : ℝˣ) :
    Function.Periodic (halfShiftWeierstrass (twoUniformizationPeriodPair q₀)) 1 :=
  halfShiftWeierstrass_periodic (twoUniformizationPeriodPair q₀)

/-- The periodic pole-free trace lands on Brizard's complexified `m = 2` curve. -/
theorem twoUniformization_trace_on_brizard_curve (q₀ : ℝˣ) (x : ℝ) :
    ((weierstrassCurve (twoParameters q₀)).map Complex.ofRealHom).toAffine.Equation
      (halfShiftWeierstrass (twoUniformizationPeriodPair q₀) x)
      (halfShiftWeierstrassPrime (twoUniformizationPeriodPair q₀) x /
        (2 * (twoUniformizationPeriodPair q₀).ω₁)) := by
  rw [← twoUniformization_curve]
  exact halfShiftWeierstrass_on_curve (twoUniformizationPeriodPair q₀) x

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
