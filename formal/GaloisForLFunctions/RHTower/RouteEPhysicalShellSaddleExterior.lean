import GaloisForLFunctions.RHTower.RouteESourceFaithfulEulerTiltUnitShell
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Physical-shell Gaussian exterior for the exact parity--energy Euler product

The finite source product has modulus at most one. This gives an unconditional
off-saddle bound at the deficit-matching Gaussian window. It does not establish
the complex central-saddle lower bound or prime-array scale asymptotics.
-/

open Complex MeasureTheory Set

namespace RHTower

theorem norm_routeEParityEnergyEulerProduct_le_one
    (sigma t : ℝ) (P : Finset Nat.Primes) :
    ‖routeEParityEnergyEulerProduct sigma t P‖ ≤ 1 := by
  unfold routeEParityEnergyEulerProduct
  rw [norm_prod]
  calc
    (∏ p ∈ P,
        ‖(1 - routeEParityEnergyLocalCoordinate sigma t p) /
          (1 + Complex.ofReal ((p : ℝ) ^ (-sigma)))‖) ≤
      ∏ _p ∈ P, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact norm_nonneg _
        · intro p hp
          let r : ℝ := (p : ℝ) ^ (-sigma)
          have hr : 0 ≤ r := by dsimp [r]; positivity
          have hr1 : 0 < 1 + r := by linarith
          have hphase : ‖Complex.exp (-(t * Real.log (p : ℕ) : ℝ) * Complex.I)‖ = 1 := by
            simpa only [Complex.ofReal_neg] using
              (Complex.norm_exp_ofReal_mul_I (-(t * Real.log (p : ℕ))))
          have hnum : ‖1 - routeEParityEnergyLocalCoordinate sigma t p‖ ≤ 1 + r := by
            calc
              ‖1 - routeEParityEnergyLocalCoordinate sigma t p‖ ≤
                  ‖(1 : ℂ)‖ + ‖routeEParityEnergyLocalCoordinate sigma t p‖ :=
                    norm_sub_le _ _
              _ = 1 + r := by
                unfold routeEParityEnergyLocalCoordinate
                rw [norm_one, norm_mul, hphase, mul_one, Complex.norm_real,
                  Real.norm_eq_abs, abs_of_nonneg hr]
          rw [norm_div]
          have hden : ‖(1 : ℂ) + Complex.ofReal r‖ = 1 + r := by
            have hcast : (1 : ℂ) + Complex.ofReal r = Complex.ofReal (1 + r) := by
              push_cast
              ring
            rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr1]
          rw [show (p : ℝ) ^ (-sigma) = r from rfl, hden]
          exact (div_le_one hr1).2 hnum
    _ = 1 := by simp

theorem routeE_gaussian_exterior_bound (b h : ℝ) (hb : 0 < b) :
    (∫ τ in {τ : ℝ | h ^ 2 ≤ τ ^ 2}, Real.exp (-b * τ ^ 2)) ≤
      Real.exp (-(b / 2) * h ^ 2) *
        ∫ τ : ℝ, Real.exp (-(b / 2) * τ ^ 2) := by
  let S : Set ℝ := {τ | h ^ 2 ≤ τ ^ 2}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le measurable_const (measurable_id.pow_const 2)
  have hhalf : 0 < b / 2 := by positivity
  have hhalf_int : Integrable (fun τ : ℝ => Real.exp (-(b / 2) * τ ^ 2)) :=
    integrable_exp_neg_mul_sq hhalf
  have hmajor : ∀ τ ∈ S,
      Real.exp (-b * τ ^ 2) ≤
        Real.exp (-(b / 2) * h ^ 2) * Real.exp (-(b / 2) * τ ^ 2) := by
    intro τ hτ
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [S] at hτ
    nlinarith [mul_nonneg (le_of_lt hhalf) (sub_nonneg.mpr hτ)]
  calc
    (∫ τ in S, Real.exp (-b * τ ^ 2)) ≤
        ∫ τ in S, Real.exp (-(b / 2) * h ^ 2) *
          Real.exp (-(b / 2) * τ ^ 2) := by
            apply integral_mono_of_nonneg (μ := volume.restrict S)
              (ae_of_all _ (fun τ => (Real.exp_pos _).le))
              (hhalf_int.const_mul _).integrableOn
            filter_upwards [ae_restrict_mem hS] with τ hτ
            exact hmajor τ hτ
    _ = Real.exp (-(b / 2) * h ^ 2) *
        ∫ τ in S, Real.exp (-(b / 2) * τ ^ 2) := by
          rw [integral_const_mul]
    _ ≤ Real.exp (-(b / 2) * h ^ 2) *
        ∫ τ : ℝ, Real.exp (-(b / 2) * τ ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · exact setIntegral_le_integral hhalf_int
              (ae_of_all _ (fun τ => (Real.exp_pos _).le))
          · exact (Real.exp_pos _).le

private theorem routeE_eulerProduct_continuous (sigma t : ℝ) (P : Finset Nat.Primes) :
    Continuous (fun τ : ℝ => routeEParityEnergyEulerProduct sigma (t - τ) P) := by
  unfold routeEParityEnergyEulerProduct routeEParityEnergyLocalCoordinate
  fun_prop

private theorem routeE_gaussian_phase_continuous (b μ : ℝ) :
    Continuous (fun τ : ℝ =>
      (Real.exp (-b * τ ^ 2) : ℂ) *
        Complex.exp (-(τ * μ : ℝ) * Complex.I)) := by
  fun_prop

theorem routeE_gaussian_eulerProduct_exterior_bound
    (sigma t μ b h : ℝ) (P : Finset Nat.Primes) (hb : 0 < b) :
    ‖∫ τ in {τ : ℝ | h ^ 2 ≤ τ ^ 2},
        (Real.exp (-b * τ ^ 2) : ℂ) *
          Complex.exp (-(τ * μ : ℝ) * Complex.I) *
            routeEParityEnergyEulerProduct sigma (t - τ) P‖ ≤
      Real.exp (-(b / 2) * h ^ 2) *
        ∫ τ : ℝ, Real.exp (-(b / 2) * τ ^ 2) := by
  let f : ℝ → ℂ := fun τ =>
    (Real.exp (-b * τ ^ 2) : ℂ) *
      Complex.exp (-(τ * μ : ℝ) * Complex.I) *
        routeEParityEnergyEulerProduct sigma (t - τ) P
  have hfcont : Continuous f := by
    dsimp [f]
    exact (routeE_gaussian_phase_continuous b μ).mul
      (routeE_eulerProduct_continuous sigma t P)
  have hpoint : ∀ τ : ℝ, ‖f τ‖ ≤ Real.exp (-b * τ ^ 2) := by
    intro τ
    dsimp [f]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hphase : ‖Complex.exp (-(τ * μ : ℝ) * Complex.I)‖ = 1 := by
      simpa only [Complex.ofReal_neg] using
        (Complex.norm_exp_ofReal_mul_I (-(τ * μ)))
    rw [hphase, mul_one]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left
        (norm_routeEParityEnergyEulerProduct_le_one sigma (t - τ) P)
        (Real.exp_nonneg _))
  have hfint : Integrable f :=
    (integrable_exp_neg_mul_sq hb).mono' hfcont.aestronglyMeasurable
      (ae_of_all _ hpoint)
  have hgint : Integrable (fun τ : ℝ => Real.exp (-b * τ ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  calc
    ‖∫ τ in {τ : ℝ | h ^ 2 ≤ τ ^ 2}, f τ‖ ≤
        ∫ τ in {τ : ℝ | h ^ 2 ≤ τ ^ 2}, ‖f τ‖ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ τ in {τ : ℝ | h ^ 2 ≤ τ ^ 2}, Real.exp (-b * τ ^ 2) := by
      apply integral_mono hfint.norm.integrableOn hgint.integrableOn
      intro τ
      exact hpoint τ
    _ ≤ Real.exp (-(b / 2) * h ^ 2) *
        ∫ τ : ℝ, Real.exp (-(b / 2) * τ ^ 2) :=
          routeE_gaussian_exterior_bound b h hb

/-- At the deficit-matching window, the entire literal finite Euler product has
Gaussian exterior mass at most one full deficit exponential. -/
theorem routeE_gaussian_eulerProduct_exterior_deficit
    (sigma t μ b D : ℝ) (P : Finset Nat.Primes)
    (hb : 0 < b) (hD : 0 ≤ D) :
    ‖∫ τ in {τ : ℝ | (Real.sqrt (2 * D / b)) ^ 2 ≤ τ ^ 2},
        (Real.exp (-b * τ ^ 2) : ℂ) *
          Complex.exp (-(τ * μ : ℝ) * Complex.I) *
            routeEParityEnergyEulerProduct sigma (t - τ) P‖ ≤
      Real.exp (-D) * Real.sqrt (Real.pi / (b / 2)) := by
  have hq : 0 ≤ 2 * D / b := div_nonneg (by positivity) hb.le
  have hh : (Real.sqrt (2 * D / b)) ^ 2 = 2 * D / b := Real.sq_sqrt hq
  have hexp : -(b / 2) * (Real.sqrt (2 * D / b)) ^ 2 = -D := by
    rw [hh]
    field_simp [hb.ne']
  simpa only [hexp, integral_gaussian] using
    (routeE_gaussian_eulerProduct_exterior_bound sigma t μ b
      (Real.sqrt (2 * D / b)) P hb)

end RHTower
