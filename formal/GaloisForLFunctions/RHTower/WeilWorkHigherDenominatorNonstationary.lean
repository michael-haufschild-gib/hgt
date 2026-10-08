import GaloisForLFunctions.HTGeometry.NonstationaryPhaseIteration
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Two integrations by parts for the moving inversion phase

The derivative chain divides the amplitude by the actual phase speed before each
derivative. All assumptions are local to the integration interval. The resulting
quadratic frequency bound will be applied to the inverted Bessel amplitude; it is
not itself a sparse-deficit theorem or an assumption on the cubic datum.
-/

noncomputable section

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

/-- A variable phase transfers one derivative to amplitude divided by phase speed. -/
theorem nonstationary_ibp {a b L : ℝ} (hL : L ≠ 0) {ψ v : ℝ → ℝ}
    (hψ : ∀ x ∈ uIcc a b, HasDerivAt ψ (v x) x)
    (hv : ContinuousOn v (uIcc a b)) (hne : ∀ x ∈ uIcc a b, v x ≠ 0)
    {A A₁ : ℝ → ℂ}
    (hA : ∀ x ∈ uIcc a b, HasDerivAt (fun t => A t / (v t : ℂ)) (A₁ x) x)
    (hA₁ : IntervalIntegrable A₁ volume a b) (ha : A a = 0) (hb : A b = 0) :
    (∫ x in a..b, Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A x) =
      -(I * (L : ℂ))⁻¹ * (∫ x in a..b, Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A₁ x) := by
  let P := fun x : ℝ => (I * (L : ℂ))⁻¹ * Complex.exp (I * (L : ℂ) * (ψ x : ℂ))
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hP : ∀ x ∈ uIcc a b, HasDerivAt P
      ((v x : ℂ) * Complex.exp (I * (L : ℂ) * (ψ x : ℂ))) x := by
    intro x hx
    have hd := (((hψ x hx).ofReal_comp.const_mul (I * (L : ℂ))).cexp).const_mul
      (I * (L : ℂ))⁻¹
    refine hd.congr_deriv ?_
    dsimp only
    field_simp [hLc]
  have hψc : ContinuousOn ψ (uIcc a b) :=
    fun x hx => (hψ x hx).continuousAt.continuousWithinAt
  have hec : ContinuousOn (fun x => Complex.exp (I * (L : ℂ) * (ψ x : ℂ))) (uIcc a b) := by
    fun_prop
  have hPi : IntervalIntegrable
      (fun x => (v x : ℂ) * Complex.exp (I * (L : ℂ) * (ψ x : ℂ))) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn hv).mul hec).intervalIntegrable
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hP hA hPi hA₁
  simp only [ha, hb, zero_div, mul_zero, sub_zero, zero_sub] at hIBP
  have hleft : (∫ x in a..b, P x * A₁ x) =
      (I * (L : ℂ))⁻¹ * (∫ x in a..b, Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A₁ x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [P]
    ring
  have hright : (∫ x in a..b, ((v x : ℂ) * Complex.exp (I * (L : ℂ) * (ψ x : ℂ))) *
      (A x / (v x : ℂ))) = ∫ x in a..b, Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxv : (v x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    field_simp [hxv]
  rw [hleft, hright] at hIBP
  linear_combination hIBP

/-- The exact twice-integrated identity, with every boundary term paid. -/
theorem nonstationary_twice_ibp {a b L : ℝ} (hL : L ≠ 0) {ψ v : ℝ → ℝ}
    (hψ : ∀ x ∈ uIcc a b, HasDerivAt ψ (v x) x)
    (hv : ContinuousOn v (uIcc a b)) (hne : ∀ x ∈ uIcc a b, v x ≠ 0)
    {A A₁ A₂ : ℝ → ℂ}
    (hA : ∀ x ∈ uIcc a b, HasDerivAt (fun t => A t / (v t : ℂ)) (A₁ x) x)
    (hA₁ : ∀ x ∈ uIcc a b, HasDerivAt (fun t => A₁ t / (v t : ℂ)) (A₂ x) x)
    (hi₁ : IntervalIntegrable A₁ volume a b) (hi₂ : IntervalIntegrable A₂ volume a b)
    (ha : A a = 0) (hb : A b = 0) (ha₁ : A₁ a = 0) (hb₁ : A₁ b = 0) :
    (∫ x in a..b, Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A x) =
      (I * (L : ℂ))⁻¹ ^ 2 * (∫ x in a..b, Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A₂ x) := by
  rw [nonstationary_ibp hL hψ hv hne hA hi₁ ha hb,
    nonstationary_ibp hL hψ hv hne hA₁ hi₂ ha₁ hb₁]
  ring

/-- Nonlinear phases retain the quadratic-frequency bound after the speed-weighted chain. -/
theorem norm_nonstationary_twice_le {a b L : ℝ} (hab : a ≤ b) (hL : L ≠ 0) {ψ v : ℝ → ℝ}
    (hψ : ∀ x ∈ uIcc a b, HasDerivAt ψ (v x) x)
    (hv : ContinuousOn v (uIcc a b)) (hne : ∀ x ∈ uIcc a b, v x ≠ 0)
    {A A₁ A₂ : ℝ → ℂ}
    (hA : ∀ x ∈ uIcc a b, HasDerivAt (fun t => A t / (v t : ℂ)) (A₁ x) x)
    (hA₁ : ∀ x ∈ uIcc a b, HasDerivAt (fun t => A₁ t / (v t : ℂ)) (A₂ x) x)
    (hi₁ : IntervalIntegrable A₁ volume a b) (hi₂ : IntervalIntegrable A₂ volume a b)
    (ha : A a = 0) (hb : A b = 0) (ha₁ : A₁ a = 0) (hb₁ : A₁ b = 0) :
    ‖∫ x in a..b, Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A x‖ ≤
      |L|⁻¹ ^ 2 * ∫ x in a..b, ‖A₂ x‖ := by
  rw [nonstationary_twice_ibp hL hψ hv hne hA hA₁ hi₁ hi₂ ha hb ha₁ hb₁,
    norm_mul, norm_pow, norm_inv, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [norm_mul, norm_phase, one_mul] using
    (intervalIntegral.norm_integral_le_integral_norm (f := fun x =>
      Complex.exp (I * (L : ℂ) * (ψ x : ℂ)) * A₂ x) hab)

end RHTower.WeilHigherDenominator
