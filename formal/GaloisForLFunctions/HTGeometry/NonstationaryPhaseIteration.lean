import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Nonstationary phase: each integration by parts buys one power of the frequency

Against a phase `e^{iLη}` with `L ≠ 0` the antiderivative of the phase is the phase itself divided
by `iL`.  So one integration by parts on an amplitude vanishing at both endpoints replaces the
amplitude by its derivative and gains the factor `|L|^{-1}`:

`∫ e^{iLη} a(η) dη = −(iL)^{-1} ∫ e^{iLη} a'(η) dη`.

Iterating `N` times gives `|L|^{-N}` against the `N`-th derivative mass.  This is the whole gain
mechanism of a dyadic block estimate: the price is `N` derivatives of the amplitude, the gain is `N`
powers of the phase frequency, and a block bound follows whenever the gain outruns the price.

The iteration is stated for an explicitly supplied chain of derivatives rather than through iterated
differentiability, so it applies directly to a family of amplitudes given by an explicit recursion.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The antiderivative of the phase `η ↦ e^{iLη}`. -/
def phaseAntideriv (L η : ℝ) : ℂ := (Complex.I * (L : ℂ))⁻¹ * Complex.exp (Complex.I * L * η)

theorem hasDerivAt_phase (L η : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * L * x))
      (Complex.I * (L : ℂ) * Complex.exp (Complex.I * L * η)) η := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 η := Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun x : ℝ => Complex.I * (L : ℂ) * (x : ℂ))
      (Complex.I * (L : ℂ)) η := by
    simpa using h1.const_mul (Complex.I * (L : ℂ))
  have hexp := HasDerivAt.cexp hlin
  refine hexp.congr_deriv ?_
  ring

theorem hasDerivAt_phaseAntideriv {L : ℝ} (hL : L ≠ 0) (η : ℝ) :
    HasDerivAt (phaseAntideriv L) (Complex.exp (Complex.I * L * η)) η := by
  have hne : (Complex.I * (L : ℂ)) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    exact_mod_cast hL
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hbase := (hasDerivAt_phase L η).const_mul (Complex.I * (L : ℂ))⁻¹
  refine hbase.congr_deriv ?_
  field_simp

theorem norm_phase (L η : ℝ) : ‖Complex.exp (Complex.I * L * η)‖ = 1 := by
  have h : Complex.I * (L : ℂ) * (η : ℂ) = ((L * η : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_phaseAntideriv (L η : ℝ) :
    ‖phaseAntideriv L η‖ = |L|⁻¹ := by
  rw [phaseAntideriv, norm_mul, norm_phase, mul_one, norm_inv, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]

/-! ## One integration by parts -/

/-- **One integration by parts.**  An amplitude vanishing at both endpoints is traded for its
derivative at the cost of a single factor `(iL)⁻¹`. -/
theorem oscillatory_ibp {a a' : ℝ → X} {α β L : ℝ} (hL : L ≠ 0)
    (ha : ∀ η ∈ uIcc α β, HasDerivAt a (a' η) η)
    (hint : IntervalIntegrable a' volume α β)
    (h0 : a α = 0) (h1 : a β = 0) :
    (∫ η in α..β, Complex.exp (Complex.I * L * η) • a η)
      = -((Complex.I * (L : ℂ))⁻¹ • ∫ η in α..β, Complex.exp (Complex.I * L * η) • a' η) := by
  have hphase : ∀ η ∈ uIcc α β,
      HasDerivAt (phaseAntideriv L) (Complex.exp (Complex.I * L * η)) η :=
    fun η _ => hasDerivAt_phaseAntideriv hL η
  have hphaseint : IntervalIntegrable
      (fun η : ℝ => Complex.exp (Complex.I * L * η)) volume α β := by
    refine (Continuous.intervalIntegrable ?_ α β)
    exact (Complex.continuous_exp.comp (by fun_prop))
  have hIBP := intervalIntegral.integral_smul_deriv_eq_deriv_smul hphase ha hphaseint hint
  rw [h0, h1] at hIBP
  simp only [smul_zero, sub_zero, zero_sub] at hIBP
  have hsplit : (∫ η in α..β, phaseAntideriv L η • a' η)
      = (Complex.I * (L : ℂ))⁻¹ • ∫ η in α..β, Complex.exp (Complex.I * L * η) • a' η := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun η _ => ?_
    rw [phaseAntideriv, mul_smul]
  rw [hsplit] at hIBP
  linear_combination (norm := module) hIBP

/-! ## The iterated gain -/

/-- **`N` integrations by parts gain `N` powers of the frequency.**  With an explicit chain of
derivatives vanishing at both endpoints, the oscillatory integral of the amplitude is bounded by
`|L|^{-N}` times the mass of the `N`-th member of the chain. -/
theorem norm_oscillatory_iterate_le {α β L : ℝ} (hL : L ≠ 0) (hαβ : α ≤ β) :
    ∀ (N : ℕ) (a : ℕ → ℝ → X),
      (∀ i, i < N → ∀ η ∈ uIcc α β, HasDerivAt (a i) (a (i + 1) η) η) →
      (∀ i, i ≤ N → IntervalIntegrable (a i) volume α β) →
      (∀ i, i < N → a i α = 0 ∧ a i β = 0) →
      ‖∫ η in α..β, Complex.exp (Complex.I * L * η) • a 0 η‖
        ≤ |L|⁻¹ ^ N * ∫ η in α..β, ‖a N η‖ := by
  intro N
  induction N with
  | zero =>
    intro a _ _ _
    have hnorm : ∀ η : ℝ, ‖Complex.exp (Complex.I * L * η) • a 0 η‖ = ‖a 0 η‖ := by
      intro η
      rw [norm_smul, norm_phase, one_mul]
    calc ‖∫ η in α..β, Complex.exp (Complex.I * L * η) • a 0 η‖
        ≤ ∫ η in α..β, ‖Complex.exp (Complex.I * L * η) • a 0 η‖ :=
          intervalIntegral.norm_integral_le_integral_norm hαβ
      _ = ∫ η in α..β, ‖a 0 η‖ := by
          exact intervalIntegral.integral_congr fun η _ => hnorm η
      _ = |L|⁻¹ ^ 0 * ∫ η in α..β, ‖a 0 η‖ := by rw [pow_zero, one_mul]
  | succ N ih =>
    intro a hderiv hintg hzero
    have hstep := oscillatory_ibp (a := a 0) (a' := a 1) hL
      (hderiv 0 (Nat.succ_pos N)) (hintg 1 (by omega)) (hzero 0 (Nat.succ_pos N)).1
      (hzero 0 (Nat.succ_pos N)).2
    have htail := ih (fun i => a (i + 1))
      (fun i hi η hη => hderiv (i + 1) (by omega) η hη)
      (fun i hi => hintg (i + 1) (by omega))
      (fun i hi => hzero (i + 1) (by omega))
    have hcoef : ‖(Complex.I * (L : ℂ))⁻¹‖ = |L|⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnn : (0 : ℝ) ≤ ∫ η in α..β, ‖a (N + 1) η‖ :=
      intervalIntegral.integral_nonneg hαβ fun η _ => norm_nonneg _
    calc ‖∫ η in α..β, Complex.exp (Complex.I * L * η) • a 0 η‖
        = |L|⁻¹ * ‖∫ η in α..β, Complex.exp (Complex.I * L * η) • a 1 η‖ := by
          rw [hstep, norm_neg, norm_smul, hcoef]
      _ ≤ |L|⁻¹ * (|L|⁻¹ ^ N * ∫ η in α..β, ‖a (N + 1) η‖) := by
          exact mul_le_mul_of_nonneg_left htail (by positivity)
      _ = |L|⁻¹ ^ (N + 1) * ∫ η in α..β, ‖a (N + 1) η‖ := by
          rw [pow_succ]
          ring

end GaloisForLFunctions.HTGeometry
