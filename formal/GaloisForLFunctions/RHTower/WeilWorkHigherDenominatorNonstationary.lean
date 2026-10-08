import GaloisForLFunctions.HTGeometry.NonstationaryPhaseIteration
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

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

/-- First amplitude after division by phase speed and differentiation. -/
def phaseAmplitudeD (A A' v v' : ℝ → ℂ) (x : ℝ) : ℂ :=
  A' x / v x - A x * v' x / v x ^ 2

/-- Second amplitude after the same operation twice. -/
def phaseAmplitudeDD (A A' A'' v v' v'' : ℝ → ℂ) (x : ℝ) : ℂ :=
  A'' x / v x ^ 2 - 3 * A' x * v' x / v x ^ 3 -
    A x * v'' x / v x ^ 3 + 3 * A x * v' x ^ 2 / v x ^ 4

private lemma hasDerivAt_complex_inv {v : ℝ → ℂ} {v' : ℂ} {x : ℝ}
    (hv : HasDerivAt v v' x) (hne : v x ≠ 0) :
    HasDerivAt (fun t => (v t)⁻¹) (-v' / v x ^ 2) x := by
  have h := (hasDerivAt_inv hne).complexToReal_fderiv.comp_hasDerivAt x hv
  refine h.congr_deriv ?_
  simp [div_eq_mul_inv, mul_comm]

private lemma hasDerivAt_complex_div {A v : ℝ → ℂ} {A' v' : ℂ} {x : ℝ}
    (hA : HasDerivAt A A' x) (hv : HasDerivAt v v' x) (hne : v x ≠ 0) :
    HasDerivAt (fun t => A t / v t) ((A' * v x - A x * v') / v x ^ 2) x := by
  have h := hA.mul (hasDerivAt_complex_inv hv hne)
  simp only [div_eq_mul_inv] at *
  refine h.congr_deriv ?_
  field_simp [hne]
  ring

theorem hasDerivAt_phaseAmplitude {A A' v v' : ℝ → ℂ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hv : HasDerivAt v (v' x) x) (hne : v x ≠ 0) :
    HasDerivAt (fun t => A t / v t) (phaseAmplitudeD A A' v v' x) x := by
  refine (hasDerivAt_complex_div hA hv hne).congr_deriv ?_
  dsimp [phaseAmplitudeD]
  field_simp [hne]

theorem hasDerivAt_phaseAmplitudeD {A A' A'' v v' v'' : ℝ → ℂ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hA' : HasDerivAt A' (A'' x) x)
    (hv : HasDerivAt v (v' x) x) (hv' : HasDerivAt v' (v'' x) x) (hne : v x ≠ 0) :
    HasDerivAt (fun t => phaseAmplitudeD A A' v v' t / v t)
      (phaseAmplitudeDD A A' A'' v v' v'' x) x := by
  have h₁ := (hasDerivAt_complex_div hA' hv hne).sub
    (hasDerivAt_complex_div (hA.mul hv') (hv.pow 2) (pow_ne_zero 2 hne))
  refine (hasDerivAt_complex_div h₁ hv hne).congr_deriv ?_
  dsimp [phaseAmplitudeDD]
  field_simp [hne]
  ring

theorem phaseAmplitudeD_eq_zero {A A' v v' : ℝ → ℂ} {x : ℝ}
    (hA : A x = 0) (hA' : A' x = 0) : phaseAmplitudeD A A' v v' x = 0 := by
  simp [phaseAmplitudeD, hA, hA']

/-- A bound on the actual amplitude jets gives an explicit frequency-independent IBP budget. -/
theorem norm_phaseAmplitudeDD_le {A A' A'' v v' v'' : ℝ → ℂ} {x M G : ℝ}
    (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hA : ‖A x‖ ≤ M) (hA' : ‖A' x‖ ≤ M) (hA'' : ‖A'' x‖ ≤ M)
    (hv : ‖(v x)⁻¹‖ ≤ G) (hv' : ‖v' x‖ ≤ G) (hv'' : ‖v'' x‖ ≤ G) :
    ‖phaseAmplitudeDD A A' A'' v v' v'' x‖ ≤ M * (G ^ 2 + 4 * G ^ 4 + 3 * G ^ 6) := by
  have h₁ : ‖A'' x / v x ^ 2‖ ≤ M * G ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow, norm_mul, norm_pow]
    gcongr
  have h₂ : ‖3 * A' x * v' x / v x ^ 3‖ ≤ 3 * M * G ^ 4 := by
    calc
      ‖3 * A' x * v' x / v x ^ 3‖ = 3 * ‖A' x‖ * ‖v' x‖ * ‖(v x)⁻¹‖ ^ 3 := by
        simp [div_eq_mul_inv, ← inv_pow]
      _ ≤ 3 * M * G * G ^ 3 := by gcongr
      _ = _ := by ring
  have h₃ : ‖A x * v'' x / v x ^ 3‖ ≤ M * G ^ 4 := by
    calc
      ‖A x * v'' x / v x ^ 3‖ = ‖A x‖ * ‖v'' x‖ * ‖(v x)⁻¹‖ ^ 3 := by
        simp only [div_eq_mul_inv, ← inv_pow, norm_mul, norm_pow]
      _ ≤ M * G * G ^ 3 := by gcongr
      _ = _ := by ring
  have h₄ : ‖3 * A x * v' x ^ 2 / v x ^ 4‖ ≤ 3 * M * G ^ 6 := by
    calc
      ‖3 * A x * v' x ^ 2 / v x ^ 4‖ = 3 * ‖A x‖ * ‖v' x‖ ^ 2 * ‖(v x)⁻¹‖ ^ 4 := by
        simp [div_eq_mul_inv, ← inv_pow]
      _ ≤ 3 * M * G ^ 2 * G ^ 4 := by gcongr
      _ = _ := by ring
  unfold phaseAmplitudeDD
  calc
    ‖A'' x / v x ^ 2 - 3 * A' x * v' x / v x ^ 3 -
        A x * v'' x / v x ^ 3 + 3 * A x * v' x ^ 2 / v x ^ 4‖ ≤
        ‖A'' x / v x ^ 2‖ + ‖3 * A' x * v' x / v x ^ 3‖ +
          ‖A x * v'' x / v x ^ 3‖ + ‖3 * A x * v' x ^ 2 / v x ^ 4‖ :=
      by
        have h₅ := norm_sub_le (A'' x / v x ^ 2) (3 * A' x * v' x / v x ^ 3)
        have h₆ := norm_sub_le (A'' x / v x ^ 2 - 3 * A' x * v' x / v x ^ 3)
          (A x * v'' x / v x ^ 3)
        have h₇ := norm_add_le (A'' x / v x ^ 2 - 3 * A' x * v' x / v x ^ 3 -
          A x * v'' x / v x ^ 3) (3 * A x * v' x ^ 2 / v x ^ 4)
        linarith
    _ ≤ M * G ^ 2 + 3 * M * G ^ 4 + M * G ^ 4 + 3 * M * G ^ 6 := by gcongr
    _ = _ := by ring

end RHTower.WeilHigherDenominator
