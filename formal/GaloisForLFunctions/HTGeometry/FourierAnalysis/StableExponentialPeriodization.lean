import GaloisForLFunctions.HTGeometry.CausalFourierBridge
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Rational Fourier coefficients of stable exponential periodizations

The causal kernel `π exp(-π exp(α) t)` has the stable pole `-π exp(α)`.
Its integer periodization has coefficient `(exp(α) + 2 i k)⁻¹`. Finite
residue-weighted banks therefore have exact rational symbols at every
frequency, and their bounds do not depend on a Fourier cutoff.
-/

open MeasureTheory Complex
open scoped BigOperators FourierTransform

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The resolvent symbol of a causal exponential with positive damping `exp α`. -/
def stableExponentialSymbol (α ξ : ℝ) : ℂ :=
  ((Real.exp α : ℂ) + 2 * I * ξ)⁻¹

/-- Exact circle coefficient of the existing causal exponential kernel. -/
theorem fourierCoeff_periodized_causalExponential (α : ℝ) (k : ℤ) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-k) (x : UnitAddCircle) *
        l1Periodization (RHTower.causalFourierExponential (Real.exp α)) x) =
      stableExponentialSymbol α k := by
  rw [integral_unit_l1Periodization_mul_fourier_eq
    (RHTower.causalFourierExponential_integrable (Real.exp_pos α))]
  exact RHTower.fourier_causalFourierExponential (Real.exp_pos α) k

/-- Positive damping excludes every real-frequency pole. -/
theorem stableExponentialSymbol_denominator_ne_zero (α ξ : ℝ) :
    (Real.exp α : ℂ) + 2 * I * ξ ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
    Complex.I_re, Complex.im_ofNat, Complex.I_im, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, zero_sub, add_zero, Complex.zero_re] at hr
  exact (Real.exp_ne_zero α) hr

/-- A resolvent is bounded by the reciprocal damping at every frequency. -/
theorem norm_stableExponentialSymbol_le (α ξ : ℝ) :
    ‖stableExponentialSymbol α ξ‖ ≤ (Real.exp α)⁻¹ := by
  have hr : Real.exp α ≤ ‖(Real.exp α : ℂ) + 2 * I * ξ‖ := by
    simpa using Complex.re_le_norm ((Real.exp α : ℂ) + 2 * I * ξ)
  rw [stableExponentialSymbol, norm_inv]
  exact inv_anti₀ (Real.exp_pos α) hr

/-- Scaling by the damping gives the unit-bounded Lorentzian symbol. -/
theorem norm_normalized_stableExponentialSymbol_le_one (α ξ : ℝ) :
    ‖(Real.exp α : ℂ) * stableExponentialSymbol α ξ‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos α).le]
  calc
    Real.exp α * ‖stableExponentialSymbol α ξ‖ ≤ Real.exp α * (Real.exp α)⁻¹ :=
      mul_le_mul_of_nonneg_left (norm_stableExponentialSymbol_le α ξ) (Real.exp_pos α).le
    _ = 1 := mul_inv_cancel₀ (Real.exp_ne_zero α)

/-- A finite bank of periodized stable causal kernels. -/
def periodizedExponentialPacket {n : ℕ} (residue : Fin n → ℂ)
    (logRate : Fin n → ℝ) (x : ℝ) : ℂ :=
  ∑ j, residue j * l1Periodization
    (RHTower.causalFourierExponential (Real.exp (logRate j))) x

/-- Every Fourier coefficient of the finite bank is the corresponding rational sum. -/
theorem fourierCoeff_periodizedExponentialPacket {n : ℕ} (residue : Fin n → ℂ)
    (logRate : Fin n → ℝ) (k : ℤ) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (-k) (x : UnitAddCircle) * periodizedExponentialPacket residue logRate x) =
      ∑ j, residue j * stableExponentialSymbol (logRate j) k := by
  have hint (j : Fin n) : IntegrableOn
      (fun x : ℝ => fourier (-k) (x : UnitAddCircle) *
        (residue j * l1Periodization
          (RHTower.causalFourierExponential (Real.exp (logRate j))) x))
      (Set.Ioc (0 : ℝ) 1) := by
    apply ((integrableOn_Ioc_l1Periodization
      (RHTower.causalFourierExponential_integrable (Real.exp_pos (logRate j)))).const_mul
        (residue j)).bdd_mul (by fun_prop) (C := 1)
    exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_exp]
  simp only [periodizedExponentialPacket, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun x : ℝ => fourier (-k) (x : UnitAddCircle) *
      (residue j * l1Periodization
        (RHTower.causalFourierExponential (Real.exp (logRate j))) x)) =
      (fun x : ℝ => residue j * (fourier (-k) (x : UnitAddCircle) *
        l1Periodization (RHTower.causalFourierExponential (Real.exp (logRate j))) x)) by
    funext x; ring]
  rw [integral_const_mul, fourierCoeff_periodized_causalExponential]

/-- The finite-bank bound holds at all real frequencies, independently of sampling. -/
theorem norm_stableExponentialPacketSymbol_le {n : ℕ} (residue : Fin n → ℂ)
    (logRate : Fin n → ℝ) (ξ : ℝ) :
    ‖∑ j, residue j * stableExponentialSymbol (logRate j) ξ‖ ≤
      ∑ j, ‖residue j‖ * (Real.exp (logRate j))⁻¹ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_stableExponentialSymbol_le _ _) (norm_nonneg _)

end

end GaloisForLFunctions.HTGeometry
