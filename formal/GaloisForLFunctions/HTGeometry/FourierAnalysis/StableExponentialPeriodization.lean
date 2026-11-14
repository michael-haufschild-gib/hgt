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

private theorem stableDenominator_re (α ξ : ℝ) :
    ((Real.exp α : ℂ) + 2 * I * ξ).re = Real.exp α := by
  change Real.exp α + ((2 : ℂ) * I * (ξ : ℂ)).re = Real.exp α
  simp

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
  have hr : Real.exp α = 0 := by
    simpa only [stableDenominator_re, Complex.zero_re] using congrArg Complex.re h
  exact (Real.exp_ne_zero α) hr

/-- A resolvent is bounded by the reciprocal damping at every frequency. -/
theorem norm_stableExponentialSymbol_le (α ξ : ℝ) :
    ‖stableExponentialSymbol α ξ‖ ≤ (Real.exp α)⁻¹ := by
  have hr : Real.exp α ≤ ‖(Real.exp α : ℂ) + 2 * I * ξ‖ := by
    simpa only [stableDenominator_re] using
      Complex.re_le_norm ((Real.exp α : ℂ) + 2 * I * ξ)
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
  have he : Continuous (fun x : ℝ => fourier (-k) (x : UnitAddCircle)) := by fun_prop
  have hint (j : Fin n) : IntegrableOn
      (fun x : ℝ => fourier (-k) (x : UnitAddCircle) *
        (residue j * l1Periodization
          (RHTower.causalFourierExponential (Real.exp (logRate j))) x))
      (Set.Ioc (0 : ℝ) 1) := by
    apply ((integrableOn_Ioc_l1Periodization
      (RHTower.causalFourierExponential_integrable (Real.exp_pos (logRate j)))).const_mul
        (residue j)).bdd_mul he.aestronglyMeasurable (c := 1)
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

/-- Each real-pole resolvent already has Hermitian frequency symmetry. -/
theorem stableExponentialSymbol_conj (α ξ : ℝ) :
    star (stableExponentialSymbol α (-ξ)) = stableExponentialSymbol α ξ := by
  simp [stableExponentialSymbol, mul_assoc, -Complex.ofReal_exp]

/-- Averaging a symbol with its conjugate reflection. -/
def hermitianFrequencyProjection (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (φ ξ + star (φ (-ξ))) / 2

/-- The completed symbol has conjugate symmetry at every frequency. -/
theorem hermitianFrequencyProjection_symmetry (φ : ℝ → ℂ) (ξ : ℝ) :
    star (hermitianFrequencyProjection φ (-ξ)) = hermitianFrequencyProjection φ ξ := by
  simp only [hermitianFrequencyProjection, neg_neg, star_div₀, star_add, star_star, star_ofNat]
  ring

/-- In particular, the zero-frequency coefficient is real. -/
theorem hermitianFrequencyProjection_zero_im (φ : ℝ → ℂ) :
    (hermitianFrequencyProjection φ 0).im = 0 := by
  have h := congrArg Complex.im (hermitianFrequencyProjection_symmetry φ 0)
  simp only [neg_zero, Complex.star_def, Complex.conj_im] at h
  linarith only [h]

/-- For real poles, Hermitian projection keeps exactly the real parts of the residues. -/
theorem hermitianFrequencyProjection_stablePacket {n : ℕ} (residue : Fin n → ℂ)
    (logRate : Fin n → ℝ) (ξ : ℝ) :
    hermitianFrequencyProjection (fun ξ =>
      ∑ j, residue j * stableExponentialSymbol (logRate j) ξ) ξ =
      ∑ j, ((residue j).re : ℂ) * stableExponentialSymbol (logRate j) ξ := by
  have hconj : star (∑ j, residue j * stableExponentialSymbol (logRate j) (-ξ)) =
      ∑ j, star (residue j) * stableExponentialSymbol (logRate j) ξ := by
    change (starRingEnd ℂ) (∑ j, residue j * stableExponentialSymbol (logRate j) (-ξ)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    change star (residue j) * star (stableExponentialSymbol (logRate j) (-ξ)) = _
    rw [stableExponentialSymbol_conj]
  unfold hermitianFrequencyProjection
  rw [hconj]
  simp only [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hr : residue j + star (residue j) = 2 * ((residue j).re : ℂ) := by
    apply Complex.ext <;> simp
    ring
  calc
    _ = (residue j + star (residue j)) * stableExponentialSymbol (logRate j) ξ / 2 := by ring
    _ = _ := by rw [hr]; ring

/-- Hermitian completion is idempotent, including the zero-frequency bin. -/
theorem hermitianFrequencyProjection_idempotent (φ : ℝ → ℂ) :
    hermitianFrequencyProjection (hermitianFrequencyProjection φ) =
      hermitianFrequencyProjection φ := by
  funext ξ
  simp only [hermitianFrequencyProjection, neg_neg, star_div₀, star_add, star_star,
    star_ofNat]
  ring

end

end GaloisForLFunctions.HTGeometry
