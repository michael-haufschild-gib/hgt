import GaloisForLFunctions.BiScaleUncertainty.CompactCorrelationDerivativeBounds
import GaloisForLFunctions.BiScaleUncertainty.UnitCorrelationBump

/-!
# Actual unit-mass compact smooth sources

Amplitude normalization preserves normalized correlation and normalized
Dirichlet energy. The literal unit-support bump supplies a nonempty controlled
class with source-derived derivative and positive-collar parameters.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

/-- Normalize the actual compact source by the square root of its correlation mass. -/
def unitMassCompactSource (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  (Real.sqrt (autocorr f 0))⁻¹ • f

/-- The constructed normalized source has squared L² norm exactly one. -/
theorem autocorr_unitMassCompactSource_zero (f : C_c(ℝ, ℝ)) (hne : f ≠ 0) :
    autocorr (unitMassCompactSource f) 0 = 1 := by
  change autocorr (fun u => (Real.sqrt (autocorr f 0))⁻¹ * f u) 0 = 1
  rw [autocorr_source_const_mul, inv_pow, Real.sq_sqrt (nyquistSourceMass_pos f hne).le]
  exact inv_mul_cancel₀ (nyquistSourceMass_pos f hne).ne'

theorem unitMassCompactSource_ne_zero (f : C_c(ℝ, ℝ)) (hne : f ≠ 0) :
    unitMassCompactSource f ≠ 0 := by
  intro h
  have he := autocorr_unitMassCompactSource_zero f hne
  rw [h] at he
  have hz : autocorr (0 : C_c(ℝ, ℝ)) 0 = 0 := by simp [autocorr]
  rw [hz] at he
  exact zero_ne_one he

/-- Amplitude normalization preserves actual compact smoothness. -/
theorem contDiff_unitMassCompactSource (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    ContDiff ℝ 2 (unitMassCompactSource f : ℝ → ℝ) := by
  change ContDiff ℝ 2 (fun u => (Real.sqrt (autocorr f 0))⁻¹ * f u)
  exact contDiff_const.mul hf

/-- The unit-mass source has exactly the original source's normalized correlation. -/
theorem autocorr_unitMassCompactSource (f : C_c(ℝ, ℝ)) (hne : f ≠ 0) (x : ℝ) :
    autocorr (unitMassCompactSource f) x = nyquistNormalizedCorrelation f x := by
  change autocorr (fun u => (Real.sqrt (autocorr f 0))⁻¹ * f u) x = autocorr f x / autocorr f 0
  rw [autocorr_source_const_mul, inv_pow, Real.sq_sqrt (nyquistSourceMass_pos f hne).le]
  ring

/-- The literal normalized derivative has exactly the source's normalized Dirichlet energy. -/
theorem integral_deriv_unitMassCompactSource_sq (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    (∫ u, (deriv (unitMassCompactSource f : ℝ → ℝ) u) ^ 2) = normalizedDirichletEnergy f := by
  have hd (u : ℝ) : deriv (unitMassCompactSource f : ℝ → ℝ) u =
      (Real.sqrt (autocorr f 0))⁻¹ * deriv (f : ℝ → ℝ) u := by
    change deriv (fun v => (Real.sqrt (autocorr f 0))⁻¹ * f v) u = _
    exact (((hf.differentiable (by norm_num)).differentiableAt.hasDerivAt).const_mul _).deriv
  simp_rw [hd, mul_pow]
  rw [integral_const_mul, inv_pow, Real.sq_sqrt (nyquistSourceMass_pos f hne).le]
  unfold normalizedDirichletEnergy
  ring

/-- Normalized derivative energy is unchanged by the actual unit-mass construction. -/
theorem normalizedDirichletEnergy_unitMassCompactSource (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    normalizedDirichletEnergy (unitMassCompactSource f) = normalizedDirichletEnergy f := by
  rw [normalizedDirichletEnergy, integral_deriv_unitMassCompactSource_sq f hf hne,
    autocorr_unitMassCompactSource_zero f hne, div_one]

/-- A source-derived explicit positive radius gives the one-half correlation collar. -/
theorem nyquistNormalizedCorrelation_half_collar (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) {x : ℝ}
    (hx : |x| ≤ 1 / (2 * (Real.sqrt (normalizedDirichletEnergy f) + 1))) :
    1 / 2 ≤ nyquistNormalizedCorrelation f x := by
  let A := Real.sqrt (normalizedDirichletEnergy f)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hden : 0 < 2 * (A + 1) := by positivity
  have hc : A / (2 * (A + 1)) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hb := abs_nyquistNormalizedCorrelation_sub_le_sqrt_dirichlet f hf hne x 0
  rw [nyquistNormalizedCorrelation_zero f hne, sub_zero] at hb
  have hm := mul_le_mul_of_nonneg_left hx hA
  have he : A * (1 / (2 * (A + 1))) = A / (2 * (A + 1)) := by ring
  rw [he] at hm
  have hh := hb.trans (hm.trans hc)
  linarith only [(abs_le.mp hh).1]

/-- A literal smooth unit-mass source realizes finite derivative energy, unit correlation support,
and an explicit positive collar simultaneously. -/
theorem exists_unit_mass_derivative_controlled_source :
    ∃ f : C_c(ℝ, ℝ), ContDiff ℝ 2 (f : ℝ → ℝ) ∧ autocorr f 0 = 1 ∧
      ∃ B : ℝ, 0 ≤ B ∧ (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) = B ∧
        (∀ x, 1 ≤ |x| → autocorr f x = 0) ∧
        (0 < 1 / (2 * (Real.sqrt B + 1))) ∧
        (∀ x, |x| ≤ 1 / (2 * (Real.sqrt B + 1)) → 1 / 2 ≤ autocorr f x) ∧
        (∀ x y, |autocorr f x - autocorr f y| ≤ Real.sqrt B * |x - y|) := by
  have hseed : SharpCycle.seed ≠ 0 := by
    intro h
    have hz := congrArg (fun f : C_c(ℝ, ℝ) => f 0) h
    change SharpCycle.seed 0 = 0 at hz
    rw [SharpCycle.seed_at_zero] at hz
    exact one_ne_zero hz
  have hsmooth : ContDiff ℝ 2 (SharpCycle.seed : ℝ → ℝ) := SharpCycle.seedBump.contDiff
  refine ⟨unitMassCompactSource SharpCycle.seed, contDiff_unitMassCompactSource _ hsmooth,
    autocorr_unitMassCompactSource_zero _ hseed, normalizedDirichletEnergy SharpCycle.seed,
    normalizedDirichletEnergy_nonneg _ hseed, integral_deriv_unitMassCompactSource_sq _ hsmooth hseed,
    ?_, by positivity, ?_, ?_⟩
  · intro x hx
    rw [autocorr_unitMassCompactSource _ hseed]
    change autocorr SharpCycle.seed x / autocorr SharpCycle.seed 0 = 0
    rw [(SharpCycle.seed_correlation_eq_zero_iff x).mpr hx, zero_div]
  · intro x hx
    rw [autocorr_unitMassCompactSource _ hseed]
    exact nyquistNormalizedCorrelation_half_collar _ hsmooth hseed hx
  · intro x y
    rw [autocorr_unitMassCompactSource _ hseed, autocorr_unitMassCompactSource _ hseed]
    exact abs_nyquistNormalizedCorrelation_sub_le_sqrt_dirichlet _ hsmooth hseed x y

end GaloisForLFunctions.BiScaleUncertainty
