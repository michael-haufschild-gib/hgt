import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAReduced
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# All stationary radii of the logarithmic-entropy coexistence landscape

The exact equal-Gibbs construction leaves one quadratic after the two
phase radii are removed from the derivative polynomial. Its positive root
is explicit. Rolle's theorem places it strictly between the phases; the
other root is negative. This supplies a complete derivative factorization
and a three-stationary-radius classification without numerical root finding.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceAStationaryLinear (τ θ : ℝ) : ℝ :=
  egbCoexistenceAPressureWeight τ θ * (thermalRatio τ + 1) - egbCoexistenceATemperatureWeight τ θ

def egbCoexistenceAStationaryDiscriminant (τ θ : ℝ) : ℝ :=
  egbCoexistenceAStationaryLinear τ θ ^ (2 : ℕ) +
    4 * egbCoexistenceAPressureWeight τ θ * egbCoexistenceAChargeWeight τ θ / thermalRatio τ

def egbCoexistenceAMiddleRadius (τ θ : ℝ) : ℝ :=
  (-egbCoexistenceAStationaryLinear τ θ + sqrt (egbCoexistenceAStationaryDiscriminant τ θ)) /
    (2 * egbCoexistenceAPressureWeight τ θ)

def egbCoexistenceANegativeRootSize (τ θ : ℝ) : ℝ :=
  egbCoexistenceAChargeWeight τ θ /
    (egbCoexistenceAPressureWeight τ θ * thermalRatio τ * egbCoexistenceAMiddleRadius τ θ)

theorem egbCoexistenceAStationaryDiscriminant_pos (τ θ : ℝ) : 0 < egbCoexistenceAStationaryDiscriminant τ θ := by
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hs := egbCoexistenceAChargeWeight_pos τ θ
  have hz := thermalRatio_pos τ
  unfold egbCoexistenceAStationaryDiscriminant
  positivity

theorem egbCoexistenceAMiddleRadius_pos (τ θ : ℝ) : 0 < egbCoexistenceAMiddleRadius τ θ := by
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hs := egbCoexistenceAChargeWeight_pos τ θ
  have hz := thermalRatio_pos τ
  have hD := egbCoexistenceAStationaryDiscriminant_pos τ θ
  have hsq := sq_sqrt (le_of_lt hD)
  have hroot := sqrt_nonneg (egbCoexistenceAStationaryDiscriminant τ θ)
  have hgap : 0 < egbCoexistenceAStationaryDiscriminant τ θ - egbCoexistenceAStationaryLinear τ θ ^ (2 : ℕ) := by
    unfold egbCoexistenceAStationaryDiscriminant
    have h : 0 < 4 * egbCoexistenceAPressureWeight τ θ * egbCoexistenceAChargeWeight τ θ / thermalRatio τ := by positivity
    linarith
  have hn : 0 < -egbCoexistenceAStationaryLinear τ θ + sqrt (egbCoexistenceAStationaryDiscriminant τ θ) := by
    by_contra h
    have h₁ : 0 ≤ egbCoexistenceAStationaryLinear τ θ - sqrt (egbCoexistenceAStationaryDiscriminant τ θ) := by linarith
    have h₂ : 0 ≤ egbCoexistenceAStationaryLinear τ θ + sqrt (egbCoexistenceAStationaryDiscriminant τ θ) := by linarith
    nlinarith [mul_nonneg h₁ h₂]
  exact div_pos hn (by positivity)

theorem egbCoexistenceAMiddleRadius_quadratic (τ θ : ℝ) :
    egbCoexistenceAPressureWeight τ θ * egbCoexistenceAMiddleRadius τ θ ^ (2 : ℕ) +
      egbCoexistenceAStationaryLinear τ θ * egbCoexistenceAMiddleRadius τ θ -
        egbCoexistenceAChargeWeight τ θ / thermalRatio τ = 0 := by
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hz := thermalRatio_pos τ
  have hs : sqrt (egbCoexistenceAStationaryDiscriminant τ θ) ^ (2 : ℕ) =
      egbCoexistenceAStationaryLinear τ θ ^ (2 : ℕ) +
        4 * egbCoexistenceAPressureWeight τ θ * egbCoexistenceAChargeWeight τ θ / thermalRatio τ :=
    sq_sqrt (le_of_lt (egbCoexistenceAStationaryDiscriminant_pos τ θ))
  have he : egbCoexistenceAPressureWeight τ θ * egbCoexistenceAMiddleRadius τ θ ^ (2 : ℕ) +
      egbCoexistenceAStationaryLinear τ θ * egbCoexistenceAMiddleRadius τ θ - egbCoexistenceAChargeWeight τ θ / thermalRatio τ =
    (sqrt (egbCoexistenceAStationaryDiscriminant τ θ) ^ (2 : ℕ) - egbCoexistenceAStationaryLinear τ θ ^ (2 : ℕ) -
      4 * egbCoexistenceAPressureWeight τ θ * egbCoexistenceAChargeWeight τ θ / thermalRatio τ) /
        (4 * egbCoexistenceAPressureWeight τ θ) := by
    unfold egbCoexistenceAMiddleRadius
    field_simp
    ring
  rw [he, hs]
  ring

theorem egbCoexistenceANegativeRootSize_pos (τ θ : ℝ) : 0 < egbCoexistenceANegativeRootSize τ θ := by
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hs := egbCoexistenceAChargeWeight_pos τ θ
  have hz := thermalRatio_pos τ
  have hw := egbCoexistenceAMiddleRadius_pos τ θ
  unfold egbCoexistenceANegativeRootSize
  positivity

/-- Complete factorization into three positive candidates and one negative radius. -/
theorem egbCoexistenceARadialPolynomial_full_factorization (τ θ v : ℝ) :
    egbCoexistenceARadialPolynomial τ θ v = egbCoexistenceAPressureWeight τ θ *
      (v - thermalRatio τ) * (v - egbCoexistenceAMiddleRadius τ θ) * (v - 1) *
        (v + egbCoexistenceANegativeRootSize τ θ) := by
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hz := thermalRatio_pos τ
  have hw := egbCoexistenceAMiddleRadius_pos τ θ
  have hq := egbCoexistenceAMiddleRadius_quadratic τ θ
  have hq' : (egbCoexistenceAPressureWeight τ θ * egbCoexistenceAMiddleRadius τ θ ^ (2 : ℕ) +
      egbCoexistenceAStationaryLinear τ θ * egbCoexistenceAMiddleRadius τ θ) * thermalRatio τ = egbCoexistenceAChargeWeight τ θ :=
    (eq_div_iff hz.ne').1 (by linarith [hq])
  have hlin : egbCoexistenceAStationaryLinear τ θ =
      egbCoexistenceAPressureWeight τ θ * (egbCoexistenceANegativeRootSize τ θ - egbCoexistenceAMiddleRadius τ θ) := by
    unfold egbCoexistenceANegativeRootSize
    field_simp
    nlinarith [hq']
  rw [egbCoexistenceARadialPolynomial_factorization]
  change (v - thermalRatio τ) * (v - 1) *
    (egbCoexistenceAPressureWeight τ θ * v ^ (2 : ℕ) + egbCoexistenceAStationaryLinear τ θ * v -
      egbCoexistenceAChargeWeight τ θ / thermalRatio τ) = _
  rw [hlin]
  unfold egbCoexistenceANegativeRootSize
  field_simp
  ring

/-- Rolle's theorem places the explicit positive quadratic root strictly between both phases. -/
theorem egbCoexistenceAMiddleRadius_bounds (τ θ : ℝ) :
    thermalRatio τ < egbCoexistenceAMiddleRadius τ θ ∧ egbCoexistenceAMiddleRadius τ θ < 1 := by
  have hz := thermalRatio_pos τ
  have hzu := thermalRatio_lt_one τ
  have hlog : log (thermalRatio τ) < 0 := log_neg hz hzu
  obtain ⟨c, hc, hzero⟩ := exists_deriv_eq_zero hlog
    (egbCoexistenceAReducedLogGibbs_continuous τ θ).continuousOn (egbCoexistenceAReducedLogGibbs_balance τ θ)
  rw [(egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ c).deriv] at hzero
  have hF : egbCoexistenceARadialPolynomial τ θ (exp c) = 0 :=
    ((div_eq_zero_iff).1 hzero).resolve_right (by positivity)
  have hzc : thermalRatio τ < exp c := by
    have h := exp_lt_exp.mpr hc.1
    simpa only [exp_log hz] using h
  have hc1 : exp c < 1 := by
    have h := exp_lt_exp.mpr hc.2
    simpa only [exp_zero] using h
  have hP := ne_of_gt (egbCoexistenceAPressureWeight_pos τ θ)
  have hZ := sub_ne_zero.mpr (ne_of_gt hzc)
  have hOne := sub_ne_zero.mpr (ne_of_lt hc1)
  have hNeg : exp c + egbCoexistenceANegativeRootSize τ θ ≠ 0 := by
    have h := egbCoexistenceANegativeRootSize_pos τ θ
    positivity
  rw [egbCoexistenceARadialPolynomial_full_factorization] at hF
  have he : exp c = egbCoexistenceAMiddleRadius τ θ := by
    simpa only [mul_eq_zero, hP, hZ, hOne, hNeg, false_or, or_false, sub_eq_zero] using hF
  rw [← he]
  exact ⟨hzc, hc1⟩

theorem egbCoexistenceAMiddleRadius_log_bounds (τ θ : ℝ) :
    log (thermalRatio τ) < log (egbCoexistenceAMiddleRadius τ θ) ∧ log (egbCoexistenceAMiddleRadius τ θ) < 0 := by
  have hw := egbCoexistenceAMiddleRadius_bounds τ θ
  exact ⟨log_lt_log (thermalRatio_pos τ) hw.1, log_neg (egbCoexistenceAMiddleRadius_pos τ θ) hw.2⟩

/-- Exactly three stationary positive radii occur in the constructed coexistence state. -/
theorem egbCoexistenceA_stationary_radii_iff (τ θ u : ℝ) :
    deriv (egbCoexistenceAReducedLogGibbs τ θ) u = 0 ↔
      exp u = thermalRatio τ ∨ exp u = egbCoexistenceAMiddleRadius τ θ ∨ exp u = 1 := by
  rw [(egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ u).deriv, egbCoexistenceARadialPolynomial_full_factorization]
  have hp := ne_of_gt (egbCoexistenceAPressureWeight_pos τ θ)
  have hden : 2 * exp u ≠ 0 := by positivity
  have hneg : exp u + egbCoexistenceANegativeRootSize τ θ ≠ 0 := by
    have hd := egbCoexistenceANegativeRootSize_pos τ θ
    positivity
  simp only [div_eq_zero_iff, hden, or_false, mul_eq_zero, hp, hneg, false_or, sub_eq_zero, or_assoc]

end GaloisForLFunctions.HTGeometry
