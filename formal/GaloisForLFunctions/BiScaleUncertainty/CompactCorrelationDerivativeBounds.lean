import GaloisForLFunctions.BiScaleUncertainty.CompactSourceDerivativeEnergy
import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalSourceQuantitative

/-!
# Derivative-energy control of actual normalized correlations

The ordinary Dirichlet energy divided by source mass controls the quadratic
origin deficit and the global Lipschitz constant. A literal source interval
also supplies its exact correlation support diameter.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported NNReal
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

/-- Ordinary derivative energy normalized by the source's actual squared norm. -/
def normalizedDirichletEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  (∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / autocorr f 0

theorem normalizedDirichletEnergy_nonneg (f : C_c(ℝ, ℝ)) (hne : f ≠ 0) :
    0 ≤ normalizedDirichletEnergy f :=
  div_nonneg (integral_nonneg fun _ => sq_nonneg _) (nyquistSourceMass_pos f hne).le

/-- The translation-square identity yields the exact unnormalized derivative bound. -/
theorem autocorr_origin_deficit_le_derivative_energy (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (t : ℝ) :
    2 * (autocorr f 0 - autocorr f t) ≤
      t ^ 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 := by
  have he : (∫ u, (f (u + t) - f u) ^ 2) =
      2 * (autocorr f 0 - autocorr f t) := by
    calc
      _ = ∫ u, (f u - f (u + t)) ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => by ring
      _ = _ := integral_sub_shift_sq f.hasCompactSupport f.continuous t
  rw [← he]
  exact SobolevShear.integral_compactSource_translation_sq_le f hf t

/-- Every normalized smooth compact source has the exact quadratic origin collar. -/
theorem nyquistNormalizedCorrelation_ge_one_sub_dirichlet (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) (t : ℝ) :
    1 - normalizedDirichletEnergy f * t ^ 2 / 2 ≤ nyquistNormalizedCorrelation f t := by
  have hQ := nyquistSourceMass_pos f hne
  have hb := autocorr_origin_deficit_le_derivative_energy f hf t
  have hd : autocorr f 0 - autocorr f t ≤
      (t ^ 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 2 := by linarith only [hb]
  have hdiv := div_le_div_of_nonneg_right hd hQ.le
  have he : 1 - nyquistNormalizedCorrelation f t =
      (autocorr f 0 - autocorr f t) / autocorr f 0 := by
    change 1 - autocorr f t / autocorr f 0 = (autocorr f 0 - autocorr f t) / autocorr f 0
    field_simp [hQ.ne']
  rw [← he] at hdiv
  have hr : (t ^ 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) / 2 / autocorr f 0 =
      normalizedDirichletEnergy f * t ^ 2 / 2 := by unfold normalizedDirichletEnergy; ring
  rw [hr] at hdiv
  linarith only [hdiv]

/-- Krein's increment inequality gives the exact squared global derivative modulus. -/
theorem nyquistNormalizedCorrelation_increment_sq_le_dirichlet (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) (x y : ℝ) :
    (nyquistNormalizedCorrelation f x - nyquistNormalizedCorrelation f y) ^ 2 ≤
      normalizedDirichletEnergy f * (x - y) ^ 2 := by
  have hQ := nyquistSourceMass_pos f hne
  have hb := autocorr_origin_deficit_le_derivative_energy f hf (x - y)
  have hk := autocorr_krein_increment_sq_le f.hasCompactSupport f.continuous x y
  have hm := mul_le_mul_of_nonneg_left hb hQ.le
  have hr : (autocorr f x - autocorr f y) ^ 2 ≤
      autocorr f 0 * ((x - y) ^ 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2) := by
    nlinarith only [hk, hm]
  calc
    _ = (autocorr f x - autocorr f y) ^ 2 / autocorr f 0 ^ 2 := by
      change (autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0) ^ 2 = _
      rw [← sub_div, div_pow]
    _ ≤ (autocorr f 0 * ((x - y) ^ 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2)) /
        autocorr f 0 ^ 2 := div_le_div_of_nonneg_right hr (sq_nonneg _)
    _ = _ := by unfold normalizedDirichletEnergy; field_simp [hQ.ne']

/-- The Lipschitz coefficient is exactly the square root of normalized derivative energy. -/
theorem abs_nyquistNormalizedCorrelation_sub_le_sqrt_dirichlet (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) (x y : ℝ) :
    |nyquistNormalizedCorrelation f x - nyquistNormalizedCorrelation f y| ≤
      Real.sqrt (normalizedDirichletEnergy f) * |x - y| := by
  have hb := nyquistNormalizedCorrelation_increment_sq_le_dirichlet f hf hne x y
  have he : (Real.sqrt (normalizedDirichletEnergy f) * |x - y|) ^ 2 =
      normalizedDirichletEnergy f * (x - y) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (normalizedDirichletEnergy_nonneg f hne), sq_abs]
  have hn := mul_nonneg (Real.sqrt_nonneg (normalizedDirichletEnergy f)) (abs_nonneg (x - y))
  nlinarith only [hb, he, hn,
    sq_abs (nyquistNormalizedCorrelation f x - nyquistNormalizedCorrelation f y),
    abs_nonneg (nyquistNormalizedCorrelation f x - nyquistNormalizedCorrelation f y)]

theorem lipschitzWith_nyquistNormalizedCorrelation_sqrt_dirichlet (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    LipschitzWith ⟨Real.sqrt (normalizedDirichletEnergy f), Real.sqrt_nonneg _⟩
      (nyquistNormalizedCorrelation f) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simp only [Real.dist_eq]
  change |nyquistNormalizedCorrelation f x - nyquistNormalizedCorrelation f y| ≤
    Real.sqrt (normalizedDirichletEnergy f) * |x - y|
  exact abs_nyquistNormalizedCorrelation_sub_le_sqrt_dirichlet f hf hne x y

/-- Literal support in an interval forces correlation support within its difference interval. -/
theorem autocorr_eq_zero_of_source_interval {f : ℝ → ℝ} {a b x : ℝ}
    (hs : ∀ u, u ∉ Icc a b → f u = 0) (hx : b - a < |x|) : autocorr f x = 0 := by
  have hz (u : ℝ) : f u * f (u + x) = 0 := by
    by_cases hu : f u = 0
    · rw [hu, zero_mul]
    by_cases hv : f (u + x) = 0
    · rw [hv, mul_zero]
    have hsu : u ∈ Icc a b := by by_contra h; exact hu (hs u h)
    have hsv : u + x ∈ Icc a b := by by_contra h; exact hv (hs (u + x) h)
    have he : |x| ≤ b - a := abs_le.mpr ⟨by linarith only [hsu.2, hsv.1],
      by linarith only [hsu.1, hsv.2]⟩
    exact (not_le_of_gt hx he).elim
  simp only [autocorr, hz, integral_zero]

/-- The same exact support diameter holds after normalization. -/
theorem nyquistNormalizedCorrelation_eq_zero_of_source_interval (f : C_c(ℝ, ℝ))
    {a b x : ℝ} (hs : ∀ u, u ∉ Icc a b → f u = 0) (hx : b - a < |x|) :
    nyquistNormalizedCorrelation f x = 0 := by
  change autocorr f x / autocorr f 0 = 0
  rw [autocorr_eq_zero_of_source_interval hs hx, zero_div]

end GaloisForLFunctions.BiScaleUncertainty
