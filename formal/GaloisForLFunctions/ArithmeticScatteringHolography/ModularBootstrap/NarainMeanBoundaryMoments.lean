import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanLineBounds
import GaloisForLFunctions.RHTower.Deninger.DeningerFourierBoundedDerivs

/-!
# Spectral moments of the averaged Narain boundary

Exponential vertical decay makes every polynomial spectral moment integrable.
Fourier differentiation gives smoothness and globally bounded clock derivatives.
-/

open Complex RHTower MeasureTheory Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual Mellin boundary in the ordinary Fourier frequency convention. -/
def narainMeanBoundaryFrequency (Y Z : Height) (t : ℝ) : ℂ :=
  narainMellinMean Y Z (2 * Real.pi * t * I)

/-- The Fourier profile of the actual averaged Mellin boundary. -/
def narainMeanBoundaryFourier (Y Z : Height) : ℝ → ℂ :=
  FourierTransform.fourier (narainMeanBoundaryFrequency Y Z)

/-- Central removability makes the entire real-frequency boundary continuous. -/
theorem continuous_narainMeanBoundaryFrequency (Y Z : Height) :
    Continuous (narainMeanBoundaryFrequency Y Z) := by
  have hc : Continuous (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) := by
    simpa using continuous_narainMellinMean_vertical Y Z (a := 0) le_rfl (by norm_num)
  have h : Continuous (fun t : ℝ => narainMellinMean Y Z (((2 * Real.pi * t : ℝ) : ℂ) * I)) :=
    hc.comp (continuous_const.mul continuous_id)
  change Continuous (fun t : ℝ => narainMellinMean Y Z (2 * (Real.pi : ℂ) * (t : ℂ) * I))
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using h

private theorem integrable_narainMeanBoundary_moment (Y Z : Height) (n : ℕ) :
    Integrable (fun t : ℝ => ‖t‖ ^ n * ‖narainMellinMean Y Z ((t : ℂ) * I)‖) := by
  obtain ⟨C, N, hC, hb⟩ := exists_narainMellinMean_boundary_bound Y Z
  have hc : Continuous (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) := by
    simpa using continuous_narainMellinMean_vertical Y Z (a := 0) le_rfl (by norm_num)
  have hw : Continuous (fun t : ℝ => ‖t‖ ^ n * ‖narainMellinMean Y Z ((t : ℂ) * I)‖) :=
    (continuous_norm.pow n).mul hc.norm
  have hg : Integrable (fun t : ℝ => (1 + |t|) ^ (N + n) * Real.exp (-(Real.pi * |t| / 2))) := by
    simpa only [div_mul_eq_mul_div] using
      integrable_polyAbs_mul_exp_neg_abs (N + n) (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))
  apply hw.locallyIntegrable.integrable_of_isBigO_cocompact
    (g := fun t : ℝ => (1 + |t|) ^ (N + n) * Real.exp (-(Real.pi * |t| / 2))) ?_
    (hg.integrableAtFilter (cocompact ℝ))
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [(isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).compl_mem_cocompact] with t ht
  have habs : 1 ≤ |t| := by
    by_contra h
    have h' := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨h'.1.le, h'.2.le⟩
  have hp : |t| ^ n ≤ (1 + |t|) ^ n := pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ |t| ^ n * ‖narainMellinMean Y Z ((t : ℂ) * I)‖ by positivity),
    abs_of_nonneg (show 0 ≤ (1 + |t|) ^ (N + n) * Real.exp (-(Real.pi * |t| / 2)) by positivity)]
  calc
    _ ≤ |t| ^ n * (C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul_of_nonneg_left (hb t habs) (by positivity)
    _ ≤ (1 + |t|) ^ n * (C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2))) := by gcongr
    _ = _ := by rw [pow_add]; ring

/-- Exponential spectral decay supplies every absolute moment in Fourier coordinates. -/
theorem integrable_narainMeanBoundaryFrequency_moment (Y Z : Height) (n : ℕ) :
    Integrable (fun t : ℝ => ‖t‖ ^ n * ‖narainMeanBoundaryFrequency Y Z t‖) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have h := ((integrable_narainMeanBoundary_moment Y Z n).comp_mul_left'
    (R := 2 * Real.pi) hp.ne').const_mul ((2 * Real.pi) ^ n)⁻¹
  apply h.congr
  filter_upwards [] with t
  simp only [narainMeanBoundaryFrequency, norm_mul, Real.norm_of_nonneg hp.le, mul_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp [pow_ne_zero n hp.ne']

/-- The actual boundary Fourier profile is smooth without differentiating reciprocal zeta. -/
theorem contDiff_narainMeanBoundaryFourier (Y Z : Height) :
    ContDiff ℝ ∞ (narainMeanBoundaryFourier Y Z) :=
  deningerFourier_contDiff (integrable_narainMeanBoundaryFrequency_moment Y Z)

/-- Every clock derivative is globally bounded by a spectral moment. -/
theorem exists_bound_narainMeanBoundaryFourier_iteratedDeriv (Y Z : Height) (r : ℕ) :
    ∃ C : ℝ, ∀ L : ℝ, ‖iteratedDeriv r (narainMeanBoundaryFourier Y Z) L‖ ≤ C :=
  deningerFourier_iteratedDeriv_bound (integrable_narainMeanBoundaryFrequency_moment Y Z)
    (continuous_narainMeanBoundaryFrequency Y Z).aestronglyMeasurable r

#print axioms integrable_narainMeanBoundaryFrequency_moment
#print axioms contDiff_narainMeanBoundaryFourier
#print axioms exists_bound_narainMeanBoundaryFourier_iteratedDeriv
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
