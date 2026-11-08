import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanVerticalBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanHalfPlane
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin
import GaloisForLFunctions.RHTower.XiMassJetIntegrand
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Integrable vertical lines for the actual averaged Narain transform

Polynomial reciprocal-zeta bounds preserve exponential decay. Continuity
at the removable center supplies absolute integrability on the boundary.
-/

open Complex RHTower Set Filter Topology MeasureTheory
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The pole-free boundary line retains exponential vertical decay. -/
theorem exists_narainMellinMean_boundary_bound (Y Z : Height) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖narainMellinMean Y Z ((t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨C, N, hC, h⟩ := exists_narainMellinMean_strip_bound Y Z (B := 0) le_rfl
  obtain ⟨K, hK, hζ⟩ := exists_norm_inv_zeta_one_line
  refine ⟨C * K * 2 ^ 11, N + 11, by positivity, ?_⟩
  intro t ht
  have ht0 : 2 * t ≠ 0 := by
    intro he
    have : t = 0 := by linarith only [he]
    norm_num [this] at ht
  have hb := h ((t : ℂ) * I) (by simp) (by simpa using ht)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hb
  have hz := hζ (2 * t) ht0
  have hs : (1 : ℂ) + ((2 * t : ℝ) : ℂ) * I = 1 + 2 * ((t : ℂ) * I) := by
    push_cast
    ring
  rw [hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hz
  have hp : (1 + 2 * |t|) ^ 11 ≤ 2 ^ 11 * (1 + |t|) ^ 11 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [abs_nonneg t]) 11
  calc
    _ ≤ _ := hb
    _ ≤ C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2)) *
        (K * (2 ^ 11 * (1 + |t|) ^ 11)) :=
      mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_left hp hK.le)) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- Every vertical line strictly inside the Euler half-plane has the same exponential envelope. -/
theorem exists_narainMellinMean_positive_line_bound (Y Z : Height) {a : ℝ} (ha : 0 < a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖narainMellinMean Y Z ((a : ℂ) + t * I)‖ ≤
        C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨C, N, hC, h⟩ := exists_narainMellinMean_strip_bound Y Z ha.le
  refine ⟨C * (1 + 1 / (2 * a)), N, by positivity, ?_⟩
  intro t ht
  have hb := h ((a : ℂ) + t * I) (by simp [abs_of_pos ha]) (by simpa using ht)
  have hz := norm_inv_riemannZeta_le_of_le_re
    (σ₁ := 1 + 2 * a) (by linarith only [ha])
    (s := 1 + 2 * ((a : ℂ) + t * I)) (by simp)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hb
  have hz' : ‖(riemannZeta (1 + 2 * ((a : ℂ) + t * I)))⁻¹‖ ≤ 1 + 1 / (2 * a) := by
    simpa using hz
  calc
    _ ≤ _ := hb
    _ ≤ C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2)) * (1 + 1 / (2 * a)) := by
      gcongr
    _ = _ := by ring

private theorem integrable_of_poly_exp_bound {f : ℝ → ℂ} (hf : Continuous f)
    {C : ℝ} {N : ℕ} (hbound : ∀ t : ℝ, 1 ≤ |t| →
      ‖f t‖ ≤ C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2))) :
    Integrable f := by
  have hg : Integrable (fun t : ℝ => (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2))) := by
    simpa only [div_mul_eq_mul_div] using
      integrable_polyAbs_mul_exp_neg_abs N (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))
  apply hf.locallyIntegrable.integrable_of_isBigO_cocompact (g := fun t : ℝ =>
    (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2))) ?_ (hg.integrableAtFilter (cocompact ℝ))
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [(isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).compl_mem_cocompact] with t ht
  have habs : 1 ≤ |t| := by
    by_contra h
    have h' := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨h'.1.le, h'.2.le⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2))), mul_assoc] using hbound t habs

/-- Absolute integrability on the boundary is supplied by the actual mean, including its center. -/
theorem integrable_narainMellinMean_boundary (Y Z : Height) :
    Integrable (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) := by
  obtain ⟨C, N, _, hbound⟩ := exists_narainMellinMean_boundary_bound Y Z
  have hc : Continuous (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) := by
    simpa using continuous_narainMellinMean_vertical Y Z (a := 0) le_rfl (by norm_num)
  exact integrable_of_poly_exp_bound hc hbound

/-- Absolute integrability on every positive vertical line except the line through the main pole. -/
theorem integrable_narainMellinMean_positive_line (Y Z : Height) {a : ℝ}
    (ha : 0 < a) (ha' : a ≠ 1 / 2) :
    Integrable (fun t : ℝ => narainMellinMean Y Z ((a : ℂ) + t * I)) := by
  obtain ⟨C, N, _, hbound⟩ := exists_narainMellinMean_positive_line_bound Y Z ha
  exact integrable_of_poly_exp_bound (continuous_narainMellinMean_vertical Y Z ha.le ha') hbound

#print axioms integrable_narainMellinMean_boundary
#print axioms integrable_narainMellinMean_positive_line
#print axioms exists_narainMellinMean_boundary_bound
#print axioms exists_narainMellinMean_positive_line_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
