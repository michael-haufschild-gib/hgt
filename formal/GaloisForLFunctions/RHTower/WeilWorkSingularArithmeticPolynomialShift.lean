import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialPairing
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianShift

/-!
# The polynomial-weighted source contour and its exact residue

Transport preserves the negative spectral contribution. The right-line
real integral has a bound independent of Gaussian width, for every real
polynomial coefficient and every full-positive source.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

theorem integrable_sourceZetaPairing_polynomial_right {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun t : ℝ => sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I) *
      sourceTwoPointWeight c ((3 / 2 : ℂ) + t * I)) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    integrable_mul_sourceTwoPointWeight (integrable_sourceZetaPairing_gaussian_right hW hT)
      c (σ := 3 / 2) (by norm_num) (by norm_num)

/-- The pole contribution survives polynomial weighting with its exact coefficient. -/
theorem sourceZetaPairing_polynomial_shift {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I) *
      sourceTwoPointWeight c ((3 / 2 : ℂ) + t * I)) -
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I) *
      sourceTwoPointWeight c ((3 / 4 : ℂ) + t * I)) =
      -(Real.pi : ℂ) * sourcePoleNumerator hW 1 * gaussWeight T 1 * sourceTwoPointWeight c 1 := by
  obtain ⟨A, hA⟩ := exists_sourceZetaPairing_gaussian_tail_decay hW hT
  obtain ⟨B, hB0, hB⟩ := exists_sourceTwoPointWeight_strip_bound c
  have hb (s : ℂ) (hs0 : 3 / 4 ≤ s.re) (hs1 : s.re ≤ 3 / 2) (ht : 2 ≤ |s.im|) :
      ‖sourceZetaPairing hW s * gaussWeight T s * sourceTwoPointWeight c s‖ ≤
        A * B * (1 + s.im ^ 2)⁻¹ := by
    rw [norm_mul]
    calc
      _ ≤ ‖sourceZetaPairing hW s * gaussWeight T s‖ * B :=
        mul_le_mul_of_nonneg_left (hB s (by linarith) hs1) (norm_nonneg _)
      _ ≤ (A * (1 + s.im ^ 2)⁻¹) * B :=
        mul_le_mul_of_nonneg_right (hA s hs0 hs1 ht) hB0
      _ = _ := by ring
  have hr := ((tendsto_mul_sourceZetaPairing hW).mul
    ((differentiable_gaussWeight T 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).mul
      ((differentiable_sourceTwoPointWeight c 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hr' : Tendsto (fun s => (s - 1) *
      (sourceZetaPairing hW s * gaussWeight T s * sourceTwoPointWeight c s)) (𝓝[≠] 1)
      (𝓝 ((-sourcePoleNumerator hW 1 / 2) * gaussWeight T 1 * sourceTwoPointWeight c 1)) := by
    simpa only [mul_assoc] using hr
  have hs := integral_line_sub_integral_line_eq
    (F := fun s => sourceZetaPairing hW s * gaussWeight T s * sourceTwoPointWeight c s)
    (a := 3 / 4) (b := 3 / 2) (p := 1) (by norm_num) (by norm_num)
    (fun s hs0 _ hs1 => ((differentiableAt_sourceZetaPairing hW (by linarith) hs1).mul
      (differentiable_gaussWeight T s)).mul (differentiable_sourceTwoPointWeight c s)) hr' hb
  push_cast at hs
  convert hs using 1
  ring

/-- Width-uniform upper bound; no sign of the pole coefficient is assumed. -/
theorem exists_re_integral_sourceZetaPairing_polynomial_right_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
        gaussWeight T ((3 / 2 : ℂ) + t * I) *
        sourceTwoPointWeight c ((3 / 2 : ℂ) + t * I)).re ≤ B := by
  refine ⟨Real.pi * ‖sourcePoleNumerator hW 1‖ * Real.exp (1 / 4) *
    ‖sourceTwoPointWeight c 1‖, by positivity, fun T hT => ?_⟩
  have hs := congrArg Complex.re (sourceZetaPairing_polynomial_shift hW c hT)
  rw [Complex.sub_re] at hs
  have hleft := re_integral_sourceZetaPairing_polynomial_nonpos hW c hT
  have hg : gaussWeight T 1 = ((Real.exp (1 / (4 * T ^ 2)) : ℝ) : ℂ) := by
    unfold gaussWeight
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hexp : Real.exp (1 / (4 * T ^ 2)) ≤ Real.exp (1 / 4) := by
    apply Real.exp_le_exp.mpr
    have hsq : 1 ≤ T ^ 2 := by nlinarith
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * T ^ 2) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hn : ‖-(Real.pi : ℂ) * sourcePoleNumerator hW 1 *
      gaussWeight T 1 * sourceTwoPointWeight c 1‖ ≤
      Real.pi * ‖sourcePoleNumerator hW 1‖ * Real.exp (1 / 4) *
        ‖sourceTwoPointWeight c 1‖ := by
    rw [hg, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
  have hre := (Complex.re_le_norm (-(Real.pi : ℂ) * sourcePoleNumerator hW 1 *
    gaussWeight T 1 * sourceTwoPointWeight c 1)).trans hn
  linarith

end RHTower.WeilSingularArithmetic
