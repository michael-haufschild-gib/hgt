import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticFiniteWeight
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticCanonicalGaussian

/-!
# Finite-polynomial pairing of the actual full-positive source

The canonical real pairing vanishes. The actual Herglotz pairing is a
positive spectral integral weighted by the squared polynomial. No
arithmetic limit or coefficient-smallness assumption enters.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

theorem integrable_mul_sourceFiniteWeight {v : ℝ → ℂ} (hv : Integrable v)
    (N : ℕ) (c : ℕ → ℝ) {σ : ℝ} (hσ0 : 1 / 4 ≤ σ) (hσ1 : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => v t * sourceFiniteWeight N c ((σ : ℂ) + t * I)) := by
  obtain ⟨B, _, hB⟩ := exists_sourceFiniteWeight_strip_bound N c
  have hc : Continuous (fun t : ℝ => sourceFiniteWeight N c ((σ : ℂ) + t * I)) :=
    (differentiable_sourceFiniteWeight N c).continuous.comp (by fun_prop)
  exact hv.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun t =>
    hB _ (by simpa using hσ0) (by simpa using hσ1))

theorem exists_zetaGaussian_finite_decay (N : ℕ) (c : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖zetaGaussianPairingTest T s * sourceFiniteWeight N c s‖ * (1 + s.im ^ 2) ^ 2 ≤ C := by
  obtain ⟨A, hA⟩ := exists_zetaGaussianPairingTest_decay hT
  obtain ⟨B, hB0, hB⟩ := exists_sourceFiniteWeight_strip_bound N c
  refine ⟨B * A, fun s hs0 hs1 => ?_⟩
  rw [norm_mul]
  calc
    _ ≤ ‖zetaGaussianPairingTest T s‖ * B * (1 + s.im ^ 2) ^ 2 := by
      gcongr
      exact hB s hs0 (by linarith)
    _ = B * (‖zetaGaussianPairingTest T s‖ * (1 + s.im ^ 2) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hA s hs0 hs1) hB0

theorem integrable_canonicalZetaPairing_finite (N : ℕ) (c : ℕ → ℝ) {T σ : ℝ}
    (hT : 1 ≤ T) (hσ0 : 1 / 4 ≤ σ) (hσ1 : σ ≤ 3 / 4) :
    Integrable (fun t : ℝ => canonicalZetaPairing ((σ : ℂ) + t * I) *
      gaussWeight T ((σ : ℂ) + t * I) * sourceFiniteWeight N c ((σ : ℂ) + t * I)) :=
  integrable_mul_sourceFiniteWeight
    (integrable_canonicalZetaPairing_gaussian hT hσ0 hσ1) N c hσ0 (by linarith)

theorem re_integral_canonicalZetaPairing_finite_eq_zero (N : ℕ) (c : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, canonicalZetaPairing ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I) *
      sourceFiniteWeight N c ((3 / 4 : ℂ) + t * I)).re = 0 := by
  obtain ⟨A, hA⟩ := exists_canonicalZetaPairing_gaussian_decay hT
  obtain ⟨B, hB0, hB⟩ := exists_sourceFiniteWeight_strip_bound N c
  have hs := integral_vertical_line_shift_of_decay
    (Φ := fun s => canonicalZetaPairing s * gaussWeight T s * sourceFiniteWeight N c s)
    (c₁ := 1 / 2) (c₂ := 3 / 4) (C := B * A)
    (fun s hs => by
      rw [uIcc_of_le (by norm_num)] at hs
      exact ((differentiableAt_canonicalZetaPairing (by linarith [hs.1]) hs.2).mul
        (differentiable_gaussWeight T s)).mul (differentiable_sourceFiniteWeight N c s))
    (fun s hs => by
      rw [uIcc_of_le (by norm_num)] at hs
      rw [norm_mul]
      calc
        _ ≤ ‖canonicalZetaPairing s * gaussWeight T s‖ * B :=
          mul_le_mul_of_nonneg_left (hB s (by linarith [hs.1]) (by linarith [hs.2]))
            (norm_nonneg _)
        _ ≤ (A / (1 + s.im ^ 2)) * B :=
          mul_le_mul_of_nonneg_right (hA s (by linarith [hs.1]) hs.2) hB0
        _ = _ := by ring)
  push_cast at hs
  have hi : Integrable (fun t : ℝ => canonicalZetaPairing ((1 / 2 : ℂ) + t * I) *
      gaussWeight T ((1 / 2 : ℂ) + t * I) *
      sourceFiniteWeight N c ((1 / 2 : ℂ) + t * I)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      integrable_canonicalZetaPairing_finite N c (σ := 1 / 2) hT (by norm_num) (by norm_num)
  rw [← hs, ← RCLike.re_eq_complex_re, ← integral_re hi]
  have hp (t : ℝ) : (canonicalZetaPairing ((1 / 2 : ℂ) + t * I) *
      gaussWeight T ((1 / 2 : ℂ) + t * I) *
      sourceFiniteWeight N c ((1 / 2 : ℂ) + t * I)).re = 0 := by
    rw [gaussWeight_critical_eq, sourceFiniteWeight_critical, Complex.re_mul_ofReal,
      Complex.re_mul_ofReal, re_canonicalZetaPairing_critical, zero_mul, zero_mul]
  simp only [RCLike.re_eq_complex_re, hp, integral_zero]

theorem integrable_weilContinuation_mul_zetaGaussian_finite {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (N : ℕ) (c : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun t : ℝ => WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) *
      (zetaGaussianPairingTest T ((3 / 4 : ℂ) + t * I) *
        sourceFiniteWeight N c ((3 / 4 : ℂ) + t * I))) := by
  have hi := integrable_mul_sourceFiniteWeight
    (integrable_weilContinuation_mul_zetaGaussian hW hT) N c (σ := 3 / 4)
    (by norm_num) (by norm_num)
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, mul_assoc] using hi

/-- Exact weighted spectral pairing for the actual full-positive source. -/
theorem re_integral_weilContinuation_mul_zetaGaussian_finite_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (N : ℕ) (c : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) *
      (zetaGaussianPairingTest T ((3 / 4 : ℂ) + t * I) *
        sourceFiniteWeight N c ((3 / 4 : ℂ) + t * I))).re =
      Real.pi * ∫ r : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + r * I)‖ ^ 2 *
        Real.exp (-(r ^ 2 / T ^ 2)) *
        ‖sourceFiniteFactor N c ((1 / 2 : ℂ) + r * I)‖ ^ 2
          ∂WeilSpectral.boundaryMeasure hW := by
  obtain ⟨C, hC⟩ := exists_zetaGaussian_finite_decay N c hT
  have h := re_integral_weilContinuation_mul_test_eq hW
    (f := fun s => zetaGaussianPairingTest T s * sourceFiniteWeight N c s) (C := C)
    (fun s hs0 hs1 => (differentiableAt_zetaGaussianPairingTest T hs0 hs1).mul
      (differentiable_sourceFiniteWeight N c s)) ?_ ?_ hC
  · simpa only [zetaGaussianPairingTest_critical, sourceFiniteWeight_critical,
      ← Complex.ofReal_mul, Complex.ofReal_re] using h
  · intro t
    rw [show (1 / 4 : ℂ) + t * I = 1 - conj ((3 / 4 : ℂ) + t * I) by
      simp only [map_add, map_div₀, map_ofNat, map_mul, conj_ofReal, conj_I]; ring,
      zetaGaussianPairingTest_one_sub, sourceFiniteWeight_one_sub,
      zetaGaussianPairingTest_conj, sourceFiniteWeight_conj, map_mul]
  · intro t
    rw [show (3 / 4 : ℂ) + (-t) * I = conj ((3 / 4 : ℂ) + t * I) by
      simp only [map_add, map_div₀, map_ofNat, map_mul, conj_ofReal, conj_I]; ring,
      zetaGaussianPairingTest_conj, sourceFiniteWeight_conj, map_mul]

theorem integrable_sourceZetaPairing_finite {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (N : ℕ) (c : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun t : ℝ => sourceZetaPairing hW ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I) *
      sourceFiniteWeight N c ((3 / 4 : ℂ) + t * I)) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    integrable_mul_sourceFiniteWeight (integrable_sourceZetaPairing_gaussian hW hT)
      N c (σ := 3 / 4) (by norm_num) (by norm_num)

/-- Polynomial positivity bounds the actual signed source, with no extra source premise. -/
theorem re_integral_sourceZetaPairing_finite_nonpos {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (N : ℕ) (c : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I) *
      sourceFiniteWeight N c ((3 / 4 : ℂ) + t * I)).re ≤ 0 := by
  have he (s : ℂ) : sourceZetaPairing hW s * gaussWeight T s * sourceFiniteWeight N c s =
      canonicalZetaPairing s * gaussWeight T s * sourceFiniteWeight N c s -
      WeilSpectral.weilContinuation hW s * (zetaGaussianPairingTest T s * sourceFiniteWeight N c s) := by
    rw [sourceZetaPairing_mul_gaussWeight]
    ring
  simp_rw [he]
  have hi : Integrable (fun t : ℝ => canonicalZetaPairing ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I) *
      sourceFiniteWeight N c ((3 / 4 : ℂ) + t * I)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      integrable_canonicalZetaPairing_finite N c (σ := 3 / 4) hT (by norm_num) (by norm_num)
  rw [integral_sub hi (integrable_weilContinuation_mul_zetaGaussian_finite hW N c hT),
    Complex.sub_re, re_integral_canonicalZetaPairing_finite_eq_zero N c hT,
    re_integral_weilContinuation_mul_zetaGaussian_finite_eq hW N c hT, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (integral_nonneg fun _ => by positivity))

end RHTower.WeilSingularArithmetic
