import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianPairing
import GaloisForLFunctions.RHTower.WeilZetaSquareBoundaryInequality
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift

/-!
# Canonical Gaussian cancellation and the signed source contour

The canonical zeta pairing has zero real critical-line value, including at
zeta zeros. Its Gaussian integral can be shifted to `Re s = 3/4`. Subtracting
the positive pairing of the actual full Weil source gives the signed contour
inequality without a boundary-value assumption on that source.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

private theorem exists_quarter_strip_poly_of_tail {F : ℂ → ℂ} {A : ℝ} {N : ℕ}
    (hf : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → DifferentiableAt ℂ F s)
    (hA : 0 ≤ A)
    (hb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → 2 ≤ |s.im| →
      ‖F s‖ ≤ A * (1 + |s.im|) ^ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖F s‖ ≤ C * (1 + |s.im|) ^ N := by
  let K : Set ℂ := Icc (1 / 4 : ℝ) (3 / 4) ×ℂ Icc (-2 : ℝ) 2
  have hc : ContinuousOn F K := fun s hs => (hf s hs.1.1 hs.1.2).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact K).exists_bound_of_continuousOn hc
  refine ⟨|B| + A, by positivity, fun s hs0 hs1 => ?_⟩
  by_cases ht : 2 ≤ |s.im|
  · exact (hb s hs0 hs1 ht).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (abs_nonneg B)) (by positivity))
  · have hsK : s ∈ K := ⟨⟨hs0, hs1⟩,
      ⟨by linarith [neg_abs_le s.im], by linarith [le_abs_self s.im]⟩⟩
    exact (hB s hsK).trans ((show B ≤ |B| + A by linarith [le_abs_self B]).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [abs_nonneg s.im]))))

private theorem exists_gaussian_decay_of_quarter_strip_poly {F : ℂ → ℂ} {A T : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hT : 1 ≤ T)
    (hb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ A * (1 + |s.im|) ^ N) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖F s * gaussWeight T s‖ ≤ C / (1 + s.im ^ 2) := by
  refine ⟨A * Real.exp 1 * ((N + 2).factorial * Real.exp (3 / 2) * T ^ (N + 2)),
    fun s hs0 hs1 => ?_⟩
  rw [le_div_iff₀ (by positivity : 0 < 1 + s.im ^ 2), norm_mul]
  have hg := norm_gaussWeight_le_of_re hT (s := s) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hs : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
  have hm := one_add_abs_pow_mul_exp_le (N + 2) hT s.im
  have he : Real.exp (-(s.im ^ 2 / (2 * T ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  calc ‖F s‖ * ‖gaussWeight T s‖ * (1 + s.im ^ 2)
      ≤ (A * (1 + |s.im|) ^ N) * (Real.exp 1 * Real.exp (-(s.im ^ 2 / T ^ 2))) *
        (1 + |s.im|) ^ 2 := by gcongr; exact hb s hs0 hs1
    _ = A * Real.exp 1 * ((1 + |s.im|) ^ (N + 2) * Real.exp (-(s.im ^ 2 / T ^ 2))) := by
      rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hm.trans (mul_le_of_le_one_right (by positivity) he)) (by positivity)

/-- Canonical numerator; it has no poles at zeta zeros. -/
def canonicalZetaPairing (s : ℂ) : ℂ :=
  ((zetaArchimedeanDatum s + 1 / (s - 1)) * riemannZeta s + deriv riemannZeta s) *
    riemannZeta (1 - s)

theorem differentiableAt_canonicalZetaPairing {s : ℂ}
    (hs0 : 1 / 4 ≤ s.re) (hs1 : s.re ≤ 3 / 4) : DifferentiableAt ℂ canonicalZetaPairing s := by
  have hne : s ≠ 1 := by intro h; rw [h] at hs1; norm_num at hs1
  have hne' : 1 - s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact ((((WeilFiniteType.differentiableAt_zetaArchimedeanDatum (by linarith)).add
    ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hne))).mul
    (differentiableAt_riemannZeta hne)).add
      (analyticAt_riemannZeta_of_ne_one hne).deriv.differentiableAt).mul
        ((differentiableAt_riemannZeta hne').comp s (by fun_prop))

private theorem exists_datum_quarter_tail_linear :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → 2 ≤ |s.im| →
      ‖zetaArchimedeanDatum s + 1 / (s - 1)‖ ≤ C * (1 + |s.im|) := by
  let d := |GaloisForLFunctions.digammaVerticalLogConstant|
  let l := |Real.log Real.pi|
  refine ⟨d + l + 10, by dsimp [d, l]; positivity, fun s hs0 hs1 ht => ?_⟩
  have hspos : 0 < s.re := by linarith
  have hψ := norm_digamma_half_le hspos (by linarith : s.re ≤ 2) ht
  rw [Complex.re_add_im] at hψ
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < |s.im| + 3)
  have hψ' : ‖Complex.digamma (s / 2)‖ ≤ |s.im| + 2 + d := by
    dsimp [d]
    linarith [le_abs_self GaloisForLFunctions.digammaVerticalLogConstant]
  have hinv : ‖(1 : ℂ) / s‖ ≤ 4 := by
    rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr (by intro h; simp [h] at hspos))]
    have := Complex.re_le_norm s
    linarith
  have hpole : ‖(1 : ℂ) / (s - 1)‖ ≤ 4 := by
    have hd : (1 / 4 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      simp only [Complex.sub_re, Complex.one_re] at this
      rw [abs_of_nonpos (by linarith : s.re - 1 ≤ 0)] at this
      linarith
    rw [norm_div, norm_one, div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hd)]
    linarith
  have hb : ‖zetaArchimedeanDatum s + 1 / (s - 1)‖ ≤ (|s.im| + 2 + d) / 2 + l / 2 + 4 + 4 := by
    unfold zetaArchimedeanDatum
    calc ‖Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s + 1 / (s - 1)‖
        ≤ ‖Complex.digamma (s / 2) / 2‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
          ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ := by
            have h₁ := norm_sub_le (Complex.digamma (s / 2) / 2) ((Real.log Real.pi : ℂ) / 2)
            have h₂ := norm_add_le (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) (1 / s)
            have h₃ := norm_add_le (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s) (1 / (s - 1))
            linarith
      _ ≤ _ := by
        have hψdiv : ‖Complex.digamma (s / 2) / 2‖ ≤ (|s.im| + 2 + d) / 2 := by
          simpa only [norm_div, RCLike.norm_ofNat] using (div_le_div_of_nonneg_right hψ' (by norm_num : (0 : ℝ) ≤ 2))
        have hldiv : ‖(Real.log Real.pi : ℂ) / 2‖ = l / 2 := by
          simp only [l, norm_div, RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        linarith
  refine hb.trans ?_
  have hd : 0 ≤ d := abs_nonneg _
  have hl : 0 ≤ l := abs_nonneg _
  nlinarith [abs_nonneg s.im, mul_nonneg hd (abs_nonneg s.im), mul_nonneg hl (abs_nonneg s.im)]

theorem exists_canonicalZetaPairing_strip_poly :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖canonicalZetaPairing s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨A, N, hA0, hA⟩ := exists_bound_norm_riemannZeta_strip 1
  obtain ⟨B, M, hB0, hB⟩ := exists_bound_norm_deriv_riemannZeta_strip 1
  obtain ⟨D, hD0, hD⟩ := exists_datum_quarter_tail_linear
  obtain ⟨C, hC0, hC⟩ := exists_quarter_strip_poly_of_tail
    (F := canonicalZetaPairing) (N := 1 + N + M + N)
    (fun _ => differentiableAt_canonicalZetaPairing)
    (A := (D * A + B * 2 ^ M) * A) (by positivity) (by
      intro s hs0 hs1 ht
      have hz := hA s.re s.im (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)
      rw [Complex.re_add_im] at hz
      have hz' := hA (1 - s).re (1 - s).im (by simp; rw [abs_le]; constructor <;> linarith) (by simpa using (show 1 ≤ |s.im| by linarith))
      rw [Complex.re_add_im] at hz'
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hz'
      have hd := hB s (abs_le.mpr ⟨by linarith, by linarith⟩) ht
      have hq : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
      have hM : (1 + |s.im|) ^ M ≤ (1 + |s.im|) ^ (1 + N + M) := pow_le_pow_right₀ hq (by omega)
      have hfirst : D * (1 + |s.im|) * (A * (1 + |s.im|) ^ N) ≤
          D * A * (1 + |s.im|) ^ (1 + N + M) := by
        calc D * (1 + |s.im|) * (A * (1 + |s.im|) ^ N)
            = D * A * (1 + |s.im|) ^ (1 + N) := by rw [pow_add, pow_one]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq (by omega)) (by positivity)
      have hN' : |s.im| ^ N ≤ (1 + |s.im|) ^ N := by gcongr; linarith
      have hd' : ‖deriv riemannZeta s‖ ≤ (B * 2 ^ M) * (1 + |s.im|) ^ M := by
        refine hd.trans ?_
        rw [mul_pow, mul_assoc]
        gcongr
        linarith
      unfold canonicalZetaPairing
      rw [norm_mul]
      calc ‖(zetaArchimedeanDatum s + 1 / (s - 1)) * riemannZeta s + deriv riemannZeta s‖ * ‖riemannZeta (1 - s)‖
          ≤ (D * (1 + |s.im|) * (A * (1 + |s.im|) ^ N) + (B * 2 ^ M) * (1 + |s.im|) ^ M) * (A * (1 + |s.im|) ^ N) := by
            apply mul_le_mul _ (hz'.trans (mul_le_mul_of_nonneg_left hN' hA0)) (norm_nonneg _) (by positivity)
            exact (norm_add_le _ _).trans (add_le_add
              (by rw [norm_mul]; exact mul_le_mul (hD s hs0 hs1 ht) (hz.trans (mul_le_mul_of_nonneg_left hN' hA0)) (norm_nonneg _) (by positivity)) hd')
        _ ≤ (D * A * (1 + |s.im|) ^ (1 + N + M) + B * 2 ^ M * (1 + |s.im|) ^ (1 + N + M)) * (A * (1 + |s.im|) ^ N) := by
          exact mul_le_mul_of_nonneg_right (add_le_add hfirst
            (mul_le_mul_of_nonneg_left hM (by positivity))) (by positivity)
        _ = _ := by rw [pow_add]; ring)
  exact ⟨C, 1 + N + M + N, hC0, hC⟩

theorem re_canonicalZetaPairing_critical (t : ℝ) :
    (canonicalZetaPairing ((1 / 2 : ℂ) + t * I)).re = 0 := by
  have hc : 1 - ((1 / 2 : ℂ) + t * I) = conj ((1 / 2 : ℂ) + t * I) := by
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
    ring
  have h := WeilZetaSquare.re_datum_normSq_add_deriv_mul_conj t
  dsimp only [RHTower.linePt] at h
  push_cast at h
  simpa only [canonicalZetaPairing, hc, riemannZeta_conj, add_mul, mul_assoc,
    RHTower.linePt] using h

theorem gaussWeight_critical_eq (T t : ℝ) :
    gaussWeight T ((1 / 2 : ℂ) + t * I) = ((Real.exp (-(t ^ 2 / T ^ 2)) : ℝ) : ℂ) := by
  unfold gaussWeight
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp [I_sq]

theorem exists_canonicalZetaPairing_gaussian_decay {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖canonicalZetaPairing s * gaussWeight T s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C, N, hC, hb⟩ := exists_canonicalZetaPairing_strip_poly
  exact exists_gaussian_decay_of_quarter_strip_poly hC hT hb

theorem integrable_canonicalZetaPairing_gaussian {T σ : ℝ}
    (hT : 1 ≤ T) (hσ0 : 1 / 4 ≤ σ) (hσ1 : σ ≤ 3 / 4) :
    Integrable (fun t : ℝ => canonicalZetaPairing ((σ : ℂ) + t * I) *
      gaussWeight T ((σ : ℂ) + t * I)) := by
  obtain ⟨C, hC⟩ := exists_canonicalZetaPairing_gaussian_decay hT
  have hc : Continuous (fun t : ℝ => canonicalZetaPairing ((σ : ℂ) + t * I) *
      gaussWeight T ((σ : ℂ) + t * I)) := continuous_iff_continuousAt.mpr fun t =>
    ((differentiableAt_canonicalZetaPairing (by simpa using hσ0) (by simpa using hσ1)).mul
      (differentiable_gaussWeight T _)).continuousAt.comp (by fun_prop)
  refine (_root_.integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simpa [div_eq_mul_inv] using hC ((σ : ℂ) + t * I) (by simpa using hσ0) (by simpa using hσ1)

/-- The canonical real Gaussian contour integral vanishes on `Re s=3/4`. -/
theorem re_integral_canonicalZetaPairing_gaussian_eq_zero {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, canonicalZetaPairing ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I)).re = 0 := by
  obtain ⟨C, hC⟩ := exists_canonicalZetaPairing_gaussian_decay hT
  have hs := integral_vertical_line_shift_of_decay
    (Φ := fun s => canonicalZetaPairing s * gaussWeight T s) (c₁ := 1 / 2) (c₂ := 3 / 4)
    (fun s hs => (differentiableAt_canonicalZetaPairing
      (by rw [uIcc_of_le (by norm_num)] at hs; linarith [hs.1])
      (by rw [uIcc_of_le (by norm_num)] at hs; exact hs.2)).mul (differentiable_gaussWeight T s))
    (fun s hs => hC s (by rw [uIcc_of_le (by norm_num)] at hs; linarith [hs.1])
      (by rw [uIcc_of_le (by norm_num)] at hs; exact hs.2))
  push_cast at hs
  have hi : Integrable (fun t : ℝ => canonicalZetaPairing ((1 / 2 : ℂ) + t * I) *
      gaussWeight T ((1 / 2 : ℂ) + t * I)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (integrable_canonicalZetaPairing_gaussian (σ := 1 / 2) hT (by norm_num) (by norm_num))
  rw [← hs, ← RCLike.re_eq_complex_re, ← integral_re
    hi]
  have hp (t : ℝ) : (canonicalZetaPairing ((1 / 2 : ℂ) + t * I) *
      gaussWeight T ((1 / 2 : ℂ) + t * I)).re = 0 := by
    rw [gaussWeight_critical_eq, Complex.re_mul_ofReal, re_canonicalZetaPairing_critical, zero_mul]
  simp only [RCLike.re_eq_complex_re, hp, integral_zero]

/-- The signed source numerator after subtracting the canonical arithmetic coefficients. -/
def sourceZetaPairing {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  ((zetaArchimedeanDatum s + 1 / (s - 1) - WeilSpectral.weilContinuation hW s) *
    riemannZeta s + deriv riemannZeta s) * riemannZeta (1 - s)

theorem sourceZetaPairing_mul_gaussWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) (s : ℂ) :
    sourceZetaPairing hW s * gaussWeight T s = canonicalZetaPairing s * gaussWeight T s -
      WeilSpectral.weilContinuation hW s * zetaGaussianPairingTest T s := by
  unfold sourceZetaPairing canonicalZetaPairing zetaGaussianPairingTest
  ring

theorem integrable_sourceZetaPairing_gaussian {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun t : ℝ => sourceZetaPairing hW ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I)) := by
  simp_rw [sourceZetaPairing_mul_gaussWeight]
  have hi : Integrable (fun t : ℝ => canonicalZetaPairing ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      (integrable_canonicalZetaPairing_gaussian (σ := 3 / 4) hT (by norm_num) (by norm_num))
  exact hi.sub (integrable_weilContinuation_mul_zetaGaussian hW hT)

/-- Exact signed source contour identity, without any additional source premise. -/
theorem re_integral_sourceZetaPairing_gaussian_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I)).re =
      -(Real.pi * ∫ r : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + r * I)‖ ^ 2 *
        Real.exp (-(r ^ 2 / T ^ 2)) ∂WeilSpectral.boundaryMeasure hW) := by
  simp_rw [sourceZetaPairing_mul_gaussWeight]
  have hi : Integrable (fun t : ℝ => canonicalZetaPairing ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      (integrable_canonicalZetaPairing_gaussian (σ := 3 / 4) hT (by norm_num) (by norm_num))
  rw [integral_sub hi
    (integrable_weilContinuation_mul_zetaGaussian hW hT), Complex.sub_re,
    re_integral_canonicalZetaPairing_gaussian_eq_zero hT,
    re_integral_weilContinuation_mul_zetaGaussian_eq hW hT, zero_sub]

theorem re_integral_sourceZetaPairing_gaussian_nonpos {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 4 : ℂ) + t * I) *
      gaussWeight T ((3 / 4 : ℂ) + t * I)).re ≤ 0 := by
  rw [re_integral_sourceZetaPairing_gaussian_eq hW hT]
  exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (integral_nonneg fun _ => by positivity))

end RHTower.WeilSingularArithmetic
