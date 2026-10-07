import GaloisForLFunctions.RHTower.WeilWorkQuantizationSubpolynomial
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseThetaTrace

/-!
# Removing the pole of the actual forward Dirichlet series

Full positivity supplies a holomorphic regular part with subpower growth on
every strict inner strip. The residue is the actual completion at one.
-/

open Complex Set Filter MeasureTheory Topology GaloisForLFunctions

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity TruncatedRadial

/-- Pole subtraction for the actual forward coefficients. No boundary
continuity or coefficient sign is an input. -/
theorem exists_forward_regularPart {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → R s =
        LSeries (sourceCoeff lam) s - sourceCompletion hW 1 / (s - 1)) ∧
      ∀ q a : ℝ, 0 < q → 0 < a → ∃ K : ℝ, 0 ≤ K ∧
        ∀ s : ℂ, 1 / 2 + q ≤ s.re → s.re ≤ 2 →
          ‖R s‖ ≤ K * (2 + |s.im|) ^ a := by
  let A : ℂ → ℂ := fun s => sourceCompletion hW s / (s * Gammaℝ s)
  let R : ℂ → ℂ := dslope A 1
  have hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    change 1 / 2 < s.re at hs
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
    exact ((hasDerivAt_sourceCompletion hW hs).differentiableAt.div
      (differentiableAt_id.mul (differentiableAt_Gammaℝ (by linarith)))
      (mul_ne_zero hs0 (Gammaℝ_ne_zero_of_re_pos (by linarith)))).differentiableWithinAt
  have hA1 : A 1 = sourceCompletion hW 1 := by simp [A, Gammaℝ_one]
  have hRd : DifferentiableOn ℂ R {s : ℂ | 1 / 2 < s.re} :=
    (Complex.differentiableOn_dslope
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).mpr hAd
  have hRF (s : ℂ) (hs : s ≠ 1) :
      R s = prodF (quantizationCompletion hW) s - sourceCompletion hW 1 / (s - 1) := by
    rw [show R s = dslope A 1 s from rfl, dslope_of_ne _ hs, slope_def_module, hA1]
    change (s - 1)⁻¹ • (sourceCompletion hW s / (s * Gammaℝ s) - _) = _
    change (s - 1)⁻¹ * (sourceCompletion hW s / (s * Gammaℝ s) - _) =
      sourceCompletion hW s / (s * (s - 1) * Gammaℝ s) - _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨R, hRd, ?_, fun q a hq ha => ?_⟩
  · intro s hs
    have hs1 : s ≠ 1 := by intro h; simp [h] at hs
    rw [hRF s hs1, quantization_prodF_eq_zetaOf hW hs, (sourceCoeff_LSeries hW hs).2]
  · obtain ⟨C, hC, hF⟩ := exists_quantizationProdF_subpolynomial hW ha
    let L : ℝ := ∑' n : ℕ, ‖LSeries.term (sourceCoeff lam) (3 / 2) n‖
    have hL : 0 ≤ L := tsum_nonneg fun _ => norm_nonneg _
    have hsum := (sourceCoeff_LSeries hW (s := 3 / 2) (by norm_num)).1.norm
    have hFL (s : ℂ) (hs : 3 / 2 ≤ s.re) :
        ‖prodF (quantizationCompletion hW) s‖ ≤ L := by
      rw [quantization_prodF_eq_zetaOf hW (by linarith),
        ← (sourceCoeff_LSeries hW (by linarith : 1 < s.re)).2, LSeries]
      have hss := LSeriesSummable.of_re_le_re (by simpa using hs)
        (sourceCoeff_LSeries hW (s := 3 / 2) (by norm_num)).1
      exact (norm_tsum_le_tsum_norm hss.norm).trans
        (Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _
          (by simpa using hs) n) hss.norm hsum)
    let S : Set ℂ := Icc (1 / 2 + q : ℝ) 2 ×ℂ Icc (-2 : ℝ) 2
    have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
    have hsub : S ⊆ {s : ℂ | 1 / 2 < s.re} := by
      intro s hs
      have := (Complex.mem_reProdIm.mp hs).1.1
      change 1 / 2 < s.re
      linarith
    obtain ⟨D, hD⟩ := hSc.exists_bound_of_continuousOn (hRd.continuousOn.mono hsub)
    let K : ℝ := max D 0 + max C L + ‖sourceCompletion hW 1‖
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨K, hK, fun s hs hs2 => ?_⟩
    have hp : 1 ≤ (2 + |s.im|) ^ a := Real.one_le_rpow
      (by linarith [abs_nonneg s.im]) ha.le
    by_cases him : |s.im| ≤ 2
    · have hmem : s ∈ S := Complex.mem_reProdIm.mpr ⟨⟨hs, hs2⟩, abs_le.mp him⟩
      calc ‖R s‖ ≤ D := hD s hmem
        _ ≤ K := by
          dsimp [K]
          linarith [le_max_left D 0, le_max_left C L, norm_nonneg (sourceCompletion hW 1)]
        _ ≤ K * (2 + |s.im|) ^ a := le_mul_of_one_le_right hK hp
    · have him2 : 2 ≤ |s.im| := (lt_of_not_ge him).le
      have hs1 : s ≠ 1 := by intro h; norm_num [h] at him2
      have hden : 1 ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
        linarith
      have hpo : ‖sourceCompletion hW 1 / (s - 1)‖ ≤ ‖sourceCompletion hW 1‖ := by
        rw [norm_div]
        exact div_le_self (norm_nonneg _) hden
      have hFb : ‖prodF (quantizationCompletion hW) s‖ ≤
          max C L * (2 + |s.im|) ^ a := by
        by_cases hre : s.re ≤ 3 / 2
        · have hb := hF s.re s.im (by linarith) hre him2
          rw [Complex.re_add_im] at hb
          exact hb.trans (mul_le_mul (le_max_left C L)
            (Real.rpow_le_rpow (by positivity) (by linarith) ha.le)
            (by positivity) (le_max_of_le_left hC))
        · exact (hFL s (le_of_not_ge hre)).trans
            ((le_max_right C L).trans
              (le_mul_of_one_le_right (le_max_of_le_right hL) hp))
      rw [hRF s hs1]
      calc _ ≤ ‖prodF (quantizationCompletion hW) s‖ +
            ‖sourceCompletion hW 1 / (s - 1)‖ := norm_sub_le _ _
        _ ≤ max C L * (2 + |s.im|) ^ a + ‖sourceCompletion hW 1‖ := add_le_add hFb hpo
        _ ≤ K * (2 + |s.im|) ^ a := by
          have hb := mul_le_mul_of_nonneg_left hp (norm_nonneg (sourceCompletion hW 1))
          have hd := mul_nonneg (le_max_right D 0)
            (Real.rpow_nonneg (by positivity : 0 ≤ 2 + |s.im|) a)
          dsimp [K]
          nlinarith

end RHTower.WeilWorkSettledPhase
