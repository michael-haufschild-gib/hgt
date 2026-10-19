import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailCombinationExplicitFormula

/-! Full signed coercivity of the zeta Weil form on the high-scale factorial tail span. The
physical Riesz bounds and the nonstationary Mellin bound exclude half of the Plancherel mass
from the band `|r| ≤ ηM`; the Gamma symbol is at least `log(ηM) - G₀` outside it and at least
`-(G₀ + log 2)` everywhere. With the exact explicit formula and the uniform polar and prime
budgets this gives `Re W(f_b, f_b) ≥ ((A/2) log M - C) ∑ ‖b_n‖²`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- **Split archimedean lower bound.** For a real test with integrable spectral density and
integrable Gamma-weighted density, and every `R > 0`,
`(1/2π) ∫ ‖F̂‖² G ≥ -(G₀ + log 2) E_{|r| ≤ R} + (log R - G₀) E_{|r| > R}` and
`(1/2π) ∫ ‖F̂‖² G ≥ -(G₀ + log 2) (E_{|r| ≤ R} + E_{|r| > R})`. -/
theorem archGammaEnergy_split_lower {F : ℝ → ℝ}
    (hmi : Integrable fun r : ℝ => ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2)
    (hDi : Integrable fun r : ℝ => ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * EF.gammaBracket r)
    {R : ℝ} (hR : 0 < R) :
    -(factorialSpanGammaOffset + Real.log 2) *
          (1 / (2 * Real.pi) * ∫ r in Icc (-R) R, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2) +
        (Real.log R - factorialSpanGammaOffset) *
          (1 / (2 * Real.pi) * ∫ r in (Icc (-R) R)ᶜ, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2) ≤
      archGammaEnergy F ∧
    -(factorialSpanGammaOffset + Real.log 2) *
        ((1 / (2 * Real.pi) * ∫ r in Icc (-R) R, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2) +
          (1 / (2 * Real.pi) * ∫ r in (Icc (-R) R)ᶜ, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2)) ≤
      archGammaEnergy F := by
  set m : ℝ → ℝ := fun r => ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 with hm
  set G0 := factorialSpanGammaOffset
  have hsplit := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hDi
  have hlow : -(G0 + Real.log 2) * ∫ r in Icc (-R) R, m r ≤
      ∫ r in Icc (-R) R, m r * EF.gammaBracket r := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hmi.integrableOn.const_mul _) hDi.integrableOn measurableSet_Icc
      fun r _ => ?_
    have h := gammaBracket_ge_neg_offset r
    have hm0 : 0 ≤ m r := sq_nonneg _
    nlinarith
  have hhigh : (Real.log R - G0) * ∫ r in (Icc (-R) R)ᶜ, m r ≤
      ∫ r in (Icc (-R) R)ᶜ, m r * EF.gammaBracket r := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hmi.integrableOn.const_mul _) hDi.integrableOn
      measurableSet_Icc.compl fun r hr => ?_
    have hrR : R ≤ |r| := by
      by_contra hlt
      push Not at hlt
      exact hr (abs_le.mp hlt.le)
    have h := gammaBracket_ge_log_of_le_abs hR hrR
    have hm0 : 0 ≤ m r := sq_nonneg _
    nlinarith
  have hglob : -(G0 + Real.log 2) * ∫ r in (Icc (-R) R)ᶜ, m r ≤
      ∫ r in (Icc (-R) R)ᶜ, m r * EF.gammaBracket r := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hmi.integrableOn.const_mul _) hDi.integrableOn
      measurableSet_Icc.compl fun r _ => ?_
    have h := gammaBracket_ge_neg_offset r
    have hm0 : 0 ≤ m r := sq_nonneg _
    nlinarith
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  unfold archGammaEnergy
  rw [← hsplit]
  constructor
  · nlinarith
  · nlinarith

/-- **Low-band exclusion.** For a real family supported on `n + 1 ≥ M ≥ 2`, the Plancherel
mass of the band `|r| ≤ ηM` is at most `(A/2) ∑ ‖b_n‖²`. -/
theorem factorialTailCombination_lowBand_energy_le (S : Finset ℕ) (d : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) :
    1 / (2 * Real.pi) * ∫ r in Icc
        (-(lowFreqRelativeCutoff factorialWeightedPhaseLower factorialLowFreqConstant * M))
        (lowFreqRelativeCutoff factorialWeightedPhaseLower factorialLowFreqConstant * M),
        ‖paperFT (fun x => (factorialTailCombination S d x : ℂ)) r‖ ^ 2 ≤
      (factorialWeightedPhaseLower / 2) *
        ∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2 := by
  set A := factorialWeightedPhaseLower
  set D := factorialLowFreqConstant
  set η := lowFreqRelativeCutoff A D
  set g := factorialTailCombination S d
  set b := factorialTailCombinationPhaseCoeff d
  set S0 := ∑ n ∈ S, ‖b n‖ ^ 2
  have hS0n : 0 ≤ S0 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hDpos : 0 < D := factorialLowFreqConstant_pos
  have hηpos : 0 < η := lowFreqRelativeCutoff_pos factorialWeightedPhaseLower_pos hDpos
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * (M : ℝ) with hR
  have hRpos : 0 < R := mul_pos hηpos hMpos
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have hspan : (fun x => (g x : ℂ)) = factorialSpanTest S b :=
    factorialTailCombination_ofReal_eq_spanTest S d
  have hFi := (integral_norm_sq_paperFT_factorialTailCombination S d).1
  have hpt : ∀ r ∈ Icc (-R) R, ‖paperFT (fun x => (g x : ℂ)) r‖ ^ 2 ≤ 2 * D ^ 2 / M * S0 := by
    intro r hr
    rw [hspan]
    refine norm_sq_paperFT_factorialSpanTest_le S b hM hS ?_
    have hηπ : η ≤ Real.pi := (min_le_right _ _).trans (min_le_left _ _)
    calc |r| ≤ R := abs_le.mpr hr
      _ ≤ Real.pi * M := mul_le_mul_of_nonneg_right hηπ hMpos.le
  have hint : (∫ r in Icc (-R) R, ‖paperFT (fun x => (g x : ℂ)) r‖ ^ 2) ≤
      (2 * R) * (2 * D ^ 2 / M * S0) := by
    calc (∫ r in Icc (-R) R, ‖paperFT (fun x => (g x : ℂ)) r‖ ^ 2) ≤
          ∫ _r in Icc (-R) R, 2 * D ^ 2 / M * S0 :=
          setIntegral_mono_on hFi.integrableOn (integrableOn_const (by simp))
            measurableSet_Icc hpt
      _ = (2 * R) * (2 * D ^ 2 / M * S0) := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          ring
  calc 1 / (2 * Real.pi) * (∫ r in Icc (-R) R, ‖paperFT (fun x => (g x : ℂ)) r‖ ^ 2) ≤
        1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * S0)) :=
        mul_le_mul_of_nonneg_left hint hpi.le
    _ = (1 / (2 * Real.pi)) * (2 * η * (M : ℝ)) * (2 * D ^ 2 * S0 / (M : ℝ)) := by
        rw [hR]
        ring
    _ ≤ (A / 2) * S0 := low_band_plancherel_energy_le_half_arch hDpos hS0n hM

/-- **High-scale Gamma coercivity.** For a real family supported on `n + 1 ≥ M ≥ 2`,
`(1/2π) ∫ ‖ĝ‖² G ≥ ((A/2) log M - B (G₀ + log 2) - (A/2) log(1/η)) ∑ ‖b_n‖²`. -/
theorem factorialTailCombination_archGammaEnergy_lower (S : Finset ℕ) (d : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) :
    ((factorialWeightedPhaseLower / 2) * Real.log M -
        factorialWeightedPhaseUpper * (factorialSpanGammaOffset + Real.log 2) -
        (factorialWeightedPhaseLower / 2) *
          Real.log (1 / lowFreqRelativeCutoff factorialWeightedPhaseLower
            factorialLowFreqConstant)) *
        (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2) ≤
      archGammaEnergy (factorialTailCombination S d) := by
  set A := factorialWeightedPhaseLower
  set D := factorialLowFreqConstant
  set η := lowFreqRelativeCutoff A D
  set g := factorialTailCombination S d with hg
  set b := factorialTailCombinationPhaseCoeff d
  set S0 := ∑ n ∈ S, ‖b n‖ ^ 2
  have hS0n : 0 ≤ S0 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hApos : 0 < A := factorialWeightedPhaseLower_pos
  have hηpos : 0 < η := lowFreqRelativeCutoff_pos hApos factorialLowFreqConstant_pos
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * (M : ℝ) with hR
  have hRpos : 0 < R := mul_pos hηpos hMpos
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  obtain ⟨hFi, hPl⟩ := integral_norm_sq_paperFT_factorialTailCombination S d
  set Elow := 1 / (2 * Real.pi) * ∫ r in Icc (-R) R, ‖paperFT (fun x => (g x : ℂ)) r‖ ^ 2
  set Ehigh := 1 / (2 * Real.pi) * ∫ r in (Icc (-R) R)ᶜ, ‖paperFT (fun x => (g x : ℂ)) r‖ ^ 2
  have htot : Elow + Ehigh = ∫ x : ℝ, ‖(g x : ℂ)‖ ^ 2 := by
    rw [← mul_add, integral_add_compl measurableSet_Icc hFi, hPl]
    field_simp
    rfl
  have hphys : (∫ x : ℝ, ‖(g x : ℂ)‖ ^ 2) =
      ∫ v in Ioi (1 : ℝ), v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2 := by
    have h := (integral_norm_sq_sum_factorialMuntzCorrectedTail S (fun n => (d n : ℂ))).2
    have e1 : (fun x => ‖(g x : ℂ)‖ ^ 2) = fun x =>
        ‖∑ n ∈ S, (d n : ℂ) * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2 := by
      funext x
      simp [hg, factorialTailCombination]
    rw [e1, h]
    rfl
  have hlo := factorialPhaseCombination_weighted_lower S b
  have hup := factorialPhaseCombination_weighted_upper S b (r := 1) le_rfl
  simp only [one_mul] at hup
  have hEhigh0 : 0 ≤ Ehigh := mul_nonneg hpi.le (integral_nonneg fun _ => sq_nonneg _)
  have hsplit := archGammaEnergy_split_lower hFi
    (integrable_norm_sq_paperFT_factorialTailCombination_mul_gammaBracket S d) hRpos
  exact high_scale_archimedean_log_coercivity hApos factorialSpanGammaOffset_nonneg hηpos hS0n hM
    hEhigh0 (by rw [htot, hphys]; exact hlo) (by rw [htot, hphys]; exact hup)
    (factorialTailCombination_lowBand_energy_le S d hM hS) hsplit.2 (fun _ => hsplit.1)

/-- The offset constant `C` of the span coercivity theorem. -/
def factorialSpanWeilOffset : ℝ :=
  factorialSpanCoercivityOffset factorialWeightedPhaseLower factorialWeightedPhaseUpper
    factorialSpanGammaOffset factorialUnitIntervalUpper factorialLowFreqConstant

theorem factorialSpanWeilOffset_nonneg : 0 ≤ factorialSpanWeilOffset := by
  unfold factorialSpanWeilOffset factorialSpanCoercivityOffset
  have hη := lowFreqRelativeCutoff_pos factorialWeightedPhaseLower_pos factorialLowFreqConstant_pos
  have hη1 := lowFreqRelativeCutoff_le_one factorialWeightedPhaseLower factorialLowFreqConstant
  have hlog : 0 ≤ Real.log (1 / lowFreqRelativeCutoff factorialWeightedPhaseLower
      factorialLowFreqConstant) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have h1 := factorialWeightedPhaseUpper_pos
  have h2 := factorialWeightedPhaseLower_pos
  have h3 := factorialUnitIntervalUpper_pos
  have h4 := factorialSpanGammaOffset_nonneg
  have h5 := canonicalPrimeMajorantConstant_nonneg
  have h6 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- **Coercivity on real tail combinations.** For a real family supported on `n + 1 ≥ M ≥ 2`,
`Re W(g, g) ≥ ((A/2) log M - C) ∑ ‖b_n‖²` with `b_n = d_n a_n`. -/
theorem factorialTailCombination_re_W_coercivity (S : Finset ℕ) (d : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) :
    ((factorialWeightedPhaseLower / 2) * Real.log M - factorialSpanWeilOffset) *
        (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2) ≤
      (zetaZeroConfig.W (fun x => (factorialTailCombination S d x : ℂ))
        (fun x => (factorialTailCombination S d x : ℂ))).re := by
  have hid := archPoleEnergy_factorialTailCombination S d
  rw [archPoleEnergy_eq_pole_add_gamma] at hid
  have hpol : |archPoleTerm (factorialTailCombination S d)| ≤
      6 * factorialUnitIntervalUpper *
        ∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2 := by
    rw [archPoleTerm, factorialTailCombination_ofReal_eq_spanTest S d]
    exact factorialSpanTest_polar_budget S _
  have hpri : |atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (crossCorr (factorialTailCombination S d) (factorialTailCombination S d))| ≤
      2 * factorialWeightedPhaseUpper * canonicalPrimeMajorantConstant *
        ∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2 :=
    (abs_atomPairing_factorialTailCombination_le S d).trans_eq (by ring)
  exact high_scale_span_weil_coercivity_bound (by linarith)
    (factorialTailCombination_archGammaEnergy_lower S d hM hS) hpol hpri

/-- **Full signed coercivity on the high-scale factorial tail span.** There are absolute
constants `c > 0` and `C ≥ 0` such that for every `M ≥ 2` and every finite complex family `b`
supported on `n + 1 ≥ M`, the combination `f_b = ∑_n (b_n / a_n) T_n` of literal correction
tails has an absolutely convergent zeta Weil sum and
`Re W(f_b, f_b) ≥ (c log M - C) ∑ ‖b_n‖²`. -/
theorem factorialTailSpan_re_W_coercivity :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M → ∀ (S : Finset ℕ) (b : ℕ → ℂ),
      (∀ n ∈ S, M ≤ n + 1) →
      Summable (fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand
        (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
          (factorialMuntzCorrectedTail n x : ℂ))
        (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
          (factorialMuntzCorrectedTail n x : ℂ)) ρ‖) ∧
      (c * Real.log M - C) * ∑ n ∈ S, ‖b n‖ ^ 2 ≤
        (zetaZeroConfig.W
          (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
            (factorialMuntzCorrectedTail n x : ℂ))
          (fun x => ∑ n ∈ S, b n / (factorialTailAmplitude n : ℂ) *
            (factorialMuntzCorrectedTail n x : ℂ))).re := by
  refine ⟨factorialWeightedPhaseLower / 2, half_pos factorialWeightedPhaseLower_pos,
    factorialSpanWeilOffset, factorialSpanWeilOffset_nonneg, fun M hM S b hS => ?_⟩
  set c : ℕ → ℂ := fun n => b n / (factorialTailAmplitude n : ℂ) with hc
  set du : ℕ → ℝ := fun n => (c n).re with hdu
  set dv : ℕ → ℝ := fun n => (c n).im with hdv
  have hF : (fun x => ∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)) =
      fun x => (factorialTailCombination S du x : ℂ) +
        Complex.I * (factorialTailCombination S dv x : ℂ) := by
    funext x
    simp only [factorialTailCombination]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    conv_lhs => rw [← Complex.re_add_im (c n)]
    ring
  have hint (dd : ℕ → ℝ) : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      Integrable fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
        (factorialTailCombination S dd x : ℂ) := fun s h0 _ =>
    (factorialTailCombinationSmoothed_readout S dd 0 (by linarith)).1
  obtain ⟨hZ, hW⟩ := zetaZeroConfig_W_ofReal_add_I_mul (factorialTailCombination S du)
    (factorialTailCombination S dv) (hint du) (hint dv)
    (factorialTailCombination_zeroSquare_summable S du)
    (factorialTailCombination_zeroSquare_summable S dv)
  rw [hF]
  refine ⟨summable_norm_Wsummand _ _ hZ hZ, ?_⟩
  rw [hW, Complex.add_re]
  have h1 := factorialTailCombination_re_W_coercivity S du hM hS
  have h2 := factorialTailCombination_re_W_coercivity S dv hM hS
  have hsum : (∑ n ∈ S, ‖b n‖ ^ 2) =
      (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff du n‖ ^ 2) +
        ∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff dv n‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have ha : (factorialTailAmplitude n : ℂ) ≠ 0 := by
      exact_mod_cast (factorialTailAmplitude_pos n).ne'
    have hb : b n = c n * (factorialTailAmplitude n : ℂ) := by
      rw [hc]
      exact (div_mul_cancel₀ (b n) ha).symm
    rw [hb, factorialTailCombinationPhaseCoeff, factorialTailCombinationPhaseCoeff, norm_mul,
      norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, mul_pow,
      mul_pow, mul_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [hdu, hdv, Real.norm_eq_abs, sq_abs]
    ring
  rw [hsum, mul_add]
  linarith

end

end GaloisForLFunctions.ArithmeticPositivityTheory
